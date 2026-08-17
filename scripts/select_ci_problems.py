#!/usr/bin/env python3
"""Select and shard the catalog work needed for a CI change.

Pull requests validate changed problem modules and every manifest root that
imports them, transitively.  Changes to shared generator/infrastructure inputs
are conservative full-catalog sentinels.  Pushes validate the full catalog.

The script deliberately has no third-party dependencies so the classify job
can run before installing Lean or restoring the Mathlib cache.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import pathlib
import re
import subprocess
import sys
import tomllib
from collections import defaultdict, deque
from collections.abc import Iterable, Sequence


IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*(?:--.*)?$")
PROBLEM_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")
ZERO_SHA = "0" * 40


@dataclasses.dataclass(frozen=True)
class Problem:
    id: str
    module: str


@dataclasses.dataclass(frozen=True)
class Change:
    status: str
    paths: tuple[str, ...]


@dataclasses.dataclass(frozen=True)
class Selection:
    mode: str
    reasons: tuple[str, ...]
    problems: tuple[str, ...]
    modules: tuple[str, ...]
    source_changed: bool
    generated_changed: bool
    run_checks: bool

    @property
    def run_catalog(self) -> bool:
        return bool(self.problems)


def load_problems(root: pathlib.Path) -> tuple[Problem, ...]:
    problems: list[Problem] = []
    seen_ids: set[str] = set()
    for path in sorted((root / "manifests" / "problems").glob("*.toml")):
        data = tomllib.loads(path.read_text(encoding="utf-8"))
        problem_id = data["id"]
        module = data["module"]
        if problem_id != path.stem or PROBLEM_ID_RE.fullmatch(problem_id) is None:
            raise ValueError(f"unsafe or mismatched problem id in {path}: {problem_id!r}")
        if problem_id in seen_ids:
            raise ValueError(f"duplicate problem id in CI selector: {problem_id}")
        if not module.startswith("LeanEval.") or any(char in module for char in ",\r\n"):
            raise ValueError(f"unsafe problem module in {path}: {module!r}")
        seen_ids.add(problem_id)
        problems.append(Problem(id=problem_id, module=module))
    return tuple(problems)


def module_name_for_path(path: pathlib.Path, source_root: pathlib.Path) -> str:
    relative = path.relative_to(source_root)
    parts = list(relative.parts)
    parts[-1] = pathlib.Path(parts[-1]).stem
    if any("." in part or not part for part in parts):
        raise ValueError(f"cannot safely derive a Lean module name from {relative}")
    return ".".join((source_root.name, *parts))


def load_import_graph(root: pathlib.Path) -> tuple[dict[str, str], dict[str, set[str]]]:
    source_root = root / "LeanEval"
    paths: dict[str, str] = {}
    imports: dict[str, set[str]] = {}
    for path in sorted(source_root.rglob("*.lean")):
        module = module_name_for_path(path, source_root)
        relative = path.relative_to(root).as_posix()
        paths[relative] = module
        local_imports: set[str] = set()
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.lstrip().startswith("import "):
                continue
            match = IMPORT_RE.match(line)
            if match is None:
                raise ValueError(f"cannot safely parse import line in {relative}: {line!r}")
            imported = match.group(1)
            if imported.startswith("LeanEval."):
                local_imports.add(imported)
        imports[module] = local_imports
    return paths, imports


def git_changes(root: pathlib.Path, base: str, head: str) -> tuple[Change, ...]:
    if base == ZERO_SHA:
        return (Change("A", ("<initial-push>",)),)
    result = subprocess.run(
        ["git", "diff", "--name-status", "--find-renames", f"{base}..{head}"],
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    changes: list[Change] = []
    for line in result.stdout.splitlines():
        fields = line.split("\t")
        if len(fields) < 2:
            raise ValueError(f"unexpected git diff record: {line!r}")
        changes.append(Change(fields[0], tuple(fields[1:])))
    return tuple(changes)


def reverse_dependants(imports: dict[str, set[str]], changed: Iterable[str]) -> set[str]:
    reverse: dict[str, set[str]] = defaultdict(set)
    for module, dependencies in imports.items():
        for dependency in dependencies:
            reverse[dependency].add(module)
    reached = set(changed)
    queue = deque(changed)
    while queue:
        dependency = queue.popleft()
        for dependant in reverse.get(dependency, ()):
            if dependant not in reached:
                reached.add(dependant)
                queue.append(dependant)
    return reached


def is_full_catalog_sentinel(path: str) -> bool:
    return (
        path.startswith("EvalTools/")
        or path.startswith("templates/")
        or path.startswith(".github/actions/")
        or path == ".github/workflows/ci.yml"
        or path == "scripts/select_ci_problems.py"
        or path in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    )


def select(
    root: pathlib.Path,
    event: str,
    changes: Sequence[Change],
    problems: Sequence[Problem] | None = None,
    graph: tuple[dict[str, str], dict[str, set[str]]] | None = None,
) -> Selection:
    problems = tuple(problems if problems is not None else load_problems(root))
    by_id = {problem.id: problem for problem in problems}
    by_module: dict[str, set[str]] = defaultdict(set)
    for problem in problems:
        by_module[problem.module].add(problem.id)

    changed_paths = [path for change in changes for path in change.paths]
    source_changed = any(
        path.startswith(("LeanEval/", "EvalTools/", "templates/", "manifests/problems/"))
        or path in {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        for path in changed_paths
    )
    generated_changed = any(path.startswith("generated/") for path in changed_paths)
    infrastructure_changed = any(
        path.startswith((".github/workflows/", ".github/actions/", "scripts/", "tests/"))
        for path in changed_paths
    )
    run_checks = source_changed or generated_changed or infrastructure_changed

    all_ids = tuple(sorted(by_id))
    all_modules = tuple(sorted(by_module))
    if event == "push":
        return Selection(
            "full", ("push to main",), all_ids, all_modules,
            source_changed, generated_changed, run_checks,
        )

    sentinel_paths = sorted({path for path in changed_paths if is_full_catalog_sentinel(path)})
    destructive = [
        change
        for change in changes
        if change.status.startswith(("D", "R"))
        and any(
            path.startswith(("LeanEval/", "manifests/problems/"))
            for path in change.paths
        )
    ]
    if sentinel_paths or destructive:
        reasons = []
        if sentinel_paths:
            reasons.append("full-catalog sentinel: " + ", ".join(sentinel_paths))
        if destructive:
            reasons.append("deleted or renamed path")
        return Selection(
            "full", tuple(reasons), all_ids, all_modules,
            source_changed, generated_changed, run_checks,
        )

    selected_ids: set[str] = set()
    changed_source_paths: set[str] = set()
    reasons: list[str] = []
    for path in changed_paths:
        if path.startswith("manifests/problems/"):
            if path.endswith(".toml"):
                problem_id = pathlib.PurePosixPath(path).stem
                if problem_id in by_id:
                    selected_ids.add(problem_id)
                    reasons.append(f"manifest {problem_id}")
        elif path.startswith("generated/"):
            parts = pathlib.PurePosixPath(path).parts
            if len(parts) >= 2 and parts[1] in by_id:
                selected_ids.add(parts[1])
                reasons.append(f"generated workspace {parts[1]}")
        elif path.startswith("LeanEval/") and path.endswith(".lean"):
            changed_source_paths.add(path)

    if changed_source_paths:
        try:
            path_modules, imports = graph if graph is not None else load_import_graph(root)
        except ValueError as error:
            return Selection(
                "full", (f"import graph fallback: {error}",), all_ids, all_modules,
                source_changed, generated_changed, run_checks,
            )
        missing = sorted(changed_source_paths - path_modules.keys())
        if missing:
            return Selection(
                "full", ("changed source missing from graph: " + ", ".join(missing),),
                all_ids, all_modules, source_changed, generated_changed, run_checks,
            )
        changed_modules = {path_modules[path] for path in changed_source_paths}
        affected_modules = reverse_dependants(imports, changed_modules)
        affected_roots = affected_modules & by_module.keys()
        for module in affected_roots:
            selected_ids.update(by_module[module])
        reasons.append(
            f"{len(changed_modules)} changed module(s), {len(affected_roots)} affected manifest root(s)"
        )

    # Keep all problems sharing a selected module together.  Inventory
    # validation is module-scoped, so splitting such entries would make tagged
    # declarations from the other half look untracked.
    selected_modules = {by_id[problem_id].module for problem_id in selected_ids}
    for module in selected_modules:
        selected_ids.update(by_module[module])

    return Selection(
        "targeted" if selected_ids else "none",
        tuple(dict.fromkeys(reasons)),
        tuple(sorted(selected_ids)),
        tuple(sorted(selected_modules)),
        source_changed,
        generated_changed,
        run_checks,
    )


def make_matrix(selection: Selection, problems: Sequence[Problem], shard_limit: int) -> dict:
    by_module: dict[str, list[str]] = defaultdict(list)
    selected = set(selection.problems)
    for problem in problems:
        if problem.id in selected:
            by_module[problem.module].append(problem.id)
    if not by_module:
        # GitHub validates a matrix before evaluating the job-level `if`.
        return {"include": [{"shard": 0, "shard_count": 1, "problems": "", "modules": ""}]}

    shard_count = min(shard_limit, len(by_module))
    shards: list[list[str]] = [[] for _ in range(shard_count)]
    weights = [0] * shard_count
    for module, module_problems in sorted(by_module.items(), key=lambda item: (-len(item[1]), item[0])):
        shard = min(range(shard_count), key=lambda index: (weights[index], index))
        shards[shard].append(module)
        weights[shard] += len(module_problems)

    include = []
    for index, modules in enumerate(shards):
        modules.sort()
        problem_ids = sorted(problem for module in modules for problem in by_module[module])
        include.append({
            "shard": index,
            "shard_count": shard_count,
            "problems": ",".join(problem_ids),
            "modules": ",".join(modules),
        })
    return {"include": include}


def write_github_output(path: pathlib.Path, selection: Selection, matrix: dict) -> None:
    values = {
        "source_changed": str(selection.source_changed).lower(),
        "generated_changed": str(selection.generated_changed).lower(),
        "run_checks": str(selection.run_checks).lower(),
        "run_catalog": str(selection.run_catalog).lower(),
        "selection_mode": selection.mode,
        "selected_problem_count": str(len(selection.problems)),
        "selected_modules": ",".join(selection.modules),
        "matrix": json.dumps(matrix, separators=(",", ":")),
    }
    with path.open("a", encoding="utf-8") as output:
        for key, value in values.items():
            output.write(f"{key}={value}\n")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=pathlib.Path, default=pathlib.Path("."))
    parser.add_argument("--event", choices=("push", "pull_request"), required=True)
    parser.add_argument("--base", required=True)
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--shards", type=int, default=8)
    parser.add_argument("--github-output", type=pathlib.Path)
    args = parser.parse_args(argv)
    if args.shards <= 0:
        parser.error("--shards must be positive")
    root = args.root.resolve()
    problems = load_problems(root)
    changes = git_changes(root, args.base, args.head)
    selection = select(root, args.event, changes, problems)
    matrix = make_matrix(selection, problems, args.shards)
    print(
        f"Catalog selection: {selection.mode}; {len(selection.problems)} problem(s), "
        f"{len(selection.modules)} module(s)"
    )
    for reason in selection.reasons:
        print(f"  - {reason}")
    if args.github_output is not None:
        write_github_output(args.github_output, selection, matrix)
    else:
        print(json.dumps(matrix, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
