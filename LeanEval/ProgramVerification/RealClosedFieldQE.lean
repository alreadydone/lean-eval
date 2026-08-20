import Mathlib.Data.Real.Basic
import EvalTools.Markers

/-!
# Quantifier elimination for real closed fields

## The task

Work in the first-order language of ordered rings: `Term`s are built from variables, integer
constants, `+`, `*` and `-`, and `Formula`s are built from the atoms `<` and `=` using `⊥`, `→`
and `∀`. `Formula.Holds` interprets a formula in `ℝ` under an environment assigning a real to
each variable, and `Formula.IsQF` says that a formula contains no quantifier.

Implement `qe`, which converts an arbitrary formula into an equivalent quantifier-free one, and
prove that it does. `isQF_qe` says the output contains no quantifier. `holds_qe` says the input
and the output are satisfied by exactly the same environments; because it quantifies over every
environment, it also forces `qe` to respect free variables, so no separate condition on those is
needed.

For example, `∃ x. x * x = a` has the de Bruijn form

    Formula.ex (.eq (.mul (.var 0) (.var 0)) (.var 1))

with `a` free, and `qe` must return something equivalent to `¬ (a < 0)`, such as

    Formula.not (.lt (.var 0) (.const 0))

This is the point at which real closedness does the work: the equivalence fails over `ℚ`.

Tarski proved that such a `qe` exists, which is what makes the theory decidable: to decide a
sentence, run `qe` and evaluate the resulting closed quantifier-free formula. Cohen-Hörmander is
the route with the smallest formalization footprint, and cylindrical algebraic decomposition is
what is used in practice but has never been formalized in any system.

The problem is posed over `ℝ` for concreteness. Tarski's theorem holds over an arbitrary real
closed field, and generalising `holds_qe` in that direction would be a strictly harder problem.

## Design notes

The trusted vocabulary is deliberately small and purely syntactic. Variables are raw de Bruijn
indices and environments are total functions `Nat → ℝ`, so there is no well-scopedness
bookkeeping to do.

`isQF_qe` and `holds_qe` are jointly load-bearing and neither can be dropped:

* with only `isQF_qe`, take `qe := fun _ => .fals`;
* with only `holds_qe`, take `qe := id`.

There is no enumeration route, because the quantifiers range over `ℝ`, and no `Classical.choice`
route, because the existence proof one would have to exhibit in order to choose from it is
Tarski's theorem itself.

A decision procedure `valid? : Formula → Bool` with `valid? φ = true ↔ ∀ env, φ.Holds env` was
considered as a further hole and rejected: `noncomputable def valid? φ := decide (∀ env,
φ.Holds env)` satisfies it with a one-line proof. Declaring it a plain `def` does make Lean
reject that, but `noncomputable` is recorded in a separate environment extension rather than in
the `ConstantInfo`, so a checker comparing name, type, universe levels and safety will not see
the difference.
-/

namespace LeanEval
namespace ProgramVerification
namespace RealClosedFieldQE

/-! ## Syntax -/

/-- Terms in the language of ordered rings, with de Bruijn variables. -/
inductive Term where
  | var : Nat → Term
  | const : Int → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | neg : Term → Term
  deriving DecidableEq, Repr, Inhabited

/--
Formulas in the language of ordered rings. The connectives are the minimal set
`⊥`, `→`, `∀`; the usual derived connectives are provided as abbreviations below.
-/
inductive Formula where
  | lt : Term → Term → Formula
  | eq : Term → Term → Formula
  /-- Falsity. -/
  | fals : Formula
  | imp : Formula → Formula → Formula
  /-- Universal quantification; binds de Bruijn index `0` in the body. -/
  | all : Formula → Formula
  deriving DecidableEq, Repr, Inhabited

namespace Formula

/-- Negation. -/
def not (φ : Formula) : Formula := .imp φ .fals

/-- Truth. -/
def tru : Formula := .not .fals

/-- Disjunction. -/
def or (φ ψ : Formula) : Formula := .imp φ.not ψ

/-- Conjunction. -/
def and (φ ψ : Formula) : Formula := (φ.imp ψ.not).not

/-- Existential quantification; binds de Bruijn index `0` in the body. -/
def ex (φ : Formula) : Formula := φ.not.all.not

end Formula

/-! ## Semantics -/

/-- Extend an environment, binding de Bruijn index `0` to `x`. -/
def cons (x : ℝ) (env : Nat → ℝ) : Nat → ℝ
  | 0 => x
  | i + 1 => env i

/-- Interpretation of a term in `ℝ`. -/
def Term.eval (env : Nat → ℝ) : Term → ℝ
  | .var i => env i
  | .const k => (k : ℝ)
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -a.eval env

/-- Satisfaction of a formula in `ℝ` under an environment. -/
def Formula.Holds (env : Nat → ℝ) : Formula → Prop
  | .lt a b => a.eval env < b.eval env
  | .eq a b => a.eval env = b.eval env
  | .fals => False
  | .imp φ ψ => φ.Holds env → ψ.Holds env
  | .all φ => ∀ x : ℝ, φ.Holds (cons x env)

/-- A formula is quantifier free if it contains no `Formula.all`. -/
def Formula.IsQF : Formula → Prop
  | .lt _ _ => True
  | .eq _ _ => True
  | .fals => True
  | .imp φ ψ => φ.IsQF ∧ ψ.IsQF
  | .all _ => False

/-! ## The problem -/

/--
Quantifier elimination: `qe φ` is a quantifier-free formula equivalent to `φ` over `ℝ`,
in the same free variables.
-/
@[eval_problem]
def qe (φ : Formula) : Formula := sorry

/-- The output of `qe` is quantifier free. -/
@[eval_problem]
theorem isQF_qe (φ : Formula) : (qe φ).IsQF := sorry

/-- The output of `qe` is equivalent to its input, under every environment. -/
@[eval_problem]
theorem holds_qe (φ : Formula) (env : Nat → ℝ) :
    (qe φ).Holds env ↔ φ.Holds env := sorry

end RealClosedFieldQE
end ProgramVerification
end LeanEval
