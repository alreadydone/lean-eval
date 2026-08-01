import ChallengeDeps
import Submission

open LeanEval.Analysis.TenMartini
open Set

theorem ten_martini_problem (α coupling θ : ℝ)
    (hα : Irrational α) (hcoupling : coupling ≠ 0) :
    ∃ H : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α coupling θ H ∧
        (spectrum ℂ H).Nonempty ∧
        IsCompact (spectrum ℂ H) ∧
        Perfect (spectrum ℂ H) ∧
        IsTotallyDisconnected (spectrum ℂ H) := by
  exact Submission.ten_martini_problem α coupling θ hα hcoupling
