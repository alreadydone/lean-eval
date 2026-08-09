import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis.TenMartini
open Set

namespace Submission

theorem ten_martini_problem (α coupling θ : ℝ)
    (hα : Irrational α) (hcoupling : coupling ≠ 0) :
    ∃ H : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α coupling θ H ∧
        (spectrum ℂ H).Nonempty ∧
        IsCompact (spectrum ℂ H) ∧
        Perfect (spectrum ℂ H) ∧
        IsTotallyDisconnected (spectrum ℂ H) := by
  sorry

end Submission
