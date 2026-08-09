import ChallengeDeps
import Submission.Helpers

open LeanEval.NumberTheory.RamanujanTauProblem
open ModularForm UpperHalfPlane

namespace Submission

theorem ramanujan_petersson :
    ∀ p : ℕ, Prime p → ‖τ p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by
  sorry

end Submission
