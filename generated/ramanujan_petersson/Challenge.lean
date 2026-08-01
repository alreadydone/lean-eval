import ChallengeDeps

open LeanEval.NumberTheory.RamanujanTauProblem
open ModularForm UpperHalfPlane

theorem ramanujan_petersson :
    ∀ p : ℕ, Prime p → ‖τ p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2) := by
  sorry
