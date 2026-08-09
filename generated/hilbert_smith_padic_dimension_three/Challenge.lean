import Mathlib

theorem hilbert_smith_padic_dimension_three (p : ℕ) [Fact p.Prime]
    (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [AddAction (PadicInt p) M] [ContinuousVAdd (PadicInt p) M]
    [FaithfulVAdd (PadicInt p) M] :
    False := by
  sorry
