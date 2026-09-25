import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import Lake.Toml
import Lake.Util.Message
import Lean

theorem classification_finite_simple_groups (G : Type) [Group G] [Finite G] [IsSimpleGroup G] :
    ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group) := by
  sorry
