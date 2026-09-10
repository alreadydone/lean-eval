import Mathlib
import EvalTools.Markers

/-!
# Aperiodic monotiles

References:

David Smith, Joseph Samuel Myers, Craig S. Kaplan, Chaim Goodman-Strauss.
An aperiodic monotile, https://arxiv.org/abs/2303.10798
A chiral aperiodic monotile, https://arxiv.org/abs/2305.17743
-/

namespace LeanEval.Geometry.AperiodicMonotiles

/-- A topological tiling of a topological space is a collection of subsets (tiles) with
pairwise disjoint interiors such that the union of the closures is the whole space. -/
structure TopologicalTiling (X : Type*) [TopologicalSpace X] : Type _ where
  sets : Set (Set X)
  disjoint : sets.Pairwise fun s t ↦ Disjoint (interior s) (interior t)
  union_eq_univ : ⋃₀ (closure '' sets) = .univ

/-- A tiling of a metric space X by another metric space T is a topological tiling in
which all tiles are isometric copies of T. -/
structure TilingBy (T X : Type*) [PseudoEMetricSpace T] [PseudoEMetricSpace X]
    extends TopologicalTiling X where
  isometry : ∀ s ∈ sets, ∃ f : T → X, Isometry f ∧ s = .range f

/-- The vectors from one boundary vertex to the next (in counterclockwise order)
of the tile Tile(a,b) defined in the paper. -/
noncomputable def vec (a b : NNReal) : Fin 13 → ℝ × ℝ :=
  ![a • (2,0), a • (1,√3) / 2, b • (√3,-1) / 2, b • (√3,1) / 2, a • (-1,√3) / 2, a • (-1,0),
    b • (0,1), b • (-√3,1) / 2, a • (-1,-√3) / 2, a • (-1,0), b • (0,-1), b • (-√3,-1) / 2,
    a • (1,-√3) / 2]

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Construct a point in the Euclidean plane from a pair of real numbers. -/
def toPlane (x : ℝ × ℝ) : Plane := .toLp (p := 2) ![x.1, x.2]

/-- The boundary vertices (in counterclockwise order) of Tile(a,b). -/
noncomputable def vertex (a b : NNReal) (i : Fin 13) : Plane :=
  toPlane <| ∑ j ∈ Finset.Ioi i, vec a b j

/-- The boundary polygon of Tile(a,b). -/
def polygon (a b : NNReal) : Set Plane :=
  ⋃ i : ZMod 13, convexHull ℝ {vertex a b i, vertex a b (i + 1 : ZMod 13)}

/-- The tile Tile(a,b), which is the closure of the bounded component of the complement of
the boundary polygon. Notice that (a, √3/2*a) always lies in the bounded component. -/
def tile (a b : NNReal) : Set Plane :=
  closure <| connectedComponentIn (polygon a b)ᶜ (.toLp (p := 2) ![a, √3/2*a])

/-- A chiral tiling of the Euclidean plane by Tile(a,b) consists of tiles that are images
of Tile(a,b) under orientation preserving isometries of the plane. -/
structure ChiralTilingBy (a b : NNReal) extends TopologicalTiling Plane where
  isometry : ∀ s ∈ sets, ∃ f : Plane →ᵃ[ℝ] Plane, Isometry f ∧ f.linear.det = 1 ∧ s = f '' tile a b

/-- A collection of sets is aperiodic if it is not invariant under any nontrivial translation. -/
def IsAperiodic {X : Type*} [AddZeroClass X] (S : Set (Set X)) : Prop :=
  ∀ x : X, (Set.image (· + x)) '' S = S → x = 0

/-- The main theorem of *An aperiodic monotile*: if a and b are distinct positive real numbers,
then the Euclidean plane admits tilings by Tile(a,b), but only aperiodic ones. -/
@[eval_problem]
theorem isAperiodic_tilingBy (a b : NNReal) (ha : a ≠ 0) (hb : b ≠ 0) (ne : a ≠ b) :
    Nonempty (TilingBy (tile a b) Plane) ∧
    ∀ t : TilingBy (tile a b) Plane, IsAperiodic t.sets := by
  sorry

/-- One of the main theorem of *A chiral aperiodic monotile*: the Euclidean plane admits chiral
tilings by Tile(1,1), but only aperiodic ones. -/
@[eval_problem]
theorem isAperiodic_chiralTilingBy :
    Nonempty (ChiralTilingBy 1 1) ∧ ∀ t : ChiralTilingBy 1 1, IsAperiodic t.sets := by
  sorry

end LeanEval.Geometry.AperiodicMonotiles
