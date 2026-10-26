/-
Connected components, cycle rank and region predicates on the clique expansion of a
hypergraph.

The module defines `spatialB0`, the number of connected components of `H.toSimpleGraph`,
and `firstBettiZ = #hyperedges − #vertices + spatialB0` in ℤ, with lower bounds for both.
It defines region membership, the spatial diameter, a boundedness predicate, four
openness predicates on vertex sets, and the family of geodesic balls at a vertex, with
elementary lemmas about each. No relation between `firstBettiZ` and a Hodge Laplacian is
proved here.
-/

import InfraFormalization.HypergraphDistance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Connected components of the clique expansion -/

/-- The connected components of `H.toSimpleGraph`: the quotient of `V` by
reachability. -/
noncomputable abbrev SpatialConnectedComponent (H : Hypergraph V) : Type _ :=
  H.toSimpleGraph.ConnectedComponent

/-- The number of connected components of `H.toSimpleGraph`. -/
noncomputable def spatialB0 (H : Hypergraph V) : ℕ :=
  Fintype.card H.SpatialConnectedComponent

/-- `H.toSimpleGraph` is connected. -/
def IsSpatiallyConnected (H : Hypergraph V) : Prop :=
  H.toSimpleGraph.Connected

/-- `spatialB0 H ≤ |V|`. The proof uses surjectivity of the map from a vertex to its
component. -/
theorem spatialB0_le_card (H : Hypergraph V) :
    H.spatialB0 ≤ Fintype.card V := by
  unfold spatialB0 SpatialConnectedComponent
  exact Fintype.card_le_of_surjective
    (fun v => H.toSimpleGraph.connectedComponentMk v)
    (fun c => Quot.exists_rep c)

/-! ## Cycle rank

For a finite graph the cycle rank is `#edges − #vertices + #components`. Here the edge
count is the number of hyperedges `H.size`, counted with multiplicity, and the value is
taken in ℤ. This differs from the cycle rank of `H.toSimpleGraph`, whose edge count is
`H.toSimpleGraph.edgeFinset.card`.
-/

/-- `H.size − |V| + spatialB0 H`, computed in ℤ. -/
noncomputable def firstBettiZ (H : Hypergraph V) : ℤ :=
  (H.size : ℤ) - (Fintype.card V : ℤ) + (H.spatialB0 : ℤ)

/-- `H.size − |V| ≤ firstBettiZ H`. -/
theorem firstBettiZ_lower_bound (H : Hypergraph V) :
    (H.size : ℤ) - (Fintype.card V : ℤ) ≤ H.firstBettiZ := by
  unfold firstBettiZ
  have : (0 : ℤ) ≤ (H.spatialB0 : ℤ) := Int.natCast_nonneg _
  linarith

/-- If `V` is nonempty, `0 < spatialB0 H`. -/
theorem spatialB0_pos_of_nonempty [Nonempty V] (H : Hypergraph V) :
    0 < H.spatialB0 := by
  unfold spatialB0 SpatialConnectedComponent
  exact Fintype.card_pos

/-! ## Region membership

Regions are values of `Finset V`. The regions `infraSphere`, `infraDisk`, `perpBisector`
and `voronoiCell` of `HypergraphDistance.lean` are filters of `Finset.univ` by
conditions on `Hypergraph.dist`. -/

/-- `v ∈ R` for `R : Finset V`. Membership is decidable through `Finset.decidableMem`. -/
abbrev IsInRegion (v : V) (R : Finset V) : Prop := v ∈ R

instance (v : V) (R : Finset V) : Decidable (IsInRegion v R) :=
  inferInstanceAs (Decidable (v ∈ R))

/-- `v ∈ infraDisk O r` iff `dist O v ≤ r`. -/
theorem isInRegion_infraDisk_iff (H : Hypergraph V) (v O : V) (r : ℕ) :
    IsInRegion v (H.infraDisk O r) ↔ H.dist O v ≤ r := by
  unfold IsInRegion Hypergraph.infraDisk Hypergraph.geodesicBall
  simp [Finset.mem_filter]

/-- `v ∈ infraSphere O r` iff `dist O v = r`. -/
theorem isInRegion_infraSphere_iff (H : Hypergraph V) (v O : V) (r : ℕ) :
    IsInRegion v (H.infraSphere O r) ↔ H.dist O v = r := by
  unfold IsInRegion Hypergraph.infraSphere
  simp [Finset.mem_filter]

/-- `v ∈ perpBisector A B` iff `dist A v = dist B v`. -/
theorem isInRegion_perpBisector_iff (H : Hypergraph V) (v A B : V) :
    IsInRegion v (H.perpBisector A B) ↔ H.dist A v = H.dist B v := by
  unfold IsInRegion
  exact H.mem_perpBisector A B v

/-! ## Diameter and boundedness -/

/-- The maximum of `H.dist u v` over all pairs of vertices. Pairs in different components
contribute `0`. -/
noncomputable def spatialDiameter (H : Hypergraph V) : ℕ :=
  Finset.univ.sup (fun u : V => Finset.univ.sup (fun v : V => H.dist u v))

/-- `H.dist u v ≤ spatialDiameter H` for all `u, v`. -/
theorem dist_le_spatialDiameter (H : Hypergraph V) (u v : V) :
    H.dist u v ≤ H.spatialDiameter := by
  unfold spatialDiameter
  calc H.dist u v
      ≤ Finset.univ.sup (fun v' : V => H.dist u v') :=
        Finset.le_sup (f := fun v' => H.dist u v') (Finset.mem_univ v)
    _ ≤ Finset.univ.sup (fun u' : V => Finset.univ.sup (fun v' => H.dist u' v')) :=
        Finset.le_sup (f := fun u' => Finset.univ.sup (fun v' => H.dist u' v'))
          (Finset.mem_univ u)

/-! ## Openness predicates

Four predicates on `Finset V`. No `TopologicalSpace V` instance is constructed. -/

/-- Every neighbour in `H.Adj` of a vertex of `R` lies in `R`. -/
def IsAlexandrovOpen (H : Hypergraph V) (R : Finset V) : Prop :=
  ∀ (u v : V), u ∈ R → H.Adj u v → v ∈ R

/-- Every vertex `v` with `H.dist u v ≤ r` for some `u ∈ R` lies in `R`. -/
def IsVRScaleOpen (H : Hypergraph V) (r : ℕ) (R : Finset V) : Prop :=
  ∀ (u v : V), u ∈ R → H.dist u v ≤ r → v ∈ R

/-- `Finset.univ` satisfies `IsAlexandrovOpen`. -/
theorem isAlexandrovOpen_univ (H : Hypergraph V) :
    H.IsAlexandrovOpen Finset.univ := by
  intros u v _ _
  exact Finset.mem_univ _

/-- `Finset.univ` satisfies `IsVRScaleOpen r` for every `r`. -/
theorem isVRScaleOpen_univ (H : Hypergraph V) (r : ℕ) :
    H.IsVRScaleOpen r Finset.univ := by
  intros u v _ _
  exact Finset.mem_univ _

/-! ## Geodesic balls at a vertex -/

/-- The family `r ↦ geodesicBall v r`. -/
noncomputable def nbhdBasis (H : Hypergraph V) (v : V) : ℕ → Finset V :=
  fun r => H.geodesicBall v r

/-- For `r ≤ s`, `nbhdBasis v r ⊆ nbhdBasis v s`. -/
theorem nbhdBasis_mono (H : Hypergraph V) (v : V) {r s : ℕ} (hrs : r ≤ s) :
    H.nbhdBasis v r ⊆ H.nbhdBasis v s := by
  intros u hu
  unfold nbhdBasis Hypergraph.geodesicBall at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact le_trans hu hrs

/-- `v ∈ nbhdBasis v r` for every `r`. -/
theorem self_mem_nbhdBasis (H : Hypergraph V) (v : V) (r : ℕ) :
    v ∈ H.nbhdBasis v r := by
  unfold nbhdBasis Hypergraph.geodesicBall
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Hypergraph.dist_self]
  exact Nat.zero_le _

/-- `nbhdBasis v 0` is the set of `u` with `H.dist v u = 0`. This set contains `v` and
every vertex not reachable from `v`, since `SimpleGraph.dist` is `0` on unreachable
pairs. -/
theorem nbhdBasis_zero_eq (H : Hypergraph V) (v : V) :
    H.nbhdBasis v 0 = Finset.univ.filter (fun u => H.dist v u = 0) := by
  unfold nbhdBasis Hypergraph.geodesicBall
  apply Finset.filter_congr
  intros u _
  exact ⟨fun h => Nat.le_zero.mp h, fun h => h ▸ Nat.le.refl⟩

end Hypergraph
end InfraFormalization
