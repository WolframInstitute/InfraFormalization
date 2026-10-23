/-
**Pre-metric topological invariants of a hypergraph** (#323 TOP1, #326 TOP4).

The two most elementary topological invariants on a hypergraph, requiring
neither metric nor measure structure:
- `b_0` = number of connected components — SWOLF's "is every point
  reachable from every other" — the partition every other invariant sits
  inside.
- `b_1` = first Betti number / cycle rank — `#hyperedges − #vertices +
  #components` — the most elementary non-trivial invariant after `b_0`.

**Connection to hypergraphs.** Native. Both are functions of the
underlying combinatorial structure; no metric tensor, no continuum.

**Connection to the Hodge-Laplacian spectrum** (IT3): on the constant
sheaf, `b_k = dim ker(Hodge Laplacian on k-forms)`. So `b_0` = nullity of
graph Laplacian, `b_1` = nullity of 1-form Hodge Laplacian. The
combinatorial definitions here agree with the spectral definitions
(bridge theorem to follow).

**Spatial flavour** is what we surface here. Causal / branchial /
rewriting-reachable flavours (the four-flavour structure documented in
`INFRAGEOMETRY.md` §5b Layer −1) live in their respective files
(`Causal.lean`, `Branchial.lean`, `Multiway.lean`).
-/

import InfraFormalization.HypergraphDistance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## b_0 — connected components (TOP4 spatial flavour)

Spatial connectedness via the clique-expansion `H.toSimpleGraph`.
Mathlib's `SimpleGraph.ConnectedComponent` plus the `Fintype` instance
from `Connectivity/Finite.lean` make this directly computable. -/

/-- **Connected components** of the spatial graph — quotient of `V` by
`Reachable`. The partition. -/
noncomputable abbrev SpatialConnectedComponent (H : Hypergraph V) : Type _ :=
  H.toSimpleGraph.ConnectedComponent

/-- **`b_0` (spatial flavour)** — number of connected components in the
clique-expansion graph. The most elementary topological invariant.
SWOLF's "is every point reachable from every other" reduces to
`b_0 = 1`. -/
noncomputable def spatialB0 (H : Hypergraph V) : ℕ :=
  Fintype.card H.SpatialConnectedComponent

/-- **Spatial connectedness predicate**: every vertex reachable from every
other (in the clique-expansion). Equivalently `spatialB0 = 1` (when `V`
is non-empty). -/
def IsSpatiallyConnected (H : Hypergraph V) : Prop :=
  H.toSimpleGraph.Connected

/-- **`spatialB0` is bounded above by `Fintype.card V`** — at most one
component per vertex. The map `V → ConnectedComponent` (taking each vertex
to its component-quotient class) is surjective; hence card-of-image ≤
card-of-source. -/
theorem spatialB0_le_card (H : Hypergraph V) :
    H.spatialB0 ≤ Fintype.card V := by
  unfold spatialB0 SpatialConnectedComponent
  exact Fintype.card_le_of_surjective
    (fun v => H.toSimpleGraph.connectedComponentMk v)
    (fun c => Quot.exists_rep c)

/-! ## b_1 — first Betti / cycle rank (TOP1)

For a finite graph: `b_1 = #edges − #vertices + #components`. For a
hypergraph, the analogous formula uses *hyperedges* rather than
clique-expanded edges:

  `b_1(H) := H.size − Fintype.card V + spatialB0(H)`

(at the integer-arithmetic level; we use ℤ to avoid `ℕ`-underflow on
disconnected examples).

This corresponds to the **simplicial-style b_1** treating each hyperedge
as a single 1-cell. The clique-expansion variant
`H.toSimpleGraph.edgeFinset.card − Fintype.card V + spatialB0` is a
distinct invariant (lives on the graph CLOSURE1 #362 chooses).
-/

/-- **First Betti number / cycle rank (hyperedge-counted, integer
arithmetic)** — `#hyperedges − #vertices + #components`. SWOLF's most
elementary non-trivial invariant after `b_0`. -/
noncomputable def firstBettiZ (H : Hypergraph V) : ℤ :=
  (H.size : ℤ) - (Fintype.card V : ℤ) + (H.spatialB0 : ℤ)

/-- **`b_1` lower bound** on a finite hypergraph: `b_1 ≥ #hyperedges −
#vertices` (since `spatialB0 ≥ 0`). When the graph is connected
(`spatialB0 = 1`), `b_1 = #hyperedges − #vertices + 1` exactly. -/
theorem firstBettiZ_lower_bound (H : Hypergraph V) :
    (H.size : ℤ) - (Fintype.card V : ℤ) ≤ H.firstBettiZ := by
  unfold firstBettiZ
  have : (0 : ℤ) ≤ (H.spatialB0 : ℤ) := Int.natCast_nonneg _
  linarith

/-! ## Higher Betti placeholder (TOP2 #324)

`b_k` for `k ≥ 2` requires a chosen cellular structure (the closure
problem CLOSURE1 #362). The `Hodge Laplacian on k-forms` from KnillCore
gives one route once a kernel-dimension API exists. -/

/-! ## Connection to MILESTONE / topology-before-metric layering -/

/-- **`spatiallyConnected_implies_b0_pos`** — if SWOLF's "every point
reachable from every other" holds, there is at least one connected
component. (The converse direction needs the unique-class characterisation
which lives in Mathlib follow-up; we surface the forward implication
which is the structurally important one.) -/
theorem spatialB0_pos_of_nonempty [Nonempty V] (H : Hypergraph V) :
    0 < H.spatialB0 := by
  unfold spatialB0 SpatialConnectedComponent
  -- nonempty quotient when source is nonempty
  exact Fintype.card_pos

/-! ## Decidable membership in regions (MEMBER1)

SWOLF's "whether a point is a member of the set of points in a region"
— the foundational topological primitive. For `Finset V` regions
membership is decidable for free (Mathlib's `Finset.decidableMem`); we
expose a uniform `IsInRegion` alias so all subsequent topology code
talks to the same predicate name.

The predicate-defined regions in `HypergraphDistance.lean` (`infraSphere`,
`infraDisk`, `perpBisector`, `voronoiCell`, etc.) are all `Finset V`
values built from `Finset.univ.filter`. Because `Hypergraph.dist` is
`noncomputable` (it uses Mathlib's `SimpleGraph.dist`), membership
decidability for these regions reduces to the standard
`Finset.decidableMem` via classical decidability — already available
without needing extra instances here. -/

/-- **`v ∈ R` for `R : Finset V`** — uniform alias surfacing the
foundational topological membership predicate SWOLF called out as the
most elementary primitive. Decidable for free via `Finset.decidableMem`. -/
abbrev IsInRegion (v : V) (R : Finset V) : Prop := v ∈ R

instance (v : V) (R : Finset V) : Decidable (IsInRegion v R) :=
  inferInstanceAs (Decidable (v ∈ R))

/-- **`v` is in the infra-disk iff its distance to the centre is at
most `r`** — restating the `Finset.mem_filter` characterisation through
the `IsInRegion` alias. -/
theorem isInRegion_infraDisk_iff (H : Hypergraph V) (v O : V) (r : ℕ) :
    IsInRegion v (H.infraDisk O r) ↔ H.dist O v ≤ r := by
  unfold IsInRegion Hypergraph.infraDisk Hypergraph.geodesicBall
  simp [Finset.mem_filter]

/-- **`v` is in the infra-sphere iff its distance to the centre equals `r`**. -/
theorem isInRegion_infraSphere_iff (H : Hypergraph V) (v O : V) (r : ℕ) :
    IsInRegion v (H.infraSphere O r) ↔ H.dist O v = r := by
  unfold IsInRegion Hypergraph.infraSphere
  simp [Finset.mem_filter]

/-- **`v` is in the perpendicular bisector iff equidistant from the
endpoints** — SWOLF's "all points equidistant from two given points". -/
theorem isInRegion_perpBisector_iff (H : Hypergraph V) (v A B : V) :
    IsInRegion v (H.perpBisector A B) ↔ H.dist A v = H.dist B v := by
  unfold IsInRegion
  exact H.mem_perpBisector A B v

/-! ## bounded / diameter (BOUND1, spatial flavour)

SWOLF's bounded/unbounded distinction. Trivial on `[Fintype V]`, but
the *value* of `spatialDiameter` is the relevant invariant for
refinement-limit / continuum-limit questions. -/

/-- **Spatial diameter** of a hypergraph: the maximum geodesic distance
between any two vertices. Trivially bounded on a finite vertex type;
the *value* is what matters for refinement-limit analysis (BOUND1's
\"under refinement, does the diameter stay bounded?\"). -/
noncomputable def spatialDiameter (H : Hypergraph V) : ℕ :=
  Finset.univ.sup (fun u : V => Finset.univ.sup (fun v : V => H.dist u v))

/-- **Every pair has distance bounded by the diameter**. -/
theorem dist_le_spatialDiameter (H : Hypergraph V) (u v : V) :
    H.dist u v ≤ H.spatialDiameter := by
  unfold spatialDiameter
  calc H.dist u v
      ≤ Finset.univ.sup (fun v' : V => H.dist u v') :=
        Finset.le_sup (f := fun v' => H.dist u v') (Finset.mem_univ v)
    _ ≤ Finset.univ.sup (fun u' : V => Finset.univ.sup (fun v' => H.dist u' v')) :=
        Finset.le_sup (f := fun u' => Finset.univ.sup (fun v' => H.dist u' v'))
          (Finset.mem_univ u)

/-- **`IsBounded` predicate for a region `R ⊆ V`** — there exists a
uniform distance bound between any two vertices in `R`. On a finite
hypergraph every subset is bounded (by the diameter); the predicate is
non-trivial only at limit / refinement scales. -/
def IsBounded (H : Hypergraph V) (R : Finset V) : Prop :=
  ∃ k : ℕ, ∀ u ∈ R, ∀ v ∈ R, H.dist u v ≤ k

/-- **Every region of a finite hypergraph is bounded** by the diameter. -/
theorem isBounded_of_finite (H : Hypergraph V) (R : Finset V) :
    H.IsBounded R := by
  refine ⟨H.spatialDiameter, ?_⟩
  intros u _ v _
  exact H.dist_le_spatialDiameter u v

/-! ## Open-set topologies (OPEN1)

SWOLF + PHAJEK pivot to formal topology. **Multiple natural topologies
on the same hypergraph**, each yielding different compactness /
continuity theorems. We surface predicate-level definitions for the
five canonical choices; the corresponding `TopologicalSpace V`
instances are deferred (each generates a topology by closure under
arbitrary union and finite intersection — additional Mathlib API). -/

/-- **Discrete-topology open** — every subset is open. Trivial; useful
only as a baseline / sanity check. -/
def IsDiscreteOpen (_H : Hypergraph V) (_R : Finset V) : Prop := True

/-- **Alexandrov-topology open** — `R` is closed under one-step
neighbour expansion (every neighbour of a vertex in `R` is also in
`R`). Useful for posets / causal-DAGs and for *closed* sets in the
Alexandrov sense. The dual notion ("open = closed under decreasing
predecessors") is the standard *Alexandrov topology* on the
specialization preorder. -/
def IsAlexandrovOpen (H : Hypergraph V) (R : Finset V) : Prop :=
  ∀ (u v : V), u ∈ R → H.Adj u v → v ∈ R

/-- **Cellular / star open** at a vertex — the union of stars of all
vertices in `R`, restricted to the cellular structure of the
hypergraph's clique complex. Predicate form: `R` contains the open
star of every vertex it contains. -/
def IsCellularStarOpen (H : Hypergraph V) (R : Finset V) : Prop :=
  ∀ (v : V), v ∈ R → ∀ (u : V), H.Adj v u → u ∈ R

/-- **VR-scale open at scale `r`** — `R` is closed under
`r`-neighbourhoods: every vertex within distance `r` of any vertex in
`R` is also in `R`. Scale-indexed family of topologies. -/
def IsVRScaleOpen (H : Hypergraph V) (r : ℕ) (R : Finset V) : Prop :=
  ∀ (u v : V), u ∈ R → H.dist u v ≤ r → v ∈ R

/-- **Everything is discrete-open**, trivially. -/
theorem isDiscreteOpen_all (H : Hypergraph V) (R : Finset V) :
    H.IsDiscreteOpen R := trivial

/-- **`Finset.univ` is Alexandrov-open** trivially: every vertex is
already in the universe. -/
theorem isAlexandrovOpen_univ (H : Hypergraph V) :
    H.IsAlexandrovOpen Finset.univ := by
  intros u v _ _
  exact Finset.mem_univ _

/-- **`Finset.univ` is VR-scale-open at every `r`** trivially. -/
theorem isVRScaleOpen_univ (H : Hypergraph V) (r : ℕ) :
    H.IsVRScaleOpen r Finset.univ := by
  intros u v _ _
  exact Finset.mem_univ _

/-! ## Neighbourhood basis (NBHD1)

SWOLF's "locally has neighbourhoods" intuition for surfaces — the
basis of geodesic balls around each vertex generates the local
topology. We expose the basis as a function `r ↦ geodesicBall v r` and
the membership-stability characterisation. -/

/-- **Geodesic-ball neighbourhood basis at vertex `v`** — the
decreasing-radius family `{geodesicBall v r}_{r ∈ ℕ}`. -/
noncomputable def nbhdBasis (H : Hypergraph V) (v : V) : ℕ → Finset V :=
  fun r => H.geodesicBall v r

/-- **The basis is monotone in radius** — `nbhdBasis v r ⊆ nbhdBasis v s`
for `r ≤ s`. Lifts `geodesicBall_mono` to the basis API. -/
theorem nbhdBasis_mono (H : Hypergraph V) (v : V) {r s : ℕ} (hrs : r ≤ s) :
    H.nbhdBasis v r ⊆ H.nbhdBasis v s := by
  intros u hu
  unfold nbhdBasis Hypergraph.geodesicBall at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact le_trans hu hrs

/-- **The basepoint lies in every basis element** (since `dist v v = 0 ≤ r`). -/
theorem self_mem_nbhdBasis (H : Hypergraph V) (v : V) (r : ℕ) :
    v ∈ H.nbhdBasis v r := by
  unfold nbhdBasis Hypergraph.geodesicBall
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Hypergraph.dist_self]
  exact Nat.zero_le _

/-- **`r = 0` basis element contains exactly the basepoint plus any
unreachable junk-value vertices** — precise content depends on
reachability; on a connected hypergraph it's just `{v}`. We surface
the equivalence with the strict-equality filter: a vertex is at
distance ≤ 0 iff its distance is 0. -/
theorem nbhdBasis_zero_eq (H : Hypergraph V) (v : V) :
    H.nbhdBasis v 0 = Finset.univ.filter (fun u => H.dist v u = 0) := by
  unfold nbhdBasis Hypergraph.geodesicBall
  apply Finset.filter_congr
  intros u _
  exact ⟨fun h => Nat.le_zero.mp h, fun h => h ▸ Nat.le.refl⟩

end Hypergraph
end InfraFormalization
