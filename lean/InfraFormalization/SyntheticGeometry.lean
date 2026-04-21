/-
**Synthetic infrageometry: circles, lines, spheres** (Group IS / #156).

Following the Srní / Madrid program on synthetic infrageometry
(Pavel Hájek et al., Pavel Pokorny's tropical-geometry exploration),
we construct Euclid-style geometric objects directly from the
hypergraph distance:

  * `SyntheticCircle H c r := {v : dist H c v = r}` — circle of
    radius `r` centered at `c`.
  * `SyntheticBall H c r := {v : dist H c v ≤ r}` — closed ball
    (= `geodesicBall`; reprovided here by the synthetic name).
  * `SyntheticLineSegment H u v := {w : on a shortest path u → v}`
    — the "minimal straight line" between `u` and `v`.
  * `SyntheticSphere H c r` — `d`-dim analog (= circle in d=2, etc.
    depending on embedding; here defined purely by equidistance).

These are the foundational constructions for the "minimal model" of
Euclidean geometry at the infra-scale. Multiple constructions
(`InfrageometricScene`) and axiomatic infrageometry are IS2 and IS3.

**Connection to hypergraphs.** Every synthetic object is a subset of
`V` defined purely in terms of `Hypergraph.dist`. No continuum objects.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Synthetic circle** of radius `r` centered at `c`: vertices
exactly at hypergraph-distance `r`. -/
noncomputable def SyntheticCircle (H : Hypergraph V) (c : V) (r : Nat) : Finset V :=
  Finset.univ.filter (fun v => H.dist c v = r)

/-- **Synthetic ball** (closed) of radius `r` centered at `c`: same
as `geodesicBall`, renamed for Euclid-style exposition. -/
noncomputable def SyntheticBall (H : Hypergraph V) (c : V) (r : Nat) :
    Finset V :=
  H.geodesicBall c r

/-- **Membership in the circle.** -/
theorem mem_syntheticCircle (H : Hypergraph V) (c v : V) (r : Nat) :
    v ∈ H.SyntheticCircle c r ↔ H.dist c v = r := by
  unfold SyntheticCircle
  simp

/-- **`c ∈ circle(c, 0)`** and `c ∉ circle(c, r)` for `r > 0`. -/
theorem syntheticCircle_zero (H : Hypergraph V) (c : V) :
    c ∈ H.SyntheticCircle c 0 := by
  rw [H.mem_syntheticCircle]
  exact H.dist_self c

theorem center_not_on_circle (H : Hypergraph V) (c : V) {r : Nat}
    (hr : 0 < r) : c ∉ H.SyntheticCircle c r := by
  rw [H.mem_syntheticCircle]
  rw [H.dist_self]
  omega

/-- **Ball contains circle** at same radius. -/
theorem syntheticCircle_subset_ball (H : Hypergraph V) (c : V) (r : Nat) :
    H.SyntheticCircle c r ⊆ H.SyntheticBall c r := by
  unfold SyntheticCircle SyntheticBall Hypergraph.geodesicBall
  intro v hv
  rw [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, le_of_eq hv.2⟩

/-- **Circles at different radii are disjoint.** -/
theorem syntheticCircle_disjoint (H : Hypergraph V) (c : V)
    {r s : Nat} (hne : r ≠ s) :
    Disjoint (H.SyntheticCircle c r) (H.SyntheticCircle c s) := by
  rw [Finset.disjoint_left]
  intros v hv_r hv_s
  rw [H.mem_syntheticCircle] at hv_r hv_s
  exact hne (hv_r.symm.trans hv_s)

/-- **Synthetic line segment** between `u` and `v`: the set of
vertices that lie on some geodesic (shortest path) from `u` to `v`.
Equivalently, `dist u w + dist w v = dist u v`. -/
noncomputable def SyntheticLineSegment (H : Hypergraph V) (u v : V) : Finset V :=
  Finset.univ.filter (fun w => H.dist u w + H.dist w v = H.dist u v)

theorem mem_syntheticLineSegment (H : Hypergraph V) (u v w : V) :
    w ∈ H.SyntheticLineSegment u v ↔ H.dist u w + H.dist w v = H.dist u v := by
  unfold SyntheticLineSegment
  simp

/-- **Endpoints are always on the segment.** -/
theorem endpoints_on_segment (H : Hypergraph V) (u v : V) :
    u ∈ H.SyntheticLineSegment u v ∧ v ∈ H.SyntheticLineSegment u v := by
  refine ⟨?_, ?_⟩
  · rw [H.mem_syntheticLineSegment, H.dist_self]; omega
  · rw [H.mem_syntheticLineSegment, H.dist_self]; omega

/-- **Synthetic sphere at dimension `d`** with center `c` and radius
`r`: same as circle for 1-dim, but we provide a named alias for
higher-dim clarity. At the hypergraph level, "dimension" is set by
the surrounding graph structure; the sphere predicate is purely
equidistance. -/
noncomputable abbrev SyntheticSphere (H : Hypergraph V) (c : V) (r : Nat) :
    Finset V :=
  H.SyntheticCircle c r

end Hypergraph
end InfraFormalization
