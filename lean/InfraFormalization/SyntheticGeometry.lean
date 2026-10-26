/-
Circles, balls and segments defined from hypergraph distance.

This module defines, for a hypergraph `H` on a finite vertex type, the
circle `{v : dist c v = r}`, the closed ball (`geodesicBall`), the segment
`{w : dist u w + dist w v = dist u v}` and the sphere (an abbreviation for
the circle). It proves membership lemmas, that the centre lies on the
circle of radius 0 and on no circle of positive radius, that circles of
different radii are disjoint, that a circle lies in the ball of the same
radius, and that both endpoints lie on a segment.
-/

import InfraFormalization.HypergraphDistance

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices at distance `r` from `c`. -/
noncomputable def SyntheticCircle (H : Hypergraph V) (c : V) (r : Nat) : Finset V :=
  Finset.univ.filter (fun v => H.dist c v = r)

/-- The vertices at distance at most `r` from `c`; equal to
`H.geodesicBall c r`. -/
noncomputable def SyntheticBall (H : Hypergraph V) (c : V) (r : Nat) :
    Finset V :=
  H.geodesicBall c r

/-- `v` lies on the circle of radius `r` about `c` if and only if
`dist c v = r`. -/
theorem mem_syntheticCircle (H : Hypergraph V) (c v : V) (r : Nat) :
    v ∈ H.SyntheticCircle c r ↔ H.dist c v = r := by
  unfold SyntheticCircle
  simp

/-- `c` lies on the circle of radius 0 about `c`. -/
theorem syntheticCircle_zero (H : Hypergraph V) (c : V) :
    c ∈ H.SyntheticCircle c 0 := by
  rw [H.mem_syntheticCircle]
  exact H.dist_self c

/-- For `r > 0`, `c` does not lie on the circle of radius `r` about `c`. -/
theorem center_not_on_circle (H : Hypergraph V) (c : V) {r : Nat}
    (hr : 0 < r) : c ∉ H.SyntheticCircle c r := by
  rw [H.mem_syntheticCircle]
  rw [H.dist_self]
  omega

/-- The circle of radius `r` is a subset of the ball of radius `r`. -/
theorem syntheticCircle_subset_ball (H : Hypergraph V) (c : V) (r : Nat) :
    H.SyntheticCircle c r ⊆ H.SyntheticBall c r := by
  unfold SyntheticCircle SyntheticBall Hypergraph.geodesicBall
  intro v hv
  rw [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, le_of_eq hv.2⟩

/-- Circles about the same centre with different radii are disjoint. -/
theorem syntheticCircle_disjoint (H : Hypergraph V) (c : V)
    {r s : Nat} (hne : r ≠ s) :
    Disjoint (H.SyntheticCircle c r) (H.SyntheticCircle c s) := by
  rw [Finset.disjoint_left]
  intros v hv_r hv_s
  rw [H.mem_syntheticCircle] at hv_r hv_s
  exact hne (hv_r.symm.trans hv_s)

/-- The vertices `w` with `dist u w + dist w v = dist u v`. -/
noncomputable def SyntheticLineSegment (H : Hypergraph V) (u v : V) : Finset V :=
  Finset.univ.filter (fun w => H.dist u w + H.dist w v = H.dist u v)

theorem mem_syntheticLineSegment (H : Hypergraph V) (u v w : V) :
    w ∈ H.SyntheticLineSegment u v ↔ H.dist u w + H.dist w v = H.dist u v := by
  unfold SyntheticLineSegment
  simp

/-- `u` and `v` lie on the segment from `u` to `v`. -/
theorem endpoints_on_segment (H : Hypergraph V) (u v : V) :
    u ∈ H.SyntheticLineSegment u v ∧ v ∈ H.SyntheticLineSegment u v := by
  refine ⟨?_, ?_⟩
  · rw [H.mem_syntheticLineSegment, H.dist_self]; omega
  · rw [H.mem_syntheticLineSegment, H.dist_self]; omega

/-- The sphere of radius `r` about `c`, defined as
`H.SyntheticCircle c r`. -/
noncomputable abbrev SyntheticSphere (H : Hypergraph V) (c : V) (r : Nat) :
    Finset V :=
  H.SyntheticCircle c r

end Hypergraph
end InfraFormalization
