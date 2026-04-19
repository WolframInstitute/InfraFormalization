/-
Bridging theorem: a trajectory's causal DAG (from `CausalLevel.lean`)
embeds into the 1+0-dim Lorentz lattice (from `Infra/LorentzLattice.lean`)
via the level function as time coordinate.

This is the first wiring between the Wolfram-model rewriting side (the
`Trajectory` structure, its causal DAG, its level function) and the
Minkowski-lattice side (events as `Fin (d+1) → ℤ`, the `CausalPrecedes`
forward-light-cone relation).

The 1+0-dim case has no spatial coordinates — the embedding carries
only time (= level). Spatial embedding of events is a separate problem
(the spatial coordinates are not determined by the trajectory; they are
auxiliary choices, reminiscent of F1). This file proves only that the
time coordinate given by `level` is compatible with the Lorentzian
causal order.

The result: `i ≺_causal j` in the trajectory ⇒
`trajectoryToEvent τ i ≺ trajectoryToEvent τ j` in the Lorentz lattice.
-/

import InfraFormalization.CausalLevel
import InfraFormalization.Infra.LorentzLattice

namespace InfraFormalization
namespace Infra

variable {P V : Type*} [DecidableEq V]

/-- Embedding of a trajectory's events into the 1+0-dim Lorentz lattice.
The time coordinate is the causal level; there are no spatial
coordinates. -/
noncomputable def trajectoryToEvent {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i : Nat) : Event 0 :=
  fun _ => (level τ i : ℤ)

theorem trajectoryToEvent_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i : Nat) :
    (trajectoryToEvent τ i) 0 = (level τ i : ℤ) := rfl

/-- **Embedding theorem.** If event `j` causally precedes event `i` in
the trajectory (as indicated by `isCausalPred τ j i = true`), then
`trajectoryToEvent τ j ≺ trajectoryToEvent τ i` in the 1+0-dim Lorentz
lattice. That is, the level function is a valid Minkowski time
coordinate for the trajectory's causal DAG. -/
theorem trajectoryToEvent_preserves_causal {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (j i : Nat)
    (hlt : j < i) (hcp : isCausalPred τ j i = true) :
    CausalPrecedes 0 (trajectoryToEvent τ j) (trajectoryToEvent τ i) := by
  unfold CausalPrecedes
  rw [trajectoryToEvent_time, trajectoryToEvent_time, spaceDist_zero_dim]
  have hmono : level τ j + 1 ≤ level τ i :=
    level_add_one_le_of_isCausalPred τ j i hlt hcp
  have hle : level τ j ≤ level τ i := by omega
  have hleZ : (level τ j : ℤ) ≤ (level τ i : ℤ) := by exact_mod_cast hle
  simp only [Nat.cast_zero]
  linarith

/-- **Strict embedding.** Same-level events are not causally related
(forward). This is the antichain property of the embedding: it maps
distinct events at the same level to the same time coordinate, and
those are not causally related in the Lorentz lattice. -/
theorem same_level_not_causal {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (j i : Nat)
    (hlt : j < i) (h_same_level : level τ j = level τ i) :
    isCausalPred τ j i = false :=
  no_causal_edge_within_level τ j i hlt h_same_level

/-- **Master bridge theorem.** The full wiring from a trajectory's
(Prop-level) causal-precedence relation to the Lorentz-lattice
causal-precedence relation under the level-as-time embedding:

  `causallyPrecedes τ i j`  (there is a hyperedge produced at i and
                             consumed at j)
  ⇒
  `CausalPrecedes 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j)`
  (the Minkowski causal-order constraint holds in the embedding). -/
theorem causallyPrecedes_implies_minkowski {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i j : Nat)
    (h : causallyPrecedes τ i j) :
    CausalPrecedes 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j) := by
  obtain ⟨hlt, _, hcp⟩ := (causallyPrecedes_iff_isCausalPred τ i j).mp h
  exact trajectoryToEvent_preserves_causal τ i j hlt hcp

end Infra
end InfraFormalization
