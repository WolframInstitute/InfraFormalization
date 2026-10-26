/-
Embedding of a trajectory's events into the 1+0-dimensional Lorentz lattice.

The map `trajectoryToEvent` sends event `i` of a `Trajectory` to the lattice event whose time
coordinate is `level τ i`; there are no spatial coordinates. This module proves that causal
precedence in the trajectory implies `CausalPrecedes` and `Timelike` between the image events, and
that two events have the same image if and only if they have the same level.
-/

import InfraFormalization.CausalLevel
import InfraFormalization.Infra.LorentzLattice

namespace InfraFormalization
namespace Infra

variable {P V : Type*} [DecidableEq V]

/-- The event of the 1+0-dimensional Lorentz lattice whose time coordinate is `level τ i`. -/
noncomputable def trajectoryToEvent {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i : Nat) : Event 0 :=
  fun _ => (level τ i : ℤ)

theorem trajectoryToEvent_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i : Nat) :
    (trajectoryToEvent τ i) 0 = (level τ i : ℤ) := rfl

/-- If `j < i` and `isCausalPred τ j i = true`, then
`CausalPrecedes 0 (trajectoryToEvent τ j) (trajectoryToEvent τ i)`. -/
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

/-- If `j < i` and `level τ j = level τ i`, then `isCausalPred τ j i = false`. -/
theorem same_level_not_causal {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (j i : Nat)
    (hlt : j < i) (h_same_level : level τ j = level τ i) :
    isCausalPred τ j i = false :=
  no_causal_edge_within_level τ j i hlt h_same_level

/-- If `causallyPrecedes τ i j` (a hyperedge produced by event `i` is consumed by event `j`), then
`CausalPrecedes 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j)` in the 1+0-dimensional
Lorentz lattice. -/
theorem causallyPrecedes_implies_lattice_time_order {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i j : Nat)
    (h : causallyPrecedes τ i j) :
    CausalPrecedes 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j) := by
  obtain ⟨hlt, _, hcp⟩ := (causallyPrecedes_iff_isCausalPred τ i j).mp h
  exact trajectoryToEvent_preserves_causal τ i j hlt hcp

/-- `level τ i = level τ j` if and only if `trajectoryToEvent τ i = trajectoryToEvent τ j`. -/
theorem trajectoryToEvent_lossy {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i j : Nat) :
    level τ i = level τ j ↔ trajectoryToEvent τ i = trajectoryToEvent τ j := by
  unfold trajectoryToEvent
  constructor
  · intro h
    funext _
    exact_mod_cast h
  · intro h
    have := congrFun h 0
    exact_mod_cast this

/-- If `causallyPrecedes τ i j`, then `Timelike 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j)`:
the time coordinate increases strictly. -/
theorem causallyPrecedes_implies_timelike {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (i j : Nat)
    (h : causallyPrecedes τ i j) :
    Timelike 0 (trajectoryToEvent τ i) (trajectoryToEvent τ j) := by
  unfold Timelike
  rw [trajectoryToEvent_time, trajectoryToEvent_time, spaceDist_zero_dim]
  obtain ⟨hlt, _, hcp⟩ := (causallyPrecedes_iff_isCausalPred τ i j).mp h
  have hmono : level τ i + 1 ≤ level τ j :=
    level_add_one_le_of_isCausalPred τ i j hlt hcp
  have : level τ i < level τ j := by omega
  have : (level τ i : ℤ) < (level τ j : ℤ) := by exact_mod_cast this
  simp only [Nat.cast_zero]
  linarith

end Infra
end InfraFormalization
