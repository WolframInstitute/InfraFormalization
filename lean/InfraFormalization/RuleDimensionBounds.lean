/-
Edge-count conservation along trajectories.

This module defines step-consistent trajectories and proves
`trajectory_size_invariant`: if every rule applied along a step-consistent
trajectory is conservative, every state has the edge count of the initial
state. It also proves `Hypergraph.geodesicBallVolume_le_card`: every
geodesic ball has at most `Fintype.card V` vertices. No theorem in this
module bounds a dimension.
-/

import InfraFormalization.Conservation
import InfraFormalization.Causal
import InfraFormalization.HypergraphDistance

namespace InfraFormalization

variable {P V : Type*} [Fintype V] [DecidableEq V]

/-- The first state of a trajectory from `init` is `init`. -/
theorem trajectory_states_zero {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (h0 : 0 < τ.states.length) :
    τ.states.get ⟨0, h0⟩ = init := by
  have hfirst := τ.first_state
  match hs : τ.states, h0 with
  | [], h0 => exact absurd h0 (Nat.not_lt_zero _)
  | first :: rest, _ =>
    rw [hs] at hfirst
    simp at hfirst
    exact hfirst

/-- A trajectory is step-consistent if, for every `i`, the application at
index `i` acts on the state at index `i`. -/
def Trajectory.StepConsistent {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) : Prop :=
  ∀ i (hi : i < τ.applications.length)
    (hi' : i < τ.states.length),
    (τ.applications.get ⟨i, hi⟩).1 = τ.states.get ⟨i, hi'⟩

/-- If a trajectory is step-consistent and every applied rule is
conservative, every state has the edge count `init.size`. -/
theorem trajectory_size_invariant {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (i : Nat) (hi : i < τ.states.length) :
    (τ.states.get ⟨i, hi⟩).size = init.size := by
  induction i with
  | zero =>
    exact congrArg Hypergraph.size (trajectory_states_zero τ hi)
  | succ k ih =>
    have hk : k + 1 < τ.states.length := hi
    have hk' : k < τ.states.length := Nat.lt_of_succ_lt hk
    have happ : k < τ.applications.length := by
      have := τ.length_eq
      omega
    have hwf := τ.well_formed k hk
    have happ_result :
        (τ.applications.get ⟨k, happ⟩).2.2.result
        = τ.states.get ⟨k + 1, hk⟩ := hwf
    have happ_start :
        (τ.applications.get ⟨k, happ⟩).1
        = τ.states.get ⟨k, hk'⟩ := hstep k happ hk'
    have hcons_k := hcons k happ
    have h_size_result :
        (τ.applications.get ⟨k, happ⟩).2.2.result.size
        = (τ.applications.get ⟨k, happ⟩).1.size :=
      (τ.applications.get ⟨k, happ⟩).2.2.size_result_of_conservative hcons_k
    calc (τ.states.get ⟨k + 1, hk⟩).size
        = (τ.applications.get ⟨k, happ⟩).2.2.result.size := by rw [happ_result]
      _ = (τ.applications.get ⟨k, happ⟩).1.size := h_size_result
      _ = (τ.states.get ⟨k, hk'⟩).size := by rw [happ_start]
      _ = init.size := ih hk'

/-- Every geodesic ball of a hypergraph on `V` has at most
`Fintype.card V` vertices. -/
theorem Hypergraph.geodesicBallVolume_le_card (H : Hypergraph V) (v : V)
    (r : ℕ) : H.geodesicBallVolume v r ≤ Fintype.card V := by
  unfold Hypergraph.geodesicBallVolume Hypergraph.geodesicBall
  calc (Finset.univ.filter (fun u => H.dist v u ≤ r)).card
      ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card V := Finset.card_univ

end InfraFormalization
