/-
Signatures of hypergraph states.

A `RuleSignature V` records, for a state on the vertex type `V`, the local
dimension estimator at each vertex and radius, the geodesic-ball volume
function, the edge count and the vertex count.
`hypergraphSignature H` computes it from `H`. The module proves that the edge
count is constant along a
step-consistent trajectory of conservative rules, that the vertex count is
`Fintype.card V`, and that ball volumes are at most `Fintype.card V`, and
derives from these conditions under which no state has a given signature.
-/

import InfraFormalization.HypergraphDistance
import InfraFormalization.DiscreteRicci
import InfraFormalization.Rule
import InfraFormalization.RuleDimensionBounds
import InfraFormalization.Multiway
import InfraFormalization.Causal

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Signature tuple components -/

/-- The signature of a hypergraph state: four invariants. -/
structure RuleSignature (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Local Wolfram–Hausdorff dimension at a reference vertex and radius. -/
  hausdorffDimAt : V → ℕ → ℝ
  /-- Ball volume function `(v, r) ↦ V(v, r)`. -/
  ballVolume     : V → ℕ → ℕ
  /-- Edge count. -/
  edgeCount      : ℕ
  /-- Vertex-set size. -/
  vertexCount    : ℕ

/-- The signature of `H`: `H.localDimension`, `H.geodesicBallVolume`,
`H.size` and `Fintype.card V`. -/
noncomputable def hypergraphSignature (H : Hypergraph V) : RuleSignature V where
  hausdorffDimAt := H.localDimension
  ballVolume     := H.geodesicBallVolume
  edgeCount      := H.size
  vertexCount    := Fintype.card V

/-! ## Signature-matching predicates -/

/-- Two signatures have equal dimension functions. -/
def RuleSignature.sameDim (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt

/-- Two signatures have equal ball-volume functions. -/
def RuleSignature.sameBallVolume (σ τ : RuleSignature V) : Prop :=
  σ.ballVolume = τ.ballVolume

/-- Two signatures have equal edge counts. -/
def RuleSignature.sameEdgeCount (σ τ : RuleSignature V) : Prop :=
  σ.edgeCount = τ.edgeCount

/-- Two signatures agree in all four components. -/
def RuleSignature.FullMatch (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt ∧
  σ.ballVolume = τ.ballVolume ∧
  σ.edgeCount = τ.edgeCount ∧
  σ.vertexCount = τ.vertexCount

/-! ## Edge count along conservative trajectories -/

/-- On a step-consistent trajectory whose applications all use
conservative rules, the signature edge count of every state equals that of
the initial state. This restates `trajectory_size_invariant`. -/
theorem RuleSignature.edgeCount_invariant_of_conservative
    {P : Type*} {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount
    = (hypergraphSignature init).edgeCount := by
  unfold hypergraphSignature
  exact trajectory_size_invariant τ hstep hcons i hi

/-- The signature vertex count of every trajectory state equals that of the
initial state; both are `Fintype.card V`, so the proof is `rfl`. -/
theorem RuleSignature.vertexCount_invariant
    {P : Type*} {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).vertexCount
    = (hypergraphSignature init).vertexCount := rfl

/-- On a step-consistent trajectory of conservative rules, if
`σ.edgeCount` differs from the edge count of the initial state, then no
state of the trajectory has signature edge count `σ.edgeCount`. -/
theorem RuleSignature.edgeCount_mismatch_unreachable_of_conservative
    {P : Type*} {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (σ : RuleSignature V) (hmis : σ.edgeCount ≠ (hypergraphSignature init).edgeCount)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount ≠ σ.edgeCount := by
  rw [RuleSignature.edgeCount_invariant_of_conservative τ hstep hcons i hi]
  exact fun h => hmis h.symm

/-- If `σ.ballVolume v r > Fintype.card V` for some `v` and `r`, then no
hypergraph `H` on `V` has `hypergraphSignature H = σ`, since
`H.geodesicBallVolume v r ≤ Fintype.card V`. -/
theorem RuleSignature.ballVolume_oversize_unreachable
    (σ : RuleSignature V) (v : V) (r : ℕ)
    (hover : σ.ballVolume v r > Fintype.card V) (H : Hypergraph V) :
    hypergraphSignature H ≠ σ := by
  intro h
  have h_vol : H.geodesicBallVolume v r = σ.ballVolume v r := by
    have := congrArg RuleSignature.ballVolume h
    exact (congrFun (congrFun this v) r)
  have h_bound := H.geodesicBallVolume_le_card v r
  rw [h_vol] at h_bound
  exact absurd h_bound (not_le.mpr hover)

/-- If `σ.vertexCount ≠ Fintype.card V`, then no hypergraph `H` on `V` has
`hypergraphSignature H = σ`. -/
theorem RuleSignature.vertexCount_mismatch_unreachable
    (σ : RuleSignature V) (hmis : σ.vertexCount ≠ Fintype.card V)
    (H : Hypergraph V) : hypergraphSignature H ≠ σ := by
  intro h
  have h_vc : (hypergraphSignature H).vertexCount = σ.vertexCount :=
    congrArg RuleSignature.vertexCount h
  simp [hypergraphSignature] at h_vc
  exact hmis h_vc.symm

/-- A signature is admissible if its vertex count is `Fintype.card V` and
every ball volume is at most `Fintype.card V`. -/
def RuleSignature.Admissible (σ : RuleSignature V) : Prop :=
  σ.vertexCount = Fintype.card V ∧
  ∀ (v : V) (r : ℕ), σ.ballVolume v r ≤ Fintype.card V

/-- If `σ` is not admissible, then no hypergraph `H` on `V` has
`hypergraphSignature H = σ`. -/
theorem RuleSignature.not_admissible_unreachable
    (σ : RuleSignature V) (hadmis : ¬ σ.Admissible)
    (H : Hypergraph V) : hypergraphSignature H ≠ σ := by
  unfold RuleSignature.Admissible at hadmis
  push_neg at hadmis
  intro h
  by_cases h_vcount : σ.vertexCount = Fintype.card V
  · obtain ⟨v, r, hover⟩ := hadmis h_vcount
    exact RuleSignature.ballVolume_oversize_unreachable σ v r hover H h
  · have h_vc : (hypergraphSignature H).vertexCount = σ.vertexCount :=
      congrArg RuleSignature.vertexCount h
    simp [hypergraphSignature] at h_vc
    exact h_vcount h_vc.symm

/-- The signature edge count of `cycleHypergraph n` is `n`, by
`cycleHypergraph_size`. -/
theorem RuleSignature.cycleHypergraph_signature_edgeCount (n : Nat) [NeZero n] :
    (hypergraphSignature (V := Fin n) (cycleHypergraph n)).edgeCount = n :=
  cycleHypergraph_size n

/-- The signature edge count of the empty hypergraph is 0. -/
theorem RuleSignature.empty_signature_edgeCount :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).edgeCount = 0 := by
  show (Hypergraph.empty : Hypergraph V).size = 0
  rfl

/-- The signature edge count of `H₁ + H₂` is the sum of the signature edge
counts of `H₁` and `H₂`, by `Hypergraph.size_add`. -/
theorem RuleSignature.signature_edgeCount_add (H₁ H₂ : Hypergraph V) :
    (hypergraphSignature (H₁ + H₂)).edgeCount
      = (hypergraphSignature H₁).edgeCount
        + (hypergraphSignature H₂).edgeCount := by
  show (H₁ + H₂).size = H₁.size + H₂.size
  exact Hypergraph.size_add H₁ H₂

/-- The signature edge count of `H₁` is at most that of `H₁ + H₂`. -/
theorem RuleSignature.signature_edgeCount_le_add_right (H₁ H₂ : Hypergraph V) :
    (hypergraphSignature H₁).edgeCount ≤ (hypergraphSignature (H₁ + H₂)).edgeCount := by
  show H₁.size ≤ (H₁ + H₂).size
  exact Hypergraph.size_le_add_right H₁ H₂

/-- On a step-consistent trajectory of conservative rules starting at
`cycleHypergraph n`, no state has signature edge count `σ.edgeCount` when
`σ.edgeCount ≠ n`. -/
theorem RuleSignature.cycleHypergraph_start_edgeCount_screen
    {n : Nat} [NeZero n] {P : Type*} {sys : RewritingSystem P}
    (τ : Trajectory sys (cycleHypergraph n))
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (σ : RuleSignature (Fin n)) (hmis : σ.edgeCount ≠ n)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount ≠ σ.edgeCount := by
  refine RuleSignature.edgeCount_mismatch_unreachable_of_conservative
    τ hstep hcons σ ?_ i hi
  rw [RuleSignature.cycleHypergraph_signature_edgeCount n]
  exact hmis

/-- On a step-consistent trajectory of conservative rules starting at the
empty hypergraph, no state has signature edge count `σ.edgeCount` when
`σ.edgeCount ≠ 0`. -/
theorem RuleSignature.empty_start_edgeCount_screen
    {P : Type*} {sys : RewritingSystem P}
    (τ : Trajectory sys (Hypergraph.empty : Hypergraph V))
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (σ : RuleSignature V) (hmis : σ.edgeCount ≠ 0)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).edgeCount ≠ σ.edgeCount := by
  refine RuleSignature.edgeCount_mismatch_unreachable_of_conservative
    τ hstep hcons σ ?_ i hi
  rw [RuleSignature.empty_signature_edgeCount]
  exact hmis

/-- Every ball volume in the signature of a trajectory state is at most
`Fintype.card V`, by `Hypergraph.geodesicBallVolume_le_card`. -/
theorem RuleSignature.signature_ballVolume_le_card
    {P : Type*} {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length) (v : V) (r : ℕ) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).ballVolume v r
      ≤ Fintype.card V :=
  (τ.states.get ⟨i, hi⟩).geodesicBallVolume_le_card v r

/-- The signature of every trajectory state is admissible. -/
theorem RuleSignature.trajectory_state_signature_admissible
    {P : Type*} {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).Admissible := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro v r
    exact RuleSignature.signature_ballVolume_le_card τ i hi v r

end InfraFormalization
