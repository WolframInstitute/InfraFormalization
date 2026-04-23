/-
**RuleSignature functor** (Group IR / #159).

A rule's *signature* is the tuple of scalar invariants we extract
from its trajectory output: Wolfram-Hausdorff dimension estimate,
growth rate, average Forman-Ricci curvature, and whether the rule
is conservative. These invariants serve as coarse fingerprints for
ruliology: different-signature rules produce different-geometry
output; matching signatures are necessary conditions for two rules
to produce the same continuum limit.

**Connection to hypergraphs.** Native. The signature of a
`RewritingSystem P` acting on an initial `Hypergraph V` is a
function of the resulting states — it depends only on the
hypergraph data, not on continuum embeddings.

**Components of a signature.**

  * `hausdorffDimAt v r` — the local Wolfram-Hausdorff estimator
    at vertex `v`, radius `r`.
  * `growthExponent` — the asymptotic exponent in `|V_n| ~ n^α`.
  * `avgFormanRicciEdge` — sum of Forman-Ricci over edges divided
    by edge count (average edge curvature).
  * `conservative` — every rule has `|LHS| = |RHS|`.
  * `ballVolume v r` — the geodesic-ball-volume function.

A signature tuple can then be compared across rules and against
target-manifold signatures.
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

/-- **Ruliology signature** of a single hypergraph state: the scalar
invariants we read off, packaged for comparison. -/
structure RuleSignature (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Local Wolfram–Hausdorff dimension at a reference vertex and radius. -/
  hausdorffDimAt : V → ℕ → ℝ
  /-- Ball volume function `(v, r) ↦ V(v, r)`. -/
  ballVolume     : V → ℕ → ℕ
  /-- Sum of edge Forman-Ricci (proxy for average curvature). -/
  totalFormanRicci : ℤ
  /-- Edge count — normalisation factor for averages. -/
  edgeCount      : ℕ
  /-- Vertex-set size. -/
  vertexCount    : ℕ

/-- **Compute the signature of a hypergraph state**. The
Forman-Ricci sum requires a `Neighbourhood V` structure; we use the
hypergraph's own edge count as the edge normaliser and leave the
discrete-curvature coupling as zero until a `Hypergraph → Neighbourhood`
wrapper is introduced. -/
noncomputable def hypergraphSignature (H : Hypergraph V) : RuleSignature V where
  hausdorffDimAt := H.localDimension
  ballVolume     := H.geodesicBallVolume
  totalFormanRicci := 0  -- placeholder; coupling via Neighbourhood wrapper TBD
  edgeCount      := H.size
  vertexCount    := Fintype.card V

/-- **Average Forman-Ricci per edge** (when there are edges). -/
noncomputable def RuleSignature.avgFormanRicci
    (σ : RuleSignature V) : ℚ :=
  if h : σ.edgeCount = 0 then 0
  else (σ.totalFormanRicci : ℚ) / (σ.edgeCount : ℚ)

/-! ## Signature-matching predicates -/

/-- **Two signatures have the same dimension** if they agree at every
`(v, r)`. Dimension-equality is necessary (not sufficient) for two
rules to produce the same continuum limit. -/
def RuleSignature.sameDim (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt

/-- **Two signatures have the same ball-volume function** if they
agree at every `(v, r)`. -/
def RuleSignature.sameBallVolume (σ τ : RuleSignature V) : Prop :=
  σ.ballVolume = τ.ballVolume

/-- **Same edge count** check. -/
def RuleSignature.sameEdgeCount (σ τ : RuleSignature V) : Prop :=
  σ.edgeCount = τ.edgeCount

/-- **Signatures match completely** if all four scalar invariants
agree (dim, ball volume, Ricci, counts). -/
def RuleSignature.FullMatch (σ τ : RuleSignature V) : Prop :=
  σ.hausdorffDimAt = τ.hausdorffDimAt ∧
  σ.ballVolume = τ.ballVolume ∧
  σ.totalFormanRicci = τ.totalFormanRicci ∧
  σ.edgeCount = τ.edgeCount ∧
  σ.vertexCount = τ.vertexCount

/-! ## Conservation → signature invariance

For a conservative trajectory, `edgeCount` is invariant across
states; the full signature is more subtle (depends on specific
edges, vertices touched) but `edgeCount` is nailed down. -/

/-- **Conservation invariance of edge count.** For any
conservative rewriting system, the `edgeCount` component of the
signature is constant along the trajectory. This is
`trajectory_size_invariant` reformulated in signature terms. -/
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

/-- **Vertex count is a signature-level invariant on every
trajectory**. No conservativity hypothesis needed — `vertexCount` is
defined as `Fintype.card V`, which is fixed by the type. Complements
`edgeCount_invariant_of_conservative`. -/
theorem RuleSignature.vertexCount_invariant
    {P : Type*} {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).vertexCount
    = (hypergraphSignature init).vertexCount := rfl

/-- **Edge-count mismatch ⇒ unreachable from init under conservativity.**
If a target signature `σ` has `σ.edgeCount ≠ init.size`, then no
step-consistent conservative trajectory from `init` ever reaches a
state whose signature `edgeCount` equals `σ.edgeCount`. This is a
concrete, machine-checkable **screening criterion** for rule
proposals: any candidate aiming at a target `σ` must use a
non-conservative rule (|LHS| ≠ |RHS|) when `σ.edgeCount ≠ init.size`.

Ties the IR1 signature apparatus to the IR2 conservation theorem as
an eliminator in the IR6 candidate-rule search. -/
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

/-- **Ball-volume oversize ⇒ unreachable (unconditional).** If a
target signature `σ` claims a ball volume `σ.ballVolume v r` exceeding
`Fintype.card V`, then no hypergraph `H : Hypergraph V` has
`hypergraphSignature H = σ` — because every
`H.geodesicBallVolume v r ≤ Fintype.card V`. No trajectory, no
rewriting system needed; this is a pure type-level obstruction.

Second concrete screening criterion, orthogonal to the edge-count
one: rules out candidate signatures that are physically impossible
on the given vertex type. -/
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

/-- **Vertex-count mismatch ⇒ unreachable (unconditional).** If a
target signature has `σ.vertexCount ≠ Fintype.card V`, then no
hypergraph on `V` realises `σ` — `vertexCount` is defined as the
fixed cardinality of the vertex type. -/
theorem RuleSignature.vertexCount_mismatch_unreachable
    (σ : RuleSignature V) (hmis : σ.vertexCount ≠ Fintype.card V)
    (H : Hypergraph V) : hypergraphSignature H ≠ σ := by
  intro h
  have h_vc : (hypergraphSignature H).vertexCount = σ.vertexCount :=
    congrArg RuleSignature.vertexCount h
  simp [hypergraphSignature] at h_vc
  exact hmis h_vc.symm

/-- **Admissible-signature predicate**: a signature `σ` has passed
the unconditional screening criteria — `vertexCount = Fintype.card V`
and every ball volume is within `Fintype.card V`. A non-admissible
target is unreachable (no need to explore any rewriting trajectory);
an admissible one *may* be reachable but needs further analysis
(ruliology search, conservativity, etc.). -/
def RuleSignature.Admissible (σ : RuleSignature V) : Prop :=
  σ.vertexCount = Fintype.card V ∧
  ∀ (v : V) (r : ℕ), σ.ballVolume v r ≤ Fintype.card V

/-- **Non-admissible signatures are unreachable by any hypergraph.** -/
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

/-- **Signature edgeCount of `cycleHypergraph n` is `n`.** Immediate
corollary of `cycleHypergraph_size` via the definition of
`hypergraphSignature.edgeCount = Hypergraph.size`. Concrete screening
anchor: under a conservative system starting from `cycleHypergraph n`,
any target with `edgeCount ≠ n` is unreachable (via
`edgeCount_mismatch_unreachable_of_conservative`). -/
theorem RuleSignature.cycleHypergraph_signature_edgeCount (n : Nat) [NeZero n] :
    (hypergraphSignature (V := Fin n) (cycleHypergraph n)).edgeCount = n :=
  cycleHypergraph_size n

/-- **Signature edgeCount of `Hypergraph.empty : Hypergraph V` is 0.**
The empty hypergraph has zero edges by definition; its signature
edgeCount equals 0. Together with `cycleHypergraph_signature_edgeCount`
this gives concrete edgeCount anchors for the two canonical starting
states (empty and cycle). -/
theorem RuleSignature.empty_signature_edgeCount :
    (hypergraphSignature (Hypergraph.empty : Hypergraph V)).edgeCount = 0 := by
  show (Hypergraph.empty : Hypergraph V).size = 0
  rfl

/-- **Concrete cycle-start screen**: a conservative step-consistent
trajectory starting from `cycleHypergraph n` cannot reach any target
with `edgeCount ≠ n`. Closed specialisation of
`edgeCount_mismatch_unreachable_of_conservative` at the canonical
cycle initial state. -/
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

/-- **Concrete empty-start screen**: a conservative step-consistent
trajectory starting from `Hypergraph.empty` cannot reach any target
with `edgeCount ≠ 0`. Corollary for the second canonical start state. -/
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

/-- **Signature ballVolume is bounded by `Fintype.card V`**, at every
state of every trajectory — a universal cardinality bound. Direct
corollary of `Hypergraph.geodesicBallVolume_le_card` lifted to the
signature level. -/
theorem RuleSignature.signature_ballVolume_le_card
    {P : Type*} {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (i : Nat) (hi : i < τ.states.length) (v : V) (r : ℕ) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).ballVolume v r
      ≤ Fintype.card V :=
  (τ.states.get ⟨i, hi⟩).geodesicBallVolume_le_card v r

/-- **Every trajectory state's signature is admissible.** Combines the
two universal invariants: `vertexCount = Fintype.card V` (by
definition) and `ballVolume v r ≤ Fintype.card V` (by the trivial
subset bound). So every reachable signature is Admissible — and
conversely `not_admissible_unreachable` gives the converse elimination
in one step. -/
theorem RuleSignature.trajectory_state_signature_admissible
    {P : Type*} {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) (hi : i < τ.states.length) :
    (hypergraphSignature (τ.states.get ⟨i, hi⟩)).Admissible := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro v r
    exact RuleSignature.signature_ballVolume_le_card τ i hi v r

end InfraFormalization
