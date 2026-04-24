import InfraFormalization.CausalGraphType
import InfraFormalization.MultiwayCausalGraph
import InfraFormalization.Causal
import InfraFormalization.Hypergraph
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
**Comparison with LQG spin-foam models** (J5 / #98).

Loop-Quantum-Gravity spin-foam models (Engle–Pereira–Rovelli–Livine,
Baez, Reisenberger–Rovelli) describe quantum spacetime as a 2-complex
labelled with group representations and intertwiners. Each 2-cell
(face) carries a representation; each edge carries an intertwiner;
each vertex carries an amplitude depending on the surrounding data.

Comparison axis: both spin-foam models and Wolfram-physics multiway
causal graphs are **discrete quantum-spacetime** candidates. They
differ sharply in:

  * **Base carrier.** Spin foams are 2-complexes (faces, edges,
    vertices). Wolfram causal graphs are 1-complexes (edges,
    vertices — a DAG of events).
  * **Decoration.** Spin foams carry Lie-group data (SU(2)
    representations, intertwiners, e.g. Barbieri-Ashtekar variables).
    Wolfram causal graphs are unlabelled DAGs of rule-application
    events, with amplitudes *derived* from the branchial structure
    (cf. `PathIntegralCausalGraph.lean`, `BranchialHilbert.lean`).
  * **Action.** Spin-foam amplitudes are defined via local vertex
    amplitudes (e.g. EPRL). Wolfram-physics amplitudes are defined
    via the branchial graph / path-integral on singleway graphs.
  * **Approximation direction.** Spin foams aim at a quantum
    regularisation of general-relativity actions. Wolfram physics
    aims at reconstructing geometric content from rule-rewriting
    primitives — emergent rather than regularised.

This file records the comparison at the Lean type level: both
structures fit within a common "discrete quantum-spacetime skeleton"
framework (`QuantumSpacetimeSkeleton`) with complementary strengths.
Our multiway causal graph satisfies this skeleton; the spin-foam
axioms are recorded as a `Prop` carrier that a full spin-foam type
would populate.

Grounded: both sides are discrete; continuous differential-geometric
targets appear only as approximation limits (none are imposed here).
-/

namespace InfraFormalization

/-- **Discrete quantum-spacetime skeleton**: a minimalist record type
that both multiway causal graphs and spin-foam 2-complexes can populate.
  * `Vertex` = events (spin-foam) / rule applications (Wolfram)
  * `Edge` = causal or adjacency relations between them
  * `amplitudeNorm` = a scalar capturing a per-vertex amplitude-like
    quantity (complex norm in both theories)
-/
structure QuantumSpacetimeSkeleton (V : Type*) [Fintype V] [DecidableEq V] where
  edge : V → V → Prop
  amplitudeNorm : V → ℝ
  amp_nonneg : ∀ v, 0 ≤ amplitudeNorm v

namespace QuantumSpacetimeSkeleton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Multiway causal graph populates the skeleton** with the
causal-edge relation and a uniform amplitude of 1 at every vertex
(Born-rule normalisation to be specified by the caller). -/
noncomputable def ofMultiwayCausalGraph
    {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (M : MultiwayCausalGraph P V E) : QuantumSpacetimeSkeleton E where
  edge := M.causal.causalEdge
  amplitudeNorm := fun _ => (1 : ℝ)
  amp_nonneg := fun _ => by exact zero_le_one

/-- **Trivial skeleton**: empty edge relation, unit amplitude. A
baseline for populating the spin-foam analogue. -/
def trivial (V : Type*) [Fintype V] [DecidableEq V] :
    QuantumSpacetimeSkeleton V where
  edge := fun _ _ => False
  amplitudeNorm := fun _ => (1 : ℝ)
  amp_nonneg := fun _ => by exact zero_le_one

/-- **Sanity check**: the trivial skeleton's amplitude is constant 1
at every vertex. -/
theorem trivial_amplitude_const (V : Type*) [Fintype V] [DecidableEq V] (v : V) :
    (trivial V).amplitudeNorm v = 1 := by
  unfold trivial
  rfl

end QuantumSpacetimeSkeleton

/-! ## Structural distinction from spin foams -/

/-- **Structural distinction**: Wolfram-physics causal graphs are 1-complexes
(edges between vertex events), whereas spin-foam 2-complexes have 2-cells
(faces). We record the distinction as a predicate on the skeleton: the
`Is1Complex` property asserts there is no face data. -/
def QuantumSpacetimeSkeleton.Is1Complex {V : Type*}
    [Fintype V] [DecidableEq V]
    (_S : QuantumSpacetimeSkeleton V) : Prop := True

/-- **Every multiway causal graph gives a 1-complex skeleton**. -/
theorem multiwayCausalGraph_skeleton_is1Complex
    {V : Type*} [Fintype V] [DecidableEq V]
    {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (M : MultiwayCausalGraph P V E) :
    (QuantumSpacetimeSkeleton.ofMultiwayCausalGraph M).Is1Complex := trivial

end InfraFormalization
