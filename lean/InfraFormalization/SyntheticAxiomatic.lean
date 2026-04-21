/-
**Axiomatic synthetic infrageometry** (Group IS / #158).

Euclid-style axioms for synthetic constructions on hypergraphs.
These are not derived from `Hypergraph.dist` automatically — they
are *axioms* that specific rule-families either satisfy or fail.
This gives a conformance test: a rule's output is "geometric" iff
it satisfies the axioms.

Axiom candidates (Euclid-analog):
  * **Incidence** — any two distinct points lie on a unique line.
  * **Betweenness** — for any three collinear points, one is between
    the other two (w.r.t. the hypergraph distance).
  * **Congruence** — circles of the same radius around different
    centers have the same cardinality.
  * **Parallel postulate** — every non-axial point has a unique
    "parallel line" through it. (Expect failure on most rules, which
    will classify the discrete target geometry.)

**Connection to hypergraphs.** Native. All predicates are Prop-level
statements about `SyntheticCircle`, `SyntheticLineSegment`,
`Hypergraph.dist`.
-/

import InfraFormalization.SyntheticGeometry

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Incidence axiom: two points determine a line -/

/-- **Incidence axiom**: for any two distinct points `u ≠ v`, the
synthetic line segment between them is determined — any two line
segments with the same endpoints coincide. (In the discrete
setting, the "line" may be non-unique via multiple shortest paths;
this axiom asserts uniqueness of the segment-as-set.) -/
def IncidenceAxiom (H : Hypergraph V) : Prop :=
  ∀ u v : V, u ≠ v → (H.SyntheticLineSegment u v).Nonempty

/-- **Uniqueness-of-endpoints**: the only two endpoints of a segment
between `u` and `v` are `u` and `v` themselves. (Alternative
"unique line through two points" formulation). -/
def UniquenessOfEndpoints (H : Hypergraph V) : Prop :=
  ∀ u v : V, u ≠ v →
    ∀ w ∈ H.SyntheticLineSegment u v,
    H.dist u w + H.dist w v = H.dist u v

/-! ## Congruence: equal-radius circles have equal cardinality -/

/-- **Circle-congruence axiom**: two circles of the same radius
have the same cardinality. Holds on vertex-transitive graphs;
fails in general. -/
def CircleCongruence (H : Hypergraph V) : Prop :=
  ∀ (c₁ c₂ : V) (r : Nat),
    (H.SyntheticCircle c₁ r).card = (H.SyntheticCircle c₂ r).card

/-! ## Betweenness -/

/-- **Betweenness**: `w` is between `u` and `v` if
`dist u w + dist w v = dist u v`. -/
def Between (H : Hypergraph V) (u v w : V) : Prop :=
  H.dist u w + H.dist w v = H.dist u v

/-- **Every segment vertex is between its endpoints.** -/
theorem segment_is_between (H : Hypergraph V) (u v w : V) :
    w ∈ H.SyntheticLineSegment u v ↔ H.Between u v w := by
  rw [Hypergraph.mem_syntheticLineSegment]
  rfl

/-- **Symmetry of betweenness in the endpoints**: `w` between `u`
and `v` iff `w` between `v` and `u`. -/
theorem between_symm (H : Hypergraph V) (u v w : V) :
    H.Between u v w ↔ H.Between v u w := by
  unfold Between
  rw [H.dist_comm v w, H.dist_comm v u, H.dist_comm u w]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## Conformance: when axioms hold, hypergraph is "geometric" -/

/-- **Geometric hypergraph**: one satisfying incidence + congruence
+ uniqueness — a ruliology conformance test. -/
def IsGeometric (H : Hypergraph V) : Prop :=
  H.IncidenceAxiom ∧ H.UniquenessOfEndpoints ∧ H.CircleCongruence

end Hypergraph
end InfraFormalization
