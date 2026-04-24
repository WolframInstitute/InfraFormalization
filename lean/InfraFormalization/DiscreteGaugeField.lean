import InfraFormalization.HypergraphConnection
import InfraFormalization.FiberedGraph
import InfraFormalization.Holonomy

/-!
**Discrete gauge field via the Rung-4 connection** (G2 / #69).

In continuum physics a gauge field is a connection 1-form on a
principal G-bundle. Its discrete analogue on a hypergraph state is
exactly an edge-indexed assignment of elements of the structure group
`G` — that is, a `HypergraphConnection H G` (already formalised for
C7).

This file gives the gauge-field reinterpretation explicitly:
  * `DiscreteGaugeField H G := HypergraphConnection H G` (alias)
  * field-strength-as-holonomy-around-loop (when the group is a monoid,
    read the Wilson loop off of the `transportWalk` monoid-hom).
  * flat-gauge-field = trivial principal bundle (no holonomy).

Grounded: everything sits on a `Hypergraph V` — the gauge field is
literally a function on the adjacency relation of a hypergraph state.
The `FiberedGraph`-level holonomy / Wilson-loop machinery (from
`Holonomy.lean`) is re-exported through the gauge-field API.
-/

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Discrete gauge field** on a hypergraph state `H : Hypergraph V`,
taking values in a structure-type `G`. An alias for
`HypergraphConnection`, chosen to emphasise the physics interpretation
(principal-G-bundle connection). -/
abbrev DiscreteGaugeField (H : Hypergraph V) (G : Type*) : Type _ :=
  HypergraphConnection H G

namespace DiscreteGaugeField

variable {G : Type*}

/-- **Flat (trivial) gauge field**: identity element of `G` on every
adjacency. -/
def trivial [One G] (H : Hypergraph V) : DiscreteGaugeField H G :=
  HypergraphConnection.flat H G

/-- **Gauge-field transport** along a walk (abbrev for
`HypergraphConnection.transportWalk`). Wilson-loop / parallel transport
in the gauge-theory idiom. -/
abbrev gaugeTransport [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) {v w : V} (p : H.toSimpleGraph.Walk v w) : G :=
  A.transportWalk p

/-- **Gauge-field holonomy at a base vertex**: transport around a loop
(abbrev for `HypergraphConnection.holonomy`). -/
abbrev gaugeHolonomy [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) {v : V} (loop : H.toSimpleGraph.Walk v v) : G :=
  A.holonomy loop

/-- **Flatness of a gauge field** in the physics sense: vanishing
field strength, i.e. all holonomies trivial. -/
abbrev IsFlat [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) : Prop :=
  HypergraphConnection.IsFlat A

/-- **The trivial gauge field is flat.** -/
theorem trivial_isFlat [Monoid G] (H : Hypergraph V) :
    IsFlat (trivial H : DiscreteGaugeField H G) :=
  HypergraphConnection.flat_isFlat H G

/-- **Wilson-loop concatenation**: transporting along a loop and then
a subsequent loop at the same basepoint composes multiplicatively.
Direct consequence of `HypergraphConnection.transportWalk_append`. -/
theorem gaugeHolonomy_append [Monoid G]
    {H : Hypergraph V} (A : DiscreteGaugeField H G)
    {v : V} (p q : H.toSimpleGraph.Walk v v) :
    gaugeHolonomy A (p.append q) = gaugeHolonomy A p * gaugeHolonomy A q :=
  HypergraphConnection.transportWalk_append A p q

end DiscreteGaugeField

end InfraFormalization
