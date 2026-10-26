import InfraFormalization.HypergraphConnection
import InfraFormalization.FiberedGraph
import InfraFormalization.Holonomy

/-!
Discrete gauge fields as hypergraph connections.

This module defines `DiscreteGaugeField H G` as an abbreviation for
`HypergraphConnection H G`, with abbreviations for transport along a walk,
holonomy around a loop, and flatness. It proves that the trivial field is
flat and that holonomy of a concatenated loop is the product of the
holonomies.
-/

namespace InfraFormalization

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An abbreviation for `HypergraphConnection H G`. -/
abbrev DiscreteGaugeField (H : Hypergraph V) (G : Type*) : Type _ :=
  HypergraphConnection H G

namespace DiscreteGaugeField

variable {G : Type*}

/-- The field with value `1 : G` on every adjacency. -/
def trivial [One G] (H : Hypergraph V) : DiscreteGaugeField H G :=
  HypergraphConnection.flat H G

/-- Transport along a walk, `HypergraphConnection.transportWalk`. -/
abbrev gaugeTransport [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) {v w : V} (p : H.toSimpleGraph.Walk v w) : G :=
  A.transportWalk p

/-- Holonomy around a loop at `v`, `HypergraphConnection.holonomy`. -/
abbrev gaugeHolonomy [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) {v : V} (loop : H.toSimpleGraph.Walk v v) : G :=
  A.holonomy loop

/-- Every loop has holonomy `1` (`HypergraphConnection.IsFlat`). -/
abbrev IsFlat [Monoid G] {H : Hypergraph V}
    (A : DiscreteGaugeField H G) : Prop :=
  HypergraphConnection.IsFlat A

/-- The trivial field satisfies `IsFlat`. -/
theorem trivial_isFlat [Monoid G] (H : Hypergraph V) :
    IsFlat (trivial H : DiscreteGaugeField H G) :=
  HypergraphConnection.flat_isFlat H G

/-- The holonomy of the concatenation `p.append q` of two loops at `v` is
the product of their holonomies. -/
theorem gaugeHolonomy_append [Monoid G]
    {H : Hypergraph V} (A : DiscreteGaugeField H G)
    {v : V} (p q : H.toSimpleGraph.Walk v v) :
    gaugeHolonomy A (p.append q) = gaugeHolonomy A p * gaugeHolonomy A q :=
  HypergraphConnection.transportWalk_append A p q

end DiscreteGaugeField

end InfraFormalization
