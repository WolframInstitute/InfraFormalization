/-
**Counting measure on a hypergraph + pushforward** (task A5 / #16).

For a finite-vertex `Hypergraph V` (`[Fintype V]`), the counting
measure assigns every vertex unit mass; the uniform probability
measure normalises by `|V|`. Pushing forward under an embedding
`φ : V → X` into any measurable space gives a finite discrete
measure on `X` — the object whose `n → ∞` weak limit to Lebesgue
measure is the content of A6 / A7.

**Connection to hypergraphs.** Native: the measure only depends on
the vertex set `V` (Fintype), but the `Hypergraph V` argument
records the Wolfram-model state we're measuring the geometry of.
-/

import InfraFormalization.HypergraphDistance
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V]

/-- **Counting measure on the vertex set** of a hypergraph. Each vertex
carries unit mass; total mass equals `|V|`. Depends only on the
Fintype / MeasurableSpace structure of `V`. -/
noncomputable def countingMeasure (_ : Hypergraph V) : MeasureTheory.Measure V :=
  MeasureTheory.Measure.count

/-- **Uniform probability measure on the vertex set** — counting measure
normalised by `|V|`. Well-defined when `V` is nonempty. -/
noncomputable def uniformProbability (H : Hypergraph V) :
    MeasureTheory.Measure V :=
  ((Fintype.card V : ENNReal))⁻¹ • countingMeasure H

/-- **Pushforward under an embedding** `φ : V → X`. For any measurable
space `X` and measurable `φ`, push the counting measure on `V` forward
to get a finite discrete measure on `X` supported on `φ '' univ`. -/
noncomputable def pushforwardCounting (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] (φ : V → X) :
    MeasureTheory.Measure X :=
  (countingMeasure H).map φ

/-- **Pushforward of the uniform probability**. -/
noncomputable def pushforwardUniform (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] (φ : V → X) :
    MeasureTheory.Measure X :=
  (uniformProbability H).map φ

/-- **Counting measure of the full vertex set** equals `|V|`. -/
theorem countingMeasure_univ (H : Hypergraph V) :
    countingMeasure H (Set.univ : Set V) = (Fintype.card V : ENNReal) := by
  unfold countingMeasure
  rw [show (Set.univ : Set V) = ((Finset.univ : Finset V) : Set V) from
        (Finset.coe_univ).symm]
  rw [MeasureTheory.Measure.count_apply_finset]
  rw [Finset.card_univ]

/-- **Uniform probability is a probability measure** when `V` is
nonempty: total mass 1. -/
theorem uniformProbability_univ [Nonempty V] (H : Hypergraph V) :
    uniformProbability H (Set.univ : Set V) = 1 := by
  unfold uniformProbability
  rw [MeasureTheory.Measure.smul_apply, countingMeasure_univ]
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  rw [smul_eq_mul]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hcard_pos.ne'
  · exact ENNReal.natCast_ne_top _

/-- **Pushforward preserves total mass.** If `φ : V → X` is measurable,
the pushforward uniform measure on `X` has total mass 1 (the full set
`Set.univ : Set X` has preimage `Set.univ : Set V`, which the uniform
probability measures at 1). -/
theorem pushforwardUniform_univ [Nonempty V] (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] {φ : V → X} (hφ : Measurable φ) :
    pushforwardUniform H φ (Set.univ : Set X) = 1 := by
  unfold pushforwardUniform
  rw [MeasureTheory.Measure.map_apply hφ MeasurableSet.univ]
  rw [show φ ⁻¹' (Set.univ : Set X) = Set.univ from rfl]
  exact uniformProbability_univ H

/-- **Pushforward of the counting measure has total mass `|V|`.** This
is the un-normalised analog of `pushforwardUniform_univ`. -/
theorem pushforwardCounting_univ (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] {φ : V → X} (hφ : Measurable φ) :
    pushforwardCounting H φ (Set.univ : Set X) = (Fintype.card V : ENNReal) := by
  unfold pushforwardCounting
  rw [MeasureTheory.Measure.map_apply hφ MeasurableSet.univ]
  rw [show φ ⁻¹' (Set.univ : Set X) = Set.univ from rfl]
  exact countingMeasure_univ H

end Hypergraph
end InfraFormalization
