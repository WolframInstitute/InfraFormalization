/-
Counting measure on the vertex set of a hypergraph, and its pushforward.

For a finite vertex type `V`, the counting measure gives each vertex mass 1 and the
uniform probability measure divides it by `|V|`. Both are pushed forward along a map
`φ : V → X` into a measurable space. The module proves the total masses: `|V|` for the
counting measure and 1 for the uniform measure, before and after pushforward. The
measures depend only on `V`; the `Hypergraph V` argument is not used.
-/

import InfraFormalization.HypergraphDistance
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace InfraFormalization
namespace Hypergraph

variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V]

/-- The counting measure on `V`. The hypergraph argument is not used. -/
noncomputable def countingMeasure (_ : Hypergraph V) : MeasureTheory.Measure V :=
  MeasureTheory.Measure.count

/-- The counting measure on `V` multiplied by `|V|⁻¹`. -/
noncomputable def uniformProbability (H : Hypergraph V) :
    MeasureTheory.Measure V :=
  ((Fintype.card V : ENNReal))⁻¹ • countingMeasure H

/-- The pushforward of `countingMeasure H` along `φ : V → X`. -/
noncomputable def pushforwardCounting (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] (φ : V → X) :
    MeasureTheory.Measure X :=
  (countingMeasure H).map φ

/-- The pushforward of `uniformProbability H` along `φ : V → X`. -/
noncomputable def pushforwardUniform (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] (φ : V → X) :
    MeasureTheory.Measure X :=
  (uniformProbability H).map φ

/-- The counting measure of `Set.univ` equals `|V|`. -/
theorem countingMeasure_univ (H : Hypergraph V) :
    countingMeasure H (Set.univ : Set V) = (Fintype.card V : ENNReal) := by
  unfold countingMeasure
  rw [show (Set.univ : Set V) = ((Finset.univ : Finset V) : Set V) from
        (Finset.coe_univ).symm]
  rw [MeasureTheory.Measure.count_apply_finset]
  rw [Finset.card_univ]

/-- For nonempty `V`, the uniform measure of `Set.univ` equals 1. -/
theorem uniformProbability_univ [Nonempty V] (H : Hypergraph V) :
    uniformProbability H (Set.univ : Set V) = 1 := by
  unfold uniformProbability
  rw [MeasureTheory.Measure.smul_apply, countingMeasure_univ]
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  rw [smul_eq_mul]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hcard_pos.ne'
  · exact ENNReal.natCast_ne_top _

/-- For nonempty `V` and measurable `φ`, the pushforward uniform measure of
`Set.univ : Set X` equals 1. -/
theorem pushforwardUniform_univ [Nonempty V] (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] {φ : V → X} (hφ : Measurable φ) :
    pushforwardUniform H φ (Set.univ : Set X) = 1 := by
  unfold pushforwardUniform
  rw [MeasureTheory.Measure.map_apply hφ MeasurableSet.univ]
  rw [show φ ⁻¹' (Set.univ : Set X) = Set.univ from rfl]
  exact uniformProbability_univ H

/-- For measurable `φ`, the pushforward counting measure of `Set.univ : Set X`
equals `|V|`. -/
theorem pushforwardCounting_univ (H : Hypergraph V)
    {X : Type*} [MeasurableSpace X] {φ : V → X} (hφ : Measurable φ) :
    pushforwardCounting H φ (Set.univ : Set X) = (Fintype.card V : ENNReal) := by
  unfold pushforwardCounting
  rw [MeasureTheory.Measure.map_apply hφ MeasurableSet.univ]
  rw [show φ ⁻¹' (Set.univ : Set X) = Set.univ from rfl]
  exact countingMeasure_univ H

end Hypergraph
end InfraFormalization
