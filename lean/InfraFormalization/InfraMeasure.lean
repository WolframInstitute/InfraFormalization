/-
**InfraMeasure: synthetic measure primitive on a hypergraph** (#388
starter).

A measure-theoretic primitive built directly from the synthetic
hypergraph data — not the marginal of a probability law on any
continuum limit. Following PHAJEK's `InfraMeasure` in the
`SyntheticInfrageometry` paclet (renamed from `VisitMeasure` in
commits `9f34fb4` → `38693c2` → `eb68944`,
`resources/SyntheticInfrageometry/Kernel/Tools.wl`).

**F5 sharpening realised at the type level.** A measure on a graph
is now its own kind of mathematical object (an `InfraMeasureData V`);
whether it can be realised as the marginal of a probability measure
on a continuum object is a separate question (the HVLE
projective-limit obstruction documented in `Refutations/F5Illdefined.lean`
and `notes/phajek_macro_observer_notes.txt`). G1 Eq 88 conflates the
two — a category error this module makes structural.

**Starter scope.** Bare primitives: vertex-weight data + non-negativity
witness, total mass over an explicit vertex list, restriction by a
Bool predicate, uniform measure on a finite vertex list, Dirac point
mass. Ollivier-Ricci screener (W₁ between vertex-neighbourhood
InfraMeasure-style measures, #368) and visit-measure walks on a graph
are downstream targets.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace InfraMeasure

/-- **Synthetic measure on a vertex type `V`**: a non-negative weight
function. Decoupled from `MeasureTheory.Measure` — this is an
infrageometric construct of its own kind, not a probability measure
on a continuum. -/
structure InfraMeasureData (V : Type*) where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v

namespace InfraMeasureData

variable {V : Type*}

/-- Total mass over an explicit list of vertices (sum of weights, with
multiplicities — caller is responsible for dedup if desired). -/
def totalMass (m : InfraMeasureData V) (vs : List V) : ℝ :=
  vs.foldr (fun v acc => m.weight v + acc) 0

/-- Total mass is non-negative. -/
theorem totalMass_nonneg (m : InfraMeasureData V) (vs : List V) :
    0 ≤ m.totalMass vs := by
  induction vs with
  | nil => simp [totalMass]
  | cons v rest ih =>
    show 0 ≤ m.weight v + m.totalMass rest
    have := m.nonneg v
    linarith

/-- Total mass on the empty list is zero. -/
@[simp] theorem totalMass_nil (m : InfraMeasureData V) :
    m.totalMass [] = 0 := rfl

/-- Cons recurrence for `totalMass`. -/
@[simp] theorem totalMass_cons (m : InfraMeasureData V) (v : V) (vs : List V) :
    m.totalMass (v :: vs) = m.weight v + m.totalMass vs := rfl

/-- **Restrict** the measure to a Bool predicate: weights outside the
predicate become `0`. The restriction is again an `InfraMeasureData`. -/
def restrict (m : InfraMeasureData V) (P : V → Bool) : InfraMeasureData V where
  weight v := if P v then m.weight v else 0
  nonneg v := by
    by_cases h : P v
    · simp [h]; exact m.nonneg v
    · simp [h]

/-- Restricting twice composes: `restrict (restrict m P) Q = restrict m (P ∧ Q)`. -/
theorem restrict_restrict (m : InfraMeasureData V) (P Q : V → Bool) (v : V) :
    ((m.restrict P).restrict Q).weight v
      = (m.restrict (fun x => P x && Q x)).weight v := by
  unfold restrict
  by_cases hP : P v
  · by_cases hQ : Q v
    · simp [hP, hQ]
    · simp [hP, hQ]
  · simp [hP]

end InfraMeasureData

/-- **Uniform measure** on a finite vertex list: weight `1` for every
vertex in the list, `0` outside. -/
def uniformOn {V : Type*} [DecidableEq V] (vs : List V) :
    InfraMeasureData V where
  weight v := if v ∈ vs then 1 else 0
  nonneg v := by
    by_cases h : v ∈ vs
    · simp [h]
    · simp [h]

/-- **Dirac point mass** at a single vertex `v₀`: weight `1` at `v₀`,
`0` elsewhere. -/
def dirac {V : Type*} [DecidableEq V] (v₀ : V) : InfraMeasureData V where
  weight v := if v = v₀ then 1 else 0
  nonneg v := by
    by_cases h : v = v₀
    · simp [h]
    · simp [h]

/-- **Dirac is supported at a single point.** -/
@[simp] theorem dirac_self {V : Type*} [DecidableEq V] (v₀ : V) :
    (dirac v₀).weight v₀ = 1 := by
  unfold dirac
  simp

/-- **Off-support weight of a Dirac is zero.** -/
theorem dirac_of_ne {V : Type*} [DecidableEq V] (v₀ v : V) (h : v ≠ v₀) :
    (dirac v₀).weight v = 0 := by
  unfold dirac
  simp [h]

end InfraMeasure
end InfraFormalization
