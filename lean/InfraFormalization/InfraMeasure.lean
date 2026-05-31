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

/-! ## Coupling + transport cost (foundation for Ollivier-Ricci screener)

A **coupling** of two `InfraMeasureData`s `m₁`, `m₂` on `V` is a
non-negative joint weight on `V × V` whose `V`-marginals (over a
finite carrier list) recover the originals. The W₁ Wasserstein
distance is the infimum of transport costs over couplings; we
formalise the per-coupling cost here as the foundation. -/

/-- A coupling on `V × V`: non-negative weights on ordered pairs. -/
structure Coupling (V : Type*) where
  jointWeight : V → V → ℝ
  jointNonneg : ∀ u v, 0 ≤ jointWeight u v

namespace Coupling

variable {V : Type*}

/-- The first marginal of a coupling over an explicit carrier: the
weight at `u` is the sum of `jointWeight u v` for `v` in the carrier. -/
def marginal1 (γ : Coupling V) (carrier : List V) (u : V) : ℝ :=
  carrier.foldr (fun v acc => γ.jointWeight u v + acc) 0

/-- The second marginal of a coupling over an explicit carrier. -/
def marginal2 (γ : Coupling V) (carrier : List V) (v : V) : ℝ :=
  carrier.foldr (fun u acc => γ.jointWeight u v + acc) 0

/-- Marginal-1 non-negativity. -/
theorem marginal1_nonneg (γ : Coupling V) (carrier : List V) (u : V) :
    0 ≤ γ.marginal1 carrier u := by
  unfold marginal1
  induction carrier with
  | nil => simp
  | cons v rest ih =>
    show 0 ≤ γ.jointWeight u v + List.foldr _ 0 rest
    have := γ.jointNonneg u v
    linarith

/-- Marginal-2 non-negativity. -/
theorem marginal2_nonneg (γ : Coupling V) (carrier : List V) (v : V) :
    0 ≤ γ.marginal2 carrier v := by
  unfold marginal2
  induction carrier with
  | nil => simp
  | cons u rest ih =>
    show 0 ≤ γ.jointWeight u v + List.foldr _ 0 rest
    have := γ.jointNonneg u v
    linarith

end Coupling

/-- A coupling **respects** a pair of `InfraMeasureData`s if its
marginals over the carrier equal the input measures' weights. -/
def IsCouplingOf {V : Type*} (carrier : List V)
    (γ : Coupling V) (m₁ m₂ : InfraMeasureData V) : Prop :=
  (∀ u, γ.marginal1 carrier u = m₁.weight u) ∧
  (∀ v, γ.marginal2 carrier v = m₂.weight v)

/-- **Transport cost** of a coupling under a non-negative cost
function `c : V × V → ℝ` (cost of moving one unit of mass from `u` to
`v`): the sum over the carrier-square of `c u v * γ.jointWeight u v`.
For W₁ on a metric space, use `c u v := d u v` (the graph distance).
Defined via a flattened list of (u, v)-pairs to keep induction clean. -/
def transportCost {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (γ : Coupling V) : ℝ :=
  (carrier.flatMap (fun u =>
    carrier.map (fun v => cost u v * γ.jointWeight u v))).foldr (· + ·) 0

/-- Helper: a foldr-sum of a non-negative list is non-negative. -/
theorem foldr_add_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ l.foldr (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    show 0 ≤ x + rest.foldr (· + ·) 0
    have h_head : 0 ≤ x := h x (by simp)
    have h_rest : 0 ≤ rest.foldr (· + ·) 0 := ih (fun y hy => h y (by simp [hy]))
    linarith

/-- **Transport cost is non-negative** when the cost function and
coupling are both non-negative. -/
theorem transportCost_nonneg {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (hcost : ∀ u v, 0 ≤ cost u v)
    (γ : Coupling V) :
    0 ≤ transportCost carrier cost γ := by
  unfold transportCost
  apply foldr_add_nonneg
  intro x hx
  simp [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨u, _, v, _, h_eq⟩ := hx
  rw [← h_eq]
  exact mul_nonneg (hcost u v) (γ.jointNonneg u v)

end InfraMeasure
end InfraFormalization
