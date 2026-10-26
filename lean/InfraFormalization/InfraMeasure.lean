/-
Weight functions on vertices, couplings and transport cost.

This module defines `InfraMeasureData V`, a non-negative weight function on a vertex type, after
P. Hajek's `InfraMeasure` in the `SyntheticInfrageometry` paclet
(`resources/SyntheticInfrageometry/Kernel/Tools.wl`). It defines total mass over a vertex list,
restriction to a Boolean predicate, the uniform weight on a list and the Dirac weight, together with
couplings, their marginals over a carrier list, transport cost, and the minimum transport cost over
a finite list of couplings. The results are non-negativity and elementary identities.
-/

import InfraFormalization.Hypergraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace InfraMeasure

/-- A non-negative weight function on a vertex type `V`. -/
structure InfraMeasureData (V : Type*) where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v

namespace InfraMeasureData

variable {V : Type*}

/-- The sum of the weights of the vertices in the list `vs`, counted with multiplicity. -/
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

/-- The weight that equals `m.weight v` where `P v` holds and 0 elsewhere. -/
def restrict (m : InfraMeasureData V) (P : V → Bool) : InfraMeasureData V where
  weight v := if P v then m.weight v else 0
  nonneg v := by
    by_cases h : P v
    · simp [h]; exact m.nonneg v
    · simp [h]

/-- Restricting by `P` and then by `Q` gives the same weight at every vertex as restricting by
`P && Q`. -/
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

/-- The weight equal to 1 on the vertices in `vs` and 0 elsewhere. -/
def uniformOn {V : Type*} [DecidableEq V] (vs : List V) :
    InfraMeasureData V where
  weight v := if v ∈ vs then 1 else 0
  nonneg v := by
    by_cases h : v ∈ vs
    · simp [h]
    · simp [h]

/-- The weight equal to 1 at `v₀` and 0 elsewhere. -/
def dirac {V : Type*} [DecidableEq V] (v₀ : V) : InfraMeasureData V where
  weight v := if v = v₀ then 1 else 0
  nonneg v := by
    by_cases h : v = v₀
    · simp [h]
    · simp [h]

/-- The Dirac weight at `v₀` equals 1 at `v₀`. -/
@[simp] theorem dirac_self {V : Type*} [DecidableEq V] (v₀ : V) :
    (dirac v₀).weight v₀ = 1 := by
  unfold dirac
  simp

/-- The Dirac weight at `v₀` equals 0 at every `v ≠ v₀`. -/
theorem dirac_of_ne {V : Type*} [DecidableEq V] (v₀ v : V) (h : v ≠ v₀) :
    (dirac v₀).weight v = 0 := by
  unfold dirac
  simp [h]

/-! ## Couplings and transport cost

A coupling is a non-negative weight on `V × V`. `IsCouplingOf carrier γ m₁ m₂` states that the
marginals of `γ` over the list `carrier` equal the weights of `m₁` and `m₂`. -/

/-- A non-negative weight on ordered pairs of vertices. -/
structure Coupling (V : Type*) where
  jointWeight : V → V → ℝ
  jointNonneg : ∀ u v, 0 ≤ jointWeight u v

namespace Coupling

variable {V : Type*}

/-- The first marginal over `carrier`: the sum of `γ.jointWeight u v` over `v` in `carrier`. -/
def marginal1 (γ : Coupling V) (carrier : List V) (u : V) : ℝ :=
  carrier.foldr (fun v acc => γ.jointWeight u v + acc) 0

/-- The second marginal over `carrier`: the sum of `γ.jointWeight u v` over `u` in `carrier`. -/
def marginal2 (γ : Coupling V) (carrier : List V) (v : V) : ℝ :=
  carrier.foldr (fun u acc => γ.jointWeight u v + acc) 0

/-- The first marginal is non-negative. -/
theorem marginal1_nonneg (γ : Coupling V) (carrier : List V) (u : V) :
    0 ≤ γ.marginal1 carrier u := by
  unfold marginal1
  induction carrier with
  | nil => simp
  | cons v rest ih =>
    show 0 ≤ γ.jointWeight u v + List.foldr _ 0 rest
    have := γ.jointNonneg u v
    linarith

/-- The second marginal is non-negative. -/
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

/-- The marginals of `γ` over `carrier` equal the weights of `m₁` and `m₂` at every vertex. -/
def IsCouplingOf {V : Type*} (carrier : List V)
    (γ : Coupling V) (m₁ m₂ : InfraMeasureData V) : Prop :=
  (∀ u, γ.marginal1 carrier u = m₁.weight u) ∧
  (∀ v, γ.marginal2 carrier v = m₂.weight v)

/-- The sum over `u, v` in `carrier` of `cost u v * γ.jointWeight u v`. With `cost` a graph
distance and `γ` a coupling of `m₁` and `m₂`, this is the cost whose minimum over couplings is the
Wasserstein-1 distance. -/
def transportCost {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (γ : Coupling V) : ℝ :=
  (carrier.flatMap (fun u =>
    carrier.map (fun v => cost u v * γ.jointWeight u v))).foldr (· + ·) 0

/-- The `foldr` sum of a list of non-negative reals is non-negative. -/
theorem foldr_add_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ l.foldr (· + ·) 0 := by
  induction l with
  | nil => simp
  | cons x rest ih =>
    show 0 ≤ x + rest.foldr (· + ·) 0
    have h_head : 0 ≤ x := h x (by simp)
    have h_rest : 0 ≤ rest.foldr (· + ·) 0 := ih (fun y hy => h y (by simp [hy]))
    linarith

/-- The transport cost is non-negative when the cost function is non-negative. -/
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

/-! ## Transport cost of the product weight and of a list of couplings

`w1ProductCost` is the transport cost of the product weight `m₁ u * m₂ v`. `w1InfimumOver` is the
minimum transport cost over a given list of couplings. Neither definition requires the couplings to
satisfy `IsCouplingOf`. -/

/-- The coupling with joint weight `m₁.weight u * m₂.weight v`. Its marginals equal `m₁` and `m₂`
only when the other weight has total mass 1 on the carrier. -/
def productCoupling {V : Type*}
    (m₁ m₂ : InfraMeasureData V) : Coupling V where
  jointWeight u v := m₁.weight u * m₂.weight v
  jointNonneg u v := mul_nonneg (m₁.nonneg u) (m₂.nonneg v)

/-- The transport cost of `productCoupling m₁ m₂`. -/
def w1ProductCost {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (m₁ m₂ : InfraMeasureData V) : ℝ :=
  transportCost carrier cost (productCoupling m₁ m₂)

/-- `w1ProductCost` is non-negative when the cost function is non-negative. -/
theorem w1ProductUpper_nonneg {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (hcost : ∀ u v, 0 ≤ cost u v)
    (m₁ m₂ : InfraMeasureData V) :
    0 ≤ w1ProductCost carrier cost m₁ m₂ :=
  transportCost_nonneg carrier cost hcost _

/-- The minimum of `transportCost carrier cost γ` over `γ` in `candidates`, or `default` if the list
is empty. -/
def w1InfimumOver {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (candidates : List (Coupling V))
    (default : ℝ) : ℝ :=
  match candidates with
  | []      => default
  | γ :: γs => γs.foldr
      (fun γ' acc => min (transportCost carrier cost γ') acc)
      (transportCost carrier cost γ)

/-- `w1InfimumOver` is at most the transport cost of each member of `candidates`. -/
theorem w1InfimumOver_le_member {V : Type*} (carrier : List V)
    (cost : V → V → ℝ) (candidates : List (Coupling V))
    (default : ℝ) (γ : Coupling V) (hγ : γ ∈ candidates) :
    w1InfimumOver carrier cost candidates default
      ≤ transportCost carrier cost γ := by
  cases candidates with
  | nil => simp at hγ
  | cons γ' γs =>
    unfold w1InfimumOver
    simp only [List.mem_cons] at hγ
    rcases hγ with heq | hmem
    · subst heq
      induction γs with
      | nil => exact le_refl _
      | cons γ'' rest ih =>
        show min (transportCost carrier cost γ'') _ ≤ transportCost carrier cost γ
        calc _ ≤ _ := min_le_right _ _
             _ ≤ _ := ih
    · induction γs with
      | nil => simp at hmem
      | cons γ'' rest ih =>
        show min (transportCost carrier cost γ'') _ ≤ transportCost carrier cost γ
        simp only [List.mem_cons] at hmem
        rcases hmem with heq | hmem'
        · subst heq
          exact min_le_left _ _
        · calc _ ≤ _ := min_le_right _ _
               _ ≤ _ := ih hmem'

end InfraMeasure
end InfraFormalization
