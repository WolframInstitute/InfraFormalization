import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
**Project-own Wasserstein-1 distance on finite supports** (task #214).

Defines `W_1(μ, ν)` on finite metric spaces as the minimum transport
cost over coupling plans:

  `W_1(μ, ν) = inf_{π ∈ couplings(μ, ν)} ∑_{x, y} π(x, y) · d(x, y)`.

A coupling plan is a nonnegative function `π : X × X → ℝ` with
row marginals `∑_y π(x, y) = μ(x)` and column marginals
`∑_x π(x, y) = ν(y)`.

This file provides:
  * `TransportPlan X μ ν` structure.
  * `TransportPlan.identity` — the self-coupling plan `π(x, y) = μ(x)
    if x = y else 0` (requires μ = ν).
  * `TransportPlan.cost π d` — the transport cost.
  * `cost_nonneg` when `d ≥ 0`.
  * `cost_self_zero` — identity coupling against a zero-self-distance
    metric has zero cost.
  * `wasserstein1` — `sInf` over transport plan costs.
  * `wasserstein1_self_zero` — `W_1(μ, μ) = 0` when `d(x, x) = 0`.
  * `wasserstein1_nonneg` — `W_1(μ, ν) ≥ 0` when `d ≥ 0`.

No reliance on any Mathlib optimal-transport API — this is the
start of our own framework, used downstream by tasks #18 (A7 cycle
Wasserstein O(1/n)), #19 (A8 d-torus lift), #215 (concrete d-torus
rate), and #220 (Ollivier-Ricci convergence).
-/

namespace InfraFormalization

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Transport plan** (coupling) between two finite probability-like
measures `μ, ν : X → ℝ`. Has nonneg entries and prescribed row /
column marginals. -/
structure TransportPlan (μ ν : X → ℝ) where
  π : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ π x y
  rowMarginal : ∀ x, ∑ y, π x y = μ x
  colMarginal : ∀ y, ∑ x, π x y = ν y

namespace TransportPlan

variable {μ ν : X → ℝ}

/-- **Identity coupling** when `μ = ν`: `π(x, y) = μ(x) [x = y]`.
Requires every component of `μ` non-negative (since the plan must
have nonneg entries). -/
noncomputable def identity (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) :
    TransportPlan μ μ where
  π := fun x y => if x = y then μ x else 0
  nonneg := by
    intros x y
    by_cases h : x = y
    · simp [h, hμ]
    · simp [h]
  rowMarginal := by
    intros x
    rw [Finset.sum_eq_single x]
    · simp
    · intros y _ hy
      simp [hy.symm]
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  colMarginal := by
    intros y
    rw [Finset.sum_eq_single y]
    · simp
    · intros x _ hx
      simp [hx]
    · intro hne
      exact absurd (Finset.mem_univ _) hne

/-- **Transport cost** of a plan against a non-negative cost
function `d`. -/
def cost (p : TransportPlan μ ν) (d : X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, p.π x y * d x y

/-- **Cost is non-negative** when `d` is non-negative. -/
theorem cost_nonneg (p : TransportPlan μ ν) (d : X → X → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) : 0 ≤ p.cost d := by
  unfold cost
  apply Finset.sum_nonneg
  intros x _
  apply Finset.sum_nonneg
  intros y _
  exact mul_nonneg (p.nonneg x y) (hd x y)

/-- **Cost of the identity coupling vanishes** when `d(x, x) = 0`
for every `x`. -/
theorem identity_cost_zero (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (d : X → X → ℝ) (hd0 : ∀ x, d x x = 0) :
    (identity μ hμ).cost d = 0 := by
  unfold cost identity
  simp only
  apply Finset.sum_eq_zero
  intros x _
  rw [Finset.sum_eq_single x]
  · simp [hd0]
  · intros y _ hy
    simp [hy.symm]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

end TransportPlan

/-- **Wasserstein-1 distance** on finite metric spaces: the infimum
of transport costs over all coupling plans between `μ` and `ν`. -/
noncomputable def wasserstein1 (d : X → X → ℝ) (μ ν : X → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ p : TransportPlan μ ν, p.cost d = c}

/-- **Non-negativity of W_1** when the cost function is non-negative
and at least one plan exists. -/
theorem wasserstein1_nonneg_of_plan (d : X → X → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (μ ν : X → ℝ) (p : TransportPlan μ ν) :
    0 ≤ wasserstein1 d μ ν := by
  unfold wasserstein1
  apply le_csInf
  · exact ⟨p.cost d, p, rfl⟩
  · rintro c ⟨q, rfl⟩
    exact q.cost_nonneg d hd

/-- **`W_1(μ, μ) = 0`** when `d(x, x) = 0` everywhere. The identity
coupling realises cost 0; the infimum cannot exceed 0 and is bounded
below by 0 by non-negativity. -/
theorem wasserstein1_self_eq_zero (d : X → X → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) :
    wasserstein1 d μ μ = 0 := by
  apply le_antisymm
  · -- W_1(μ, μ) ≤ 0 because identity plan has cost 0.
    unfold wasserstein1
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro c ⟨q, rfl⟩
      exact q.cost_nonneg d hd
    · exact ⟨TransportPlan.identity μ hμ,
        TransportPlan.identity_cost_zero μ hμ d hd0⟩
  · -- W_1(μ, μ) ≥ 0 by non-negativity.
    exact wasserstein1_nonneg_of_plan d hd μ μ (TransportPlan.identity μ hμ)

namespace TransportPlan

variable {μ ν : X → ℝ}

/-- **Transpose of a transport plan**: swap roles of source and target. -/
def transpose (p : TransportPlan μ ν) : TransportPlan ν μ where
  π := fun x y => p.π y x
  nonneg := fun x y => p.nonneg y x
  rowMarginal := p.colMarginal
  colMarginal := p.rowMarginal

/-- **Cost of the transpose under a symmetric metric** equals the
cost of the original plan. Uses `Finset.sum_comm` to swap the two
sums. -/
theorem cost_transpose_of_symm (p : TransportPlan μ ν) (d : X → X → ℝ)
    (hsym : ∀ x y, d x y = d y x) :
    (p.transpose).cost d = p.cost d := by
  unfold cost transpose
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intros x _
  refine Finset.sum_congr rfl ?_
  intros y _
  rw [hsym]

end TransportPlan

/-- **The cost set is in bijection with its transpose-cost set** for
a symmetric cost function: every plan's cost equals the transpose
plan's cost, and transpose is an involution. Together, the two sets
`{cost p | p ∈ Plans(μ, ν)}` and `{cost q | q ∈ Plans(ν, μ)}` are
equal. -/
theorem wasserstein1_costSet_eq (d : X → X → ℝ)
    (hsym : ∀ x y, d x y = d y x) (μ ν : X → ℝ) :
    {c : ℝ | ∃ p : TransportPlan μ ν, p.cost d = c}
      = {c : ℝ | ∃ q : TransportPlan ν μ, q.cost d = c} := by
  ext c
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.transpose, ?_⟩
    exact p.cost_transpose_of_symm d hsym
  · rintro ⟨q, rfl⟩
    refine ⟨q.transpose, ?_⟩
    exact q.cost_transpose_of_symm d hsym

/-- **Symmetry of W_1** under a symmetric cost function: transporting
from `μ` to `ν` costs the same as transporting from `ν` to `μ`. The
two coupling-cost sets are equal via plan transpose. -/
theorem wasserstein1_symm (d : X → X → ℝ) (hsym : ∀ x y, d x y = d y x)
    (μ ν : X → ℝ) : wasserstein1 d μ ν = wasserstein1 d ν μ := by
  unfold wasserstein1
  rw [wasserstein1_costSet_eq d hsym μ ν]

namespace TransportPlan

variable {μ ν : X → ℝ}

/-- **Scaling a transport plan** by a non-negative real `c` produces
a plan between the scaled marginals `c • μ` and `c • ν`. -/
def scale (p : TransportPlan μ ν) (c : ℝ) (hc : 0 ≤ c) :
    TransportPlan (fun x => c * μ x) (fun x => c * ν x) where
  π := fun x y => c * p.π x y
  nonneg := fun x y => mul_nonneg hc (p.nonneg x y)
  rowMarginal := fun x => by
    rw [← Finset.mul_sum]
    exact congrArg (c * ·) (p.rowMarginal x)
  colMarginal := fun y => by
    rw [← Finset.mul_sum]
    exact congrArg (c * ·) (p.colMarginal y)

/-- **Cost scales linearly** with the scalar. -/
theorem cost_scale (p : TransportPlan μ ν) (c : ℝ) (hc : 0 ≤ c)
    (d : X → X → ℝ) :
    (p.scale c hc).cost d = c * p.cost d := by
  unfold cost scale
  simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intros x _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intros y _
  ring

/-- **Two plans on disjoint row-supports combine additively**: the
sum of `π₁ + π₂` is a plan with marginals equal to the sums of the
corresponding marginals. -/
def add {μ₁ μ₂ ν₁ ν₂ : X → ℝ}
    (p : TransportPlan μ₁ ν₁) (q : TransportPlan μ₂ ν₂) :
    TransportPlan (fun x => μ₁ x + μ₂ x) (fun x => ν₁ x + ν₂ x) where
  π := fun x y => p.π x y + q.π x y
  nonneg := fun x y => add_nonneg (p.nonneg x y) (q.nonneg x y)
  rowMarginal := fun x => by
    rw [Finset.sum_add_distrib]
    rw [p.rowMarginal x, q.rowMarginal x]
  colMarginal := fun y => by
    rw [Finset.sum_add_distrib]
    rw [p.colMarginal y, q.colMarginal y]

/-- **Cost is additive over plan sum.** -/
theorem cost_add {μ₁ μ₂ ν₁ ν₂ : X → ℝ}
    (p : TransportPlan μ₁ ν₁) (q : TransportPlan μ₂ ν₂)
    (d : X → X → ℝ) :
    (p.add q).cost d = p.cost d + q.cost d := by
  unfold cost add
  simp only
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intros x _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intros y _
  ring

end TransportPlan

/-! ## Dirac-delta measures and their Wasserstein distance -/

/-- **Dirac-delta measure** at a point `x : X`: unit mass at `x`,
zero elsewhere. -/
def delta (x : X) : X → ℝ := fun y => if y = x then 1 else 0

theorem delta_nonneg (x y : X) : 0 ≤ delta x y := by
  unfold delta
  by_cases h : y = x <;> simp [h]

theorem delta_total (x : X) : ∑ y : X, delta x y = 1 := by
  unfold delta
  rw [Finset.sum_eq_single x]
  · simp
  · intros y _ hy
    simp [hy]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-- **Dirac-delta transport plan** between `δ_x` and `δ_y`: the unique
plan supported on `(x, y)` with mass `1`. -/
def deltaPlan (x y : X) : TransportPlan (delta x) (delta y) where
  π := fun a b => if a = x ∧ b = y then 1 else 0
  nonneg := by
    intros a b
    by_cases h : a = x ∧ b = y <;> simp [h]
  rowMarginal := by
    intro a
    unfold delta
    by_cases h : a = x
    · subst h
      rw [Finset.sum_eq_single y]
      · simp
      · intros b _ hb
        simp [hb]
      · intro hne
        exact absurd (Finset.mem_univ _) hne
    · have : ∀ b, (if a = x ∧ b = y then (1 : ℝ) else 0) = 0 := by
        intro b; simp [h]
      simp [this, h]
  colMarginal := by
    intro b
    unfold delta
    by_cases h : b = y
    · subst h
      rw [Finset.sum_eq_single x]
      · simp
      · intros a _ ha
        simp [ha]
      · intro hne
        exact absurd (Finset.mem_univ _) hne
    · have : ∀ a, (if a = x ∧ b = y then (1 : ℝ) else 0) = 0 := by
        intro a; simp [h]
      simp [this, h]

/-- **Dirac-delta plan cost equals `d x y`.** -/
theorem deltaPlan_cost (x y : X) (d : X → X → ℝ) :
    (deltaPlan x y).cost d = d x y := by
  unfold TransportPlan.cost deltaPlan
  simp only
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intros b _ hb
      simp [hb]
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  · intros a _ ha
    have : ∀ b, (if a = x ∧ b = y then (1 : ℝ) else 0) * d a b = 0 := by
      intro b
      by_cases hab : a = x ∧ b = y
      · exact absurd hab.1 ha
      · simp [hab]
    simp [this]
  · intro hne
    exact absurd (Finset.mem_univ _) hne

/-- **Uniqueness of the Dirac-delta coupling**: any transport plan
between `δ_x` and `δ_y` equals `deltaPlan x y` pointwise. The marginal
constraints force the plan to be supported only on `(x, y)` with
mass `1`. -/
theorem deltaPlan_unique (x y : X) (p : TransportPlan (delta x) (delta y))
    (a b : X) :
    p.π a b = (deltaPlan x y).π a b := by
  unfold deltaPlan
  simp only
  by_cases h : a = x ∧ b = y
  · -- a = x ∧ b = y: plan value must equal 1
    obtain ⟨hax, hby⟩ := h
    subst hax
    subst hby
    -- Need π a b = 1. Use rowMarginal x: ∑_b π x b = delta x x = 1.
    -- Since off-diagonal entries are 0 (forced by colMarginal), only π x y contributes.
    have hrow := p.rowMarginal a
    have hδx : delta a a = 1 := by unfold delta; simp
    rw [hδx] at hrow
    -- Show that π a b' = 0 for b' ≠ b via colMarginal.
    have hother : ∀ b', b' ≠ b → p.π a b' = 0 := by
      intros b' hbb'
      have hcol := p.colMarginal b'
      have hδy : delta b b' = 0 := by
        unfold delta; simp [hbb']
      rw [hδy] at hcol
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun a' _ => p.nonneg a' b') |>.mp hcol a (Finset.mem_univ a)
    rw [Finset.sum_eq_single b] at hrow
    · simpa using hrow
    · intros b' _ hb'
      exact hother b' hb'
    · intro hne
      exact absurd (Finset.mem_univ _) hne
  · -- a ≠ x or b ≠ y: plan value must be 0
    rw [if_neg h]
    rcases Decidable.not_and_iff_or_not.mp h with hax | hby
    · -- a ≠ x: rowMarginal at a is delta x a = 0.
      have hrow := p.rowMarginal a
      have hδ : delta x a = 0 := by unfold delta; simp [hax]
      rw [hδ] at hrow
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun b' _ => p.nonneg a b') |>.mp hrow b (Finset.mem_univ b)
    · -- b ≠ y: colMarginal at b is delta y b = 0.
      have hcol := p.colMarginal b
      have hδ : delta y b = 0 := by unfold delta; simp [hby]
      rw [hδ] at hcol
      exact Finset.sum_eq_zero_iff_of_nonneg
        (fun a' _ => p.nonneg a' b) |>.mp hcol a (Finset.mem_univ a)

/-- **Every plan between `δ_x` and `δ_y` has cost `d x y`.** -/
theorem deltaPlan_forall_cost (x y : X) (d : X → X → ℝ)
    (p : TransportPlan (delta x) (delta y)) :
    p.cost d = d x y := by
  have hπ : p.π = (deltaPlan x y).π := by
    funext a b
    exact deltaPlan_unique x y p a b
  unfold TransportPlan.cost
  rw [hπ]
  exact deltaPlan_cost x y d

/-- **W_1 between Dirac-deltas equals the distance**: `W_1(δ_x, δ_y) = d(x, y)`.
Every plan in the set achieves cost `d x y`, so the infimum is a
singleton and equals `d x y`. -/
theorem wasserstein1_delta_eq_dist (d : X → X → ℝ) (x y : X) :
    wasserstein1 d (delta x) (delta y) = d x y := by
  unfold wasserstein1
  have hset : {c : ℝ | ∃ p : TransportPlan (delta x) (delta y), p.cost d = c}
      = {d x y} := by
    ext c
    constructor
    · rintro ⟨p, hpc⟩
      simp only [Set.mem_singleton_iff]
      rw [← hpc]
      exact deltaPlan_forall_cost x y d p
    · rintro hc
      rw [Set.mem_singleton_iff] at hc
      refine ⟨deltaPlan x y, ?_⟩
      rw [deltaPlan_cost]
      exact hc.symm
  rw [hset]
  exact csInf_singleton _

end InfraFormalization
