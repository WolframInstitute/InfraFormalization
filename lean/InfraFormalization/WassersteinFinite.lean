import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Wasserstein-1 distance on a finite type.

A transport plan between `μ ν : X → ℝ` is a nonnegative `π : X → X → ℝ`
with row sums `μ` and column sums `ν`. `wasserstein1 d μ ν` is the infimum
of `∑ π x y · d x y` over plans. This module defines identity, transpose,
scaled, summed, tensor, Dirac and glued plans, and proves for nonnegative
`d`: nonnegativity, `W_1(μ, μ) = 0` when `d x x = 0`, symmetry for
symmetric `d`, `W_1(δ_x, δ_y) = d x y`, the bound by the supremum of `d`,
`|E_μ f − E_ν f| ≤ L · W_1(μ, ν)` for `L`-Lipschitz `f`, and the triangle
inequality for probability vectors.
-/

namespace InfraFormalization

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A nonnegative `π : X → X → ℝ` with row sums `μ` and column sums `ν`. -/
structure TransportPlan (μ ν : X → ℝ) where
  π : X → X → ℝ
  nonneg : ∀ x y, 0 ≤ π x y
  rowMarginal : ∀ x, ∑ y, π x y = μ x
  colMarginal : ∀ y, ∑ x, π x y = ν y

namespace TransportPlan

variable {μ ν : X → ℝ}

/-- The plan `π(x, y) = μ(x)` if `x = y` and 0 otherwise, between `μ` and
itself, for nonnegative `μ`. -/
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

/-- `∑_x ∑_y π x y · d x y`. -/
def cost (p : TransportPlan μ ν) (d : X → X → ℝ) : ℝ :=
  ∑ x, ∑ y, p.π x y * d x y

/-- The cost is nonnegative when `d` is nonnegative. -/
theorem cost_nonneg (p : TransportPlan μ ν) (d : X → X → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) : 0 ≤ p.cost d := by
  unfold cost
  apply Finset.sum_nonneg
  intros x _
  apply Finset.sum_nonneg
  intros y _
  exact mul_nonneg (p.nonneg x y) (hd x y)

/-- The identity plan has cost 0 when `d x x = 0` for every `x`. -/
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

/-- The infimum of `p.cost d` over transport plans `p` between `μ` and
`ν`. -/
noncomputable def wasserstein1 (d : X → X → ℝ) (μ ν : X → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ p : TransportPlan μ ν, p.cost d = c}

/-- If `d` is nonnegative and some plan between `μ` and `ν` exists, then
`wasserstein1 d μ ν ≥ 0`. -/
theorem wasserstein1_nonneg_of_plan (d : X → X → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) (μ ν : X → ℝ) (p : TransportPlan μ ν) :
    0 ≤ wasserstein1 d μ ν := by
  unfold wasserstein1
  apply le_csInf
  · exact ⟨p.cost d, p, rfl⟩
  · rintro c ⟨q, rfl⟩
    exact q.cost_nonneg d hd

/-- For nonnegative `d` with `d x x = 0` and nonnegative `μ`,
`wasserstein1 d μ μ = 0`. -/
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

/-- The plan `π(y, x)` between `ν` and `μ`. -/
def transpose (p : TransportPlan μ ν) : TransportPlan ν μ where
  π := fun x y => p.π y x
  nonneg := fun x y => p.nonneg y x
  rowMarginal := p.colMarginal
  colMarginal := p.rowMarginal

/-- For symmetric `d`, the transpose has the same cost. -/
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

/-- For symmetric `d`, the set of plan costs between `μ` and `ν` equals the
set of plan costs between `ν` and `μ`. -/
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

/-- For symmetric `d`, `wasserstein1 d μ ν = wasserstein1 d ν μ`. -/
theorem wasserstein1_symm (d : X → X → ℝ) (hsym : ∀ x y, d x y = d y x)
    (μ ν : X → ℝ) : wasserstein1 d μ ν = wasserstein1 d ν μ := by
  unfold wasserstein1
  rw [wasserstein1_costSet_eq d hsym μ ν]

namespace TransportPlan

variable {μ ν : X → ℝ}

/-- For `c ≥ 0`, `c · π` is a plan between `c • μ` and `c • ν`. -/
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

/-- The cost of `c · π` is `c` times the cost of `π`. -/
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

/-- The entrywise sum of a plan between `μ₁` and `ν₁` and a plan between
`μ₂` and `ν₂` is a plan between `μ₁ + μ₂` and `ν₁ + ν₂`. -/
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

/-- The cost of the sum of two plans is the sum of their costs. -/
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

/-- For nonnegative `μ`, `ν` with total mass 1, `π(x, y) = μ(x) ν(y)` is a
plan between `μ` and `ν`. -/
def tensor (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (_hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1) :
    TransportPlan μ ν where
  π := fun x y => μ x * ν y
  nonneg := fun x y => mul_nonneg (hμ x) (hν y)
  rowMarginal := fun x => by
    rw [← Finset.mul_sum, hνsum, mul_one]
  colMarginal := fun y => by
    rw [← Finset.sum_mul, _hμsum, one_mul]

/-- The cost of the tensor plan is `∑_x ∑_y μ x ν y d x y`. -/
theorem tensor_cost (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1)
    (d : X → X → ℝ) :
    (tensor μ ν hμ hν hμsum hνsum).cost d
      = ∑ x, ∑ y, μ x * ν y * d x y := by
  unfold cost tensor
  rfl

end TransportPlan

/-- For nonnegative `d` and nonnegative `μ`, `ν` of total mass 1,
`wasserstein1 d μ ν ≥ 0`. -/
theorem wasserstein1_nonneg
    (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1) :
    0 ≤ wasserstein1 d μ ν :=
  wasserstein1_nonneg_of_plan d hd μ ν
    (TransportPlan.tensor μ ν hμ hν hμsum hνsum)

/-! ## Dirac measures -/

/-- The function equal to 1 at `x` and 0 elsewhere. -/
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

/-- The plan between `δ_x` and `δ_y` with mass 1 at `(x, y)`. -/
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

/-- `deltaPlan x y` has cost `d x y`. -/
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

/-- Every plan between `δ_x` and `δ_y` equals `deltaPlan x y`
entrywise. -/
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

/-- Every plan between `δ_x` and `δ_y` has cost `d x y`. -/
theorem deltaPlan_forall_cost (x y : X) (d : X → X → ℝ)
    (p : TransportPlan (delta x) (delta y)) :
    p.cost d = d x y := by
  have hπ : p.π = (deltaPlan x y).π := by
    funext a b
    exact deltaPlan_unique x y p a b
  unfold TransportPlan.cost
  rw [hπ]
  exact deltaPlan_cost x y d

/-- `wasserstein1 d (delta x) (delta y) = d x y`. -/
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

/-! ## Upper bounds -/

/-- For nonnegative `d` and nonnegative `μ`, `ν` of total mass 1,
`wasserstein1 d μ ν ≤ ∑_x ∑_y μ x ν y d x y`. -/
theorem wasserstein1_le_tensor_cost (d : X → X → ℝ)
    (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1)
    (hd : ∀ x y, 0 ≤ d x y) :
    wasserstein1 d μ ν ≤ ∑ x, ∑ y, μ x * ν y * d x y := by
  unfold wasserstein1
  refine csInf_le ⟨0, ?_⟩ ?_
  · rintro c ⟨q, rfl⟩
    exact q.cost_nonneg d hd
  · refine ⟨TransportPlan.tensor μ ν hμ hν hμsum hνsum, ?_⟩
    exact TransportPlan.tensor_cost μ ν hμ hν hμsum hνsum d

/-- If `0 ≤ d ≤ C` and `μ`, `ν` are nonnegative of total mass 1, then
`wasserstein1 d μ ν ≤ C`. -/
theorem wasserstein1_le_sup (d : X → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x y, d x y ≤ C)
    (hd : ∀ x y, 0 ≤ d x y)
    (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1) :
    wasserstein1 d μ ν ≤ C := by
  calc wasserstein1 d μ ν
      ≤ ∑ x, ∑ y, μ x * ν y * d x y :=
        wasserstein1_le_tensor_cost d μ ν hμ hν hμsum hνsum hd
    _ ≤ ∑ x, ∑ y, μ x * ν y * C := by
        refine Finset.sum_le_sum ?_
        intros x _
        refine Finset.sum_le_sum ?_
        intros y _
        have hμν : 0 ≤ μ x * ν y := mul_nonneg (hμ x) (hν y)
        exact mul_le_mul_of_nonneg_left (hbound x y) hμν
    _ = C := by
        have step1 : ∀ x : X, (∑ y : X, μ x * ν y * C) = μ x * C := by
          intros x
          rw [show (∑ y, μ x * ν y * C) = (μ x * C) * ∑ y, ν y by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intros y _; ring]
          rw [hνsum, mul_one]
        rw [show (∑ x, ∑ y, μ x * ν y * C) = ∑ x, μ x * C from
              Finset.sum_congr rfl (fun x _ => step1 x)]
        rw [← Finset.sum_mul, hμsum, one_mul]

/-! ## Lipschitz test functions -/

/-- For a plan `p` and a function `f` with `|f x − f y| ≤ L · d x y`,
`|∑ μ f − ∑ ν f| ≤ L · p.cost d`. -/
theorem cost_bounds_expectation_diff
    (d : X → X → ℝ) (μ ν : X → ℝ) (p : TransportPlan μ ν)
    (f : X → ℝ) (L : ℝ)
    (hfLip : ∀ x y, |f x - f y| ≤ L * d x y) :
    |(∑ x, μ x * f x) - (∑ x, ν x * f x)|
      ≤ L * p.cost d := by
  -- μ x * f x = (Σ_y π(x,y)) * f x; ν y * f y = (Σ_x π(x,y)) * f y.
  have h1 : ∑ x, μ x * f x = ∑ x, ∑ y, p.π x y * f x := by
    refine Finset.sum_congr rfl ?_
    intros x _
    rw [← p.rowMarginal x, Finset.sum_mul]
  have h2 : ∑ y, ν y * f y = ∑ y, ∑ x, p.π x y * f y := by
    refine Finset.sum_congr rfl ?_
    intros y _
    rw [← p.colMarginal y, Finset.sum_mul]
  have h3 : ∑ y, ∑ x, p.π x y * f y = ∑ x, ∑ y, p.π x y * f y := by
    rw [Finset.sum_comm]
  have hdiff : (∑ x, μ x * f x) - (∑ x, ν x * f x)
      = ∑ x, ∑ y, p.π x y * (f x - f y) := by
    rw [h1]
    rw [show (∑ x, ν x * f x) = ∑ y, ν y * f y from rfl]
    rw [h2, h3]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intros x _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intros y _
    ring
  rw [hdiff]
  -- |Σ_x Σ_y π * (f x - f y)| ≤ Σ_x Σ_y π * |f x - f y| ≤ Σ_x Σ_y π * L d
  calc |∑ x, ∑ y, p.π x y * (f x - f y)|
      ≤ ∑ x, |∑ y, p.π x y * (f x - f y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, |p.π x y * (f x - f y)| := by
        refine Finset.sum_le_sum ?_
        intros x _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y, p.π x y * |f x - f y| := by
        refine Finset.sum_congr rfl ?_; intros x _
        refine Finset.sum_congr rfl ?_; intros y _
        rw [abs_mul]
        rw [abs_of_nonneg (p.nonneg x y)]
    _ ≤ ∑ x, ∑ y, p.π x y * (L * d x y) := by
        refine Finset.sum_le_sum ?_; intros x _
        refine Finset.sum_le_sum ?_; intros y _
        exact mul_le_mul_of_nonneg_left (hfLip x y) (p.nonneg x y)
    _ = L * p.cost d := by
        show _ = L * (∑ x, ∑ y, p.π x y * d x y)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intros x _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_; intros y _
        ring

/-- For `L ≥ 0`, nonnegative `d`, nonnegative `μ`, `ν` of total mass 1,
and `f` with `|f x − f y| ≤ L · d x y`,
`|∑ μ f − ∑ ν f| ≤ L · wasserstein1 d μ ν`. -/
theorem wasserstein1_lipschitz_bound
    (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (μ ν : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1)
    (f : X → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hfLip : ∀ x y, |f x - f y| ≤ L * d x y) :
    |(∑ x, μ x * f x) - (∑ x, ν x * f x)|
      ≤ L * wasserstein1 d μ ν := by
  -- The plan cost bounds |E_μ[f] - E_ν[f]|, for every plan.
  -- Hence inf cost bounds |...| / L, i.e., L · W_1 bounds |...|.
  have hbound : ∀ p : TransportPlan μ ν,
      |(∑ x, μ x * f x) - (∑ x, ν x * f x)| ≤ L * p.cost d :=
    fun p => cost_bounds_expectation_diff d μ ν p f L hfLip
  -- Use the tensor plan as an existence witness + lower bound (via csInf properties).
  have hwNn : ∀ c ∈ {c : ℝ | ∃ p : TransportPlan μ ν, p.cost d = c}, 0 ≤ c := by
    rintro c ⟨p, rfl⟩; exact p.cost_nonneg d hd
  have hNE : {c : ℝ | ∃ p : TransportPlan μ ν, p.cost d = c}.Nonempty :=
    ⟨(TransportPlan.tensor μ ν hμ hν hμsum hνsum).cost d, _, rfl⟩
  -- Divide the bound by L (if L > 0) or handle L = 0 separately.
  rcases lt_or_eq_of_le hL with hLpos | hL0
  · -- L > 0: use (|...|/L) ≤ inf cost ⇒ |...| ≤ L · inf cost.
    have hdivbound : ∀ p : TransportPlan μ ν,
        |(∑ x, μ x * f x) - (∑ x, ν x * f x)| / L ≤ p.cost d := by
      intro p
      rw [div_le_iff₀ hLpos]
      rw [mul_comm]
      exact hbound p
    show |(∑ x, μ x * f x) - (∑ x, ν x * f x)| ≤ L * sInf _
    rw [← div_le_iff₀' hLpos]
    refine le_csInf hNE ?_
    rintro c ⟨p, rfl⟩
    exact hdivbound p
  · -- L = 0: then f is constant, so μ, ν must have same f-expectation.
    subst hL0
    have habs0 : ∀ x y, |f x - f y| ≤ 0 := by
      intros x y
      have h := hfLip x y
      rw [zero_mul] at h
      exact h
    have hf_const : ∀ x y, f x = f y := by
      intros x y
      have habs : |f x - f y| ≤ 0 := habs0 x y
      have hnn := abs_nonneg (f x - f y)
      have hzero : |f x - f y| = 0 := le_antisymm habs hnn
      have hfxy : f x - f y = 0 := abs_eq_zero.mp hzero
      linarith
    have hEeq : (∑ x, μ x * f x) = (∑ x, ν x * f x) := by
      by_cases hnonempty : (Finset.univ : Finset X).Nonempty
      · obtain ⟨x₀, _⟩ := hnonempty
        have h1 : ∀ x, f x = f x₀ := fun x => hf_const x x₀
        rw [show (∑ x, μ x * f x) = (∑ x, μ x * f x₀) from
              Finset.sum_congr rfl (fun x _ => by rw [h1 x])]
        rw [show (∑ x, ν x * f x) = (∑ x, ν x * f x₀) from
              Finset.sum_congr rfl (fun x _ => by rw [h1 x])]
        rw [← Finset.sum_mul, ← Finset.sum_mul, hμsum, hνsum]
      · rw [Finset.not_nonempty_iff_eq_empty] at hnonempty
        rw [hnonempty, Finset.sum_empty, Finset.sum_empty]
    rw [hEeq, sub_self, abs_zero, zero_mul]

/-! ## Gluing of plans and the triangle inequality

For `p` between `μ` and `ν` and `q` between `ν` and `ρ`, `p.glue q` is a
plan between `μ` and `ρ` whose cost is at most `p.cost d + q.cost d` when
`d` satisfies the triangle inequality. -/

namespace TransportPlan

variable {μ ν ρ : X → ℝ}

/-- If `ν j = 0`, then `p.π i j = 0` for every `i`. -/
theorem entry_zero_of_col_zero (p : TransportPlan μ ν)
    (j : X) (hνj : ν j = 0) (i : X) : p.π i j = 0 := by
  have hsum : ∑ i', p.π i' j = 0 := by rw [p.colMarginal]; exact hνj
  have hnn : ∀ i' ∈ (Finset.univ : Finset X), 0 ≤ p.π i' j :=
    fun i' _ => p.nonneg i' j
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ _)

theorem entry_zero_of_row_zero (p : TransportPlan μ ν)
    (i : X) (hμi : μ i = 0) (j : X) : p.π i j = 0 := by
  have hsum : ∑ j', p.π i j' = 0 := by rw [p.rowMarginal]; exact hμi
  have hnn : ∀ j' ∈ (Finset.univ : Finset X), 0 ≤ p.π i j' :=
    fun j' _ => p.nonneg i j'
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)

/-- The plan `∑_j p.π i j · q.π j k / ν j`. Where `ν j = 0`, the terms
`p.π i j` are 0 and the division by 0 contributes 0. -/
noncomputable def glue (p : TransportPlan μ ν) (q : TransportPlan ν ρ) :
    TransportPlan μ ρ where
  π := fun i k => ∑ j, p.π i j * q.π j k / ν j
  nonneg := by
    intros i k
    apply Finset.sum_nonneg
    intros j _
    by_cases hν : ν j = 0
    · have hp : p.π i j = 0 := entry_zero_of_col_zero p j hν i
      rw [hp]; simp
    · exact div_nonneg (mul_nonneg (p.nonneg i j) (q.nonneg j k)) (by
        have : 0 ≤ ν j := by
          have := q.rowMarginal j
          have hnn : ∀ k' ∈ (Finset.univ : Finset X), 0 ≤ q.π j k' :=
            fun k' _ => q.nonneg j k'
          have := Finset.sum_nonneg hnn
          rw [q.rowMarginal] at this
          exact this
        exact this)
  rowMarginal := by
    intro i
    -- ∑ k ∑ j p.π i j * q.π j k / ν j = ∑ j (p.π i j / ν j) * (∑ k q.π j k)
    rw [Finset.sum_comm]
    have h1 : ∀ j, ∑ k, p.π i j * q.π j k / ν j
        = p.π i j / ν j * ν j := by
      intro j
      rw [show (∑ k, p.π i j * q.π j k / ν j)
            = p.π i j / ν j * ∑ k, q.π j k by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros k _
        ring]
      rw [q.rowMarginal]
    have h2 : ∀ j, p.π i j / ν j * ν j = p.π i j := by
      intro j
      by_cases hν : ν j = 0
      · have hp : p.π i j = 0 := entry_zero_of_col_zero p j hν i
        rw [hp, hν]; simp
      · exact div_mul_cancel₀ _ hν
    simp only [h1, h2]
    exact p.rowMarginal i
  colMarginal := by
    intro k
    have h1 : ∀ j, ∑ i, p.π i j * q.π j k / ν j
        = (∑ i, p.π i j) * (q.π j k / ν j) := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intros i _
      ring
    rw [show (∑ i, ∑ j, p.π i j * q.π j k / ν j)
          = ∑ j, ∑ i, p.π i j * q.π j k / ν j by rw [Finset.sum_comm]]
    simp only [h1]
    have h2 : ∀ j, (∑ i, p.π i j) * (q.π j k / ν j) = q.π j k := by
      intro j
      rw [p.colMarginal]
      by_cases hν : ν j = 0
      · have hq : q.π j k = 0 := entry_zero_of_row_zero q j hν k
        rw [hq, hν]; simp
      · field_simp
    simp only [h2]
    exact q.colMarginal k

/-- If `d i k ≤ d i j + d j k` for all `i`, `j`, `k`, then
`(p.glue q).cost d ≤ p.cost d + q.cost d`. -/
theorem glue_cost_le (p : TransportPlan μ ν) (q : TransportPlan ν ρ)
    (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (htri : ∀ i j k, d i k ≤ d i j + d j k) :
    (p.glue q).cost d ≤ p.cost d + q.cost d := by
  unfold cost glue
  simp only
  -- cost(glue) = ∑ i, ∑ k, (∑ j, p.π i j * q.π j k / ν j) * d i k
  -- ≤ ∑ i,j,k, p.π i j * q.π j k / ν j * (d i j + d j k)
  -- = ∑ i,j,k, [p.π i j / ν j] * q.π j k * d i j
  --   + ∑ i,j,k, p.π i j * [q.π j k / ν j] * d j k
  -- Note: p.π i j * q.π j k / ν j is ≥ 0 (via nonneg helper above).
  have hνnn : ∀ j, 0 ≤ ν j := by
    intro j
    have := q.rowMarginal j
    have hnn : ∀ k' ∈ (Finset.univ : Finset X), 0 ≤ q.π j k' :=
      fun k' _ => q.nonneg j k'
    have := Finset.sum_nonneg hnn
    rw [q.rowMarginal] at this
    exact this
  -- We first distribute the outer sum via sum_mul.
  have step1 : ∀ i k,
      (∑ j, p.π i j * q.π j k / ν j) * d i k
        = ∑ j, p.π i j * q.π j k / ν j * d i k := by
    intros i k
    rw [Finset.sum_mul]
  simp only [step1]
  -- The RHS: split each term via triangle inequality.
  calc ∑ i, ∑ k, ∑ j, p.π i j * q.π j k / ν j * d i k
      ≤ ∑ i, ∑ k, ∑ j, p.π i j * q.π j k / ν j * (d i j + d j k) := by
        refine Finset.sum_le_sum ?_; intros i _
        refine Finset.sum_le_sum ?_; intros k _
        refine Finset.sum_le_sum ?_; intros j _
        have hcoeff : 0 ≤ p.π i j * q.π j k / ν j := by
          by_cases hν : ν j = 0
          · have hp : p.π i j = 0 := entry_zero_of_col_zero p j hν i
            rw [hp]; simp
          · exact div_nonneg (mul_nonneg (p.nonneg i j) (q.nonneg j k)) (hνnn j)
        exact mul_le_mul_of_nonneg_left (htri i j k) hcoeff
    _ = ∑ i, ∑ k, ∑ j, (p.π i j * q.π j k / ν j * d i j
          + p.π i j * q.π j k / ν j * d j k) := by
        refine Finset.sum_congr rfl ?_; intros i _
        refine Finset.sum_congr rfl ?_; intros k _
        refine Finset.sum_congr rfl ?_; intros j _
        ring
    _ = (∑ i, ∑ k, ∑ j, p.π i j * q.π j k / ν j * d i j)
        + (∑ i, ∑ k, ∑ j, p.π i j * q.π j k / ν j * d j k) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_; intros i _
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_; intros k _
        rw [← Finset.sum_add_distrib]
    _ = p.cost d + q.cost d := by
        unfold cost
        congr 1
        · -- first summand: ∑ i ∑ k ∑ j p.π*q.π/ν * d_ij = ∑ i ∑ j p.π * d_ij
          refine Finset.sum_congr rfl ?_
          intros i _
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intros j _
          -- Goal: ∑ k, p.π i j * q.π j k / ν j * d i j = p.π i j * d i j
          have hsumk : ∑ k, p.π i j * q.π j k / ν j * d i j
              = (p.π i j * d i j / ν j) * ∑ k, q.π j k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intros k _
            ring
          rw [hsumk, q.rowMarginal]
          by_cases hν : ν j = 0
          · have hp : p.π i j = 0 := entry_zero_of_col_zero p j hν i
            rw [hp, hν]; simp
          · field_simp
        · -- second summand: ∑ i ∑ k ∑ j p.π*q.π/ν * d_jk = ∑ j ∑ k q.π * d_jk
          -- Reindex (i,k,j) → (j,k,i).
          -- Step A: (i,k,j) → (i,j,k).
          have hstepA : (∑ i : X, ∑ k : X, ∑ j : X,
                p.π i j * q.π j k / ν j * d j k)
              = (∑ i : X, ∑ j : X, ∑ k : X,
                p.π i j * q.π j k / ν j * d j k) := by
            refine Finset.sum_congr rfl ?_
            intros i _
            rw [Finset.sum_comm]
          -- Step B: (i,j,k) → (j,i,k).
          have hstepB : (∑ i : X, ∑ j : X, ∑ k : X,
                p.π i j * q.π j k / ν j * d j k)
              = (∑ j : X, ∑ i : X, ∑ k : X,
                p.π i j * q.π j k / ν j * d j k) := by
            rw [Finset.sum_comm]
          -- Step C: (j,i,k) → (j,k,i).
          have hstepC : (∑ j : X, ∑ i : X, ∑ k : X,
                p.π i j * q.π j k / ν j * d j k)
              = (∑ j : X, ∑ k : X, ∑ i : X,
                p.π i j * q.π j k / ν j * d j k) := by
            refine Finset.sum_congr rfl ?_
            intros j _
            rw [Finset.sum_comm]
          rw [hstepA, hstepB, hstepC]
          refine Finset.sum_congr rfl ?_
          intros j _
          refine Finset.sum_congr rfl ?_
          intros k _
          -- Goal: ∑ i, p.π i j * q.π j k / ν j * d j k = q.π j k * d j k
          have hsumi : ∑ i, p.π i j * q.π j k / ν j * d j k
              = (q.π j k * d j k / ν j) * ∑ i, p.π i j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intros i _
            ring
          rw [hsumi, p.colMarginal]
          by_cases hν : ν j = 0
          · have hq : q.π j k = 0 := entry_zero_of_row_zero q j hν k
            rw [hq, hν]; simp
          · field_simp

end TransportPlan

/-- For nonnegative `d` satisfying the triangle inequality and
nonnegative `μ`, `ν`, `ρ` of total mass 1,
`W_1(μ, ρ) ≤ W_1(μ, ν) + W_1(ν, ρ)`. -/
theorem wasserstein1_triangle
    (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (μ ν ρ : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) (hρ : ∀ x, 0 ≤ ρ x)
    (hμsum : ∑ x, μ x = 1) (hνsum : ∑ x, ν x = 1) (hρsum : ∑ x, ρ x = 1) :
    wasserstein1 d μ ρ ≤ wasserstein1 d μ ν + wasserstein1 d ν ρ := by
  -- Witness existence of plans via tensor.
  let pμν : TransportPlan μ ν := TransportPlan.tensor μ ν hμ hν hμsum hνsum
  let qνρ : TransportPlan ν ρ := TransportPlan.tensor ν ρ hν hρ hνsum hρsum
  -- Lower bound for the μρ cost-set (bdd below by 0).
  have hboundμρ : ∀ c ∈ {c : ℝ | ∃ r : TransportPlan μ ρ, r.cost d = c}, 0 ≤ c := by
    rintro c ⟨r, rfl⟩; exact r.cost_nonneg d hd
  -- Key step: W_1(μ, ρ) ≤ p.cost d + q.cost d for every pair (p, q).
  have keystep : ∀ (p : TransportPlan μ ν) (q : TransportPlan ν ρ),
      wasserstein1 d μ ρ ≤ p.cost d + q.cost d := by
    intros p q
    calc wasserstein1 d μ ρ
        ≤ (p.glue q).cost d := by
          show sInf _ ≤ (p.glue q).cost d
          exact csInf_le ⟨0, hboundμρ⟩ ⟨p.glue q, rfl⟩
      _ ≤ p.cost d + q.cost d := p.glue_cost_le q d hd htri
  -- step1: W_1(μ, ρ) - q.cost d ≤ W_1(μ, ν) for every q.
  have step1 : ∀ q : TransportPlan ν ρ,
      wasserstein1 d μ ρ - q.cost d ≤ wasserstein1 d μ ν := by
    intro q
    have hbdd : ∀ p : TransportPlan μ ν,
        wasserstein1 d μ ρ - q.cost d ≤ p.cost d := by
      intro p
      have := keystep p q
      linarith
    show wasserstein1 d μ ρ - q.cost d ≤ sInf _
    refine le_csInf ⟨pμν.cost d, pμν, rfl⟩ ?_
    rintro c ⟨p, rfl⟩
    exact hbdd p
  -- step2: W_1(μ, ρ) - W_1(μ, ν) ≤ W_1(ν, ρ).
  have step2 :
      wasserstein1 d μ ρ - wasserstein1 d μ ν ≤ wasserstein1 d ν ρ := by
    have hbdd : ∀ q : TransportPlan ν ρ,
        wasserstein1 d μ ρ - wasserstein1 d μ ν ≤ q.cost d := by
      intro q
      have := step1 q
      linarith
    show wasserstein1 d μ ρ - wasserstein1 d μ ν ≤ sInf _
    refine le_csInf ⟨qνρ.cost d, qνρ, rfl⟩ ?_
    rintro c ⟨q, rfl⟩
    exact hbdd q
  linarith

end InfraFormalization
