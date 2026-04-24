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

end InfraFormalization
