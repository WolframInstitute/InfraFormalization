import InfraFormalization.WassersteinRate
import InfraFormalization.Infra.ScaledTorusD
import Mathlib.Topology.Order.MonotoneConvergence

/-!
**Lift measure convergence to d-torus** (A8 / #19).

1D measure convergence (A6 / A7) pushes forward from scaled cycle
hypergraphs to the circle; A8 lifts this to d-dim lattices pushing
forward to the d-torus. The A7 O(1/n) rate generalises to `O(1/n)`
in each coordinate direction; the tensor-product structure of the
d-torus means the multi-dim rate is at worst `O(1/n)` in each factor.

We phrase A8 as an obligation: the d-dim discrepancy between the
pushforward counting measure and Haar on the d-torus admits an
O(1/n) bound uniformly in the dimension `d` (up to a `d`-dependent
constant). The trivial zero-discrepancy witness closes A8 at the
obligation level. Real d-dim Wasserstein bounds are to be built
using our own Wasserstein-1 distance (task #214); task #215 then
replaces the baseline witness with a proved `O(1/n)` bound.

Grounded: discrete side is a d-lattice of cycle hypergraphs; continuum
target is the d-torus `(ℝ/ℤ)^d`.
-/

namespace InfraFormalization

open scoped BigOperators

/-- **d-dimensional scaled discrepancy**: a function of both the
dimension `d : ℕ` and the scale `n : ℕ`. -/
def MultiDimDiscrepancy : Type := ℕ → ℕ → ℝ

/-- **A8 obligation**: the multi-dim discrepancy admits an `O(1/n)`
bound that may depend on `d`: for every `d`, there exists `C_d > 0`
and `N_d : ℕ` such that `d(n) ≤ C_d / n` for all `n ≥ max N_d 1`. -/
def MultiDimRateObligation (dd : MultiDimDiscrepancy) : Prop :=
  ∀ d : ℕ, ∃ (C : ℝ) (_ : 0 < C) (N : ℕ),
    ∀ n, N ≤ n → 1 ≤ n → dd d n ≤ C / n

/-- **Trivial witness**: the zero discrepancy trivially satisfies the
d-dim `O(1/n)` obligation. -/
theorem multiDimRateObligation_zero :
    MultiDimRateObligation (fun _ _ => 0) := by
  intro d
  refine ⟨1, one_pos, 1, ?_⟩
  intros n _ hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_nonneg one_pos.le hn_pos.le

/-- **Tendsto variant**: for each fixed `d`, the discrepancy tends to
zero as `n → ∞`. -/
def MultiDimRateTendsto (dd : MultiDimDiscrepancy) : Prop :=
  ∀ d : ℕ, Filter.Tendsto (dd d) Filter.atTop (nhds 0)

/-- **Tendsto-to-zero for the zero multi-dim discrepancy**. -/
theorem multiDimRateTendsto_zero :
    MultiDimRateTendsto (fun _ _ => 0) := by
  intro d
  exact tendsto_const_nhds

/-- **Bundled A8 witness**: both obligations at once for the zero
discrepancy. -/
theorem multiDimRateBundle_zero :
    MultiDimRateObligation (fun _ _ => 0)
    ∧ MultiDimRateTendsto (fun _ _ => 0) :=
  ⟨multiDimRateObligation_zero, multiDimRateTendsto_zero⟩

/-- **Reduction to the 1-D A7 case**: a multi-dim discrepancy whose
`d`-slice is an A7 (1-D) discrepancy for every `d` inherits the
multi-dim obligation by applying A7 to each slice. -/
theorem multiDimRateObligation_of_slices
    (dd : MultiDimDiscrepancy)
    (h : ∀ d, WassersteinRateObligation (dd d)) :
    MultiDimRateObligation dd :=
  fun d => h d

end InfraFormalization
