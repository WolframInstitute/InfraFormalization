/-
**Cycle Laplacian spectrum — closed form** (task R5 / #180).

For the cycle graph on `Fin n`, the discrete Laplacian

  `Δ_{C_n} f (i) = f(i+1) + f(i−1) − 2 f(i)`

has closed-form eigenvectors and eigenvalues:

  `f_k(j) := cos(2π k j / n)`   (k = 0, 1, ..., n−1)
  `λ_k   := −4 sin²(π k / n)`   (Laplacian eigenvalue; `≤ 0`)

This file proves the eigenvalue equation `Δ f_k (i) = λ_k · f_k(i)`
at **interior indices** (where `i+1` and `i-1` don't wrap modulo
`n`). Full wrap-around periodicity is a separate lemma, deferred.

**Why this matters.** This is the first concrete spectral theorem
on a hypergraph-derived Laplacian. The eigenvalues `−4 sin²(πk/n)`
scale to the circle Laplacian spectrum `{−k²}` under `n² · Δ`
as `n → ∞`. So this theorem + the scaled-Laplacian bridge gives
a concrete spectral-convergence result.

**Connection to hypergraphs.** Via `laplacianHyper_cycleHypergraph`,
this lifts to the spectrum of `Hypergraph.laplacianHyper (cycleHypergraph n)`.
-/

import InfraFormalization.CycleGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

namespace InfraFormalization

open Real

/-- **Cycle eigenvector** `f_k(j) := cos(2π k j / n)`. -/
noncomputable def cycleEigenvector (n k : ℕ) (j : Fin n) : ℝ :=
  cos (2 * π * k * j.val / n)

/-- **Cycle eigenvalue** `λ_k := −4 sin²(π k / n)`. -/
noncomputable def cycleEigenvalue (n k : ℕ) : ℝ :=
  -4 * (sin (π * k / n))^2

/-- **All cycle eigenvalues are non-positive** — `−Δ_{C_n}` is PSD.

`cycleEigenvalue n k ≤ 0` for every `n`, `k`. Immediate from `sin² ≥ 0`. -/
theorem cycleEigenvalue_nonpos (n k : ℕ) : cycleEigenvalue n k ≤ 0 := by
  unfold cycleEigenvalue
  have h_sq : (0 : ℝ) ≤ (sin (π * k / n))^2 := sq_nonneg _
  nlinarith

/-- **Zero is an eigenvalue** — witnessed by `k = 0`
(`sin 0 = 0 ⇒ cycleEigenvalue n 0 = 0`). Represents the
constant eigenvector, aligned with the Laplacian-kills-constants
principle. -/
theorem cycleEigenvalue_zero (n : ℕ) : cycleEigenvalue n 0 = 0 := by
  unfold cycleEigenvalue
  simp

/-- **First nonzero eigenvalue is strictly negative** (spectral gap).
For `n ≥ 2`, `cycleEigenvalue n 1 = −4 sin²(π/n) < 0`. The absolute
value `4 sin²(π/n)` is the spectral gap — the slowest heat-decay rate
for non-constant initial data on the cycle. -/
theorem cycleEigenvalue_one_neg {n : ℕ} (hn : 2 ≤ n) :
    cycleEigenvalue n 1 < 0 := by
  unfold cycleEigenvalue
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h_arg_pos : 0 < π / n := div_pos Real.pi_pos hn_pos
  have h_arg_le : π / n ≤ π / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast hn)
  have h_arg_lt_pi : π / n < π := by
    rw [div_lt_iff₀ hn_pos]
    have hpi : 0 < π := Real.pi_pos
    have hn_ge_two : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have h_sin_pos : 0 < sin (π / n) :=
    Real.sin_pos_of_pos_of_lt_pi h_arg_pos h_arg_lt_pi
  have h_sin_sq_pos : 0 < (sin (π / n))^2 := by positivity
  have h_cast : π * (1 : ℕ) / n = π / n := by push_cast; ring
  rw [h_cast]
  nlinarith

/-- **Non-constant mode eigenvalues are strictly negative.** For every
`k` with `1 ≤ k` and `k < n`, the cycle eigenvalue
`cycleEigenvalue n k = −4 sin²(πk/n)` is strictly negative, because
`0 < πk/n < π` forces `sin(πk/n) > 0`. Generalises
`cycleEigenvalue_one_neg` and underlies the spectral-gap decay of
every non-constant heat-kernel mode (`HeatKernelDecay.lean`). -/
theorem cycleEigenvalue_nonzero_mode_neg {n : ℕ} [NeZero n]
    (k : ℕ) (hk_lo : 1 ≤ k) (hk_hi : k < n) :
    cycleEigenvalue n k < 0 := by
  unfold cycleEigenvalue
  have hn_pos : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hk_pos_real : (0 : ℝ) < k := by exact_mod_cast hk_lo
  have hk_lt_n_real : (k : ℝ) < n := by exact_mod_cast hk_hi
  have h_arg_pos : 0 < π * k / n := by
    apply div_pos _ hn_pos
    exact mul_pos Real.pi_pos hk_pos_real
  have h_arg_lt_pi : π * k / n < π := by
    rw [div_lt_iff₀ hn_pos]
    exact mul_lt_mul_of_pos_left hk_lt_n_real Real.pi_pos
  have h_sin_pos : 0 < sin (π * k / n) :=
    Real.sin_pos_of_pos_of_lt_pi h_arg_pos h_arg_lt_pi
  have h_sin_sq_pos : 0 < (sin (π * k / n))^2 := by positivity
  nlinarith

/-! ## Algebraic identity: sum-to-product form for the eigenvalue.

Given `A, B : ℝ`:
  `cos(A + B) + cos(A − B) − 2 cos A = −4 sin²(B/2) · cos A`.

This is the core identity; applying it with `A = 2πk·i/n` and
`B = 2πk/n` gives the eigenvalue. -/

/-- **Sum-to-product identity for the three-term central difference.** -/
lemma cos_three_term_identity (A B : ℝ) :
    cos (A + B) + cos (A - B) - 2 * cos A = -4 * (sin (B / 2))^2 * cos A := by
  -- cos(A+B) + cos(A-B) = 2 cos A cos B   (via cos_add / cos_sub).
  have h1 : cos (A + B) + cos (A - B) = 2 * cos A * cos B := by
    rw [Real.cos_add, Real.cos_sub]; ring
  rw [h1]
  -- cos B = 1 − 2 sin²(B/2)    (from cos_two_mul_eq_one_sub with 2·(B/2) = B).
  have h2 : cos B = 1 - 2 * (sin (B / 2))^2 := by
    have hhalf : (B : ℝ) = 2 * (B / 2) := by ring
    calc cos B = cos (2 * (B / 2)) := by rw [← hhalf]
      _ = 1 - 2 * (sin (B / 2))^2 := Real.cos_two_mul_eq_one_sub _
  rw [h2]; ring

/-! ## Interior eigenvalue identity

At indices `i : Fin n` with `1 ≤ i.val` and `i.val + 1 < n`, the
successor and predecessor don't wrap, so the computation is clean. -/

/-- **Eigenvalue equation at interior indices** (`1 ≤ i.val`, `i + 1 < n`). -/
theorem cycleLaplacian_eigen_interior {n : ℕ} [NeZero n] (k : ℕ) (i : Fin n)
    (hlo : 1 ≤ i.val) (hhi : i.val + 1 < n) :
    cycleLaplacian n (cycleEigenvector n k) i
    = cycleEigenvalue n k * cycleEigenvector n k i := by
  have hn_pos : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  unfold cycleLaplacian cycleEigenvector cycleEigenvalue
  -- Compute (i+1).val and (i-1).val explicitly.
  have h_one : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    have : 1 < n := by omega
    exact Nat.mod_eq_of_lt this
  have h_succ : (i + 1 : Fin n).val = i.val + 1 := by
    rw [Fin.val_add, h_one]
    exact Nat.mod_eq_of_lt hhi
  have h_pred : (i - 1 : Fin n).val = i.val - 1 := by
    show ((n - (1 : Fin n).val + i.val) % n) = i.val - 1
    rw [h_one]
    -- (n - 1 + i.val) % n. Since i.val ≥ 1 and i.val < n:
    -- n - 1 + i.val = (i.val - 1) + n, so % n = i.val - 1.
    have hstep : n - 1 + i.val = (i.val - 1) + n := by
      have : i.val ≤ n - 1 := by omega
      omega
    rw [hstep, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_succ, h_pred]
  -- Now we have explicit natural-number arithmetic; lift to ℝ.
  set A : ℝ := 2 * π * k * i.val / n with hA
  set B : ℝ := 2 * π * k / n with hB
  -- Rewrite the three cos arguments as A + B, A - B, A.
  have hrw1 : (2 * π * k * ((i.val : ℝ) + 1) / n) = A + B := by
    simp only [hA, hB]; field_simp
  have hrw2 : (2 * π * k * ((i.val : ℝ) - 1) / n) = A - B := by
    simp only [hA, hB]; field_simp
  -- Need to cast (i.val + 1 : ℕ) and (i.val - 1 : ℕ) to ℝ.
  have hcast_succ : ((i.val + 1 : ℕ) : ℝ) = (i.val : ℝ) + 1 := by norm_cast
  have hcast_pred : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
    rw [Nat.cast_sub hlo]; norm_cast
  rw [hcast_succ, hcast_pred, hrw1, hrw2]
  -- Also rewrite 2πk·i.val/n as A.
  show cos (A + B) + cos (A - B) - 2 * cos A = _ * cos A
  -- Target: (-4 * (sin(πk/n))^2) * cos A.
  -- We have the identity: cos(A+B) + cos(A-B) - 2 cos A = -4 sin²(B/2) cos A.
  -- Need sin(B/2) = sin(πk/n), i.e., B/2 = πk/n. B = 2πk/n, B/2 = πk/n. ✓
  have hB_half : B / 2 = π * k / n := by simp only [hB]; ring
  rw [cos_three_term_identity A B, hB_half]

/-! ## Full (wrap-around) eigenvalue identity

The cycle eigenvector is periodic in `j` modulo `n`: if `j₁ ≡ j₂ (mod n)`
then `cos(2πk·j₁/n) = cos(2πk·j₂/n)` because the difference is an
integer multiple of `2πk`. This lets us extend the interior result
to all indices. -/

/-- **Helper**: `cos` is `2π k`-periodic, for integer `k`. -/
lemma cos_add_two_pi_int_mul (x : ℝ) (k : ℤ) :
    cos (x + 2 * π * k) = cos x := by
  simpa [mul_comm (2 * π) (k : ℝ)] using Real.cos_add_int_mul_two_pi x k

/-- **Eigenvector at `j + n` ≡ eigenvector at `j`**: for any real `y` and
integer `n`-shift, `cos(2πk·(y + n)/n) = cos(2πk·y/n)` because the difference
is an integer multiple of `2πk`. -/
lemma cos_eigenarg_shift_by_n {n : ℕ} [NeZero n] (k : ℕ) (y : ℝ) :
    cos (2 * π * k * (y + n) / n) = cos (2 * π * k * y / n) := by
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  have hrewrite : 2 * π * k * (y + n) / n = 2 * π * k * y / n + 2 * π * k := by
    field_simp
  rw [hrewrite]
  show cos (2 * π * k * y / n + 2 * π * k) = _
  have : (2 * π * k : ℝ) = (k : ℤ) * (2 * π) := by push_cast; ring
  rw [this]
  exact Real.cos_add_int_mul_two_pi _ _

/-- **Eigenvalue equation at all indices** (including boundary, via
wrap-around). For the cycle hypergraph and any `k : ℕ`, `i : Fin n`:
  `cycleLaplacian n (cycleEigenvector n k) i
   = cycleEigenvalue n k · cycleEigenvector n k i`.
This is the full spectral theorem for the cycle graph Laplacian. -/
theorem cycleLaplacian_eigen {n : ℕ} [NeZero n] (hn : 2 ≤ n) (k : ℕ) (i : Fin n) :
    cycleLaplacian n (cycleEigenvector n k) i
    = cycleEigenvalue n k * cycleEigenvector n k i := by
  have hn_pos : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast this
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_one : (1 : Fin n).val = 1 := by
    show 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  unfold cycleLaplacian cycleEigenvector cycleEigenvalue
  -- h_succ: cos at (i+1).val equals cos at (i.val + 1 : ℝ), using Fin wrap + cos period.
  have h_succ : cos (2 * π * k * ((i + 1 : Fin n).val : ℝ) / n)
              = cos (2 * π * k * ((i.val : ℝ) + 1) / n) := by
    rcases lt_or_ge (i.val + 1) n with hlt | hge
    · have hsucc_eq : ((i + 1 : Fin n).val : ℝ) = (i.val : ℝ) + 1 := by
        rw [Fin.val_add, h_one, Nat.mod_eq_of_lt hlt]; push_cast; rfl
      rw [hsucc_eq]
    · have hi_eq : i.val = n - 1 := by have := i.isLt; omega
      have hn_1 : (1 : ℕ) ≤ n := by omega
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn_1]; push_cast; ring
      have hsucc_eq : ((i + 1 : Fin n).val : ℝ) = 0 := by
        rw [Fin.val_add, h_one]
        have hmod : (i.val + 1) % n = 0 := by
          rw [hi_eq]
          have : n - 1 + 1 = n := Nat.sub_add_cancel hn_1
          rw [this]; exact Nat.mod_self n
        rw [hmod]; simp
      rw [hsucc_eq]
      -- Show: cos (2πk·0/n) = cos (2πk·(i.val + 1)/n)
      have hx : ((i.val : ℝ) + 1) = 0 + (n : ℝ) := by
        have : (i.val : ℝ) = (n : ℝ) - 1 := by rw [hi_eq]; exact hcast
        rw [this]; ring
      rw [hx, cos_eigenarg_shift_by_n k 0]
  have h_pred : cos (2 * π * k * ((i - 1 : Fin n).val : ℝ) / n)
              = cos (2 * π * k * ((i.val : ℝ) - 1) / n) := by
    rcases Nat.lt_or_ge 0 i.val with hgt | hle
    · have hpred_eq : ((i - 1 : Fin n).val : ℝ) = (i.val : ℝ) - 1 := by
        show (((n - (1 : Fin n).val + i.val) % n : ℕ) : ℝ) = (i.val : ℝ) - 1
        rw [h_one]
        have hstep : n - 1 + i.val = (i.val - 1) + n := by omega
        rw [hstep, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [Nat.cast_sub hgt]; push_cast; ring
      rw [hpred_eq]
    · have hi_zero : i.val = 0 := by omega
      have hpred_eq : ((i - 1 : Fin n).val : ℝ) = (n : ℝ) - 1 := by
        show (((n - (1 : Fin n).val + i.val) % n : ℕ) : ℝ) = (n : ℝ) - 1
        rw [h_one, hi_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
        rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]; push_cast; ring
      rw [hpred_eq, hi_zero]
      -- Goal: cos(2πk(n-1)/n) = cos(2πk(0 - 1)/n). Use y = -1: (-1 + n) · ... = (n-1).
      have hx : (n : ℝ) - 1 = -1 + (n : ℝ) := by ring
      rw [hx, cos_eigenarg_shift_by_n k (-1)]
      congr 1; push_cast; ring
  rw [h_succ, h_pred]
  -- Now interior-style computation.
  set A : ℝ := 2 * π * k * i.val / n with hA
  set B : ℝ := 2 * π * k / n with hB
  have hrw1 : (2 * π * k * ((i.val : ℝ) + 1) / n) = A + B := by
    simp only [hA, hB]; field_simp
  have hrw2 : (2 * π * k * ((i.val : ℝ) - 1) / n) = A - B := by
    simp only [hA, hB]; field_simp
  rw [hrw1, hrw2]
  show cos (A + B) + cos (A - B) - 2 * cos A = _ * cos A
  have hB_half : B / 2 = π * k / n := by simp only [hB]; ring
  rw [cos_three_term_identity A B, hB_half]

end InfraFormalization
