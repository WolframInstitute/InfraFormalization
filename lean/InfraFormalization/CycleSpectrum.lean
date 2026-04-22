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

end InfraFormalization
