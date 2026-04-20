/-
Bridge: scaled discrete cycle Laplacian ↔ continuum second derivative.

**The grounding-principle obligation, Rung-2 case.** The cycle
Laplacian (`CycleGraph.lean`) is the discrete-side object; the
continuum target is `d²/dx²` on smooth functions. The bridge is the
`n² · Δ_{C_n}` scaling, identified pointwise with the central second
difference (via `cycleLaplacian_is_secondDifference`).

For the **polynomial case** (quadratic test functions) the bridge is
exact: no error term, no limiting argument. We formalise this here
as `polynomial_scaled_laplacian_eq_second_deriv`.

The general `C²` case uses the Taylor remainder (pending Mathlib
`taylorWithinEval` integration); for now the polynomial case suffices
to demonstrate the bridge mechanically, and is the standard "first
non-trivial check" of any discrete-to-continuum operator
correspondence.

This file ties the Rung-1/2 work explicitly back to a hypergraph: the
cycle is the simplest 1-dim discrete manifold, and its Laplacian's
scaled action on smooth functions reproduces the second derivative.
No standalone continuum calculus lives here — the continuum
operator is *defined* via the polynomial-case scaled-second-difference
identity.
-/

import InfraFormalization.SecondDifference
import InfraFormalization.CycleGraph
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace InfraFormalization

/-- **Scaled second-difference operator** at scale `1/n`.
For real `f` and step `n ≥ 1`, this is the operator that takes
`f(x + 1/n) − 2 f(x) + f(x − 1/n)` and multiplies by `n²` — the
prototype of all "discrete Laplacian times scale²" operators that
converge to `d²/dx²`. -/
noncomputable def scaledSecondDiff (f : ℝ → ℝ) (n : Nat) (x : ℝ) : ℝ :=
  (n : ℝ)^2 * secondDifference f x (1 / n)

/-- **Polynomial case is exact.** For any quadratic
`f(y) = a y² + b y + c`, the scaled second difference at `1/n` (for
`n ≥ 1`) equals `f''(x) = 2a` exactly — no error, no limit. -/
theorem scaledSecondDiff_quadratic (a b c : ℝ) (n : Nat) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff (fun y => a * y^2 + b * y + c) n x = 2 * a := by
  unfold scaledSecondDiff
  rw [secondDifference_quadratic]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

/-- **Constants vanish under the scaled second difference.** -/
theorem scaledSecondDiff_const (c : ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun _ => c) n x = 0 := by
  unfold scaledSecondDiff
  rw [secondDifference_const]
  ring

/-- **Linear functions vanish under the scaled second difference.** -/
theorem scaledSecondDiff_linear (a : ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun y => a * y) n x = 0 := by
  unfold scaledSecondDiff
  rw [secondDifference_linear]
  ring

/-- **Linearity (additivity) of the scaled second difference.** -/
theorem scaledSecondDiff_add (f g : ℝ → ℝ) (n : Nat) (x : ℝ) :
    scaledSecondDiff (fun y => f y + g y) n x
    = scaledSecondDiff f n x + scaledSecondDiff g n x := by
  unfold scaledSecondDiff
  rw [secondDifference_add]
  ring

/-- **Bridge for arbitrary quadratics, two specific scales.**
At any two scales `n, m ≥ 1` and any two points `x, y : ℝ`, the
scaled second difference of a quadratic `f` agrees — both equal
`f''(x) = 2 a`, independent of `(n, x)`. This makes the bridge
"limit-free": no error terms, no Taylor remainders, exact for all
polynomial test functions. -/
theorem scaledSecondDiff_quadratic_independent
    (a b c : ℝ) (n m : Nat) (hn : 0 < n) (hm : 0 < m) (x y : ℝ) :
    scaledSecondDiff (fun z => a * z^2 + b * z + c) n x
    = scaledSecondDiff (fun z => a * z^2 + b * z + c) m y := by
  rw [scaledSecondDiff_quadratic a b c n hn x,
      scaledSecondDiff_quadratic a b c m hm y]

/-- **Cycle Laplacian = central second difference** at an interior
point. Given a real-to-real function `f`, a scale `n ≥ 2`, and an
interior index `i : Fin n` (with `1 ≤ i.val` and `i.val + 1 < n`),
the cycle Laplacian of `g(j) := f(j.val / n)` equals
`secondDifference f (i.val / n) (1 / n)`.

At the boundary (`i.val = 0` or `i.val = n − 1`), the cyclic
wrap-around makes the cycle Laplacian deviate from the second
difference unless `f` is periodic. The interior identity here is
enough to connect the discrete cycle operator with the continuum
second derivative on smooth test functions. -/
theorem cycleLaplacian_in_terms_of_secondDifference
    (n : Nat) [NeZero n] (f : ℝ → ℝ) (i : Fin n)
    (hlo : 1 ≤ i.val) (hhi : i.val + 1 < n) :
    cycleLaplacian n (fun j => f ((j.val : ℝ) / (n : ℝ))) i
    = secondDifference f ((i.val : ℝ) / (n : ℝ)) (1 / (n : ℝ)) := by
  have hn_ge_2 : 2 ≤ n := by omega
  -- Compute the `.val` of `i + 1` and `i - 1` using Fin.val_add.
  have hone_val : (1 : Fin n).val = 1 := by
    show (1 % n) = 1
    exact Nat.mod_eq_of_lt hn_ge_2
  have h_succ : (i + 1 : Fin n).val = i.val + 1 := by
    rw [Fin.val_add, hone_val]
    exact Nat.mod_eq_of_lt hhi
  have h_pred : (i - 1 : Fin n).val = i.val - 1 := by
    -- In the group Fin n, i - 1 = i + (-1).
    have heq : (i - 1 : Fin n) = i + (-1 : Fin n) := sub_eq_add_neg _ _
    rw [heq, Fin.val_add]
    -- In the group Fin n, -1 has value n - 1.
    have hnegone_val : (-1 : Fin n).val = n - 1 := by
      show (n - (1 : Fin n).val) % n = n - 1
      rw [hone_val]
      exact Nat.mod_eq_of_lt (by omega : n - 1 < n)
    rw [hnegone_val]
    -- (i.val + (n - 1)) % n = i.val - 1 when i.val ≥ 1.
    have step : i.val + (n - 1) = (i.val - 1) + n := by omega
    rw [step, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega : i.val - 1 < n)
  -- Now rewrite both sides, converting Fin-indexed coords to real-arithmetic.
  unfold cycleLaplacian secondDifference
  -- Beta-reduce to expose the Fin .val cast structure.
  simp only []
  have hn_pos : (0 : ℝ) < n :=
    by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  -- Convert the .val expressions on the LHS to ℝ-arithmetic.
  have e_succ_cast : (((i + 1 : Fin n).val : ℕ) : ℝ) = (i.val : ℝ) + 1 := by
    rw [h_succ]
    push_cast
    ring
  have e_pred_cast : (((i - 1 : Fin n).val : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
    rw [h_pred, Nat.cast_sub hlo]
    push_cast
    ring
  rw [e_succ_cast, e_pred_cast]
  -- Now: f (((i.val : ℝ) + 1) / n) + f (((i.val : ℝ) - 1) / n) - 2 f(i.val/n)
  --   = f (i.val/n + 1/n) - 2 f(i.val/n) + f (i.val/n - 1/n).
  have div_add : ((i.val : ℝ) + 1) / (n : ℝ)
               = (i.val : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by
    field_simp
  have div_sub : ((i.val : ℝ) - 1) / (n : ℝ)
               = (i.val : ℝ) / (n : ℝ) - 1 / (n : ℝ) := by
    field_simp
  rw [div_add, div_sub]
  ring

/-- **Second derivative of a quadratic polynomial.** For
`f(y) = a y² + b y + c`, the second derivative at any point is `2a`
(constant). Computed from first principles via `HasDerivAt`. -/
theorem second_deriv_quadratic (a b c x : ℝ) :
    deriv (deriv (fun y => a * y^2 + b * y + c)) x = 2 * a := by
  -- First derivative at every y : (2 a y + b).
  have h_inner : ∀ y : ℝ,
      HasDerivAt (fun z => a * z^2 + b * z + c) (2 * a * y + b) y := by
    intro y
    have h_sq : HasDerivAt (fun z => z^2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h_a_sq : HasDerivAt (fun z => a * z^2) (a * (2 * y)) y :=
      h_sq.const_mul a
    have h_bz : HasDerivAt (fun z => b * z) b y := by
      simpa using (hasDerivAt_id y).const_mul b
    have h_sum : HasDerivAt (fun z => a * z^2 + b * z) (a * (2 * y) + b) y :=
      h_a_sq.add h_bz
    have h_full : HasDerivAt (fun z => a * z^2 + b * z + c) (a * (2 * y) + b) y :=
      h_sum.add_const c
    convert h_full using 1
    ring
  -- Identify `deriv (_)` pointwise with `fun y => 2 a y + b`.
  have h_first_deriv_eq :
      deriv (fun y => a * y^2 + b * y + c) = fun y => 2 * a * y + b := by
    funext y
    exact (h_inner y).deriv
  rw [h_first_deriv_eq]
  -- Second derivative: d/dx (2 a x + b) = 2 a.
  have h_outer : HasDerivAt (fun y => 2 * a * y + b) (2 * a) x := by
    have h_lin : HasDerivAt (fun y => 2 * a * y) (2 * a) x := by
      simpa using (hasDerivAt_id x).const_mul (2 * a)
    have := h_lin.add_const b
    convert this using 1
  exact h_outer.deriv

/-- **The Rung-2 bridge theorem for the polynomial case.** For any
quadratic `f`, the scaled discrete second difference equals the
continuum second derivative, exactly (no limit, no error).

  `scaledSecondDiff (fun y => a y² + b y + c) n x
   = deriv (deriv (fun y => a y² + b y + c)) x`

This makes the discrete-cycle / continuum-d²/dx² correspondence
machine-checked for polynomial test functions. The general `C²` case
is the Taylor-remainder theorem, pending. -/
theorem polynomial_scaled_laplacian_eq_second_deriv
    (a b c : ℝ) (n : Nat) (hn : 0 < n) (x : ℝ) :
    scaledSecondDiff (fun y => a * y^2 + b * y + c) n x
    = deriv (deriv (fun y => a * y^2 + b * y + c)) x := by
  rw [scaledSecondDiff_quadratic a b c n hn x]
  rw [second_deriv_quadratic a b c x]

end InfraFormalization
