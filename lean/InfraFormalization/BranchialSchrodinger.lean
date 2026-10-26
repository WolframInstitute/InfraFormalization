/-
Schrödinger equation for an adjacency operator on a finite set.

For a finite type `S` and a symmetric relation `adj` on `S`, this module
writes `ψ = u + i v` with real `u v : ℝ → S → ℝ` and defines solutions
of `i ∂_t ψ = A ψ`, where `A` is the adjacency sum operator, as pairs
with `u' = A v` and `v' = -A u` at every time. It proves that
`∑_s u(t,s)² + v(t,s)²` has derivative 0 at every `t` and is therefore
constant. The relation `adj` is arbitrary and is not derived from a
rewriting system.
-/

import InfraFormalization.BranchialHilbert
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

namespace InfraFormalization

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The adjacency operator on `S → ℝ`: `(A u)(v) = ∑_{x : adj v x} u x`. -/
def branchialAdjReal (adj : S → S → Prop) [DecidableRel adj]
    (u : S → ℝ) (v : S) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => adj v x), u x

/-- For symmetric `adj`, `∑_s u s · (A v)(s) = ∑_s v s · (A u)(s)`. -/
theorem branchialAdjReal_symm (adj : S → S → Prop) [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a) (u v : S → ℝ) :
    ∑ s, u s * branchialAdjReal adj v s
      = ∑ s, v s * branchialAdjReal adj u s := by
  unfold branchialAdjReal
  simp only [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  by_cases h : adj a b
  · have h' : adj b a := hsymm _ _ h
    simp [h, h']; ring
  · have h' : ¬ adj b a := fun hba => h (hsymm _ _ hba)
    simp [h, h']

/-- `u` and `v` satisfy `∂_t u = A v` and `∂_t v = -A u` at every time
`t` and every `s`. -/
structure BranchialSchrodinger
    (adj : S → S → Prop) [DecidableRel adj] (u v : ℝ → S → ℝ) : Prop where
  real_eq : ∀ t s, HasDerivAt (fun r => u r s) (branchialAdjReal adj (v t) s) t
  imag_eq : ∀ t s, HasDerivAt (fun r => v r s) (- branchialAdjReal adj (u t) s) t

/-- `∑_s u(t,s)² + v(t,s)²`. -/
noncomputable def branchialSchrodinger_probability
    (u v : ℝ → S → ℝ) (t : ℝ) : ℝ :=
  ∑ s, ((u t s) ^ 2 + (v t s) ^ 2)

/-- For symmetric `adj` and a solution `(u, v)`, the function
`branchialSchrodinger_probability u v` has derivative 0 at every `t`. -/
theorem branchialSchrodinger_unitary_evolution
    {adj : S → S → Prop} [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a)
    {u v : ℝ → S → ℝ} (hsol : BranchialSchrodinger adj u v)
    (t : ℝ) :
    HasDerivAt (branchialSchrodinger_probability u v)
      0 t := by
  unfold branchialSchrodinger_probability
  have h_deriv : ∀ s, HasDerivAt
      (fun r => (u r s) ^ 2 + (v r s) ^ 2)
      (2 * u t s * branchialAdjReal adj (v t) s
        + 2 * v t s * (- branchialAdjReal adj (u t) s)) t := by
    intro s
    have h_u2 : HasDerivAt (fun r => (u r s) ^ 2)
        (2 * u t s * branchialAdjReal adj (v t) s) t := by
      have := ((hsol.real_eq t s).fun_pow 2)
      simpa [pow_succ, pow_zero, one_mul, mul_comm, two_mul, mul_assoc]
        using this
    have h_v2 : HasDerivAt (fun r => (v r s) ^ 2)
        (2 * v t s * (- branchialAdjReal adj (u t) s)) t := by
      have := ((hsol.imag_eq t s).fun_pow 2)
      simpa [pow_succ, pow_zero, one_mul, mul_comm, two_mul, mul_assoc]
        using this
    exact h_u2.add h_v2
  have h_sum : HasDerivAt (fun t => ∑ s, (u t s ^ 2 + v t s ^ 2))
      (∑ s, (2 * u t s * branchialAdjReal adj (v t) s
        + 2 * v t s * (- branchialAdjReal adj (u t) s))) t :=
    HasDerivAt.fun_sum (fun s _ => h_deriv s)
  -- The derivative sum is 0 by `branchialAdjReal_symm`.
  have h_zero :
      ∑ s, (2 * u t s * branchialAdjReal adj (v t) s
        + 2 * v t s * (- branchialAdjReal adj (u t) s)) = 0 := by
    have h_eq : ∑ s, u t s * branchialAdjReal adj (v t) s
              = ∑ s, v t s * branchialAdjReal adj (u t) s :=
      branchialAdjReal_symm adj hsymm (u t) (v t)
    calc ∑ s, (2 * u t s * branchialAdjReal adj (v t) s
          + 2 * v t s * (- branchialAdjReal adj (u t) s))
        = ∑ s, 2 * (u t s * branchialAdjReal adj (v t) s
            - v t s * branchialAdjReal adj (u t) s) := by
              apply Finset.sum_congr rfl
              intro s _
              ring
      _ = 2 * (∑ s, u t s * branchialAdjReal adj (v t) s
            - ∑ s, v t s * branchialAdjReal adj (u t) s) := by
              rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ = 2 * (∑ s, u t s * branchialAdjReal adj (v t) s
            - ∑ s, u t s * branchialAdjReal adj (v t) s) := by rw [← h_eq]
      _ = 0 := by ring
  rw [← h_zero]
  exact h_sum

/-- For symmetric `adj` and a solution `(u, v)`,
`branchialSchrodinger_probability u v s = branchialSchrodinger_probability u v t`
for all `s` and `t`. The proof applies `is_const_of_deriv_eq_zero` to
`branchialSchrodinger_unitary_evolution`. -/
theorem branchialSchrodinger_probability_const
    {adj : S → S → Prop} [DecidableRel adj]
    (hsymm : ∀ a b, adj a b → adj b a)
    {u v : ℝ → S → ℝ} (hsol : BranchialSchrodinger adj u v)
    (s t : ℝ) :
    branchialSchrodinger_probability u v s
      = branchialSchrodinger_probability u v t := by
  have h_deriv : ∀ x : ℝ,
      HasDerivAt (branchialSchrodinger_probability u v) 0 x :=
    fun x => branchialSchrodinger_unitary_evolution hsymm hsol x
  have h_const : ∀ x y, branchialSchrodinger_probability u v x
      = branchialSchrodinger_probability u v y := by
    intro x y
    have h_diffble : Differentiable ℝ (branchialSchrodinger_probability u v) := by
      intro z
      exact (h_deriv z).differentiableAt
    have h_deriv_zero : ∀ z, deriv (branchialSchrodinger_probability u v) z = 0 :=
      fun z => (h_deriv z).deriv
    exact (is_const_of_deriv_eq_zero h_diffble h_deriv_zero x y)
  exact h_const s t

end InfraFormalization
