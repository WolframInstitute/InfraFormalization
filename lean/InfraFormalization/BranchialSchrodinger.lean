/-
**Branchial Schrödinger equation** (I5 / #88 partial, I8 / #91 groundwork).

Discrete Schrödinger equation on a branchial slice / finite `S`,
with the Hamiltonian given by the graph adjacency operator from
`BranchialHilbert.lean`.

**Representation.** We represent the ℂ-valued wavefunction
`ψ : ℝ → S → ℂ` as a pair of real-valued functions `u v : ℝ → S → ℝ`
with `ψ t s = u t s + i v t s`. The Schrödinger equation

  `i ∂_t ψ = A ψ`    ⇔    `∂_t ψ = -i A ψ`

with `A` the branchial adjacency operator `Σ_{x : adj s x} ψ(x)`,
decomposes into

  `u' =  A v`,    `v' = -A u`.

**What this file contributes.**

  * `branchialAdjReal` — the adjacency operator restricted to
    `S → ℝ`; same formula as `branchialAdj` but real-valued.
  * `branchialAdjReal_symm` — symmetry (Hermitian) of the real-valued
    operator via sum-swap on symmetric `adj`.
  * `BranchialSchrodinger adj u v` — the structure capturing the two
    real equations of motion.
  * `branchialSchrodinger_probability u v t := ∑ s (u t s)² + (v t s)²`
    (the discrete ℓ² norm squared of `ψ(t)`).
  * `branchialSchrodinger_unitary_evolution` — total probability is
    conserved for all `t` (finite-dim Stone-type unitarity).

The proof uses self-adjointness of `branchialAdjReal`.

This is a direct port of `SchrodingerEquation.lean` (D10) to the
branchial-slice setting.
-/

import InfraFormalization.BranchialHilbert
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

namespace InfraFormalization

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Real-valued branchial adjacency operator**. Same sum-over-neighbors
formula as `branchialAdj` but acting on `S → ℝ` instead of
`BranchialHilbert S = S → ℂ`. -/
def branchialAdjReal (adj : S → S → Prop) [DecidableRel adj]
    (u : S → ℝ) (v : S) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => adj v x), u x

/-- **Self-adjointness (ℝ-symmetry) of the real adjacency operator** for
symmetric `adj`. -/
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

/-- **Branchial Schrödinger solution** (structure). `ψ = u + i v`
satisfies `∂_t ψ = -i A ψ` iff

  `∂_t u =  A v`    and    `∂_t v = -A u`.

-/
structure BranchialSchrodinger
    (adj : S → S → Prop) [DecidableRel adj] (u v : ℝ → S → ℝ) : Prop where
  real_eq : ∀ t s, HasDerivAt (fun r => u r s) (branchialAdjReal adj (v t) s) t
  imag_eq : ∀ t s, HasDerivAt (fun r => v r s) (- branchialAdjReal adj (u t) s) t

/-- **Total probability** `‖ψ(t)‖² = ∑_s (u(t,s))² + (v(t,s))²`. -/
noncomputable def branchialSchrodinger_probability
    (u v : ℝ → S → ℝ) (t : ℝ) : ℝ :=
  ∑ s, ((u t s) ^ 2 + (v t s) ^ 2)

/-- **Unitarity / probability conservation** for branchial Schrödinger
evolution. Total probability is constant on any interval on which the
solution exists. -/
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
  -- Show the total derivative is 0 using self-adjointness of A.
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

end InfraFormalization
