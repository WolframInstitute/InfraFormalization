/-
A discrete d'Alembertian with the Benincasa–Dowker 4D layer weights on the events of a
trajectory.

G3 (arXiv:2102.09363, §5) uses the Benincasa–Dowker operator `B_ρ` and the convergence
`⟨B_ρ φ⟩ → □ φ − ½ R φ` as `ρ → ∞` over Poisson sprinklings, which is an open conjecture
in causal-set theory. The module defines interval sizes and layers from the Boolean
causal-predecessor test `isCausalPred`, the operator `discreteDAlembertian4` with weights
`(1, -9, 16, -8)`, the action `discreteAction`, and the predicate `discreteEL`. It proves
linearity of the operator, disjointness of layers, scaling of the action by `c²`, and
vanishing at the zero function. The Benincasa-Dowker convergence conjecture is not formalised.
-/

import InfraFormalization.CausalLevel
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- The indices `k` with `j < k < i` such that `isCausalPred τ j k` and `isCausalPred τ k i`
hold. These are one-step causal-predecessor relations, not the transitive order. -/
noncomputable def openInterval {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) : Finset Nat :=
  (Finset.range i).filter (fun k =>
    j < k ∧ isCausalPred τ j k = true ∧ isCausalPred τ k i = true)

/-- The cardinality of `openInterval τ j i`. -/
noncomputable def intervalSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) : Nat :=
  (openInterval τ j i).card

/-- Layer `L_k(i)`: the indices `j < i` with `isCausalPred τ j i = true` and
`intervalSize τ j i = k`. -/
noncomputable def layer {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k i : Nat) : Finset Nat :=
  (Finset.range i).filter (fun j =>
    isCausalPred τ j i = true ∧ intervalSize τ j i = k)

/-- The discrete d'Alembertian with Benincasa–Dowker 4D weights, applied to `φ : ℕ → ℝ` at
event `i`:

  `B^{(4)}(φ)(i) := −φ(i)
                    + ∑_{j ∈ L_0(i)} φ(j)
                    − 9 · ∑_{j ∈ L_1(i)} φ(j)
                    + 16 · ∑_{j ∈ L_2(i)} φ(j)
                    − 8 · ∑_{j ∈ L_3(i)} φ(j)`.

The coefficients `(1, -9, 16, -8)` are the Benincasa–Dowker 4D layer weights. The
density prefactor `(4/√6) ρ^{1/2}` is omitted. -/
noncomputable def discreteDAlembertian4
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (φ : Nat → ℝ) (i : Nat) : ℝ :=
  - φ i
  + (∑ j ∈ layer τ 0 i, φ j)
  - 9 * (∑ j ∈ layer τ 1 i, φ j)
  + 16 * (∑ j ∈ layer τ 2 i, φ j)
  - 8 * (∑ j ∈ layer τ 3 i, φ j)

/-- `discreteDAlembertian4` is additive in `φ`. -/
theorem discreteDAlembertian4_add
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (φ ψ : Nat → ℝ) (i : Nat) :
    discreteDAlembertian4 τ (fun j => φ j + ψ j) i
    = discreteDAlembertian4 τ φ i + discreteDAlembertian4 τ ψ i := by
  unfold discreteDAlembertian4
  have h0 : (∑ j ∈ layer τ 0 i, (φ j + ψ j))
          = (∑ j ∈ layer τ 0 i, φ j) + (∑ j ∈ layer τ 0 i, ψ j) :=
    Finset.sum_add_distrib
  have h1 : (∑ j ∈ layer τ 1 i, (φ j + ψ j))
          = (∑ j ∈ layer τ 1 i, φ j) + (∑ j ∈ layer τ 1 i, ψ j) :=
    Finset.sum_add_distrib
  have h2 : (∑ j ∈ layer τ 2 i, (φ j + ψ j))
          = (∑ j ∈ layer τ 2 i, φ j) + (∑ j ∈ layer τ 2 i, ψ j) :=
    Finset.sum_add_distrib
  have h3 : (∑ j ∈ layer τ 3 i, (φ j + ψ j))
          = (∑ j ∈ layer τ 3 i, φ j) + (∑ j ∈ layer τ 3 i, ψ j) :=
    Finset.sum_add_distrib
  rw [h0, h1, h2, h3]
  ring

/-- `discreteDAlembertian4 τ (c · φ) i = c · discreteDAlembertian4 τ φ i`. -/
theorem discreteDAlembertian4_smul
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (c : ℝ) (φ : Nat → ℝ) (i : Nat) :
    discreteDAlembertian4 τ (fun j => c * φ j) i
    = c * discreteDAlembertian4 τ φ i := by
  unfold discreteDAlembertian4
  rw [show (∑ j ∈ layer τ 0 i, c * φ j) = c * ∑ j ∈ layer τ 0 i, φ j from
        (Finset.mul_sum _ _ _).symm]
  rw [show (∑ j ∈ layer τ 1 i, c * φ j) = c * ∑ j ∈ layer τ 1 i, φ j from
        (Finset.mul_sum _ _ _).symm]
  rw [show (∑ j ∈ layer τ 2 i, c * φ j) = c * ∑ j ∈ layer τ 2 i, φ j from
        (Finset.mul_sum _ _ _).symm]
  rw [show (∑ j ∈ layer τ 3 i, c * φ j) = c * ∑ j ∈ layer τ 3 i, φ j from
        (Finset.mul_sum _ _ _).symm]
  ring

/-- `discreteDAlembertian4` of the zero function is 0. -/
theorem discreteDAlembertian4_zero
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) :
    discreteDAlembertian4 τ (fun _ => 0) i = 0 := by
  unfold discreteDAlembertian4
  simp

/-- For `k ≠ k'`, the layers `L_k(i)` and `L_k'(i)` are disjoint. -/
theorem layer_disjoint {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k k' i : Nat) (hne : k ≠ k') :
    Disjoint (layer τ k i) (layer τ k' i) := by
  unfold layer
  rw [Finset.disjoint_filter]
  intros j _ hj hj'
  -- `hj.2` and `hj'.2` give `k = intervalSize τ j i = k'`.
  exact absurd (hj.2.symm.trans hj'.2) hne

/-- `j ∈ layer τ k i` implies `isCausalPred τ j i = true`. -/
theorem mem_layer_isCausalPred {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k i j : Nat) (h : j ∈ layer τ k i) :
    isCausalPred τ j i = true := by
  unfold layer at h
  rw [Finset.mem_filter] at h
  exact h.2.1

/-- The sum `S[φ] := ∑_{i < N} φ(i) · B[φ](i)` with `B = discreteDAlembertian4`. G1
(arXiv:2004.14810, Eq. 86) uses the continuum action `S[g^{ab}] = ∫ μ_g · R`. -/
noncomputable def discreteAction
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (φ : Nat → ℝ) (N : Nat) : ℝ :=
  ∑ i ∈ Finset.range N, φ i * discreteDAlembertian4 τ φ i

/-- Replacing `φ` by `c · φ` multiplies `discreteAction` by `c²`. -/
theorem discreteAction_smul
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (c : ℝ) (φ : Nat → ℝ) (N : Nat) :
    discreteAction τ (fun j => c * φ j) N = c^2 * discreteAction τ φ N := by
  unfold discreteAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros i _
  rw [discreteDAlembertian4_smul]
  ring

/-- `discreteAction` of the zero function is 0. -/
theorem discreteAction_zero
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (N : Nat) :
    discreteAction τ (fun _ => 0) N = 0 := by
  unfold discreteAction
  apply Finset.sum_eq_zero
  intros i _
  simp

/-- `discreteDAlembertian4 τ φ i = 0` for every `i`. This predicate is not derived as the
Euler–Lagrange equation of `discreteAction`. -/
def discreteEL {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (φ : Nat → ℝ) : Prop :=
  ∀ i : Nat, discreteDAlembertian4 τ φ i = 0

/-- The zero function satisfies `discreteEL`. -/
theorem discreteEL_zero
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) :
    discreteEL τ (fun _ => 0) := by
  intros i
  exact discreteDAlembertian4_zero τ i

end InfraFormalization
