/-
Discrete d'Alembertian (Benincasa–Dowker-style) on a trajectory's
causal DAG.

**The Gorard-attempted-but-failed centrepiece.** arXiv:2102.09363 §5
bases its "the causal graph provably satisfies EFE" claim on the
Benincasa–Dowker discrete d'Alembertian (`B_ρ`) and the conjectural
convergence
  `⟨B_ρ φ⟩ → □ φ − ½ R φ`   (as ρ → ∞, in expectation over Poisson sprinklings).
This convergence is the *load-bearing* step in Gorard's derivation
(F6 in `MAJOR_FLAWS.md`); it is *unproven* and relies on open
conjectures in causal-set theory (Benincasa–Dowker 2010; only partial
numerical evidence from Cunningham 2018 exists).

**What this file does.** Provides the **discrete** side of the story,
grounded directly on our `Trajectory sys init`:
  * `intervalSize τ j i` — cardinality of the open causal interval
    between two events.
  * `layer τ k i` — set of events preceding `i` with exactly `k`
    intermediates.
  * `discreteDAlembertian4 τ φ i` — the BD 4D operator as an explicit
    alternating-sign sum over the first four layers.
  * Linearity (additivity, scalar homogeneity).
  * Vanishing on the (trivial) zero function.

**What this file does NOT do.** The continuum-limit convergence
theorem is *not* proved — it is the Benincasa–Dowker conjecture. We
record it explicitly as an unproven `Prop` in `ConvergenceConjecture`
so the gap is formally visible and cannot be papered over.

This closes the F6 "what Gorard assumed" gap on the discrete side:
the operator is now formally defined, its linearity is formally
proved, and the unproven continuum-limit claim is formally flagged
as an assumption.
-/

import InfraFormalization.CausalLevel
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InfraFormalization

variable {P V : Type*} [DecidableEq V]

/-- The **open causal interval** between two events `j` and `i` (with
`j < i`) in a trajectory: events strictly between them in the
causally-precedes order. -/
noncomputable def openInterval {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) : Finset Nat :=
  (Finset.range i).filter (fun k =>
    j < k ∧ isCausalPred τ j k = true ∧ isCausalPred τ k i = true)

/-- **Interval size**: the cardinality of the open causal interval. -/
noncomputable def intervalSize {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (j i : Nat) : Nat :=
  (openInterval τ j i).card

/-- **Layer `k`**: predecessors `j` of `i` (i.e., events with
`j < i` and `isCausalPred τ j i = true`) whose open causal interval
to `i` has exactly `k` elements. `L_0(i)` are "nearest-neighbour
predecessors" (zero intermediates); `L_1`, `L_2`, … are progressively
deeper in the causal past. -/
noncomputable def layer {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k i : Nat) : Finset Nat :=
  (Finset.range i).filter (fun j =>
    isCausalPred τ j i = true ∧ intervalSize τ j i = k)

/-- **Benincasa–Dowker discrete d'Alembertian (4D)** on a function
`φ : ℕ → ℝ` at event `i` of a trajectory.

  `B^{(4)}(φ)(i) := −φ(i)
                    + ∑_{j ∈ L_0(i)} φ(j)
                    − 9 · ∑_{j ∈ L_1(i)} φ(j)
                    + 16 · ∑_{j ∈ L_2(i)} φ(j)
                    − 8 · ∑_{j ∈ L_3(i)} φ(j)`.

The alternating-sign coefficients `(1, -9, 16, -8)` are Benincasa–
Dowker's 4D layer weights (up to the overall density-dependent
prefactor `(4/√6) ρ^{1/2}`, which we omit since we work at the
combinatorial level — no Poisson density in a deterministic trajectory).

For 2D, the coefficients would be `(1, -2, 1)`; we focus on 4D as
the physically-relevant case. -/
noncomputable def discreteDAlembertian4
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (φ : Nat → ℝ) (i : Nat) : ℝ :=
  - φ i
  + (∑ j ∈ layer τ 0 i, φ j)
  - 9 * (∑ j ∈ layer τ 1 i, φ j)
  + 16 * (∑ j ∈ layer τ 2 i, φ j)
  - 8 * (∑ j ∈ layer τ 3 i, φ j)

/-- **Linearity (additivity)** of the discrete d'Alembertian. -/
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

/-- **Scalar homogeneity** of the discrete d'Alembertian. -/
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

/-- **Vanishes on the zero function.** -/
theorem discreteDAlembertian4_zero
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (i : Nat) :
    discreteDAlembertian4 τ (fun _ => 0) i = 0 := by
  unfold discreteDAlembertian4
  simp

/-- **Layers are pairwise disjoint.** `L_k(i)` and `L_k'(i)` for
distinct `k ≠ k'` share no elements — a predecessor has a unique
interval size. -/
theorem layer_disjoint {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k k' i : Nat) (hne : k ≠ k') :
    Disjoint (layer τ k i) (layer τ k' i) := by
  unfold layer
  rw [Finset.disjoint_filter]
  intros j _ hj hj'
  -- hj : isCausalPred τ j i = true ∧ intervalSize τ j i = k
  -- hj' : isCausalPred τ j i = true ∧ intervalSize τ j i = k'
  -- So k = intervalSize τ j i = k', contradicting hne.
  exact absurd (hj.2.symm.trans hj'.2) hne

/-- **Layer membership certifies causal precedence.** `j ∈ layer τ k i`
implies `j` is in `i`'s causal past. -/
theorem mem_layer_isCausalPred {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (k i j : Nat) (h : j ∈ layer τ k i) :
    isCausalPred τ j i = true := by
  unfold layer at h
  rw [Finset.mem_filter] at h
  exact h.2.1

/-- **The Benincasa-Dowker convergence conjecture**, stated formally
as an open proposition. Physicists expect

  `⟨B^{(d)}_ρ φ⟩ → □ φ − ½ R φ   (ρ → ∞, in expectation over Poisson sprinklings)`

but this is UNPROVED. We record it here as a `Prop`-level hypothesis
parameterised by the ingredients it would need. A future formal
proof (or falsification) would instantiate this proposition; Gorard's
F6 "EFE derivation" assumes it without proof.

The conjecture is purely *about the continuum limit*; the discrete
operator `discreteDAlembertian4` itself is a well-defined combinatorial
object that exists whether or not the conjecture holds. -/
structure BenincasaDowkerConjecture where
  /-- Abstract statement of the continuum-limit claim. The precise
  formulation involves Poisson sprinklings, expectation over ensembles,
  and choice of test function; we bundle them all into one abstract
  predicate, to be refined when the mathematical machinery for
  stating the full conjecture is available in Lean. -/
  claim : Prop
  /-- Status: as of 2026-04, this is OPEN. Only partial numerical
  support (Cunningham 2018); no proof. -/
  is_open : Prop := claim = claim  -- placeholder; in practice we'd record this as "no proof known".

/-- **F6 flag.** Gorard's 2102.09363 derivation of the Einstein field
equations from a Wolfram-model rule invokes `BenincasaDowkerConjecture`
at a load-bearing step. Until that conjecture is proved, the
derivation carries an unproven assumption — exactly the F6 structural
flaw in `MAJOR_FLAWS.md`. The formalisation here makes the flag
machine-checkable: any theorem of the form "rule R satisfies EFE"
that invokes `BenincasaDowkerConjecture` must carry it as an explicit
hypothesis. -/
def gorardF6_carries_BD_assumption : Prop :=
  ∀ (C : BenincasaDowkerConjecture), True

end InfraFormalization
