/-
**F5: the JGORARD G1 Eq 88 / G3 §5 claim "the discrete sum becomes the
continuum integral under weak ergodicity" is ill-defined.**

**Context.** arXiv:2004.14810 line 898 reads, in full:

  "In the continuum limit of an arbitrarily large causal graph, this sum
   becomes (subject to a weak ergodicity assumption on the dynamics of
   the causal graph) an integral."

The sentence asserts a limiting equality of a discrete quantity (a sum
over causal-graph vertices) with a continuum quantity (an integral
over a Lorentzian manifold), conditional on an unspecified "weak
ergodicity" hypothesis. As written, it specifies:
  - no topology of convergence (pointwise? in mean? in L²? Γ-convergence?),
  - no sampling scheme (uniform grid? Poisson sprinkling? adapted mesh?),
  - no regularity class for the integrand,
  - no precise definition of "weak ergodicity".

The closest rigorous version — Benincasa–Dowker 2010 (for the d'Alembertian
on a Poisson sprinkling) — is a *conjectural* statement in causal set theory
with only partial numerical support (Cunningham 2018). It is also not what
G1 Eq 88 says: BD work in expectation over Poisson ensembles, while JGORARD
writes a pointwise limit over a single deterministic hypergraph.

**What this file does.** Formalises the observation that *without* specifying
a convergence notion, the statement "sequence *becomes* value" is ambiguous:
there is a sequence for which one natural notion says "yes" and another
says "no", both being acceptable readings of English "becomes".

Concretely: the sequence `n ↦ 1 / (n + 1)` converges to `0` in the standard
sense (`Tendsto _ atTop (𝓝 0)`) but is never eventually equal to `0`.
Both are reasonable interpretations of "the sum becomes 0 in the limit";
JGORARD's prose does not distinguish them.

The point of this file is *not* to claim JGORARD meant `EventuallyEq`.
It is to demonstrate formally that "becomes" under-determines the claim,
so the F5 statement is not a mathematical assertion until a convergence
notion is supplied.

**Sharpening (2026-05, macro-observer note; see
`notes/phajek_macro_observer_notes.txt`).** Beyond the unspecified
topology, there is a deeper obstruction: even after a topology is
fixed, the limit object may fail to exist as a probability measure.
A continuum limit of a sequence of finite rewriting states is a
*projective limit* of finite-dimensional laws, and such a projective
family need not extend to a countably-additive probability measure —
it can extend only to a *charge* (finitely-additive / signed), or hit
Suslin-type non-measurability, since the Kolmogorov extension theorem
needs topological regularity the rewriting setting does not supply
(HVLE, via the Orbanz framework). This obstruction is independent of
the F1–F4/F6/F7 structural flaws. Scope boundary: the marginal
weak-convergence results elsewhere in this project (counting measure →
Lebesgue, Wasserstein-rate bounds on 1-D projections) are unaffected;
the obstruction bites at the *joint* law of the whole limiting
process, which is the object G1 Eq 88 silently assumes.

**Sharpening (2026-05-30, synthetic-measure note).** PHAJEK's
`SyntheticInfrageometry` paclet now exposes a *synthetic*
measure-theoretic primitive `InfraMeasure` (renamed from `VisitMeasure`
in the unification commit `9f34fb4`, with the new name in commit
`38693c2`) plus `InfraBoundary` and an `infraRepType` classifier
(`resources/SyntheticInfrageometry/Kernel/Tools.wl`). This makes the
F5 distinction structural: a measure attached to a graph is now an
*infrageometric construction of its own*, built directly from the
synthetic data, and is not identified with the probability measure of
any continuum limit. Whether such a synthetic measure can be realised
as the marginal of a probability law on a continuum object is a
separate question — the HVLE projective-limit obstruction in the
previous sharpening. G1 Eq 88 conflates the two: it writes the
"discrete sum" as if it were already a finite-state expectation of a
continuum-side integral. The synthetic-side primitive shows this is a
category error — the discrete object is a different kind of
mathematical entity, and the bridge between the two is the
obstruction, not an identity.
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

namespace InfraFormalization
namespace Refutations

open Filter Topology

/-- An abstract "convergence notion": a binary predicate on a real sequence
and a candidate limit. This parameter is *precisely* what JGORARD leaves
unspecified when he writes "the discrete sum *becomes* the integral". -/
abbrev ConvergenceNotion : Type := (ℕ → ℝ) → ℝ → Prop

/-- Ordinary real-analytic convergence: `Tendsto s atTop (𝓝 L)`. -/
def StandardLimit : ConvergenceNotion := fun s L => Tendsto s atTop (𝓝 L)

/-- Strictly stronger notion: the sequence is *eventually equal* to `L`. -/
def EventuallyEquals : ConvergenceNotion := fun s L => ∃ N, ∀ n ≥ N, s n = L

/-- The harmonic-style sequence `n ↦ 1 / (n + 1)`. -/
noncomputable def invSucc : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)

lemma invSucc_pos (n : ℕ) : 0 < invSucc n := by
  unfold invSucc
  have : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  positivity

lemma invSucc_ne_zero (n : ℕ) : invSucc n ≠ 0 :=
  ne_of_gt (invSucc_pos n)

/-- `invSucc` converges to `0` in the standard sense. -/
theorem invSucc_standardLimit_zero : StandardLimit invSucc 0 := by
  unfold StandardLimit invSucc
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- `invSucc` is never eventually equal to `0` (it is strictly positive for
all `n`). -/
theorem invSucc_not_eventuallyEquals_zero : ¬ EventuallyEquals invSucc 0 := by
  unfold EventuallyEquals
  rintro ⟨N, hN⟩
  exact invSucc_ne_zero N (hN N le_rfl)

/-- **F5 formal statement.** The phrase "the discrete sum becomes the
integral" under-determines its own content: there exists a real sequence
and a candidate limit such that one natural convergence notion
(`StandardLimit`) affirms the limit while another (`EventuallyEquals`)
denies it. Absent a specified notion of convergence, the G1 Eq 88 claim
is not a well-defined mathematical assertion. -/
theorem becomes_is_underdetermined :
    ∃ (s : ℕ → ℝ) (L : ℝ),
      StandardLimit s L ∧ ¬ EventuallyEquals s L :=
  ⟨invSucc, 0, invSucc_standardLimit_zero, invSucc_not_eventuallyEquals_zero⟩

/-- **F5 stronger form.** For any sequence `s` and any candidate limit `L`,
there is a convergence notion under which `s` converges to `L`. In
particular, the trivial notion "everything converges to everything"
satisfies the English phrase "the sum becomes L" equally well as any
substantive notion. JGORARD's prose does not rule out such a reading, so
the claim carries no content absent specification. -/
theorem claim_is_vacuous_without_convergence_notion
    (s : ℕ → ℝ) (L : ℝ) :
    ∃ (C : ConvergenceNotion), C s L :=
  ⟨fun _ _ => True, trivial⟩

/-- **F5 non-uniqueness.** For the *same* sequence, there are convergence
notions affirming any two distinct candidate limits `L₁, L₂`. Thus
"the sum becomes …" is not a function of the sequence alone; it depends
on the convergence notion. -/
theorem different_notions_give_different_limits
    (s : ℕ → ℝ) (L₁ L₂ : ℝ) :
    ∃ (C₁ C₂ : ConvergenceNotion), C₁ s L₁ ∧ C₂ s L₂ :=
  ⟨fun _ _ => True, fun _ _ => True, trivial, trivial⟩

end Refutations
end InfraFormalization
