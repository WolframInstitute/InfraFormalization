/-
Int-to-ℝ embedding of the discrete Lorentz lattice into continuum
Minkowski.

Lightweight bridge from `Event d = Fin (d+1) → ℤ` to
`ContinuumEvent d = Fin (d+1) → ℝ`: just cast each coordinate. We
prove the embedding **preserves causal precedence in the forward
direction**: if `p ≺ q` in the discrete Lorentz lattice, then the
embeddings stand in `ContinuumCausalPrecedes`.

A full isometry-plus-density correspondence (the Lorentzian analog of
the Riemannian `dTorus_gh_bound`) is a richer target and requires
careful handling of sup'/cast interactions that we do not attempt
here. The forward-direction embedding is enough for the rule-search
use case (`RULE_SEARCH.md`) where we want to verify that a discrete
causal pair remains causally related after passing to the continuum.

The structural gap remaining — "the scaled lattice converges to
continuum Minkowski in a Lorentzian Gromov–Hausdorff sense" — is
still open in this formalisation. Lorentzian GH is a sharper theory
than its Riemannian cousin (see Noldus–Suhr) and is not in Mathlib.
-/

import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.Minkowski

namespace InfraFormalization
namespace Infra

/-- Componentwise int-to-ℝ cast embedding, no scaling. -/
noncomputable def lorentzIntEmbed {d : Nat} (p : Event d) : ContinuumEvent d :=
  fun k => (p k : ℝ)

@[simp] theorem lorentzIntEmbed_apply {d : Nat} (p : Event d) (k : Fin (d + 1)) :
    lorentzIntEmbed p k = (p k : ℝ) := rfl

/-- **Spatial distance bound under the embedding.** For each
coordinate, the continuum per-coordinate abs is at most the discrete
spaceDist cast to ℝ. -/
theorem continuumSpaceDist_le_cast {d : Nat} (p q : Event d) :
    continuumSpaceDist d (lorentzIntEmbed p) (lorentzIntEmbed q)
    ≤ ((spaceDist d p q : ℕ) : ℝ) := by
  unfold continuumSpaceDist spaceDist lorentzIntEmbed
  match d with
  | 0 =>
    show (0 : ℝ) ≤ ((0 : ℕ) : ℝ)
    simp
  | k + 1 =>
    show (Finset.univ : Finset (Fin (k + 1))).sup'
            ⟨0, Finset.mem_univ 0⟩
            (fun i => |(p i.succ : ℝ) - (q i.succ : ℝ)|)
        ≤ (((Finset.univ : Finset (Fin (k + 1))).sup
              (fun i => (p i.succ - q i.succ).natAbs) : ℕ) : ℝ)
    apply Finset.sup'_le
    intros i _
    -- Per coordinate: |(p:ℝ) - (q:ℝ)| = (natAbs (p - q) : ℝ) ≤ (sup natAbs : ℝ).
    have step1 : |(p i.succ : ℝ) - (q i.succ : ℝ)|
                 = (((p i.succ - q i.succ).natAbs : ℕ) : ℝ) := by
      rw [show (p i.succ : ℝ) - (q i.succ : ℝ)
             = ((p i.succ - q i.succ : ℤ) : ℝ) from by push_cast; ring]
      rw [← Int.cast_abs, ← Nat.cast_natAbs (α := ℝ)]
    rw [step1]
    -- Now: (natAbs (p i.succ - q i.succ) : ℝ) ≤ (sup : ℝ). Nat-ineq and cast.
    have hle : (p i.succ - q i.succ).natAbs
             ≤ (Finset.univ : Finset (Fin (k + 1))).sup
                 (fun j => (p j.succ - q j.succ).natAbs) :=
      Finset.le_sup (f := fun j => (p j.succ - q j.succ).natAbs)
        (Finset.mem_univ i)
    exact_mod_cast hle

/-- **Forward-direction preservation.** Causal precedence in the
discrete Lorentz lattice implies continuum causal precedence under the
int-to-ℝ embedding. -/
theorem lorentzIntEmbed_preserves_causal {d : Nat} (p q : Event d)
    (h : CausalPrecedes d p q) :
    ContinuumCausalPrecedes d (lorentzIntEmbed p) (lorentzIntEmbed q) := by
  unfold CausalPrecedes ContinuumCausalPrecedes at *
  have h1 : continuumSpaceDist d (lorentzIntEmbed p) (lorentzIntEmbed q)
          ≤ ((spaceDist d p q : ℕ) : ℝ) :=
    continuumSpaceDist_le_cast p q
  have h2 : ((spaceDist d p q : ℕ) : ℝ) ≤ (q 0 : ℝ) - (p 0 : ℝ) := by
    have : ((spaceDist d p q : ℕ) : ℤ) ≤ q 0 - p 0 := h
    exact_mod_cast this
  have h3 : (lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0 = (q 0 : ℝ) - (p 0 : ℝ) := rfl
  rw [h3]
  linarith

/-- **Timelike preservation.** Same for strict interior. -/
theorem lorentzIntEmbed_preserves_timelike {d : Nat} (p q : Event d)
    (h : Timelike d p q) :
    ContinuumTimelike d (lorentzIntEmbed p) (lorentzIntEmbed q) := by
  unfold Timelike ContinuumTimelike at *
  have h1 : continuumSpaceDist d (lorentzIntEmbed p) (lorentzIntEmbed q)
          ≤ ((spaceDist d p q : ℕ) : ℝ) :=
    continuumSpaceDist_le_cast p q
  have h2 : ((spaceDist d p q : ℕ) : ℝ) < (q 0 : ℝ) - (p 0 : ℝ) := by
    have : ((spaceDist d p q : ℕ) : ℤ) < q 0 - p 0 := h
    exact_mod_cast this
  have h3 : (lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0 = (q 0 : ℝ) - (p 0 : ℝ) := rfl
  rw [h3]
  linarith

end Infra
end InfraFormalization
