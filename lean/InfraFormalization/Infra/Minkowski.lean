/-
Continuum Minkowski spacetime `ℝ^{1,d}` with L∞ spatial metric.

Mirrors the structure of `Infra/LorentzLattice.lean` on ℝ-valued
coordinates instead of ℤ. Used as the target of the scaled Lorentz
lattice (`Infra/ScaledLorentz.lean`): in the continuum limit, the
scaled discrete lattice sits densely inside this Minkowski space and
the discrete `CausalPrecedes` matches the continuum one exactly
(not just approximately — both are defined by the same inequality
`spaceDist ≤ Δt`).

We use L∞ as the spatial metric to match the discrete side. Other
choices (L¹, L²) give different causal cones in the continuum but are
not what the discrete rewriting framework suggests.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Abs

namespace InfraFormalization
namespace Infra

/-- Continuum event: `Fin (d+1) → ℝ` (index `0` = time, indices
`1..d` = space). -/
abbrev ContinuumEvent (d : Nat) : Type := Fin (d + 1) → ℝ

/-- Continuum spatial L∞ distance. For `d = 0` there are no spatial
coordinates; we take the sup over the empty finset via ℕ-like fallback
by using `Finset.sup'` when `d ≥ 1` and `0` when `d = 0`. Implementation
via `Finset.sup` is cleaner on ℝ but ℝ has no `OrderBot`, so we use
`Finset.sup'` (requiring nonemptiness) for `d ≥ 1` and handle `d = 0`
by cases. -/
noncomputable def continuumSpaceDist (d : Nat) (p q : ContinuumEvent d) : ℝ :=
  match d with
  | 0 => 0
  | k + 1 =>
    (Finset.univ : Finset (Fin (k + 1))).sup'
      ⟨0, Finset.mem_univ 0⟩
      (fun i => |p i.succ - q i.succ|)

@[simp] theorem continuumSpaceDist_zero_dim (p q : ContinuumEvent 0) :
    continuumSpaceDist 0 p q = 0 := rfl

theorem continuumSpaceDist_nonneg {d : Nat} (p q : ContinuumEvent d) :
    0 ≤ continuumSpaceDist d p q := by
  unfold continuumSpaceDist
  match d with
  | 0 => exact le_refl 0
  | k + 1 =>
    apply le_trans (abs_nonneg (p (⟨0, Nat.succ_pos k⟩ : Fin (k+1)).succ
                                - q (⟨0, Nat.succ_pos k⟩ : Fin (k+1)).succ))
    exact Finset.le_sup'
      (f := fun i => |p i.succ - q i.succ|)
      (Finset.mem_univ (⟨0, Nat.succ_pos k⟩ : Fin (k+1)))

theorem continuumSpaceDist_self {d : Nat} (p : ContinuumEvent d) :
    continuumSpaceDist d p p = 0 := by
  unfold continuumSpaceDist
  match d with
  | 0 => rfl
  | k + 1 =>
    apply le_antisymm
    · apply Finset.sup'_le
      intros i _
      simp
    · have h : (0 : ℝ) = |p (⟨0, Nat.succ_pos k⟩ : Fin (k+1)).succ
                         - p (⟨0, Nat.succ_pos k⟩ : Fin (k+1)).succ| := by simp
      rw [h]
      exact Finset.le_sup'
        (f := fun i => |p i.succ - p i.succ|)
        (Finset.mem_univ (⟨0, Nat.succ_pos k⟩ : Fin (k+1)))

theorem continuumSpaceDist_symm {d : Nat} (p q : ContinuumEvent d) :
    continuumSpaceDist d p q = continuumSpaceDist d q p := by
  unfold continuumSpaceDist
  match d with
  | 0 => rfl
  | k + 1 =>
    apply Finset.sup'_congr ⟨0, Finset.mem_univ 0⟩ rfl
    intros i _
    rw [abs_sub_comm]

theorem continuumSpaceDist_triangle {d : Nat} (p q r : ContinuumEvent d) :
    continuumSpaceDist d p r
      ≤ continuumSpaceDist d p q + continuumSpaceDist d q r := by
  unfold continuumSpaceDist
  match d with
  | 0 => simp
  | k + 1 =>
    apply Finset.sup'_le
    intros i _
    have habs : |p i.succ - r i.succ|
              ≤ |p i.succ - q i.succ| + |q i.succ - r i.succ| := by
      have eq1 : p i.succ - r i.succ
                 = (p i.succ - q i.succ) + (q i.succ - r i.succ) := by ring
      rw [eq1]
      exact abs_add_le _ _
    have h1 : |p i.succ - q i.succ|
              ≤ (Finset.univ : Finset (Fin (k + 1))).sup'
                  ⟨0, Finset.mem_univ 0⟩
                  (fun j => |p j.succ - q j.succ|) :=
      Finset.le_sup'
        (f := fun j => |p j.succ - q j.succ|)
        (Finset.mem_univ i)
    have h2 : |q i.succ - r i.succ|
              ≤ (Finset.univ : Finset (Fin (k + 1))).sup'
                  ⟨0, Finset.mem_univ 0⟩
                  (fun j => |q j.succ - r j.succ|) :=
      Finset.le_sup'
        (f := fun j => |q j.succ - r j.succ|)
        (Finset.mem_univ i)
    linarith

/-- **Continuum causal precedence** on ℝ^{1,d}: `p ≺ q` iff the time
increment dominates the spatial L∞ increment. -/
def ContinuumCausalPrecedes (d : Nat) (p q : ContinuumEvent d) : Prop :=
  continuumSpaceDist d p q ≤ q 0 - p 0

theorem continuumCausal_refl (d : Nat) (p : ContinuumEvent d) :
    ContinuumCausalPrecedes d p p := by
  unfold ContinuumCausalPrecedes
  rw [continuumSpaceDist_self]
  simp

theorem continuumCausal_trans {d : Nat} {p q r : ContinuumEvent d}
    (hpq : ContinuumCausalPrecedes d p q)
    (hqr : ContinuumCausalPrecedes d q r) :
    ContinuumCausalPrecedes d p r := by
  unfold ContinuumCausalPrecedes at *
  have htri := continuumSpaceDist_triangle p q r
  linarith

/-- **Continuum timelike:** strict interior of the forward light cone. -/
def ContinuumTimelike (d : Nat) (p q : ContinuumEvent d) : Prop :=
  continuumSpaceDist d p q < q 0 - p 0

/-- **Continuum null:** light-cone edge, forward-oriented. -/
def ContinuumNull (d : Nat) (p q : ContinuumEvent d) : Prop :=
  continuumSpaceDist d p q = q 0 - p 0 ∧ p 0 < q 0

/-- **Continuum spacelike:** outside both forward and backward cones. -/
def ContinuumSpacelike (d : Nat) (p q : ContinuumEvent d) : Prop :=
  ¬ ContinuumCausalPrecedes d p q ∧ ¬ ContinuumCausalPrecedes d q p

/-- Continuum signed Minkowski interval squared. -/
noncomputable def continuumMinkowskiIntervalSq
    (d : Nat) (p q : ContinuumEvent d) : ℝ :=
  (q 0 - p 0)^2 - (continuumSpaceDist d p q)^2

/-- Trichotomy on the continuum. -/
theorem continuumCausal_or_spacelike (d : Nat) (p q : ContinuumEvent d) :
    ContinuumCausalPrecedes d p q ∨
    ContinuumCausalPrecedes d q p ∨
    ContinuumSpacelike d p q := by
  unfold ContinuumCausalPrecedes ContinuumSpacelike
  by_cases h1 : continuumSpaceDist d p q ≤ q 0 - p 0
  · exact Or.inl h1
  by_cases h2 : continuumSpaceDist d q p ≤ p 0 - q 0
  · exact Or.inr (Or.inl h2)
  · right; right
    exact ⟨h1, h2⟩

end Infra
end InfraFormalization
