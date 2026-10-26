/-
Real coordinates `Fin (d+1) → ℝ` with an L∞ spatial distance and the causal relations it
defines.

The module defines the spatial L∞ distance `continuumSpaceDist` and proves that it is
nonnegative, symmetric, zero on the diagonal and satisfies the triangle inequality. It
defines causal precedence (`spaceDist ≤ Δt`), timelike, null and spacelike relations and
the interval `Δt² - spaceDist²`, and proves reflexivity and transitivity of causal
precedence. These definitions are the ℝ-valued versions of those in
`Infra/LorentzLattice.lean`. With the L∞ distance the causal cones are pyramids, not the
round cones of Minkowski space with the Euclidean spatial norm.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Abs

namespace InfraFormalization
namespace Infra

/-- A point of `ℝ^{d+1}`. Index `0` is time and indices `1..d` are space. -/
abbrev ContinuumEvent (d : Nat) : Type := Fin (d + 1) → ℝ

/-- The L∞ distance between the spatial coordinates of `p` and `q`: the maximum of
`|p i - q i|` over `i = 1..d`, and `0` when `d = 0`. -/
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

/-- `p` causally precedes `q` when `continuumSpaceDist d p q ≤ q 0 - p 0`. -/
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

/-- `continuumSpaceDist d p q < q 0 - p 0`. -/
def ContinuumTimelike (d : Nat) (p q : ContinuumEvent d) : Prop :=
  continuumSpaceDist d p q < q 0 - p 0

/-- `continuumSpaceDist d p q = q 0 - p 0` and `p 0 < q 0`. -/
def ContinuumNull (d : Nat) (p q : ContinuumEvent d) : Prop :=
  continuumSpaceDist d p q = q 0 - p 0 ∧ p 0 < q 0

/-- Neither `p` causally precedes `q` nor `q` causally precedes `p`. -/
def ContinuumSpacelike (d : Nat) (p q : ContinuumEvent d) : Prop :=
  ¬ ContinuumCausalPrecedes d p q ∧ ¬ ContinuumCausalPrecedes d q p

/-- `(q 0 - p 0)² - (continuumSpaceDist d p q)²`. -/
noncomputable def continuumMinkowskiIntervalSq
    (d : Nat) (p q : ContinuumEvent d) : ℝ :=
  (q 0 - p 0)^2 - (continuumSpaceDist d p q)^2

end Infra
end InfraFormalization
