/-
Causal relations on the integer lattice `ℤ^{d+1}` with an L∞ spatial distance.

Events are functions `Fin (d+1) → ℤ`, with index `0` the time coordinate and indices
`1..d` the spatial ones. `p ≺ q` is defined by `q 0 - p 0 ≥ max_{i ≥ 1} |p i - q i|`, with
the maximum over an empty index set equal to `0`. The module proves that `≺` is reflexive
and transitive, that mutual precedence forces equal time and zero spatial distance, that
every pair is causally related in some direction or spacelike, and that the interval
`Δt² - spaceDist²` is positive on timelike, zero on null and negative on spacelike pairs.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfraFormalization
namespace Infra

/-- A point of `ℤ^{d+1}`. Index `0` is time and indices `1..d` are space. -/
abbrev Event (d : Nat) : Type := Fin (d + 1) → ℤ

/-- The maximum of `|p i - q i|` over the spatial indices `i = 1..d`, as a natural
number. It is `0` when `d = 0`. -/
def spaceDist (d : Nat) (p q : Event d) : ℕ :=
  (Finset.univ : Finset (Fin d)).sup
    (fun i => (p i.succ - q i.succ).natAbs)

theorem spaceDist_zero_dim (p q : Event 0) : spaceDist 0 p q = 0 := by
  unfold spaceDist
  simp

theorem spaceDist_self {d : Nat} (p : Event d) : spaceDist d p p = 0 := by
  unfold spaceDist
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intros i _
  simp

theorem spaceDist_symm {d : Nat} (p q : Event d) :
    spaceDist d p q = spaceDist d q p := by
  unfold spaceDist
  apply Finset.sup_congr rfl
  intros i _
  have h : (p i.succ - q i.succ).natAbs = (q i.succ - p i.succ).natAbs := by
    conv_lhs => rw [show p i.succ - q i.succ = -(q i.succ - p i.succ) by ring]
    exact Int.natAbs_neg _
  exact h

/-- Triangle inequality for `spaceDist`. -/
theorem spaceDist_triangle {d : Nat} (p q r : Event d) :
    spaceDist d p r ≤ spaceDist d p q + spaceDist d q r := by
  unfold spaceDist
  apply Finset.sup_le
  intros i _
  have hnat : (p i.succ - r i.succ).natAbs
            ≤ (p i.succ - q i.succ).natAbs + (q i.succ - r i.succ).natAbs := by
    have eq1 : p i.succ - r i.succ
               = (p i.succ - q i.succ) + (q i.succ - r i.succ) := by ring
    rw [eq1]
    exact Int.natAbs_add_le _ _
  have h1 : (p i.succ - q i.succ).natAbs
            ≤ (Finset.univ : Finset (Fin d)).sup
                (fun j => (p j.succ - q j.succ).natAbs) :=
    Finset.le_sup (f := fun j => (p j.succ - q j.succ).natAbs)
      (Finset.mem_univ i)
  have h2 : (q i.succ - r i.succ).natAbs
            ≤ (Finset.univ : Finset (Fin d)).sup
                (fun j => (q j.succ - r j.succ).natAbs) :=
    Finset.le_sup (f := fun j => (q j.succ - r j.succ).natAbs)
      (Finset.mem_univ i)
  omega

/-- `p ≺ q` when `spaceDist d p q ≤ q 0 - p 0`. -/
def CausalPrecedes (d : Nat) (p q : Event d) : Prop :=
  (spaceDist d p q : ℤ) ≤ q 0 - p 0

/-- Every event causally precedes itself. -/
theorem causal_refl (d : Nat) (p : Event d) : CausalPrecedes d p p := by
  unfold CausalPrecedes
  rw [spaceDist_self]
  simp

/-- `p ≺ q` and `q ≺ r` imply `p ≺ r`. -/
theorem causal_trans {d : Nat} {p q r : Event d}
    (hpq : CausalPrecedes d p q) (hqr : CausalPrecedes d q r) :
    CausalPrecedes d p r := by
  unfold CausalPrecedes at *
  have htri : (spaceDist d p r : ℤ)
            ≤ (spaceDist d p q : ℤ) + (spaceDist d q r : ℤ) := by
    exact_mod_cast spaceDist_triangle p q r
  linarith

/-- If `p ≺ q` and `q ≺ p`, then `q 0 = p 0` and `spaceDist d p q = 0`. -/
theorem causal_antisymm_time {d : Nat} {p q : Event d}
    (hpq : CausalPrecedes d p q) (hqp : CausalPrecedes d q p) :
    q 0 = p 0 ∧ spaceDist d p q = 0 := by
  unfold CausalPrecedes at *
  have hnn : (0 : ℤ) ≤ (spaceDist d p q : ℤ) := Int.natCast_nonneg _
  have hnn' : (0 : ℤ) ≤ (spaceDist d q p : ℤ) := Int.natCast_nonneg _
  have hsymm : spaceDist d q p = spaceDist d p q := spaceDist_symm q p
  rw [hsymm] at hqp
  refine ⟨?_, ?_⟩
  · linarith
  · have : (spaceDist d p q : ℤ) ≤ 0 := by linarith
    omega

/-- `spaceDist d p q < q 0 - p 0`. -/
def Timelike (d : Nat) (p q : Event d) : Prop :=
  (spaceDist d p q : ℤ) < q 0 - p 0

/-- `spaceDist d p q = q 0 - p 0` and `p 0 < q 0`. -/
def Null (d : Nat) (p q : Event d) : Prop :=
  (spaceDist d p q : ℤ) = q 0 - p 0 ∧ p 0 < q 0

/-- `Timelike d p q` implies `p ≺ q`. -/
theorem causalPrecedes_of_timelike {d : Nat} {p q : Event d}
    (h : Timelike d p q) : CausalPrecedes d p q :=
  le_of_lt h

/-- `Null d p q` implies `p ≺ q`. -/
theorem causalPrecedes_of_null {d : Nat} {p q : Event d}
    (h : Null d p q) : CausalPrecedes d p q :=
  le_of_eq h.1

/-- Neither `p ≺ q` nor `q ≺ p`. -/
def Spacelike (d : Nat) (p q : Event d) : Prop :=
  ¬ CausalPrecedes d p q ∧ ¬ CausalPrecedes d q p

/-- `Spacelike d p q` holds iff `q 0 - p 0 < spaceDist d p q` and
`p 0 - q 0 < spaceDist d q p`. -/
theorem spacelike_iff {d : Nat} (p q : Event d) :
    Spacelike d p q ↔
      q 0 - p 0 < (spaceDist d p q : ℤ)
      ∧ p 0 - q 0 < (spaceDist d q p : ℤ) := by
  unfold Spacelike CausalPrecedes
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨not_le.mp h1, not_le.mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨not_le.mpr h1, not_le.mpr h2⟩

/-- If `p 0 = q 0` and `0 < spaceDist d p q`, then `Spacelike d p q`. -/
theorem spacelike_of_equal_time {d : Nat} (p q : Event d)
    (ht : p 0 = q 0) (hsp : 0 < spaceDist d p q) :
    Spacelike d p q := by
  unfold Spacelike CausalPrecedes
  have hsymm := spaceDist_symm p q
  refine ⟨?_, ?_⟩
  · intro h
    have : (spaceDist d p q : ℤ) ≤ 0 := by rw [ht] at h; linarith
    omega
  · intro h
    have : (spaceDist d q p : ℤ) ≤ 0 := by rw [ht] at h; linarith
    omega

/-- `p ≺ q` iff `spaceDist d p q ≤ q 0 - p 0`; this is the definition of `≺`. -/
theorem causalPrecedes_iff_time_space {d : Nat} (p q : Event d) :
    CausalPrecedes d p q ↔ (spaceDist d p q : ℤ) ≤ q 0 - p 0 := Iff.rfl

/-- `Timelike d p q` and `Timelike d q r` imply `Timelike d p r`. -/
theorem timelike_trans {d : Nat} {p q r : Event d}
    (hpq : Timelike d p q) (hqr : Timelike d q r) :
    Timelike d p r := by
  unfold Timelike at *
  have htri : (spaceDist d p r : ℤ)
            ≤ (spaceDist d p q : ℤ) + (spaceDist d q r : ℤ) := by
    exact_mod_cast spaceDist_triangle p q r
  linarith

/-- The set of events `q` with `p ≺ q`. -/
def forwardCone (d : Nat) (p : Event d) : Set (Event d) :=
  { q | CausalPrecedes d p q }

/-- If `q ∈ forwardCone d p` and `q ≺ r`, then `r ∈ forwardCone d p`. -/
theorem forwardCone_upward_closed {d : Nat} (p q r : Event d)
    (hq : q ∈ forwardCone d p) (hqr : CausalPrecedes d q r) :
    r ∈ forwardCone d p :=
  causal_trans hq hqr

/-- A point is in its own forward cone. -/
theorem self_mem_forwardCone {d : Nat} (p : Event d) :
    p ∈ forwardCone d p := causal_refl d p

/-- `(q 0 - p 0)² - (spaceDist d p q)²`. -/
def minkowskiIntervalSq (d : Nat) (p q : Event d) : ℤ :=
  (q 0 - p 0)^2 - (spaceDist d p q : ℤ)^2

/-- `Timelike d p q` implies `0 < minkowskiIntervalSq d p q`. -/
theorem minkowskiIntervalSq_pos_of_timelike {d : Nat} {p q : Event d}
    (h : Timelike d p q) :
    0 < minkowskiIntervalSq d p q := by
  unfold minkowskiIntervalSq Timelike at *
  have hnn : (0 : ℤ) ≤ (spaceDist d p q : ℤ) := Int.natCast_nonneg _
  have htime' : 0 < q 0 - p 0 := lt_of_le_of_lt hnn h
  have factor : (q 0 - p 0)^2 - (spaceDist d p q : ℤ)^2
              = ((q 0 - p 0) - (spaceDist d p q : ℤ))
                * ((q 0 - p 0) + (spaceDist d p q : ℤ)) := by ring
  rw [factor]
  apply mul_pos
  · linarith
  · linarith

/-- `Null d p q` implies `minkowskiIntervalSq d p q = 0`. -/
theorem minkowskiIntervalSq_zero_of_null {d : Nat} {p q : Event d}
    (h : Null d p q) :
    minkowskiIntervalSq d p q = 0 := by
  unfold minkowskiIntervalSq Null at *
  rw [h.1]
  ring

/-- `Spacelike d p q` implies `minkowskiIntervalSq d p q < 0`. -/
theorem minkowskiIntervalSq_neg_of_spacelike {d : Nat} {p q : Event d}
    (h : Spacelike d p q) :
    minkowskiIntervalSq d p q < 0 := by
  unfold minkowskiIntervalSq
  rw [spacelike_iff] at h
  obtain ⟨h1, h2⟩ := h
  -- h1 : q 0 - p 0 < spaceDist d p q
  -- h2 : p 0 - q 0 < spaceDist d q p
  have hsymm : (spaceDist d q p : ℤ) = (spaceDist d p q : ℤ) := by
    rw [spaceDist_symm q p]
  rw [hsymm] at h2
  -- Both (q 0 - p 0) < spaceDist p q, and -(q 0 - p 0) < spaceDist p q
  -- So |q 0 - p 0| < spaceDist p q, hence (q 0 - p 0)^2 < (spaceDist p q)^2.
  have habs : (q 0 - p 0)^2 < (spaceDist d p q : ℤ)^2 := by
    have h1' : q 0 - p 0 < (spaceDist d p q : ℤ) := h1
    have h2' : -(q 0 - p 0) < (spaceDist d p q : ℤ) := by linarith
    have hnn : (0 : ℤ) ≤ (spaceDist d p q : ℤ) := Int.natCast_nonneg _
    nlinarith
  linarith

end Infra
end InfraFormalization
