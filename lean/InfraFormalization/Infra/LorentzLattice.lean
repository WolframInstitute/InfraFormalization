/-
Discrete Lorentzian causal structure on a cubic lattice.

Takes events as functions `Fin (d+1) → ℤ` (1 time index `0`, and `d`
space indices `1..d`), and declares:

  `p ≺ q`   iff   `q 0 - p 0 ≥ max_{i ≥ 1} |p i - q i|`.

That is, `q` lies in the forward L∞ light cone of `p`. This is the
discrete analogue of the Minkowski causal structure on ℝ^{1,d} with
the L∞ spatial metric.

Implementation: we define `spaceDist` as a `ℕ`-valued quantity via
`natAbs` and `Finset.sup` (which uses `OrderBot = 0` on ℕ and needs
no nonemptiness witness — the `d = 0` case sits cleanly in the
definition as "sup over empty = 0").

Parameter mapping:
  * `d = 1`  — 1+1-dim;
  * `d = 2`  — 1+2-dim;
  * `d = 3`  — 1+3-dim (physical spacetime).

The `d = 0` edge case (events with only a time coordinate) is handled
without pattern-matching by the underlying `Finset.sup` on the empty
finset.

**Why this matters.** The Wolfram-model causal graph is supposed to
converge to a Lorentzian manifold. The lightest test of the
infrageometry framework is whether a trivial cubic lattice exhibits
the basic Lorentzian-manifold features (partial order + light-cone
dichotomy). This file verifies it does. Subsequent work will replace
the lattice with a rewriting-system causal graph.
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace InfraFormalization
namespace Infra

/-- Coordinates of an event: `Fin (d+1) → ℤ` (1 time + `d` space). -/
abbrev Event (d : Nat) : Type := Fin (d + 1) → ℤ

/-- Spatial L∞ distance between two events as a natural number. Ignores
the time coord. For `d = 0`, this is sup over empty = `0`. -/
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

/-- **Causal precedence.** `p ≺ q` iff the time-increment from `p` to
`q` matches or exceeds the spatial L∞ increment. -/
def CausalPrecedes (d : Nat) (p q : Event d) : Prop :=
  (spaceDist d p q : ℤ) ≤ q 0 - p 0

/-- Reflexivity: every event causally precedes itself. -/
theorem causal_refl (d : Nat) (p : Event d) : CausalPrecedes d p p := by
  unfold CausalPrecedes
  rw [spaceDist_self]
  simp

/-- Transitivity: `p ≺ q` and `q ≺ r` ⇒ `p ≺ r`. -/
theorem causal_trans {d : Nat} {p q r : Event d}
    (hpq : CausalPrecedes d p q) (hqr : CausalPrecedes d q r) :
    CausalPrecedes d p r := by
  unfold CausalPrecedes at *
  have htri : (spaceDist d p r : ℤ)
            ≤ (spaceDist d p q : ℤ) + (spaceDist d q r : ℤ) := by
    exact_mod_cast spaceDist_triangle p q r
  linarith

/-- Antisymmetry in the time direction. If `p ≺ q` and `q ≺ p`, they
have equal time coordinates and are at zero spatial distance. -/
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

/-- A timelike separation: `p ≺ q` and time coordinates strictly differ. -/
def Timelike (d : Nat) (p q : Event d) : Prop :=
  CausalPrecedes d p q ∧ p 0 < q 0

/-- A spacelike pair: neither causally precedes the other. -/
def Spacelike (d : Nat) (p q : Event d) : Prop :=
  ¬ CausalPrecedes d p q ∧ ¬ CausalPrecedes d q p

/-- Every pair of events is either causally related (in some
direction) or spacelike. -/
theorem causal_or_spacelike (d : Nat) (p q : Event d) :
    CausalPrecedes d p q ∨ CausalPrecedes d q p ∨ Spacelike d p q := by
  unfold CausalPrecedes Spacelike
  by_cases h1 : (spaceDist d p q : ℤ) ≤ q 0 - p 0
  · exact Or.inl h1
  by_cases h2 : (spaceDist d q p : ℤ) ≤ p 0 - q 0
  · exact Or.inr (Or.inl h2)
  · right; right
    exact ⟨h1, h2⟩

/-- On a spacelike pair, the spatial distance strictly exceeds the
time-coordinate gap (in both directions). -/
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

/-- **Simultaneous distinct events are spacelike.** If `p 0 = q 0`
(they share a time coordinate) and they are spatially separated
(`0 < spaceDist d p q`), then neither causally precedes the other. -/
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

/-- **Forward-cone characterization.** `p ≺ q` iff `q`'s time
coordinate is at least `p`'s, and the spatial separation is no larger
than the time increment. -/
theorem causalPrecedes_iff_time_space {d : Nat} (p q : Event d) :
    CausalPrecedes d p q ↔ (spaceDist d p q : ℤ) ≤ q 0 - p 0 := Iff.rfl

/-- Timelike separations compose: `Timelike p q` and `Timelike q r`
imply `Timelike p r`. -/
theorem timelike_trans {d : Nat} {p q r : Event d}
    (hpq : Timelike d p q) (hqr : Timelike d q r) :
    Timelike d p r := by
  unfold Timelike at *
  refine ⟨causal_trans hpq.1 hqr.1, ?_⟩
  linarith [hpq.2, hqr.2]

/-- **Forward cone.** The set of events causally preceded by `p`. -/
def forwardCone (d : Nat) (p : Event d) : Set (Event d) :=
  { q | CausalPrecedes d p q }

/-- Forward cones are upward-closed under `CausalPrecedes`: if `q` is
in `p`'s forward cone and `q ≺ r`, then `r` is in `p`'s cone too. -/
theorem forwardCone_upward_closed {d : Nat} (p q r : Event d)
    (hq : q ∈ forwardCone d p) (hqr : CausalPrecedes d q r) :
    r ∈ forwardCone d p :=
  causal_trans hq hqr

/-- A point is in its own forward cone. -/
theorem self_mem_forwardCone {d : Nat} (p : Event d) :
    p ∈ forwardCone d p := causal_refl d p

end Infra
end InfraFormalization
