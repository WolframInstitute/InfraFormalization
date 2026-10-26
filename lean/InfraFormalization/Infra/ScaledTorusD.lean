/-
(d+1)-dimensional torus lattice with metric scaled by `1/n`.

Vertices are functions `Fin (d+1) → Fin n`. This module defines the L∞ lattice distance
`dTorusLatticeDist` (the maximum of the `d+1` cycle distances), the L∞ circle distance `dTorusDist`
on `Fin (d+1) → ℝ`, and the componentwise embedding `dTorusEmbed d n p i = p i / n`. It proves that
the embedding scales distances by `1/n` and that every point of [0, 1)^(d+1) is within `1/(2n)` of
its image. The index type `Fin (d+1)` makes `Finset.univ` nonempty, as `Finset.sup'` requires.
-/

import InfraFormalization.Infra.ScaledCycle
import InfraFormalization.Infra.Circle
import Mathlib.Data.Finset.Lattice.Fold

namespace InfraFormalization
namespace Infra

/-- `Finset.univ` on `Fin (d+1)` is nonempty. -/
theorem finUniv_succ_nonempty (d : Nat) :
    (Finset.univ : Finset (Fin (d + 1))).Nonempty :=
  ⟨0, Finset.mem_univ 0⟩

/-- `Nat.cast` commutes with `sup'` over a nonempty finset. -/
private lemma sup'_nat_cast {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (f : α → ℕ) :
    ((s.sup' hs f : ℕ) : ℝ) = s.sup' hs (fun a => (f a : ℝ)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s has hs ih =>
    rw [Finset.sup'_cons hs (f := f),
        Finset.sup'_cons hs (f := fun a => (f a : ℝ)),
        Nat.cast_max, ih]

/-- Division by a positive constant commutes with `sup'`. -/
private lemma sup'_div_const {α : Type*} {s : Finset α} (hs : s.Nonempty)
    (f : α → ℝ) {c : ℝ} (hc : 0 < c) :
    s.sup' hs (fun a => f a / c) = s.sup' hs f / c := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s has hs ih =>
    rw [Finset.sup'_cons hs (f := fun a => f a / c),
        Finset.sup'_cons hs (f := f),
        ih]
    exact max_div_div_right (le_of_lt hc) _ _

/-- L∞ product of cycle distances on `(Fin n)^(d+1)`:
`dTorusLatticeDist d n p q = max_i cycleDist n (p i) (q i)`, computed with `Finset.sup'`. -/
def dTorusLatticeDist (d n : Nat) (p q : Fin (d + 1) → Fin n) : Nat :=
  (Finset.univ : Finset (Fin (d + 1))).sup'
    (finUniv_succ_nonempty d) (fun i => cycleDist n (p i) (q i))

theorem dTorusLatticeDist_self {d n : Nat} (p : Fin (d + 1) → Fin n) :
    dTorusLatticeDist d n p p = 0 := by
  unfold dTorusLatticeDist
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup'_le
  intros i _
  simp

theorem dTorusLatticeDist_symm {d n : Nat} (p q : Fin (d + 1) → Fin n) :
    dTorusLatticeDist d n p q = dTorusLatticeDist d n q p := by
  unfold dTorusLatticeDist
  exact Finset.sup'_congr (finUniv_succ_nonempty d) rfl
    (fun i _ => cycleDist_symm (p i) (q i))

theorem dTorusLatticeDist_triangle {d n : Nat} (p q r : Fin (d + 1) → Fin n) :
    dTorusLatticeDist d n p r
      ≤ dTorusLatticeDist d n p q + dTorusLatticeDist d n q r := by
  unfold dTorusLatticeDist
  apply Finset.sup'_le
  intros i _
  have h := cycleDist_triangle (p i) (q i) (r i)
  have hpq : cycleDist n (p i) (q i)
               ≤ (Finset.univ : Finset (Fin (d + 1))).sup'
                   (finUniv_succ_nonempty d)
                   (fun j => cycleDist n (p j) (q j)) :=
    Finset.le_sup' (f := fun j => cycleDist n (p j) (q j))
      (Finset.mem_univ i)
  have hqr : cycleDist n (q i) (r i)
               ≤ (Finset.univ : Finset (Fin (d + 1))).sup'
                   (finUniv_succ_nonempty d)
                   (fun j => cycleDist n (q j) (r j)) :=
    Finset.le_sup' (f := fun j => cycleDist n (q j) (r j))
      (Finset.mem_univ i)
  omega

/-- L∞ product of circle distances on `Fin (d+1) → ℝ`:
`dTorusDist d p q = max_i circleDist (p i) (q i)`. -/
noncomputable def dTorusDist (d : Nat) (p q : Fin (d + 1) → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin (d + 1))).sup'
    (finUniv_succ_nonempty d) (fun i => circleDist (p i) (q i))

/-- The componentwise embedding `(Fin n)^(d+1) → ℝ^(d+1)`, `p ↦ (i ↦ p i / n)`. -/
noncomputable def dTorusEmbed (d n : Nat) (p : Fin (d + 1) → Fin n) :
    Fin (d + 1) → ℝ :=
  fun i => latticeEmbed n (p i)

theorem dTorusEmbed_mem_unit_cube {d n : Nat} (hn : 0 < n)
    (p : Fin (d + 1) → Fin n) :
    ∀ i, 0 ≤ dTorusEmbed d n p i ∧ dTorusEmbed d n p i < 1 := by
  intro i
  exact latticeEmbed_mem_unit_interval hn (p i)

/-- For `n > 0`,
`dTorusDist d (dTorusEmbed d n p) (dTorusEmbed d n q) = dTorusLatticeDist d n p q / n`. The proof
applies `latticeEmbed_isometry` in each coordinate and moves the division by `n` out of `sup'`. -/
theorem dTorusEmbed_isometry {d n : Nat} (hn : 0 < n)
    (p q : Fin (d + 1) → Fin n) :
    dTorusDist d (dTorusEmbed d n p) (dTorusEmbed d n q) =
      (dTorusLatticeDist d n p q : ℝ) / n := by
  unfold dTorusDist dTorusEmbed dTorusLatticeDist
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Rewrite each coordinate's circleDist as cycleDist / n.
  rw [Finset.sup'_congr (finUniv_succ_nonempty d) rfl
        (g := fun i => (cycleDist n (p i) (q i) : ℝ) / n)
        (fun i _ => latticeEmbed_isometry hn (p i) (q i))]
  rw [sup'_div_const (finUniv_succ_nonempty d)
        (f := fun i => (cycleDist n (p i) (q i) : ℝ)) hn_pos]
  rw [← sup'_nat_cast (finUniv_succ_nonempty d)
        (f := fun i => cycleDist n (p i) (q i))]

/-- For `n > 0`, every `x : Fin (d+1) → ℝ` with each component in [0, 1) is within `dTorusDist`
distance `1/(2n)` of some `dTorusEmbed d n p`. -/
theorem dTorusEmbed_covers {d n : Nat} (hn : 0 < n)
    (x : Fin (d + 1) → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) :
    ∃ p : Fin (d + 1) → Fin n,
      dTorusDist d x (dTorusEmbed d n p) ≤ 1 / (2 * n) := by
  have choose : ∀ i, ∃ pi : Fin n,
      circleDist (x i) (latticeEmbed n pi) ≤ 1 / (2 * n) := by
    intro i
    rcases hx i with ⟨hxi, hxi'⟩
    exact latticeEmbed_covers hn (x i) hxi hxi'
  choose p hp using choose
  refine ⟨p, ?_⟩
  unfold dTorusDist dTorusEmbed
  apply Finset.sup'_le
  intro i _
  exact hp i

/-- For `n > 0`, there is a map `f : (Fin n)^(d+1) → ℝ^(d+1)` with values in [0, 1)^(d+1) such that
`dTorusDist d (f p) (f q) = dTorusLatticeDist d n p q / n` and every point of [0, 1)^(d+1) is within
`1/(2n)` of the image of `f`. -/
theorem dTorus_gh_bound (d n : Nat) (hn : 0 < n) :
    ∃ f : (Fin (d + 1) → Fin n) → (Fin (d + 1) → ℝ),
      (∀ p i, 0 ≤ f p i ∧ f p i < 1) ∧
      (∀ p q, dTorusDist d (f p) (f q) = (dTorusLatticeDist d n p q : ℝ) / n) ∧
      (∀ x, (∀ i, 0 ≤ x i ∧ x i < 1) →
        ∃ p, dTorusDist d x (f p) ≤ 1 / (2 * n)) := by
  refine ⟨dTorusEmbed d n, ?_, ?_, ?_⟩
  · intro p i; exact dTorusEmbed_mem_unit_cube hn p i
  · intro p q; exact dTorusEmbed_isometry hn p q
  · intro x hx; exact dTorusEmbed_covers hn x hx

end Infra
end InfraFormalization
