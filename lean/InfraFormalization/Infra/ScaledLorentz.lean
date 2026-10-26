/-
Embedding of the integer Lorentz lattice into continuum Minkowski space.

This module defines the coordinatewise cast `lorentzIntEmbed` from `Event d = Fin (d+1) → ℤ` to
`ContinuumEvent d = Fin (d+1) → ℝ` and the scaled embedding `scaledLorentzEmbed n`, which divides
each coordinate by `n`. It proves that both embeddings preserve the spatial distance (divided by `n`
in the scaled case), that both preserve and reflect `CausalPrecedes`, that `lorentzIntEmbed`
preserves and reflects `Timelike`, and that the scaled lattice is within `1/(2n)` of every
continuum event in each coordinate. Lorentzian Gromov–Hausdorff convergence is not stated here.
-/

import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.Minkowski
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

namespace InfraFormalization
namespace Infra

/-- Division by a positive constant commutes with `sup'` on real-valued functions over a nonempty
finset. -/
private lemma sup'_div_const_real {α : Type*} {s : Finset α}
    (hs : s.Nonempty) (f : α → ℝ) {c : ℝ} (hc : 0 < c) :
    s.sup' hs (fun a => f a / c) = s.sup' hs f / c := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s has hs ih =>
    rw [Finset.sup'_cons hs (f := fun a => f a / c),
        Finset.sup'_cons hs (f := f), ih]
    exact max_div_div_right (le_of_lt hc) _ _

/-- Componentwise int-to-ℝ cast embedding, no scaling. -/
noncomputable def lorentzIntEmbed {d : Nat} (p : Event d) : ContinuumEvent d :=
  fun k => (p k : ℝ)

@[simp] theorem lorentzIntEmbed_apply {d : Nat} (p : Event d) (k : Fin (d + 1)) :
    lorentzIntEmbed p k = (p k : ℝ) := rfl

/-- The continuum spatial distance of the embedded events is at most the discrete spatial distance
cast to ℝ. -/
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

/-- If `CausalPrecedes d p q` holds in the integer lattice, then `ContinuumCausalPrecedes` holds
for the embedded events. -/
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

/-- If `Timelike d p q` holds in the integer lattice, then `ContinuumTimelike` holds for the
embedded events. -/
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

/-- The discrete spatial distance cast to ℝ is at most the continuum spatial distance of the
embedded events. -/
theorem continuumSpaceDist_ge_cast {d : Nat} (p q : Event d) :
    ((spaceDist d p q : ℕ) : ℝ)
    ≤ continuumSpaceDist d (lorentzIntEmbed p) (lorentzIntEmbed q) := by
  unfold continuumSpaceDist spaceDist lorentzIntEmbed
  match d with
  | 0 =>
    show ((0 : ℕ) : ℝ) ≤ (0 : ℝ)
    simp
  | k + 1 =>
    -- Both sides are sup' / sup of the same per-coordinate quantity.
    -- Strategy: find an index achieving the max on the Nat side, and
    -- use it to lower-bound the ℝ-side sup'.
    show (((Finset.univ : Finset (Fin (k + 1))).sup
              (fun i => (p i.succ - q i.succ).natAbs) : ℕ) : ℝ)
        ≤ (Finset.univ : Finset (Fin (k + 1))).sup'
              ⟨0, Finset.mem_univ 0⟩
              (fun i => |(p i.succ : ℝ) - (q i.succ : ℝ)|)
    -- Pick an iMax achieving the sup on the nat side.
    obtain ⟨iMax, _, hmax⟩ :=
      (Finset.univ : Finset (Fin (k + 1))).exists_mem_eq_sup'
        ⟨0, Finset.mem_univ 0⟩ (fun i => (p i.succ - q i.succ).natAbs)
    -- Then cast natAbs ↔ real abs at iMax, and use le_sup'.
    have hpt : |(p iMax.succ : ℝ) - (q iMax.succ : ℝ)|
               = (((p iMax.succ - q iMax.succ).natAbs : ℕ) : ℝ) := by
      rw [show (p iMax.succ : ℝ) - (q iMax.succ : ℝ)
             = ((p iMax.succ - q iMax.succ : ℤ) : ℝ) from by push_cast; ring]
      rw [← Int.cast_abs, ← Nat.cast_natAbs (α := ℝ)]
    calc (((Finset.univ : Finset (Fin (k + 1))).sup
              (fun i => (p i.succ - q i.succ).natAbs) : ℕ) : ℝ)
        = ((((Finset.univ : Finset (Fin (k + 1))).sup'
              ⟨0, Finset.mem_univ 0⟩
              (fun i => (p i.succ - q i.succ).natAbs)) : ℕ) : ℝ) := by
            congr 1
            exact (Finset.sup'_eq_sup ⟨0, Finset.mem_univ 0⟩ _).symm
      _ = (((p iMax.succ - q iMax.succ).natAbs : ℕ) : ℝ) := by rw [hmax]
      _ = |(p iMax.succ : ℝ) - (q iMax.succ : ℝ)| := hpt.symm
      _ ≤ (Finset.univ : Finset (Fin (k + 1))).sup'
              ⟨0, Finset.mem_univ 0⟩
              (fun i => |(p i.succ : ℝ) - (q i.succ : ℝ)|) :=
          Finset.le_sup'
            (f := fun i => |(p i.succ : ℝ) - (q i.succ : ℝ)|)
            (Finset.mem_univ iMax)

/-- The continuum spatial distance of the embedded events equals the discrete spatial distance cast
to ℝ. -/
theorem continuumSpaceDist_eq_cast {d : Nat} (p q : Event d) :
    continuumSpaceDist d (lorentzIntEmbed p) (lorentzIntEmbed q)
    = ((spaceDist d p q : ℕ) : ℝ) :=
  le_antisymm (continuumSpaceDist_le_cast p q) (continuumSpaceDist_ge_cast p q)

/-- `CausalPrecedes d p q` holds if and only if `ContinuumCausalPrecedes` holds for the embedded
events. -/
theorem lorentzIntEmbed_preserves_causal_iff {d : Nat} (p q : Event d) :
    CausalPrecedes d p q
    ↔ ContinuumCausalPrecedes d (lorentzIntEmbed p) (lorentzIntEmbed q) := by
  unfold CausalPrecedes ContinuumCausalPrecedes
  rw [continuumSpaceDist_eq_cast]
  have h3 : (lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0
          = ((q 0 - p 0 : ℤ) : ℝ) := by
    unfold lorentzIntEmbed
    push_cast
    ring
  rw [h3]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- `Timelike d p q` holds if and only if `ContinuumTimelike` holds for the embedded events. -/
theorem lorentzIntEmbed_preserves_timelike_iff {d : Nat} (p q : Event d) :
    Timelike d p q
    ↔ ContinuumTimelike d (lorentzIntEmbed p) (lorentzIntEmbed q) := by
  unfold Timelike ContinuumTimelike
  rw [continuumSpaceDist_eq_cast]
  have h3 : (lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0
          = ((q 0 - p 0 : ℤ) : ℝ) := by
    unfold lorentzIntEmbed
    push_cast
    ring
  rw [h3]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-! ## Scaled embedding

Dividing each integer coordinate by `n` gives a lattice with spacing `1/n`. Every point of
`ℝ^{d+1}` is within `1/(2n)` of this lattice in each coordinate.
-/

/-- The embedding at scale `1/n`: each integer coordinate is cast to ℝ and divided by `n`. -/
noncomputable def scaledLorentzEmbed (n : Nat) {d : Nat} (p : Event d) :
    ContinuumEvent d :=
  fun k => (p k : ℝ) / n

@[simp] theorem scaledLorentzEmbed_apply (n : Nat) {d : Nat} (p : Event d)
    (k : Fin (d + 1)) :
    scaledLorentzEmbed n p k = (p k : ℝ) / n := rfl

/-- For `n > 0`, every real `x` is within `1/(2n)` of some `k/n` with `k : ℤ`. The witness is
`round (n · x)`. -/
theorem oneOverN_lattice_dense_R (n : Nat) (hn : 0 < n) (x : ℝ) :
    ∃ k : ℤ, |x - (k : ℝ) / n| ≤ 1 / (2 * n) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨round ((n : ℝ) * x), ?_⟩
  have habs : |(n : ℝ) * x - round ((n : ℝ) * x)| ≤ 1 / 2 := abs_sub_round _
  have heq : x - (round ((n : ℝ) * x) : ℝ) / n
           = ((n : ℝ) * x - round ((n : ℝ) * x)) / n := by
    field_simp
  rw [heq, abs_div, abs_of_pos hn_pos]
  -- Goal: |...| / n ≤ 1 / (2n).  Use 1/(2n) = (1/2)/n and divide by n.
  have hbound : (1 : ℝ) / (2 * n) = (1 / 2) / n := by
    field_simp
  rw [hbound, div_le_div_iff_of_pos_right hn_pos]
  exact habs

/-- For `n > 0`, every continuum event `x` is within `1/(2n)` of some `scaledLorentzEmbed n p` in
every coordinate. -/
theorem scaledLorentzEmbed_dense {n : Nat} (hn : 0 < n) {d : Nat}
    (x : ContinuumEvent d) :
    ∃ p : Event d,
      ∀ k : Fin (d + 1), |x k - (scaledLorentzEmbed n p) k| ≤ 1 / (2 * n) := by
  -- Pick the rounded integer for each coordinate.
  have choose : ∀ k : Fin (d + 1), ∃ i : ℤ,
      |x k - (i : ℝ) / n| ≤ 1 / (2 * n) :=
    fun k => oneOverN_lattice_dense_R n hn (x k)
  choose p hp using choose
  refine ⟨p, ?_⟩
  intro k
  simpa [scaledLorentzEmbed] using hp k

/-- For `n > 0`, dividing every coordinate of `f` and `g` by `n` divides their spatial distance by
`n`. -/
theorem continuumSpaceDist_scale_div {d : Nat} (n : Nat) (hn : 0 < n)
    (f g : ContinuumEvent d) :
    continuumSpaceDist d (fun k => f k / n) (fun k => g k / n)
    = continuumSpaceDist d f g / n := by
  unfold continuumSpaceDist
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  match d with
  | 0 => simp
  | k + 1 =>
    -- Per-coordinate: |f i.succ / n - g i.succ / n| = |f i.succ - g i.succ| / n.
    have hpc : ∀ i : Fin (k + 1),
        |(fun k => f k / n) i.succ - (fun k => g k / n) i.succ|
        = |f i.succ - g i.succ| / n := by
      intro i
      show |f i.succ / n - g i.succ / n| = |f i.succ - g i.succ| / n
      rw [show f i.succ / n - g i.succ / n = (f i.succ - g i.succ) / n from by ring]
      rw [abs_div, abs_of_pos hn_pos]
    show (Finset.univ : Finset (Fin (k + 1))).sup'
            ⟨0, Finset.mem_univ 0⟩
            (fun i => |(fun k => f k / n) i.succ - (fun k => g k / n) i.succ|)
        = (Finset.univ : Finset (Fin (k + 1))).sup'
            ⟨0, Finset.mem_univ 0⟩
            (fun i => |f i.succ - g i.succ|) / n
    rw [Finset.sup'_congr ⟨0, Finset.mem_univ 0⟩ rfl
          (g := fun i : Fin (k + 1) => |f i.succ - g i.succ| / n)
          (fun i _ => hpc i)]
    exact sup'_div_const_real ⟨0, Finset.mem_univ 0⟩
            (f := fun i : Fin (k + 1) => |f i.succ - g i.succ|) hn_pos

/-- The spatial distance under `scaledLorentzEmbed n` equals the spatial distance under
`lorentzIntEmbed` divided by `n`. -/
theorem scaledLorentzEmbed_spaceDist {n : Nat} (hn : 0 < n)
    {d : Nat} (p q : Event d) :
    continuumSpaceDist d
        (scaledLorentzEmbed n p) (scaledLorentzEmbed n q)
    = continuumSpaceDist d
        (lorentzIntEmbed p) (lorentzIntEmbed q) / n := by
  unfold scaledLorentzEmbed lorentzIntEmbed
  exact continuumSpaceDist_scale_div n hn _ _

/-- The spatial distance under `scaledLorentzEmbed n` equals the discrete spatial distance cast to ℝ
and divided by `n`. -/
theorem scaledLorentzEmbed_spaceDist_eq_cast {n : Nat} (hn : 0 < n)
    {d : Nat} (p q : Event d) :
    continuumSpaceDist d
        (scaledLorentzEmbed n p) (scaledLorentzEmbed n q)
    = ((spaceDist d p q : ℕ) : ℝ) / n := by
  rw [scaledLorentzEmbed_spaceDist hn, continuumSpaceDist_eq_cast]

/-- For `n > 0`, if `CausalPrecedes d p q`, then `ContinuumCausalPrecedes` holds for the scaled
embedded events. -/
theorem scaledLorentzEmbed_preserves_causal {n : Nat} (hn : 0 < n)
    {d : Nat} (p q : Event d)
    (h : CausalPrecedes d p q) :
    ContinuumCausalPrecedes d
      (scaledLorentzEmbed n p) (scaledLorentzEmbed n q) := by
  have hcont : ContinuumCausalPrecedes d
                  (lorentzIntEmbed p) (lorentzIntEmbed q) :=
    lorentzIntEmbed_preserves_causal p q h
  unfold ContinuumCausalPrecedes at *
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [scaledLorentzEmbed_spaceDist hn]
  have htime : (scaledLorentzEmbed n q) 0 - (scaledLorentzEmbed n p) 0
             = ((lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0) / n := by
    unfold scaledLorentzEmbed lorentzIntEmbed
    field_simp
  rw [htime]
  exact (div_le_div_iff_of_pos_right hn_pos).mpr hcont

/-- For `n > 0`, `CausalPrecedes d p q` holds if and only if `ContinuumCausalPrecedes` holds for the
scaled embedded events. -/
theorem scaledLorentzEmbed_preserves_causal_iff {n : Nat} (hn : 0 < n)
    {d : Nat} (p q : Event d) :
    CausalPrecedes d p q
    ↔ ContinuumCausalPrecedes d
        (scaledLorentzEmbed n p) (scaledLorentzEmbed n q) := by
  rw [lorentzIntEmbed_preserves_causal_iff p q]
  unfold ContinuumCausalPrecedes
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [scaledLorentzEmbed_spaceDist hn]
  have htime : (scaledLorentzEmbed n q) 0 - (scaledLorentzEmbed n p) 0
             = ((lorentzIntEmbed q) 0 - (lorentzIntEmbed p) 0) / n := by
    unfold scaledLorentzEmbed lorentzIntEmbed
    field_simp
  rw [htime, div_le_div_iff_of_pos_right hn_pos]

end Infra
end InfraFormalization
