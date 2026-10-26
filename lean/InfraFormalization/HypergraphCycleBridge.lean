/-
The cycle hypergraph and its Laplacian.

This module defines `cycleHypergraph n : Hypergraph (Fin n)` with the `n` edges `[j, j+1]`, and proves `laplacianHyper (cycleHypergraph n) f v = cycleLaplacian n f v` for `n ≥ 2`, where `cycleLaplacian` is defined in `CycleGraph.lean`. Combined with `LaplacianBridge.lean`, it proves that for a quadratic `f(y) = a y² + b y + c` and an interior index `i`, `n² · laplacianHyper (cycleHypergraph n) (f(j/n)) i = f''(i/n)` exactly. The statement covers quadratic polynomials only.
-/

import InfraFormalization.HypergraphLaplacian
import InfraFormalization.CycleGraph
import InfraFormalization.LaplacianBridge
import Mathlib.Data.List.Basic

namespace InfraFormalization

variable {n : Nat}

/-! ## The cycle hypergraph as a concrete `Hypergraph (Fin n)` -/

/-- The hyperedge `[j, j+1]`, with addition in `Fin n`. -/
def cycleHyperedge (n : Nat) [NeZero n] (j : Fin n) : Hyperedge (Fin n) :=
  { verts := [j, j + 1]
    nonempty := by simp }

/-- The hypergraph on `Fin n` whose edges are `cycleHyperedge n j` for each `j : Fin n`. -/
noncomputable def cycleHypergraph (n : Nat) [NeZero n] :
    Hypergraph (Fin n) :=
  { edges := (Finset.univ : Finset (Fin n)).val.map (cycleHyperedge n) }

/-- The vertex finset of `cycleHyperedge n j` is `{j, j+1}`. -/
theorem cycleHyperedge_toFinset {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (j : Fin n) :
    (cycleHyperedge n j).verts.toFinset = {j, j + 1} := by
  unfold cycleHyperedge
  simp [List.toFinset_cons, List.toFinset_nil]

/-- For `n ≥ 2`, the successor `j + 1` differs from `j` in `Fin n`. -/
theorem cycle_succ_ne {n : Nat} [NeZero n] (hn : 2 ≤ n) (j : Fin n) :
    j + 1 ≠ j := by
  intro heq
  have h1 : (j + 1 : Fin n).val = (j.val + (1 : Fin n).val) % n := Fin.val_add j 1
  have h2 : (1 : Fin n).val = 1 % n := rfl
  have h3 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h4 : (j + 1 : Fin n).val = j.val := congrArg Fin.val heq
  have hjlt : j.val < n := j.isLt
  rw [h2, h3] at h1
  -- Now h1 : (j+1).val = (j.val + 1) % n and h4 : (j+1).val = j.val
  rw [h4] at h1
  -- h1 : j.val = (j.val + 1) % n — impossible since j.val + 1 ≤ n
  by_cases hjv : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hjv] at h1
    omega
  · push_neg at hjv
    have : j.val + 1 = n := by omega
    rw [this, Nat.mod_self] at h1
    -- h1 : j.val = 0 and j.val + 1 = n ≥ 2 are inconsistent.
    omega

/-! ## `laplacianHyper (cycleHypergraph n) = cycleLaplacian n` -/

/-- For `n ≥ 2`, the contribution of `cycleHyperedge n j` to the Laplacian at `v` is `f(j+1) − f v` if `v = j`, `f j − f v` if `v = j+1`, and `0` otherwise. -/
theorem cycleHyperedge_perEdge_contribution {n : Nat} [NeZero n]
    (hn : 2 ≤ n) (f : Fin n → ℝ) (j v : Fin n) :
    (∑ w ∈ (cycleHyperedge n j).others v, (f w - f v))
    = (if v = j then f (j + 1) - f v else 0)
      + (if v = j + 1 then f j - f v else 0) := by
  unfold Hyperedge.others
  rw [cycleHyperedge_toFinset hn]
  -- {j, j+1}.toFinset as a Finset: {j, j+1}. The erase of v:
  --   - if v = j and v = j+1: impossible (n ≥ 2).
  --   - if v = j: {j, j+1}.erase j = {j+1}, sum = f(j+1) - f v.
  --   - if v = j+1: {j, j+1}.erase (j+1) = {j}, sum = f j - f v.
  --   - if v ∉ {j, j+1}: if-then-else gives ∅, sum = 0.
  have hsuccne : j + 1 ≠ j := cycle_succ_ne hn j
  by_cases hv : v ∈ ({j, j + 1} : Finset (Fin n))
  · rw [if_pos hv]
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    cases hv with
    | inl hv_eq_j =>
      -- v = j; erase j from {j, j+1} gives {j+1}.
      subst hv_eq_j
      have hne1 : v + 1 ≠ v := cycle_succ_ne hn v
      have hv_notin : v ∉ ({v + 1} : Finset (Fin n)) := by
        rw [Finset.mem_singleton]
        exact hne1.symm
      have h1 : ({v, v + 1} : Finset (Fin n)).erase v = {v + 1} := by
        rw [show ({v, v + 1} : Finset (Fin n)) = insert v {v + 1} from rfl]
        rw [Finset.erase_insert hv_notin]
      rw [h1]
      simp only [Finset.sum_singleton]
      have hne_sym : v ≠ v + 1 := hne1.symm
      rw [if_neg hne_sym]
      simp
    | inr hv_eq_succ_j =>
      -- v = j+1; erase (j+1) from {j, j+1} gives {j}.
      subst hv_eq_succ_j
      have hjne : j ≠ j + 1 := (cycle_succ_ne hn j).symm
      have hj_succ_ne : j + 1 ≠ j := cycle_succ_ne hn j
      have h_erase_sing : ({j + 1} : Finset (Fin n)).erase (j + 1) = ∅ :=
        Finset.erase_singleton (j + 1)
      have h2 : ({j, j + 1} : Finset (Fin n)).erase (j + 1) = {j} := by
        rw [show ({j, j + 1} : Finset (Fin n)) = insert j {j + 1} from rfl]
        rw [Finset.erase_insert_of_ne hjne, h_erase_sing]
        rfl
      rw [h2]
      simp only [Finset.sum_singleton]
      rw [if_neg hj_succ_ne]
      simp
  · rw [if_neg hv]
    simp only [Finset.sum_empty]
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    push_neg at hv
    obtain ⟨hvne_j, hvne_succ⟩ := hv
    simp [hvne_j, hvne_succ]

/-- For `n ≥ 2`, `laplacianHyper (cycleHypergraph n) f v = cycleLaplacian n f v`. -/
theorem laplacianHyper_cycleHypergraph {n : Nat} [NeZero n] (hn : 2 ≤ n)
    (f : Fin n → ℝ) (v : Fin n) :
    Hypergraph.laplacianHyper (cycleHypergraph n) f v = cycleLaplacian n f v := by
  unfold Hypergraph.laplacianHyper cycleHypergraph
  -- Rewrite the sum over the edge multiset as a sum over Fin n.
  rw [show ((Finset.univ : Finset (Fin n)).val.map (cycleHyperedge n)).map
        (fun e => ∑ w ∈ e.others v, (f w - f v))
        = (Finset.univ : Finset (Fin n)).val.map
            (fun j => ∑ w ∈ (cycleHyperedge n j).others v, (f w - f v))
      from by rw [Multiset.map_map]; rfl]
  rw [show (((Finset.univ : Finset (Fin n)).val.map
          (fun j => ∑ w ∈ (cycleHyperedge n j).others v, (f w - f v))).sum)
        = ∑ j : Fin n, (∑ w ∈ (cycleHyperedge n j).others v, (f w - f v))
        from rfl]
  -- Now apply per-edge contribution formula to each j.
  rw [Finset.sum_congr rfl
    (fun j _ => cycleHyperedge_perEdge_contribution hn f j v)]
  -- The sum splits: ∑_j (indicator j=v · ...) + ∑_j (indicator j=v-1 · ...).
  rw [Finset.sum_add_distrib]
  -- Collapse ∑_j (if v = j then (f(j+1) - f v) else 0) to j = v.
  have hfirst : (∑ j : Fin n, (if v = j then f (j + 1) - f v else 0))
              = f (v + 1) - f v := by
    rw [Finset.sum_eq_single v]
    · simp
    · intros j _ hjv
      rw [if_neg (Ne.symm hjv)]
    · intros h; exact absurd (Finset.mem_univ _) h
  -- Collapse ∑_j (if v = j + 1 then (f j - f v) else 0) to j = v - 1.
  have hsecond : (∑ j : Fin n, (if v = j + 1 then f j - f v else 0))
               = f (v - 1) - f v := by
    rw [Finset.sum_eq_single (v - 1)]
    · have hv_eq : v = (v - 1) + 1 := by abel
      rw [if_pos hv_eq]
    · intros j _ hj_ne
      have : v ≠ j + 1 := by
        intro heq
        apply hj_ne
        have : v - 1 = (j + 1) - 1 := by rw [heq]
        simp at this
        exact this.symm
      rw [if_neg this]
    · intros h; exact absurd (Finset.mem_univ _) h
  rw [hfirst, hsecond]
  unfold cycleLaplacian
  ring

/-! ## Quadratic test functions

For `f(y) = a y² + b y + c`, `fn j = f (j.val / n)` and an index `i` with `1 ≤ i.val` and `i.val + 1 < n`, the identity `n² · laplacianHyper (cycleHypergraph n) fn i = deriv (deriv f) (i.val / n)` holds exactly. -/

theorem hypergraph_scaled_laplacian_eq_second_deriv
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (a b c : ℝ) (i : Fin n) (hlo : 1 ≤ i.val) (hhi : i.val + 1 < n) :
    (n : ℝ)^2 * Hypergraph.laplacianHyper (cycleHypergraph n)
        (fun j : Fin n => a * ((j.val : ℝ) / n)^2 + b * ((j.val : ℝ) / n) + c)
        i
    = deriv (deriv (fun y : ℝ => a * y^2 + b * y + c)) ((i.val : ℝ) / n) := by
  -- Step 1: hypergraph laplacian = cycle laplacian.
  rw [laplacianHyper_cycleHypergraph hn]
  -- Step 2: cycle laplacian = secondDifference at interior index.
  rw [cycleLaplacian_in_terms_of_secondDifference n
        (fun y : ℝ => a * y^2 + b * y + c) i hlo hhi]
  -- Step 3: n² · secondDifference = scaledSecondDiff (by definition).
  show (n : ℝ)^2 * secondDifference (fun y => a * y^2 + b * y + c)
                     ((i.val : ℝ) / n) (1 / n)
     = deriv (deriv (fun y => a * y^2 + b * y + c)) ((i.val : ℝ) / n)
  have h_rewrite : (n : ℝ)^2 * secondDifference
                     (fun y => a * y^2 + b * y + c) ((i.val : ℝ) / n) (1 / n)
                 = scaledSecondDiff (fun y => a * y^2 + b * y + c) n
                     ((i.val : ℝ) / n) := by
    unfold scaledSecondDiff; rfl
  rw [h_rewrite]
  -- Step 4: scaledSecondDiff on quadratic = f'' (exactly).
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  exact polynomial_scaled_laplacian_eq_second_deriv a b c n hn_pos ((i.val : ℝ) / n)

/-- `(cycleHypergraph n).size = n`. -/
theorem cycleHypergraph_size (n : Nat) [NeZero n] :
    (cycleHypergraph n).size = n := by
  unfold cycleHypergraph Hypergraph.size
  simp

end InfraFormalization
