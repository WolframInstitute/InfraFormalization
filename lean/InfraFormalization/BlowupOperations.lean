/-
Cycle doubling.

This module defines the index map `Fin n → Fin (2n)`, `i ↦ 2i`, proves it
injective for `n > 0`, and defines the scale factor `1/2^k` with its
positivity and halving identity.
-/

import InfraFormalization.HypergraphCycleBridge
import InfraFormalization.DagBlowup

namespace InfraFormalization

/-! ## Cycle-doubling blowup -/

/-- The map `Fin n → Fin (2n)` sending `i` to `2i`. -/
def cycleDoubleIndex (n : Nat) (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val, by
    have := i.isLt
    omega⟩

/-- For `n > 0`, `cycleDoubleIndex n` is injective. -/
theorem cycleDoubleIndex_injective {n : Nat} (hn : 0 < n) :
    Function.Injective (cycleDoubleIndex n) := by
  intros i j hij
  unfold cycleDoubleIndex at hij
  have hval := congrArg Fin.val hij
  simp at hval
  ext
  omega

/-- The real number `1/2^k`. -/
noncomputable def blowupScale (k : Nat) : ℝ := (1 : ℝ) / (2 ^ k)

theorem blowupScale_pos (k : Nat) : 0 < blowupScale k := by
  unfold blowupScale
  positivity

theorem blowupScale_halves (k : Nat) : blowupScale (k + 1) = blowupScale k / 2 := by
  unfold blowupScale
  rw [pow_succ]
  ring

end InfraFormalization
