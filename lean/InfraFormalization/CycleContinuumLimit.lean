/-
Forman scalar of the cycle hypergraph.

The module defines the `n`-cycle `cycleHG n` as an `ExecHG ℕ` and the sequence
`cycleFormanLimitTrace n = execFormanScalar (cycleHG (n + 4))`. It proves
`execFormanScalar (cycleHG n) = 0` for `n ∈ {4, 5, 6, 7, 8, 12, 16, 24, 32}`, each checked by
`native_decide`, and restates these values as values of `cycleFormanLimitTrace`. The general case
`n ≥ 4` is not formalized.
-/

import InfraFormalization.DiscreteRicciConvergence
import Mathlib.Topology.Order

namespace InfraFormalization
namespace CycleContinuumLimit

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecMetrics
open DiscreteRicciConvergence

/-! ## Cycle hypergraph construction -/

/-- The `n`-cycle as an `ExecHG ℕ`: edges `{i, (i+1) mod n}` for
`i ∈ {0, …, n-1}`. -/
def cycleHG (n : ℕ) : ExecHG ℕ :=
  (List.range n).map (fun i =>
    ⟨[i, (i + 1) % n], List.cons_ne_nil _ _⟩)

/-! ## Forman scalar of small cycles

In a cycle with at least 4 vertices every vertex has degree 2 and no edge lies on a triangle, so
the triangle-corrected Forman value of each edge is `4 − 2 − 2 + 0 = 0`. The values below are
checked by `native_decide`. -/

theorem cycleHG_4_forman_zero : execFormanScalar (cycleHG 4) = 0 := by native_decide
theorem cycleHG_5_forman_zero : execFormanScalar (cycleHG 5) = 0 := by native_decide
theorem cycleHG_6_forman_zero : execFormanScalar (cycleHG 6) = 0 := by native_decide
theorem cycleHG_7_forman_zero : execFormanScalar (cycleHG 7) = 0 := by native_decide
theorem cycleHG_8_forman_zero : execFormanScalar (cycleHG 8) = 0 := by native_decide
theorem cycleHG_12_forman_zero : execFormanScalar (cycleHG 12) = 0 := by native_decide
theorem cycleHG_16_forman_zero : execFormanScalar (cycleHG 16) = 0 := by native_decide
theorem cycleHG_24_forman_zero : execFormanScalar (cycleHG 24) = 0 := by native_decide
theorem cycleHG_32_forman_zero : execFormanScalar (cycleHG 32) = 0 := by native_decide

/-! ## Cycle sequence -/

/-- The infinite sequence `n ↦ cycleHG (n + 4)`. -/
def cycleSeq (n : ℕ) : ExecHG ℕ := cycleHG (n + 4)

/-- The Forman scalar of `cycleSeq n`, as a function `ℕ → ℤ`. Its value is 0 at the nine
indices checked below. -/
def cycleFormanLimitTrace : ℕ → ℤ := fun n => execFormanScalar (cycleSeq n)

/-! ## Values of the cycle sequence

`cycleFormanLimitTrace n = 0` for `n ∈ {0, 1, 2, 3, 4, 8, 12, 20, 28}`. -/

theorem cycleFormanLimitTrace_eq_zero_at_0 :
    cycleFormanLimitTrace 0 = 0 := cycleHG_4_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_1 :
    cycleFormanLimitTrace 1 = 0 := cycleHG_5_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_2 :
    cycleFormanLimitTrace 2 = 0 := cycleHG_6_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_3 :
    cycleFormanLimitTrace 3 = 0 := cycleHG_7_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_4 :
    cycleFormanLimitTrace 4 = 0 := cycleHG_8_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_8 :
    cycleFormanLimitTrace 8 = 0 := cycleHG_12_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_12 :
    cycleFormanLimitTrace 12 = 0 := cycleHG_16_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_20 :
    cycleFormanLimitTrace 20 = 0 := cycleHG_24_forman_zero
theorem cycleFormanLimitTrace_eq_zero_at_28 :
    cycleFormanLimitTrace 28 = 0 := cycleHG_32_forman_zero

end CycleContinuumLimit
end InfraFormalization
