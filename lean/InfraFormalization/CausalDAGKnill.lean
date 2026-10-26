/-
Scaled Knill Euler characteristic of seven small directed graphs written as `ExecHG ℕ`.

The module defines a path `causalChain n`, a fork, a join, a 4-cycle (`causalDiamond`), two
4-cycles sharing a vertex (`causalTripleDiamond`), the complete bipartite graph `K_{2,3}`
and a triangle. It computes `knillEulerScaled` of each: 6 for the path (n = 3, 5, 8, 16),
the fork, the join and the triangle, 0 for the 4-cycle, and -6 for the other two. Each
value equals 6 times the Euler characteristic of the clique complex of the underlying
undirected graph. The graphs are written by hand and are not produced by a rule evolution.
All values are checked by `native_decide`.
-/

import InfraFormalization.KnillRuleBridge

namespace InfraFormalization
namespace CausalDAGKnill

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet

/-! ## Graphs -/

/-- The path `0 → 1 → 2 → … → (n − 1)` with `n − 1` edges. -/
def causalChain (n : ℕ) : ExecHG ℕ :=
  (List.range (n - 1)).map (fun i => ⟨[i, i + 1], List.cons_ne_nil _ _⟩)

/-- The edges `0 → 1` and `0 → 2`. -/
def causalFork : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[0, 2], List.cons_ne_nil _ _⟩]

/-- The edges `0 → 2` and `1 → 2`. -/
def causalJoin : ExecHG ℕ :=
  [⟨[0, 2], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩]

/-- The edges `0 → 1`, `0 → 2`, `1 → 3`, `2 → 3`; the underlying graph is the 4-cycle
`0-1-3-2-0`. -/
def causalDiamond : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[0, 2], List.cons_ne_nil _ _⟩,
   ⟨[1, 3], List.cons_ne_nil _ _⟩,
   ⟨[2, 3], List.cons_ne_nil _ _⟩]

/-- Two copies of `causalDiamond` sharing vertex `3`: 7 vertices and 8 edges. -/
def causalTripleDiamond : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[0, 2], List.cons_ne_nil _ _⟩,
   ⟨[1, 3], List.cons_ne_nil _ _⟩,
   ⟨[2, 3], List.cons_ne_nil _ _⟩,
   ⟨[3, 4], List.cons_ne_nil _ _⟩,
   ⟨[3, 5], List.cons_ne_nil _ _⟩,
   ⟨[4, 6], List.cons_ne_nil _ _⟩,
   ⟨[5, 6], List.cons_ne_nil _ _⟩]

/-- The complete bipartite graph `K_{2,3}` with edges from `{0, 1}` to `{2, 3, 4}`;
`χ = 5 − 6 = -1`. -/
def causalBipartite23 : ExecHG ℕ :=
  [⟨[0, 2], List.cons_ne_nil _ _⟩, ⟨[0, 3], List.cons_ne_nil _ _⟩,
   ⟨[0, 4], List.cons_ne_nil _ _⟩, ⟨[1, 2], List.cons_ne_nil _ _⟩,
   ⟨[1, 3], List.cons_ne_nil _ _⟩, ⟨[1, 4], List.cons_ne_nil _ _⟩]

/-- The edges `0 → 1`, `1 → 2`, `0 → 2`. Its clique complex is a filled triangle, `χ = 1`. -/
def causalTriangle : ExecHG ℕ :=
  [⟨[0, 1], List.cons_ne_nil _ _⟩,
   ⟨[1, 2], List.cons_ne_nil _ _⟩,
   ⟨[0, 2], List.cons_ne_nil _ _⟩]

/-! ## Values of `knillEulerScaled`

Each value is checked by `native_decide`. -/

theorem causalChain_3_knill : knillEulerScaled (causalChain 3) = 6 := by native_decide
theorem causalChain_5_knill : knillEulerScaled (causalChain 5) = 6 := by native_decide
theorem causalChain_8_knill : knillEulerScaled (causalChain 8) = 6 := by native_decide
theorem causalChain_16_knill : knillEulerScaled (causalChain 16) = 6 := by native_decide

theorem causalFork_knill : knillEulerScaled causalFork = 6 := by native_decide
theorem causalJoin_knill : knillEulerScaled causalJoin = 6 := by native_decide

theorem causalDiamond_knill : knillEulerScaled causalDiamond = 0 := by native_decide

theorem causalTripleDiamond_knill :
    knillEulerScaled causalTripleDiamond = -6 := by native_decide

theorem causalBipartite23_knill :
    knillEulerScaled causalBipartite23 = -6 := by native_decide

theorem causalTriangle_knill : knillEulerScaled causalTriangle = 6 := by native_decide

/-- The conjunction of seven of the values above: 6 for `causalChain 8`, the fork, the join
and the triangle, 0 for the diamond, and -6 for the triple diamond and `K_{2,3}`. -/
theorem causal_dag_knill_classification :
    -- χ = 1
    knillEulerScaled (causalChain 8) = 6 ∧
    knillEulerScaled causalFork = 6 ∧
    knillEulerScaled causalJoin = 6 ∧
    knillEulerScaled causalTriangle = 6 ∧
    -- χ = 0
    knillEulerScaled causalDiamond = 0 ∧
    -- χ = -1
    knillEulerScaled causalTripleDiamond = -6 ∧
    knillEulerScaled causalBipartite23 = -6 :=
  ⟨causalChain_8_knill, causalFork_knill, causalJoin_knill, causalTriangle_knill,
   causalDiamond_knill, causalTripleDiamond_knill, causalBipartite23_knill⟩

end CausalDAGKnill
end InfraFormalization
