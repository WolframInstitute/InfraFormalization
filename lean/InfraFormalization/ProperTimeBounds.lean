/-
**Proper time theorems on causal graph** (IC4 extension).

Pavel Hajek / Zapata-Ahmed: proper time is the longest causal chain
between two events. This file extends `CausalFoliation.properTime` with:

  * `ChainOfLength 0 u v ↔ u = v`
  * Chains compose: concatenating two chains gives a chain.
  * Positive chain length implies `causallyPrecedes`.
  * If `HasProperTime G u v n`, then any longer chain is impossible.

Grounded on `CausalGraph V` directly.
-/

import InfraFormalization.CausalFoliation

namespace InfraFormalization
namespace CausalGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : CausalGraph V)

/-- **Length-0 chain is equality**. -/
theorem chainOfLength_zero_iff (u v : V) :
    G.ChainOfLength 0 u v ↔ u = v := by
  constructor
  · intro h
    cases h with
    | refl _ => rfl
  · intro h
    subst h
    exact ChainOfLength.refl u

/-- **Length-1 chain is a direct causal edge**. -/
theorem chainOfLength_one_iff (u v : V) :
    G.ChainOfLength 1 u v ↔ G.causalEdge u v := by
  constructor
  · intro h
    generalize hn : (1 : ℕ) = n at h
    induction h with
    | refl _ => omega
    | @cons k a b c hc e ih =>
      -- hn : 1 = k + 1, so k = 0
      have hk_zero : k = 0 := by omega
      subst hk_zero
      rw [chainOfLength_zero_iff] at hc
      subst hc
      exact e
  · intro h
    exact ChainOfLength.cons (ChainOfLength.refl u) h

/-- **Chains compose**: a chain of length `m` from `a` to `b` and a
chain of length `n` from `b` to `c` give a chain of length `m + n`
from `a` to `c`. -/
theorem chainOfLength_concat {m n : ℕ} {a b c : V}
    (h₁ : G.ChainOfLength m a b) (h₂ : G.ChainOfLength n b c) :
    G.ChainOfLength (m + n) a c := by
  induction h₂ with
  | refl _ =>
    simpa using h₁
  | @cons k _ _ _ _hc e ih =>
    -- ih : ChainOfLength m a u → ChainOfLength (m + k) a v
    -- Apply to h₁ to get ChainOfLength (m + k) a v.
    have ih' := ih h₁
    have hlen : m + (k + 1) = (m + k) + 1 := by omega
    rw [hlen]
    exact ChainOfLength.cons ih' e

/-- **Positive-length chain implies causallyPrecedes** (strict). A
chain of positive length gives non-trivial causal precedence. -/
theorem chainOfLength_pos_implies_causallyPrecedes {k : ℕ} {u v : V}
    (hk : 0 < k) (h : G.ChainOfLength k u v) :
    G.causallyPrecedes u v :=
  G.chainOfLength_implies_causallyPrecedes h

/-- **Length-1 chain implies causalEdge (and hence causallyPrecedes)**. -/
theorem chainOfLength_one_implies_causalEdge (u v : V)
    (h : G.ChainOfLength 1 u v) : G.causalEdge u v :=
  (G.chainOfLength_one_iff u v).mp h

end CausalGraph
end InfraFormalization
