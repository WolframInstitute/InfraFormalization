/-
**B4-corpus-balance-spectrum: balance α* spectrum across the
multi-rule corpus** (#470; corpus-aggregated Planck-constant
characterization).

The balance α* (#465) is the value at which the unified EH action
`S = R + α·B` vanishes. Different multi-rule combos give different
α* values — this module **collects the α* spectrum** across the
combo corpus, characterizing the framework's discrete-Planck-
constant spread.

**Balance α* spectrum** (all rationally certified via integer
arithmetic):

  | Combo                       | R(d=3) | B(d=3) | α* = -R/B |
  |-----------------------------|--------|--------|-----------|
  | edgeReversal + identityKeep |  -24   |   30   |   4/5     |
  | edgeReversal + forkRule_2   |  -42   |   66   |   7/11    |
  | edgeReversal + tripleMerger |  -36   |   78   |   6/13    |
  | edgeReversal + doubleCycle  |  -24   |   ?    |     ?     |

**Why these are rational**: by integer arithmetic, certifying
`b·R + a·B = 0` proves `α* = a/b` exactly. No floating-point.

**Spectrum observation**: the α* values span:

  * `eR + tripleMerger`: ≈ 0.46 (lowest — most "quantum-leaning").
  * `eR + id`: ≈ 0.80 (balanced).
  * `eR + fork`: ≈ 0.636 (intermediate).

These rational values are the framework's discrete-physics
candidates for the "natural" quantum-gravity coupling.

**Implication for H9**: in the continuum limit, if α* values
converge (or have a well-defined accumulation point), that point
is the framework's prediction for the natural QG coupling. This
is a precise H9 sub-question.

**Strongest research angle**: among the discovered combos,
`eR + tripleMerger` gives the lowest α* (≈ 0.46) — i.e., classical
contribution dominates earliest in α. This makes it the most
"GR-like" combo and a natural BBH-modeling candidate.
-/

import InfraFormalization.UnifiedEHBalance

namespace InfraFormalization
namespace CorpusBalanceSpectrum

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open BranchialEventTrace
open DiscoveredRules
open DiscoveredRulesExpanded
open MultiRuleDiscovered
open BBHInitialData
open DiscreteRicciScalar
open BranchialUniversalAdditivity

/-! ## R and B values for the corpus at depth 3 -/

theorem R_eR_tripleMerger_3 : discreteRicciScalar edgeReversal_tripleMerger_Sys 3 = -36 := by
  native_decide

theorem B_eR_tripleMerger_3 : discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 78 := by
  native_decide

/-! ## Balance α* for eR + tripleMerger -/

/-- **`balance_eR_tripleMerger`**: at depth 3 on edge12, the balance
α* for `eR + tripleMerger` is `36/78 = 6/13` (rational form).
Certified via `13·R + 6·B = 0`. -/
theorem balance_eR_tripleMerger :
    13 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      6 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 0 := by
  native_decide

/-! ## The α* spectrum theorem -/

/-- **`corpus_balance_spectrum`**: balance α* values across the
multi-rule corpus at depth 3, certified rationally.

  * eR + id: α* = 4/5 (via 5R + 4B = 0).
  * eR + fork: α* = 7/11 (via 11R + 7B = 0).
  * eR + tripleMerger: α* = 6/13 (via 13R + 6B = 0). -/
theorem corpus_balance_spectrum :
    -- eR + id: α* = 4/5
    5 * discreteRicciScalar edgeReversal_identity_Sys 3 +
      4 * discreteBranchialDensity edgeReversal_identity_Sys 3 = 0 ∧
    -- eR + fork: α* = 7/11
    11 * discreteRicciScalar edgeReversal_fork_Sys 3 +
      7 * discreteBranchialDensity edgeReversal_fork_Sys 3 = 0 ∧
    -- eR + tripleMerger: α* = 6/13
    13 * discreteRicciScalar edgeReversal_tripleMerger_Sys 3 +
      6 * discreteBranchialDensity edgeReversal_tripleMerger_Sys 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## The "most GR-like" combo -/

/-- **`most_GR_like_combo`**: among the 3 multi-rule combos, the
balance α* for `eR + tripleMerger` is the smallest (6/13 ≈ 0.46),
making it the combo where classical-GR contribution dominates
earliest. This is the framework's strongest candidate for "most
GR-like" multi-rule dynamics.

(Certified via cross-multiplication: 6/13 < 4/5 iff 30 < 52,
and 6/13 < 7/11 iff 66 < 91, both true.) -/
theorem most_GR_like_combo :
    -- 6/13 < 4/5: cross-multiplication 6 * 5 < 13 * 4
    6 * 5 < 13 * 4 ∧
    -- 6/13 < 7/11: cross-multiplication 6 * 11 < 13 * 7
    6 * 11 < 13 * 7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## What this delivers

**First corpus-aggregated balance α* spectrum**:

  * `corpus_balance_spectrum` — 3 certified rational α* values.
  * `balance_eR_tripleMerger` — new 6/13 balance for tripleMerger
    combo.
  * `most_GR_like_combo` — eR + tripleMerger has the smallest
    α*, making it the most GR-like.

**Why this matters**:

The framework now has a **rational spectrum** of discrete-QG
coupling candidates. Each multi-rule combo gives a specific α*
value — these are the framework's discrete-physics predictions for
the natural Planck-constant scale.

**Implication for H9 / BBH endgame**:

If α* values converge (or accumulate) in the continuum limit, that
gives the framework's prediction for the natural QG coupling. The
3 verified values (4/5, 7/11, 6/13) provide concrete data points
for analysis.

**For BBH modeling**: the smallest α* (6/13 for eR + tripleMerger)
indicates the combo where classical contribution dominates — the
**most GR-like** combo, a natural candidate for modeling binary
systems where classical GR is the dominant description.

This module concludes the dual-side framework's structural
characterization: the discrete-Planck-constant analog is now
explicitly indexed by rule + depth, with concrete corpus values.
-/

end CorpusBalanceSpectrum
end InfraFormalization
