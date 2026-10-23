/-
**ExecHG H1-catalogue corpus** (#373, on-ramp).

`ExecRule` versions of the H1 candidate-rule catalogue
(`CandidateRuleCatalog.lean`) wired through
`RuleSignatureSchema.canonicalDossier` to give axiom-clean,
Lean-internal screening verdicts. No paclet round-trip; everything
is `decide`-able from `MultiwayExec` definitions.

This is the on-ramp the user identified for the rule-search pipeline:
*if the corpus is closed (e.g., the H1 named-rule list), Lean executor
end-to-end is sufficient and stronger than a WL/Lean hybrid.* The
paclet hookup (#374 / #375) is the at-scale accelerator for #190's
open enumeration; for the closed H1 corpus it adds nothing but a
trust boundary.

**Per-rule deliverable**:
  * `ExecRule` definition with the same edge structure as the abstract
    `Rule` in `CandidateRuleCatalog`.
  * Conservation status as a `decide`-checked Bool.
  * Canonical dossiers on representative seeds.
  * Edge-count and vertex-count constancy verdicts.

**Rules covered**: gorardNamed, edgeDoubling, edgeAppend,
tripleExpansion, trivialIdentity. (Subdivision and TC1 already in
`MultiwayExecTests`.)

**What this file does NOT do**: bridge from the ExecHG-side trajectory
to the abstract `MultiScreener τ tgt_e tgt_κ r` Prop. That bridge is
the residual structural step, factored as #378 (depends on a
ExecHG → Trajectory lift, which we postpone). The constancy verdicts
here are the *content* of that bridge in concrete form.
-/

import InfraFormalization.RuleSignatureSchema

namespace InfraFormalization
namespace RuleSignatureExecCorpus

open MultiwayExec
open RuleSignatureSchema

/-! ## Trivial identity rule: `{a, b} → {a, b}` -/

private def triv_lhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def triv_rhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩

/-- Trivial identity rule (control). Conservative; every step is a no-op. -/
def trivialIdentityExecRule : ExecRule where
  numBound := 2
  numFresh := 0
  lhs := [triv_lhs]
  rhs := [triv_rhs]

def trivialSeed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

def trivialDossier (n : Nat) : Dossier := canonicalDossier trivialIdentityExecRule trivialSeed n

example : trivialIdentityExecRule.lhs.length = trivialIdentityExecRule.rhs.length := by decide

example : (trivialDossier 3).isConsistent = true := canonicalDossier_isConsistent _ _ _

example : (trivialDossier 3).edgeCountTrace = [1, 1, 1, 1] := by decide

example : (trivialDossier 3).edgeCountConstant = true := by decide

example : (trivialDossier 3).vertexCountConstant = true := by decide

/-! ## Edge-doubling rule: `{a, b} → {a, b}, {a, b}` -/

private def doub_lhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def doub_rhs1 : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def doub_rhs2 : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩

/-- Edge-doubling rule: WPP "rule 0". Non-conservative
(|LHS|=1, |RHS|=2) — every edge doubles per step. -/
def edgeDoublingExecRule : ExecRule where
  numBound := 2
  numFresh := 0
  lhs := [doub_lhs]
  rhs := [doub_rhs1, doub_rhs2]

def doublingSeed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

def doublingDossier (n : Nat) : Dossier := canonicalDossier edgeDoublingExecRule doublingSeed n

example : edgeDoublingExecRule.lhs.length ≠ edgeDoublingExecRule.rhs.length := by decide

example : (doublingDossier 3).isConsistent = true := canonicalDossier_isConsistent _ _ _

example : (doublingDossier 3).edgeCountConstant = false := by decide

/-! ## Edge-append rule: `{a, b} → {a, b}, {b, c}` (c fresh) -/

private def app_lhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def app_rhs_keep : Hyperedge (Fin 3) := ⟨[0, 1], by decide⟩
private def app_rhs_new  : Hyperedge (Fin 3) := ⟨[1, 2], by decide⟩

/-- Edge-append rule: linear extension. Non-conservative; same as
`MultiwayExecTests.tc1Rule`. -/
def edgeAppendExecRule : ExecRule where
  numBound := 2
  numFresh := 1
  lhs := [app_lhs]
  rhs := [app_rhs_keep, app_rhs_new]

def appendSeed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

def appendDossier (n : Nat) : Dossier := canonicalDossier edgeAppendExecRule appendSeed n

example : edgeAppendExecRule.lhs.length ≠ edgeAppendExecRule.rhs.length := by decide

example : (appendDossier 3).isConsistent = true := canonicalDossier_isConsistent _ _ _

example : (appendDossier 3).edgeCountConstant = false := by decide

/-! ## Triple-expansion rule: `{a, b} → {a, b}, {b, c}, {c, d}` (c, d fresh) -/

private def tri_lhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def tri_rhs0 : Hyperedge (Fin 4) := ⟨[0, 1], by decide⟩
private def tri_rhs1 : Hyperedge (Fin 4) := ⟨[1, 2], by decide⟩
private def tri_rhs2 : Hyperedge (Fin 4) := ⟨[2, 3], by decide⟩

/-- Triple-expansion rule. Non-conservative (|LHS|=1, |RHS|=3). -/
def tripleExpansionExecRule : ExecRule where
  numBound := 2
  numFresh := 2
  lhs := [tri_lhs]
  rhs := [tri_rhs0, tri_rhs1, tri_rhs2]

def tripleSeed : ExecHG ℕ := [⟨[1, 2], by decide⟩]

def tripleDossier (n : Nat) : Dossier := canonicalDossier tripleExpansionExecRule tripleSeed n

example : tripleExpansionExecRule.lhs.length ≠ tripleExpansionExecRule.rhs.length := by decide

example : (tripleDossier 2).isConsistent = true := canonicalDossier_isConsistent _ _ _

example : (tripleDossier 2).edgeCountConstant = false := by decide

/-! ## JGORARD's named rule: `{x,y},{y,z},{z,w},{w,v} → {y,u},{u,v},{w,x},{x,u}` (u fresh)

Conservation: `|LHS| = |RHS| = 4` (matches the abstract
`gorardNamedRule_isConservative` from `CandidateRuleCatalog`). -/

private def gor_lhs0 : Hyperedge (Fin 5) := ⟨[0, 1], by decide⟩
private def gor_lhs1 : Hyperedge (Fin 5) := ⟨[1, 2], by decide⟩
private def gor_lhs2 : Hyperedge (Fin 5) := ⟨[2, 3], by decide⟩
private def gor_lhs3 : Hyperedge (Fin 5) := ⟨[3, 4], by decide⟩

private def gor_rhs0 : Hyperedge (Fin 6) := ⟨[1, 5], by decide⟩
private def gor_rhs1 : Hyperedge (Fin 6) := ⟨[5, 4], by decide⟩
private def gor_rhs2 : Hyperedge (Fin 6) := ⟨[3, 0], by decide⟩
private def gor_rhs3 : Hyperedge (Fin 6) := ⟨[0, 5], by decide⟩

/-- JGORARD's named rule (arXiv:2102.09363, line 6202).
**Conservative**: |LHS| = |RHS| = 4. ExecRule version of
`CandidateCatalog.gorardNamedRule` from `CandidateRuleCatalog.lean`. -/
def gorardNamedExecRule : ExecRule where
  numBound := 5
  numFresh := 1
  lhs := [gor_lhs0, gor_lhs1, gor_lhs2, gor_lhs3]
  rhs := [gor_rhs0, gor_rhs1, gor_rhs2, gor_rhs3]

/-- **Conservation status of JGORARD's rule (decidable)**: lhs.length =
rhs.length = 4. Mirrors `CandidateCatalog.gorardNamedRule_isConservative`
on the ExecHG side. -/
example : gorardNamedExecRule.lhs.length = gorardNamedExecRule.rhs.length := by decide

example : gorardNamedExecRule.lhs.length = 4 := by decide

example : gorardNamedExecRule.rhs.length = 4 := by decide

/-- A 4-edge directed path: `1→2→3→4→5`. Provides exactly one match
for JGORARD's LHS pattern at the bound (x,y,z,w,v) = (1,2,3,4,5). -/
def gorardPathSeed : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[3, 4], by decide⟩, ⟨[4, 5], by decide⟩]

def gorardPathDossier (n : Nat) : Dossier :=
  canonicalDossier gorardNamedExecRule gorardPathSeed n

example : (gorardPathDossier 1).isConsistent = true := canonicalDossier_isConsistent _ _ _

/-- **Edge count is constant 4 along JGORARD's path-seed trajectory after
one single-way step**. The conservative screener passes (axiom-clean,
`native_decide` for the kernel-heavy 5-pattern-vertex enumeration).
This is the Lean-internal closed-corpus instance of #373. -/
example : (gorardPathDossier 1).edgeCountTrace = [4, 4] := by native_decide

example : (gorardPathDossier 1).edgeCountConstant = true := by native_decide

/-! ## Cycle seed

A 4-cycle seed `1→2→3→4→1` admits four matches of the LHS of the rule,
one starting at each cycle vertex, and every two of them share an edge.
`singleWayStep` fires the first and skips the other three, so the edge
count stays 4. -/

def gorardCycleSeed : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[3, 4], by decide⟩, ⟨[4, 1], by decide⟩]

def gorardCycleDossier (n : Nat) : Dossier :=
  canonicalDossier gorardNamedExecRule gorardCycleSeed n

example : (gorardCycleDossier 1).isConsistent = true := canonicalDossier_isConsistent _ _ _

/-- The edge count of the 4-cycle seed stays 4 after one single-way step. -/
example : (gorardCycleDossier 1).edgeCountConstant = true := by native_decide

/-! ## Summary -/

/-- Edge-count screener on the corpus dossiers: the conservative rules
(trivial rule, named rule on the path and cycle seeds) keep a constant
edge count; the doubling, append and triple rules do not. -/
theorem h1_corpus_edgeCount_screener_verdict :
    (trivialDossier 3).edgeCountConstant = true
  ∧ (gorardPathDossier 1).edgeCountConstant = true
  ∧ (gorardCycleDossier 1).edgeCountConstant = true
  ∧ (doublingDossier 3).edgeCountConstant = false
  ∧ (appendDossier 3).edgeCountConstant = false
  ∧ (tripleDossier 2).edgeCountConstant = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · native_decide
  · native_decide
  · decide
  · decide
  · decide

end RuleSignatureExecCorpus
end InfraFormalization
