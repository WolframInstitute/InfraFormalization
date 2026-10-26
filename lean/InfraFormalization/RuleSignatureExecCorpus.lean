/-
Engine versions of five catalogue rules.

This module defines `ExecRule` versions of five rules of
`CandidateRuleCatalog.lean`: the identity rule, edge doubling, edge append,
triple expansion and the rule of G3 line 6202. For each it builds
`canonicalDossier` runs of `singleWayStep` on fixed seeds and checks, by
`decide` or `native_decide`, whether the edge count stays constant. No
theorem relates these runs to the abstract `Trajectory` type.
-/

import InfraFormalization.RuleSignatureSchema

namespace InfraFormalization
namespace RuleSignatureExecCorpus

open MultiwayExec
open RuleSignatureSchema

/-! ## Identity rule: `{a, b} → {a, b}` -/

private def triv_lhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩
private def triv_rhs : Hyperedge (Fin 2) := ⟨[0, 1], by decide⟩

/-- The rule `{a, b} → {a, b}`. -/
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

/-- The rule `{a, b} → {a, b}, {a, b}`, with one left-hand and two
right-hand edges. -/
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

/-- The rule `{a, b} → {a, b}, {b, c}` with `c` fresh; the same rule as
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

/-- The rule `{a, b} → {a, b}, {b, c}, {c, d}` with `c`, `d` fresh. -/
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

/-! ## The rule of G3: `{x,y},{y,z},{z,w},{w,v} → {y,u},{u,v},{w,x},{x,u}` (u fresh)

Both sides have 4 edges, as in `gorardNamedRule_isConservative` of
`CandidateRuleCatalog`. -/

private def gor_lhs0 : Hyperedge (Fin 5) := ⟨[0, 1], by decide⟩
private def gor_lhs1 : Hyperedge (Fin 5) := ⟨[1, 2], by decide⟩
private def gor_lhs2 : Hyperedge (Fin 5) := ⟨[2, 3], by decide⟩
private def gor_lhs3 : Hyperedge (Fin 5) := ⟨[3, 4], by decide⟩

private def gor_rhs0 : Hyperedge (Fin 6) := ⟨[1, 5], by decide⟩
private def gor_rhs1 : Hyperedge (Fin 6) := ⟨[5, 4], by decide⟩
private def gor_rhs2 : Hyperedge (Fin 6) := ⟨[3, 0], by decide⟩
private def gor_rhs3 : Hyperedge (Fin 6) := ⟨[0, 5], by decide⟩

/-- The rule of G3 (`papers/gorard_2102.09363.txt` line 6202), the engine
version of `CandidateCatalog.gorardNamedRule`. -/
def gorardNamedExecRule : ExecRule where
  numBound := 5
  numFresh := 1
  lhs := [gor_lhs0, gor_lhs1, gor_lhs2, gor_lhs3]
  rhs := [gor_rhs0, gor_rhs1, gor_rhs2, gor_rhs3]

/-- The two sides of `gorardNamedExecRule` have equal length. -/
example : gorardNamedExecRule.lhs.length = gorardNamedExecRule.rhs.length := by decide

example : gorardNamedExecRule.lhs.length = 4 := by decide

example : gorardNamedExecRule.rhs.length = 4 := by decide

/-- The directed path `1→2→3→4→5`. The left-hand side matches it with
`(x, y, z, w, v) = (1, 2, 3, 4, 5)`. -/
def gorardPathSeed : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[3, 4], by decide⟩, ⟨[4, 5], by decide⟩]

def gorardPathDossier (n : Nat) : Dossier :=
  canonicalDossier gorardNamedExecRule gorardPathSeed n

example : (gorardPathDossier 1).isConsistent = true := canonicalDossier_isConsistent _ _ _

/-- On the path seed, the edge counts of the first two states are
`[4, 4]`, checked by `native_decide`. -/
example : (gorardPathDossier 1).edgeCountTrace = [4, 4] := by native_decide

example : (gorardPathDossier 1).edgeCountConstant = true := by native_decide

/-! ## Cycle seed

The 4-cycle `1→2→3→4→1` admits four matches of the left-hand side, one
starting at each vertex, and every two of them share an edge.
`singleWayStep` applies the first and skips the other three, so the edge
count stays 4. -/

def gorardCycleSeed : ExecHG ℕ :=
  [⟨[1, 2], by decide⟩, ⟨[2, 3], by decide⟩, ⟨[3, 4], by decide⟩, ⟨[4, 1], by decide⟩]

def gorardCycleDossier (n : Nat) : Dossier :=
  canonicalDossier gorardNamedExecRule gorardCycleSeed n

example : (gorardCycleDossier 1).isConsistent = true := canonicalDossier_isConsistent _ _ _

/-- The edge count of the 4-cycle seed stays 4 after one single-way step. -/
example : (gorardCycleDossier 1).edgeCountConstant = true := by native_decide

/-! ## Conjunction -/

/-- The edge count is constant on the runs of the identity rule (3 steps)
and of the rule of G3 on the path and cycle seeds (1 step), and is not
constant on the runs of the doubling, append and triple-expansion rules. -/
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
