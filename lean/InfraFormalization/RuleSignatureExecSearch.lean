/-
Enumeration and curvature classification of small rules.

The module enumerates the rules with left-hand side `{0,1}` whose right-hand side is a nonempty
set of at most `maxRHS` ordered pairs over `Fin 3`. Each rule is run with `canonicalDossier`, which
applies `singleWayStep`, and the Forman-scalar trace is classified as flat, positive, negative or
zero. The module counts the rules in each class on one seed and on the seed set
`[edge12, path123, cycle4]`, and defines a finite rate bound `|trace[i] − tgt| · (i + 1) ≤ c` on
traces. All counts are checked by `native_decide`.
-/

import InfraFormalization.RuleSignatureExecMetrics

namespace InfraFormalization
namespace RuleSignatureExecSearch

open MultiwayExec
open RuleSignatureSchema
open RuleSignatureExecCorpus
open RuleSignatureExecMetrics

/-! ## Classification of a Forman trace -/

/-- The class of a Forman-scalar trace: `flat` if the trace is constant, otherwise the sign of
its last entry. -/
inductive CurvatureTrend
  | flat | positive | negative | zero
deriving DecidableEq, Repr

/-- Classifies a Forman-scalar trace: `flat` if constant or empty, otherwise the sign of the last
entry. -/
def classifyForman (trace : List ℤ) : CurvatureTrend :=
  if allEqHead trace then CurvatureTrend.flat
  else match trace.getLast? with
    | some x => if x > 0 then CurvatureTrend.positive
                else if x < 0 then CurvatureTrend.negative
                else CurvatureTrend.zero
    | none => CurvatureTrend.flat

/-- The class of the Forman-scalar trace of `canonicalDossier r seed n`. -/
def trendOf (r : ExecRule) (seed : ExecHG ℕ) (n : Nat) : CurvatureTrend :=
  classifyForman ((canonicalDossier r seed n).formanScalarTrace)

/-! ## Rule enumeration -/

/-- A 2-vertex hyperedge `[i, j]` over `Fin p`. -/
def mkEdgeFin {p : Nat} (i j : Fin p) : Hyperedge (Fin p) :=
  ⟨[i, j], List.cons_ne_nil i [j]⟩

/-- All ordered pairs `[i, j]` with `i ≠ j` over `Fin p`. -/
def allOrderedPairsFin (p : Nat) : List (Hyperedge (Fin p)) :=
  (List.finRange p).flatMap (fun i =>
    (List.finRange p).filterMap (fun j =>
      if i = j then none else some (mkEdgeFin i j)))

/-- The rules with left-hand side `{0,1}`, two bound vertices and one fresh vertex, whose
right-hand side is a nonempty sublist of length at most `maxRHS` of the ordered pairs over
`Fin 3`. -/
def enumerateRules2_1 (maxRHS : Nat) : List ExecRule :=
  let edges := allOrderedPairsFin 3
  let lhsE : ExecHG (Fin 2) := [mkEdgeFin 0 1]
  (edges.sublists.filter (fun s => !s.isEmpty && decide (s.length ≤ maxRHS))).map
    (fun s => { numBound := 2, numFresh := 1, lhs := lhsE, rhs := s })

/-! ## Size of the family -/

/-- `enumerateRules2_1 2` has `C(6,1) + C(6,2) = 21` members. -/
example : (enumerateRules2_1 2).length = 21 := by decide

/-! ## Selection by class on one seed -/

/-- The candidates whose trace on `seed` over `n` steps has class `tgt`. -/
def selectByTrend (cands : List ExecRule) (seed : ExecHG ℕ) (n : Nat)
    (tgt : CurvatureTrend) : List ExecRule :=
  cands.filter (fun r => decide (trendOf r seed n = tgt))

/-! ### Class counts on `edge12`

On the seed `edge12 = [{1,2}]` over two steps, the 21 rules split into 13 flat, 4 zero, 2 negative
and 2 positive. -/

/-- 13 rules are flat. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.flat).length = 13 := by
  native_decide

/-- 4 rules have a non-constant trace ending in 0. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.zero).length = 4 := by
  native_decide

/-- 2 rules have a non-constant trace ending in a negative value. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.negative).length = 2 := by
  native_decide

/-- 2 rules have a non-constant trace ending in a positive value. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.positive).length = 2 := by
  native_decide

/-- The four counts sum to the size of the family: `13 + 4 + 2 + 2 = 21`. -/
example :
    (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.flat).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.zero).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.negative).length
    + (selectByTrend (enumerateRules2_1 2) edge12 2 CurvatureTrend.positive).length
      = (enumerateRules2_1 2).length := by
  native_decide

/-! ## Selection by class on several seeds

A rule is stably of class `t` on a seed set if its trace has class `t` on every seed. -/

/-- The seeds `edge12` (one edge), `path123` (a path of two edges) and `cycle4` (a 4-cycle).
None contains a triangle. -/
def seedSet : List (ExecHG ℕ) := [edge12, path123, cycle4]

/-- The classes of the traces of `r` on each seed. -/
def trendsAcross (r : ExecRule) (seeds : List (ExecHG ℕ)) (n : Nat) :
    List CurvatureTrend :=
  seeds.map (fun s => trendOf r s n)

/-- `true` iff the trace of `r` has class `tgt` on every seed. -/
def isStablyTrend (r : ExecRule) (seeds : List (ExecHG ℕ)) (n : Nat)
    (tgt : CurvatureTrend) : Bool :=
  (trendsAcross r seeds n).all (fun t => decide (t = tgt))

/-- `true` iff the traces of `r` have the same class on every seed. -/
def stablyClassifiable (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) : Bool :=
  match trendsAcross r seeds n with
  | [] => true
  | t :: rest => rest.all (fun t' => decide (t' = t))

/-- The candidates whose trace has class `tgt` on every seed. -/
def stableSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : CurvatureTrend) : List ExecRule :=
  cands.filter (fun r => isStablyTrend r seeds n tgt)

/-! ### Class counts on `seedSet`, `maxRHS = 2`, two steps -/

/-- 7 rules are flat on every seed. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).length = 7 := by
  native_decide

/-- 2 rules are negative on every seed. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.negative).length = 2 := by
  native_decide

/-- 2 rules are positive on every seed. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.positive).length = 2 := by
  native_decide

/-- No rule is zero on every seed. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.zero).length = 0 := by
  native_decide

/-- 11 rules have the same class on every seed. -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length = 11 := by
  native_decide

/-- The four stable counts sum to the stably classifiable count: `7 + 2 + 2 + 0 = 11`. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.negative).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.positive).length
    + (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.zero).length
      = ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length := by
  native_decide

/-- 10 rules have different classes on different seeds. -/
example :
    (enumerateRules2_1 2).length
      - ((enumerateRules2_1 2).filter
          (fun r => stablyClassifiable r seedSet 2)).length = 10 := by
  native_decide

/-! ### Family with `maxRHS = 3` -/

/-- `enumerateRules2_1 3` has `C(6,1) + C(6,2) + C(6,3) = 41` members. -/
example : (enumerateRules2_1 3).length = 41 := by decide

/-- `enumerateRules2_1 3` has 41 members. -/
example : (enumerateRules2_1 3).length = 41 := by decide

/-! ### Class counts on `seedSet`, `maxRHS = 3`, one step -/

/-- 19 of the 41 rules have the same class on every seed. -/
example :
    ((enumerateRules2_1 3).filter
        (fun r => stablyClassifiable r seedSet 1)).length = 19 := by
  native_decide

/-- 11 rules are flat on every seed. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.flat).length = 11 := by
  native_decide

/-- 8 rules are positive on every seed. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.positive).length = 8 := by
  native_decide

/-- No rule is negative on every seed. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.negative).length = 0 := by
  native_decide

/-- No rule is zero on every seed. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.zero).length = 0 := by
  native_decide

/-- 22 rules have different classes on different seeds. -/
example :
    (enumerateRules2_1 3).length
      - ((enumerateRules2_1 3).filter
          (fun r => stablyClassifiable r seedSet 1)).length = 22 := by
  native_decide

/-- The four stable counts sum to the stably classifiable count: `11 + 8 + 0 + 0 = 19`. -/
example :
    (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.flat).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.negative).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.positive).length
    + (stableSelect (enumerateRules2_1 3) seedSet 1 CurvatureTrend.zero).length
      = ((enumerateRules2_1 3).filter
          (fun r => stablyClassifiable r seedSet 1)).length := by
  native_decide

/-! ## Rate bound on a finite trace

A trace satisfies the rate bound `(tgt, c)` if `|trace[i] − tgt| · (i + 1) ≤ c` for every index
`i`. This is a condition on finitely many entries. -/

/-- The rate bound on a trace whose first entry has index `i`. -/
def rateBoundedAux : Nat → List ℤ → ℤ → ℕ → Bool
  | _, [], _, _ => true
  | i, x :: xs, tgt, c =>
    decide ((x - tgt).natAbs * (i + 1) ≤ c) && rateBoundedAux (i + 1) xs tgt c

/-- `rateBounded trace tgt c = true` iff `|trace[i] − tgt| · (i + 1) ≤ c` for every `i`. -/
def rateBounded (trace : List ℤ) (tgt : ℤ) (c : ℕ) : Bool :=
  rateBoundedAux 0 trace tgt c

/-- `true` iff the Forman-scalar trace of `d` satisfies `rateBounded _ tgt c`. -/
def dossierRateBounded (d : Dossier) (tgt : ℤ) (c : ℕ) : Bool :=
  rateBounded d.formanScalarTrace tgt c

/-- `true` iff the Forman-scalar trace of `canonicalDossier r s n` satisfies
`rateBounded _ tgt c` for every seed `s`. -/
def stablyRateBounded (r : ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : Bool :=
  seeds.all (fun s => dossierRateBounded (canonicalDossier r s n) tgt c)

/-- The candidates that satisfy the rate bound `(tgt, c)` on every seed. -/
def stableRateSelect (cands : List ExecRule) (seeds : List (ExecHG ℕ))
    (n : Nat) (tgt : ℤ) (c : ℕ) : List ExecRule :=
  cands.filter (fun r => stablyRateBounded r seeds n tgt c)

/-! ### Rate-bound counts on `seedSet`, `maxRHS = 2`, two steps -/

/-- No rule has Forman scalar 0 at every state on every seed (`tgt = 0, c = 0`). -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 0).length = 0 := by
  native_decide

/-- 7 rules satisfy the rate bound `(0, 12)`. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12).length = 7 := by
  native_decide

/-- 9 rules satisfy the rate bound `(0, 36)`. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 36).length = 9 := by
  native_decide

/-- 17 rules satisfy the rate bound `(0, 200)`. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 200).length = 17 := by
  native_decide

/-- No rule satisfies the rate bound `(-4, 12)`. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 (-4) 12).length = 0 := by
  native_decide

/-- 7 rules satisfy the rate bound `(4, 16)`. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 4 16).length = 7 := by
  native_decide

/-! ### Rate bound `(0, 12)` and stable flatness

On this family the rules satisfying the rate bound `(0, 12)` are the rules that are flat on every
seed. -/

/-- Every candidate passing the rate-(0, 12) envelope is stably flat. -/
example :
    (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12).all
      (fun r => isStablyTrend r seedSet 2 CurvatureTrend.flat) = true := by
  native_decide

/-- Every candidate that is flat on every seed passes the rate-(0, 12) check. -/
example :
    (stableSelect (enumerateRules2_1 2) seedSet 2 CurvatureTrend.flat).all
      (fun r => stablyRateBounded r seedSet 2 0 12) = true := by
  native_decide

/-! ### Rate bound `(0, 200)` and stable classification -/

/-- The stably classifiable count (11) is less than the rate-(0, 200) count (17). -/
example :
    ((enumerateRules2_1 2).filter
        (fun r => stablyClassifiable r seedSet 2)).length
      < (stableRateSelect (enumerateRules2_1 2) seedSet 2 0 200).length := by
  native_decide

/-! ### First rule of the rate-(0, 12) selection -/

/-- The rules of `enumerateRules2_1 2` whose Forman traces on every seed of
`seedSet` over 2 steps satisfy `rateBounded _ 0 12`. -/
def rate12Witnesses : List ExecRule :=
  stableRateSelect (enumerateRules2_1 2) seedSet 2 0 12

/-- The first rule of `rate12Witnesses`. -/
def witnessRule0 : ExecRule :=
  rate12Witnesses.headD trivialIdentityExecRule

/-- `rate12Witnesses` has 7 elements. -/
example : rate12Witnesses.length = 7 := by native_decide

/-- `witnessRule0` passes the rate-(0, 12) check on `seedSet` over 2 steps. -/
theorem witnessRule0_passes :
    stablyRateBounded witnessRule0 seedSet 2 0 12 = true := by
  native_decide

/-- If `rateBoundedAux i trace tgt c = true`, then entry k of `trace`
satisfies `|trace[k] − tgt| · (i + k + 1) ≤ c`. -/
lemma rateBoundedAux_implies :
    ∀ (i : ℕ) {trace : List ℤ} {tgt : ℤ} {c : ℕ}
      (_h : rateBoundedAux i trace tgt c = true)
      (k : ℕ) (hk : k < trace.length),
      ((trace.get ⟨k, hk⟩) - tgt).natAbs * (i + k + 1) ≤ c := by
  intro i trace
  induction trace generalizing i with
  | nil =>
    intro tgt c _h k hk
    exact absurd hk (by simp)
  | cons x xs ih =>
    intro tgt c h k hk
    unfold rateBoundedAux at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h_head, h_tail⟩ := h
    have h_head' : (x - tgt).natAbs * (i + 1) ≤ c := by
      simpa using h_head
    rcases k with _ | k'
    · show (x - tgt).natAbs * (i + 0 + 1) ≤ c
      simpa using h_head'
    · have hk' : k' < xs.length := by
        simpa [List.length_cons] using Nat.lt_of_succ_lt_succ hk
      have ih_step := ih (i := i + 1) h_tail k' hk'
      show ((xs.get ⟨k', hk'⟩) - tgt).natAbs * (i + (k' + 1) + 1) ≤ c
      have h_eq : (i + 1) + k' + 1 = i + (k' + 1) + 1 := by omega
      rw [← h_eq]
      exact ih_step

/-- If `rateBounded trace tgt c = true`, then every entry k of `trace`
satisfies `|trace[k] − tgt| · (k + 1) ≤ c`. -/
lemma rateBounded_implies {trace : List ℤ} {tgt : ℤ} {c : ℕ}
    (h : rateBounded trace tgt c = true)
    (k : ℕ) (hk : k < trace.length) :
    ((trace.get ⟨k, hk⟩) - tgt).natAbs * (k + 1) ≤ c := by
  have := rateBoundedAux_implies 0 h k hk
  simpa using this

/-- The Forman-scalar trace of `witnessRule0` on `edge12` over 2 steps. -/
def witnessRule0_edge12_trace : List ℤ :=
  (canonicalDossier witnessRule0 edge12 2).formanScalarTrace

/-- `witnessRule0_edge12_trace` satisfies `rateBounded _ 0 12`. -/
theorem witnessRule0_edge12_trace_rateBounded :
    rateBounded witnessRule0_edge12_trace 0 12 = true := by
  native_decide

end RuleSignatureExecSearch
end InfraFormalization
