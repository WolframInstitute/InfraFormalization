/-
Dossiers: recorded runs of a single rule.

A `Dossier` holds an `ExecRule`, a seed and a list of states.
`isConsistent` is the Boolean test that the first state is the seed and
each state is `singleWayStep` of the previous one. This module defines
edge-count and vertex-count traces, the run `canonicalDossier` produced by
`singleWayStep`, and proves `canonicalDossier_isConsistent` (the canonical
run passes the test) and `consistent_dossier_eq_canonical` (every
consistent dossier has the states of the canonical run).
-/

import InfraFormalization.MultiwayExec
import InfraFormalization.MultiwayExecTests

namespace InfraFormalization
namespace RuleSignatureSchema

open MultiwayExec

/-! ## The dossier type -/

/-- A rule, a seed and a list of states. -/
structure Dossier where
  rule    : ExecRule
  seed    : ExecHG ℕ
  states  : List (ExecHG ℕ)

namespace Dossier

variable (d : Dossier)

/-- The system whose only rule is `d.rule`. -/
def system : ExecSystem := ⟨[d.rule]⟩

/-- The number of recorded states. -/
def length : Nat := d.states.length

/-! ## Consistency -/

/-- Every consecutive pair `(Hᵢ, Hᵢ₊₁)` of the list satisfies
`Hᵢ₊₁ = singleWayStep sys Hᵢ`. -/
def stepsConsistentList (sys : ExecSystem) : List (ExecHG ℕ) → Bool
  | []           => true
  | [_]          => true
  | a :: b :: rs =>
      if singleWayStep sys a = b then stepsConsistentList sys (b :: rs)
      else false

/-- `stepsConsistentList` on the states of the dossier. -/
def stepsConsistent : Bool := stepsConsistentList d.system d.states

/-- The state list is nonempty and its first entry is the seed. -/
def seedConsistent : Bool :=
  match d.states with
  | []     => false
  | s :: _ => decide (s = d.seed)

/-- `seedConsistent` and `stepsConsistent`. -/
def isConsistent : Bool := d.seedConsistent && d.stepsConsistent

/-! ## Traces -/

/-- The list of edge counts of the states. -/
def edgeCountTrace : List Nat := d.states.map hgEdgeCount

/-- The list of vertex counts of the states. -/
def vertexCountTrace : List Nat := d.states.map hgVertexCount

/-- The state at index `i`, or the seed if `i` is out of range. -/
def stateAt (i : Nat) : ExecHG ℕ := (d.states[i]?).getD d.seed

/-! ## Constancy tests -/

/-- The list is empty or all entries equal its first entry. -/
def listAllEqHead : List Nat → Bool
  | []      => true
  | x :: rs => rs.all (decide <| · = x)

/-- The edge-count trace is constant. -/
def edgeCountConstant : Bool := listAllEqHead d.edgeCountTrace

/-- The vertex-count trace is constant. -/
def vertexCountConstant : Bool := listAllEqHead d.vertexCountTrace

end Dossier

/-! ## Canonical dossier -/

/-- The list `[seed, sw seed, sw² seed, ..., swⁿ seed]` with
`sw = singleWayStep sys`, defined by recursion on `n`. -/
def evolveTrace (sys : ExecSystem) : ExecHG ℕ → Nat → List (ExecHG ℕ)
  | seed, 0     => [seed]
  | seed, n + 1 => seed :: evolveTrace sys (singleWayStep sys seed) n

@[simp] theorem evolveTrace_zero (sys : ExecSystem) (seed : ExecHG ℕ) :
    evolveTrace sys seed 0 = [seed] := rfl

@[simp] theorem evolveTrace_succ (sys : ExecSystem) (seed : ExecHG ℕ) (n : Nat) :
    evolveTrace sys seed (n + 1) = seed :: evolveTrace sys (singleWayStep sys seed) n := rfl

theorem evolveTrace_length (sys : ExecSystem) (seed : ExecHG ℕ) (n : Nat) :
    (evolveTrace sys seed n).length = n + 1 := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simp [ih]

theorem evolveTrace_ne_nil (sys : ExecSystem) (seed : ExecHG ℕ) (n : Nat) :
    evolveTrace sys seed n ≠ [] := by
  intro h
  have hlen := evolveTrace_length sys seed n
  rw [h] at hlen
  simp at hlen

/-- The dossier whose states are `evolveTrace ⟨[rule]⟩ seed n`. -/
def canonicalDossier (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    Dossier where
  rule   := rule
  seed   := seed
  states := evolveTrace ⟨[rule]⟩ seed n

@[simp] theorem canonicalDossier_rule (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).rule = rule := rfl

@[simp] theorem canonicalDossier_seed_field (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).seed = seed := rfl

@[simp] theorem canonicalDossier_states (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).states = evolveTrace ⟨[rule]⟩ seed n := rfl

@[simp] theorem canonicalDossier_length (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).length = n + 1 := by
  unfold Dossier.length canonicalDossier
  exact evolveTrace_length _ _ _

/-! ## The canonical dossier is consistent -/

/-- The first state of a canonical dossier is its seed. -/
theorem canonicalDossier_seedConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).seedConsistent = true := by
  unfold Dossier.seedConsistent canonicalDossier
  simp only []
  cases n with
  | zero => simp [evolveTrace]
  | succ k => simp [evolveTrace]

/-- Unfolding of `stepsConsistentList` on a list with at least two
entries. -/
theorem stepsConsistentList_cons_cons_eq (sys : ExecSystem)
    (a b : ExecHG ℕ) (rs : List (ExecHG ℕ)) :
    Dossier.stepsConsistentList sys (a :: b :: rs) =
      (if singleWayStep sys a = b
        then Dossier.stepsConsistentList sys (b :: rs)
        else false) := rfl

/-- `stepsConsistentList sys (evolveTrace sys seed n) = true` for every
`seed` and `n`. -/
theorem stepsConsistentList_evolveTrace (sys : ExecSystem) :
    ∀ (seed : ExecHG ℕ) (n : Nat),
      Dossier.stepsConsistentList sys (evolveTrace sys seed n) = true := by
  intro seed n
  induction n generalizing seed with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero =>
      -- evolveTrace sys seed 1 = [seed, sw seed]
      show Dossier.stepsConsistentList sys [seed, singleWayStep sys seed] = true
      rw [stepsConsistentList_cons_cons_eq, if_pos rfl]
      rfl
    | succ m =>
      -- evolveTrace sys seed (m+2) = seed :: sw seed :: evolveTrace sys (sw (sw seed)) m
      show Dossier.stepsConsistentList sys
        (seed :: singleWayStep sys seed ::
          evolveTrace sys (singleWayStep sys (singleWayStep sys seed)) m) = true
      rw [stepsConsistentList_cons_cons_eq, if_pos rfl]
      -- The remaining list is `evolveTrace sys (sw seed) (m+1)` by `evolveTrace_succ`.
      exact ih (singleWayStep sys seed)

/-- A canonical dossier satisfies `stepsConsistent`. -/
theorem canonicalDossier_stepsConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).stepsConsistent = true := by
  unfold Dossier.stepsConsistent canonicalDossier Dossier.system
  simp only []
  exact stepsConsistentList_evolveTrace _ _ _

/-- A canonical dossier satisfies `isConsistent`. -/
theorem canonicalDossier_isConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).isConsistent = true := by
  unfold Dossier.isConsistent
  rw [canonicalDossier_seedConsistent, canonicalDossier_stepsConsistent]
  rfl

/-! ## Every consistent dossier has the canonical states -/

/-- If `stepsConsistentList sys (s :: states)` holds, then
`s :: states = evolveTrace sys s states.length`. -/
theorem stepsConsistentList_implies_eq_evolveTrace (sys : ExecSystem) :
    ∀ (s : ExecHG ℕ) (states : List (ExecHG ℕ)),
      Dossier.stepsConsistentList sys (s :: states) = true →
      s :: states = evolveTrace sys s states.length := by
  intro s states
  induction states generalizing s with
  | nil =>
    intro _
    rfl
  | cons b rest ih =>
    intro h
    rw [stepsConsistentList_cons_cons_eq] at h
    by_cases hsw : singleWayStep sys s = b
    · rw [if_pos hsw] at h
      have ih_h : b :: rest = evolveTrace sys b rest.length := ih b h
      show s :: b :: rest = evolveTrace sys s (b :: rest).length
      rw [List.length_cons]
      show s :: b :: rest = evolveTrace sys s (rest.length + 1)
      rw [evolveTrace_succ, hsw, ih_h]
    · rw [if_neg hsw] at h
      exact absurd h Bool.false_ne_true

/-- If `d.isConsistent`, then the states of `d` are
`evolveTrace d.system d.seed (d.length - 1)`. -/
theorem consistent_dossier_eq_canonical (d : Dossier) (h : d.isConsistent = true) :
    d.states = evolveTrace d.system d.seed (d.length - 1) := by
  unfold Dossier.isConsistent at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h_seed, h_steps⟩ := h
  unfold Dossier.seedConsistent at h_seed
  unfold Dossier.stepsConsistent at h_steps
  match hstates : d.states with
  | [] =>
    rw [hstates] at h_seed
    exact absurd h_seed Bool.false_ne_true
  | s :: rest =>
    rw [hstates] at h_seed h_steps
    simp at h_seed
    subst h_seed
    have hev := stepsConsistentList_implies_eq_evolveTrace d.system d.seed rest h_steps
    have hlen : d.length = rest.length + 1 := by
      unfold Dossier.length
      rw [hstates]
      rfl
    rw [hev, hlen]
    simp

/-! ## Subdivision rule, 4 steps, checked by `decide` -/

/-- The canonical dossier of the subdivision rule from `subdSeed` for 4
steps. -/
def subdivisionDossier4 : Dossier :=
  canonicalDossier MultiwayExec.Test.subdivisionRule MultiwayExec.Test.subdSeed 4

example : subdivisionDossier4.seedConsistent = true := by decide

example : subdivisionDossier4.length = 5 := by decide

/-- Edge counts `1, 2, 4, 8, 16`. -/
example : subdivisionDossier4.edgeCountTrace = [1, 2, 4, 8, 16] := by decide

/-- Vertex counts `2, 3, 5, 9, 17`. -/
example : subdivisionDossier4.vertexCountTrace = [2, 3, 5, 9, 17] := by decide

/-! ## `tc1Rule`, 1 step, checked by `decide` -/

/-- The canonical dossier of `tc1Rule` from `tc1Seed` for 1 step. -/
def tc1Dossier1 : Dossier :=
  canonicalDossier MultiwayExec.Test.tc1Rule MultiwayExec.Test.tc1Seed 1

example : tc1Dossier1.seedConsistent = true := by decide

example : tc1Dossier1.length = 2 := by decide

example : tc1Dossier1.edgeCountTrace = [1, 2] := by decide

end RuleSignatureSchema
end InfraFormalization
