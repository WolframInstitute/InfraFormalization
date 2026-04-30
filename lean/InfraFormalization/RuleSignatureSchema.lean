/-
**Rule-signature dossier schema** (#372).

Lean-internal data model for the per-rule trajectory dossiers exchanged
between the WL-side enumerator (Pokorny's `Infrageometry` paclet, #374)
and the Lean-side validator (#375). Three fields:

  * `rule` — the `ExecRule` whose trajectory is being recorded;
  * `seed` — the initial state;
  * `states` — the claimed sequence `[H₀, H₁, ..., Hₙ]`.

The dossier is the *trajectory*, not the *verdict*. Lean never trusts
WL-side curvature/angle numerics; instead, Lean recomputes signatures
from the per-step states.

**Correctness contract.** A *consistent* dossier (`isConsistent = true`)
is one whose claimed `states` agree exactly with what `singleWayEvolve`
produces from `seed` for the dossier's single-rule system. Consistency
is `Decidable` and computed from the dossier alone — no external trust.

**`canonicalDossier`** is the reference dossier built by the Lean
executor itself. We exhibit (decidably, by `decide`) that the
`canonicalDossier` for several concrete rules from `MultiwayExecTests`
passes the consistency check. The general theorem that *every*
consistent dossier equals the canonical one is the substance of #377
(spun off from #372).

**Out-of-scope here.**
  * JSON parsing — handled by an out-of-Lean script that emits a Lean
    term file. We do not parse JSON inside Lean.
  * Curvature signature recomputation — happens in #373 by lifting
    `ExecHG ℕ → Hypergraph V` and feeding into `MultiScreener`.
-/

import InfraFormalization.MultiwayExec
import InfraFormalization.MultiwayExecTests

namespace InfraFormalization
namespace RuleSignatureSchema

open MultiwayExec

/-! ## The dossier type -/

/-- A rule-trajectory dossier. The data model for the JSON interchange
used by the WL paclet (#374). -/
structure Dossier where
  rule    : ExecRule
  seed    : ExecHG ℕ
  states  : List (ExecHG ℕ)

namespace Dossier

variable (d : Dossier)

/-- The single-rule executable system implied by the dossier. -/
def system : ExecSystem := ⟨[d.rule]⟩

/-- Number of recorded states (`n+1` for an `n`-step trajectory). -/
def length : Nat := d.states.length

/-! ## Step-by-step consistency check

Each consecutive pair `(Hᵢ, Hᵢ₊₁)` must satisfy
`Hᵢ₊₁ = singleWayStep sys Hᵢ`. -/

/-- Auxiliary: walk through a list of states and check consecutive-pair
single-way consistency. -/
def stepsConsistentList (sys : ExecSystem) : List (ExecHG ℕ) → Bool
  | []           => true
  | [_]          => true
  | a :: b :: rs =>
      if singleWayStep sys a = b then stepsConsistentList sys (b :: rs)
      else false

/-- Step consistency over the dossier: each `Hᵢ₊₁ = singleWayStep sys Hᵢ`. -/
def stepsConsistent : Bool := stepsConsistentList d.system d.states

/-- Seed consistency: `states[0] = seed`. -/
def seedConsistent : Bool :=
  match d.states with
  | []     => false
  | s :: _ => decide (s = d.seed)

/-- Full consistency: nonempty states, seed at head, single-way steps. -/
def isConsistent : Bool := d.seedConsistent && d.stepsConsistent

/-! ## Trivial signature traces (decidable, total) -/

/-- Edge-count trajectory: `n ↦ |states[n]|`. The trivial signature. -/
def edgeCountTrace : List Nat := d.states.map hgEdgeCount

/-- Vertex-count trajectory: `n ↦ #{vertices in states[n]}`. -/
def vertexCountTrace : List Nat := d.states.map hgVertexCount

/-- The state at step `i`, with default seed if out-of-range. Total. -/
def stateAt (i : Nat) : ExecHG ℕ := (d.states[i]?).getD d.seed

/-! ## Constancy predicates (decidable screener verdicts)

These are the simplest screener obligations: edge-count constant
across the trajectory (the conservation screener), vertex-count
constant. Both are `Bool`-valued and decidable; given a concrete
canonical dossier, `decide` produces an axiom-clean verdict. -/

/-- All entries of a `List Nat` equal the head (or list is empty). -/
def listAllEqHead : List Nat → Bool
  | []      => true
  | x :: rs => rs.all (decide <| · = x)

/-- Edge-count is constant across the dossier's trajectory. The
ExecHG-side analogue of `RuleSignatureScreener.edgeCountTrajectory_const`. -/
def edgeCountConstant : Bool := listAllEqHead d.edgeCountTrace

/-- Vertex-count is constant across the dossier's trajectory. -/
def vertexCountConstant : Bool := listAllEqHead d.vertexCountTrace

end Dossier

/-! ## Canonical (Lean-internal) reference dossier

Built by running the Lean executor directly. Reference for what any
externally-emitted dossier must equal. -/

/-- Recursive trajectory builder: `[seed, sw¹ seed, sw² seed, ...,
swⁿ seed]`. Equivalent to `(List.range (n+1)).map (singleWayEvolve …)`
but easier to reason about inductively. -/
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

/-- The canonical dossier produced by the Lean executor on `(rule, seed)`
for `n` steps. -/
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

/-! ## Canonical dossier passes the consistency check

These are the validation theorems for the schema itself: any
`canonicalDossier` is provably `isConsistent = true`. The general
theorem that *every* consistent dossier equals a canonical one is
task #377. -/

/-- The canonical dossier always has its head equal to the seed. -/
theorem canonicalDossier_seedConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).seedConsistent = true := by
  unfold Dossier.seedConsistent canonicalDossier
  simp only []
  cases n with
  | zero => simp [evolveTrace]
  | succ k => simp [evolveTrace]

/-- Equation lemma: `stepsConsistentList` on a `cons cons` list reduces
to the `if`-form. -/
theorem stepsConsistentList_cons_cons_eq (sys : ExecSystem)
    (a b : ExecHG ℕ) (rs : List (ExecHG ℕ)) :
    Dossier.stepsConsistentList sys (a :: b :: rs) =
      (if singleWayStep sys a = b
        then Dossier.stepsConsistentList sys (b :: rs)
        else false) := rfl

/-- Core lemma: `stepsConsistentList` returns `true` on any
`evolveTrace`. The strong induction hypothesis is universal over the
seed. -/
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
      -- Goal after simp: stepsConsistentList sys (sw seed :: evolveTrace sys (sw (sw seed)) m)
      -- = stepsConsistentList sys (evolveTrace sys (sw seed) (m+1)) by rfl on evolveTrace_succ
      exact ih (singleWayStep sys seed)

/-- The canonical dossier always passes the steps-consistency check. -/
theorem canonicalDossier_stepsConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).stepsConsistent = true := by
  unfold Dossier.stepsConsistent canonicalDossier Dossier.system
  simp only []
  exact stepsConsistentList_evolveTrace _ _ _

/-- **Headline:** the canonical dossier passes the full consistency check.
This is the soundness statement for the schema — the Lean executor
itself produces a consistent dossier, validating the schema's `decide`
check is non-trivial. -/
theorem canonicalDossier_isConsistent (rule : ExecRule) (seed : ExecHG ℕ) (n : Nat) :
    (canonicalDossier rule seed n).isConsistent = true := by
  unfold Dossier.isConsistent
  rw [canonicalDossier_seedConsistent, canonicalDossier_stepsConsistent]
  rfl

/-! ## Strong correctness: every consistent dossier IS the canonical one (#377)

The substantive correctness theorem for the schema. Combined with
`canonicalDossier_isConsistent`, it shows the consistency check is
both *sound* (canonical passes) and *characterising* (only canonical
passes). The WL paclet cannot smuggle a non-canonical trajectory past
the consistency check. -/

/-- Auxiliary: a step-consistent `s :: states` is exactly the
`evolveTrace` from `s` of length `states.length + 1`. -/
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

/-- **Strong correctness theorem (#377).** Any consistent dossier *is*
the canonical Lean-executor trajectory for its rule and seed. The WL
side becomes a precomputed cache, not a source of new claims. -/
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

/-! ## Example: the subdivision rule's canonical dossier is consistent

`MultiwayExecTests.subdivisionSys` evolved from `subdSeed` for 4 steps
gives a 5-state trajectory. We exhibit (by `decide`) that the resulting
dossier passes the consistency check. -/

/-- Canonical 4-step subdivision-rule dossier. -/
def subdivisionDossier4 : Dossier :=
  canonicalDossier MultiwayExec.Test.subdivisionRule MultiwayExec.Test.subdSeed 4

/-- The 4-step subdivision-rule canonical dossier passes seed consistency. -/
example : subdivisionDossier4.seedConsistent = true := by decide

/-- The 4-step subdivision-rule canonical dossier has the expected length. -/
example : subdivisionDossier4.length = 5 := by decide

/-- The 4-step subdivision-rule canonical dossier has edge counts
matching the geometric path-doubling: `1, 2, 4, 8, 16`. -/
example : subdivisionDossier4.edgeCountTrace = [1, 2, 4, 8, 16] := by decide

/-- The 4-step subdivision-rule canonical dossier has vertex counts
matching the geometric path-doubling: `2, 3, 5, 9, 17`. -/
example : subdivisionDossier4.vertexCountTrace = [2, 3, 5, 9, 17] := by decide

/-! ## Example: TC1 canonical dossier is consistent (multiway, 1 step) -/

/-- Canonical 1-step TC1 dossier (single-way evolution of `tc1Rule`). -/
def tc1Dossier1 : Dossier :=
  canonicalDossier MultiwayExec.Test.tc1Rule MultiwayExec.Test.tc1Seed 1

example : tc1Dossier1.seedConsistent = true := by decide

example : tc1Dossier1.length = 2 := by decide

example : tc1Dossier1.edgeCountTrace = [1, 2] := by decide

end RuleSignatureSchema
end InfraFormalization
