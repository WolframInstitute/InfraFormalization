/-
**Executable multiway hypergraph rewriting** (X4 / #75).

Computable counterpart to `Multiway.lean` (which only states `Step` /
`MultiStep` as `Prop`s). This module provides actual `def`s that take a
rule + state + step count and return all reachable states / signature
trajectories — runnable inside Lean's kernel via `#eval`, suitable for
cross-checking against external engines like `HypergraphRewritingEngine`
(../efficient_rewriting_final/).

**Why a separate exec type.** The abstract `Hypergraph V := { edges :
Multiset (Hyperedge V) }` from `Hypergraph.lean` uses `Multiset` for
proof convenience, but `Multiset.toList` is noncomputable. For
execution we use a parallel `List`-based type `ExecHG V := List
(Hyperedge V)` with a canonical lift `ExecHG.toHypergraph` to the
abstract side.

**Design.** Rules use `Fin numBound + numFresh` pattern vertices: the
first `numBound` appear in LHS (and may appear in RHS); the last
`numFresh` are RHS-only and get fresh `ℕ` IDs allocated when the rule
fires. State carries `V = ℕ`; fresh allocation is `max(existing) + 1, +2, ...`.

**Pipeline.**
  1. `vertexList H` — deduped vertex list of `H`.
  2. `allFunctions n vs` — all functions `Fin n → V` (Cartesian product).
  3. `bindingMatches lhs H ρ` — checks `lhs.map ρ ⊆ H` as multisets-of-edges.
  4. `allMatches r H` — filter binding candidates to those matching.
  5. `applyMatch r H ρ` — produce the next state.
  6. `oneStepStates r H` — all next states from one rule.
  7. `multiwayStep sys H` — all next states across all rules in system.
  8. `multiwayEvolve sys H n` — n-step evolution as a list of states.

**Cross-check rationale.** For any rule + seed + small `n`, signature
trajectories (edge-count, vertex-count) should match what
`HypergraphRewritingEngine` produces.
-/

import InfraFormalization.Multiway

namespace InfraFormalization
namespace MultiwayExec

open Hypergraph

/-! ## Executable hypergraph type -/

/-- `List`-based hypergraph: explicit ordering of edges. -/
abbrev ExecHG (V : Type*) := List (Hyperedge V)

/-- Lift to the abstract `Hypergraph V`. -/
def ExecHG.toHypergraph {V : Type*} (H : ExecHG V) : Hypergraph V :=
  ⟨↑H⟩

/-! ## Vertex enumeration -/

/-- All vertices appearing in the edges of `H`, deduplicated. -/
def vertexList {V : Type*} [DecidableEq V] (H : ExecHG V) : List V :=
  (H.flatMap (fun e => e.verts)).dedup

/-! ## Binding enumeration

Pattern variables are `Fin n`; bindings are functions `Fin n → V`.
We enumerate them as length-`n` Cartesian products from a fixed pool. -/

/-- All functions `Fin n → V` whose values come from a fixed pool `vs`. -/
def allFunctions {V : Type*} : (n : Nat) → (vs : List V) → List (Fin n → V)
  | 0, _ => [Fin.elim0]
  | n+1, vs =>
      vs.flatMap (fun x =>
        (allFunctions n vs).map (fun ρ i =>
          if h : i.val = 0 then x
          else ρ ⟨i.val - 1, by
            have h1 : i.val < n + 1 := i.isLt
            omega⟩))

/-! ## Match testing -/

/-- Multiset-cardinality count of `e` in `edges`. -/
def edgeCount {V : Type*} [DecidableEq V] (e : Hyperedge V)
    (edges : List (Hyperedge V)) : Nat :=
  edges.count e

/-- Check that one list of hyperedges (with multiplicity) is contained
in another. -/
def edgesContained {V : Type*} [DecidableEq V]
    (sub : List (Hyperedge V)) (whole : List (Hyperedge V)) : Bool :=
  -- For each distinct edge in `sub`, count in `sub` ≤ count in `whole`.
  sub.dedup.all (fun e => decide (edgeCount e sub ≤ edgeCount e whole))

/-- Image of an LHS pattern under a binding `ρ`. -/
def mapPattern {n : Nat} {V : Type*} (ρ : Fin n → V)
    (lhs : ExecHG (Fin n)) : ExecHG V :=
  lhs.map (Hyperedge.map ρ)

/-- A binding matches iff `lhs.map ρ ⊆ H` as multisets-of-edges. -/
def bindingMatches {n : Nat} {V : Type*} [DecidableEq V]
    (lhs : ExecHG (Fin n)) (H : ExecHG V) (ρ : Fin n → V) : Bool :=
  edgesContained (mapPattern ρ lhs) H

/-! ## Fresh-vertex allocation (specialised to `V = ℕ`) -/

/-- The next fresh `ℕ` vertex for `H`. -/
def nextFresh (H : ExecHG ℕ) : ℕ :=
  (vertexList H).foldr Nat.max 0 + 1

/-- Generate `k` fresh `ℕ` vertices for `H`. -/
def freshVertices (H : ExecHG ℕ) (k : ℕ) : List ℕ :=
  (List.range k).map (nextFresh H + ·)

/-! ## Executable Rule: bound + fresh pattern variables -/

/-- An executable rule with `numBound` pattern variables that must be
matched in the LHS plus `numFresh` RHS-only fresh variables. -/
structure ExecRule where
  numBound : Nat
  numFresh : Nat
  lhs : ExecHG (Fin numBound)
  rhs : ExecHG (Fin (numBound + numFresh))

/-- Extend a binding `ρ : Fin numBound → ℕ` with fresh ℕ vertices for
the RHS-only variables. -/
def extendBinding (r : ExecRule) (H : ExecHG ℕ)
    (ρ : Fin r.numBound → ℕ) : Fin (r.numBound + r.numFresh) → ℕ :=
  fun i =>
    if h : i.val < r.numBound then ρ ⟨i.val, h⟩
    else
      let k := i.val - r.numBound
      (freshVertices H r.numFresh).getD k 0

/-! ## Single-rule step: enumerate matches and apply -/

/-- Multiset-aware list subtraction: remove each occurrence of edges
in `sub` from `whole` (counted with multiplicity). -/
def removeEdges {V : Type*} [DecidableEq V]
    (whole : List (Hyperedge V)) (sub : List (Hyperedge V)) : List (Hyperedge V) :=
  sub.foldl (fun acc e => acc.erase e) whole

/-- All bindings `Fin r.numBound → ℕ` matching the LHS in `H`. -/
def allMatches (r : ExecRule) (H : ExecHG ℕ) :
    List (Fin r.numBound → ℕ) :=
  let candidates := allFunctions r.numBound (vertexList H)
  candidates.filter (bindingMatches r.lhs H ·)

/-- Apply a single matched binding to produce the next state. -/
def applyMatch (r : ExecRule) (H : ExecHG ℕ)
    (ρ : Fin r.numBound → ℕ) : ExecHG ℕ :=
  let consumed := mapPattern ρ r.lhs
  let ρExt := extendBinding r H ρ
  let produced := mapPattern ρExt r.rhs
  removeEdges H consumed ++ produced

/-- All states reachable from `H` by a single application of `r`. -/
def oneStepStates (r : ExecRule) (H : ExecHG ℕ) : List (ExecHG ℕ) :=
  (allMatches r H).map (applyMatch r H)

/-! ## Multiway: union over rules -/

/-- An executable rewriting system: a list of `ExecRule`s. -/
structure ExecSystem where
  rules : List ExecRule

/-- All states reachable from `H` by applying any rule in the system. -/
def multiwayStep (sys : ExecSystem) (H : ExecHG ℕ) : List (ExecHG ℕ) :=
  sys.rules.flatMap (fun r => oneStepStates r H)

/-- Multiway evolution: list of all states reached after exactly `n`
steps. Branches are not deduplicated — two distinct application
sequences landing on the same state are counted twice. -/
def multiwayEvolve (sys : ExecSystem) (H : ExecHG ℕ) :
    Nat → List (ExecHG ℕ)
  | 0 => [H]
  | n+1 => (multiwayEvolve sys H n).flatMap (multiwayStep sys)

/-! ## Signature trace: useful for cross-checking with external engines -/

/-- Edge count of `H`. -/
def hgEdgeCount (H : ExecHG ℕ) : Nat := H.length

/-- Vertex count of `H` (after dedup). -/
def hgVertexCount (H : ExecHG ℕ) : Nat := (vertexList H).length

/-- Cheap signature: `(numStates, totalEdges, totalVertices)` summed
across the `n`-th step's state list. Should match the analogous
Wolfram-engine output up to canonicalisation modulo isomorphism. -/
def stepSignature (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    Nat × Nat × Nat :=
  let states := multiwayEvolve sys H n
  (states.length,
    (states.map hgEdgeCount).foldr (· + ·) 0,
    (states.map hgVertexCount).foldr (· + ·) 0)

end MultiwayExec
end InfraFormalization
