/-
Executable hypergraph rewriting.

`Multiway.lean` states `Step` and `MultiStep` as propositions. This module defines computable
counterparts on the list-based type `ExecHG V := List (Hyperedge V)`, which maps to the
multiset-based `Hypergraph V` by `ExecHG.toHypergraph`. A rule `ExecRule` has `numBound` pattern
variables matched in the left-hand side and `numFresh` right-hand-side variables that receive fresh
natural-number vertices `max + 1, max + 2, …`. The module defines match enumeration (`allMatches`),
application of a match (`applyMatch`), the multiway step and evolution, the single-way step
`singleWayStep` (a greedy maximal set of edge-disjoint matches), and the fire-all step `fireAllStep`
(every match, including overlapping ones, which is not a Wolfram model update).
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

/-- All functions `Fin n → V` with values in the list `vs`. -/
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

/-! `allMatches` enumerates distinct bindings `Fin numBound → ℕ`, so two equal edges of `H` give one
match. In the Wolfram model each occurrence of an edge gives its own match. -/

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

/-! ## Single-way evolution

One single-way step applies a set of pairwise edge-disjoint matches to
the input state `H`. Matches are taken in the order of `sys.rules` and,
within a rule, in the order of `allMatches r H`. A match fires when its
consumed edges are still contained (with multiplicity) in the edges of
`H` that earlier matches of the same step left unconsumed; otherwise it
is skipped. Edges produced in the step are not available to later
matches of the same step. The fired set is therefore a maximal set of
edge-disjoint matches, chosen greedily in enumeration order.

`allMatches` enumerates distinct bindings, so a state holding two equal
edges gives one match for a one-edge left-hand side where the Wolfram
model gives two. -/

/-- Accumulator of one single-way step: edges of the input state not yet
consumed, edges produced so far, the fresh-vertex offset, and the fired
matches as `(rule index, consumed edges, produced edges)`. -/
structure StepAcc where
  avail : ExecHG ℕ
  produced : ExecHG ℕ
  offset : ℕ
  fired : List (ℕ × ExecHG ℕ × ExecHG ℕ)

/-- Fire the match `ρ` of rule `r` (rule index `ri`) if its consumed
edges are contained in `acc.avail`; fresh vertices are
`baseFresh + acc.offset + k`. -/
def fireIfFree (r : ExecRule) (ri baseFresh : ℕ) (acc : StepAcc)
    (ρ : Fin r.numBound → ℕ) : StepAcc :=
  let consumed : ExecHG ℕ := mapPattern ρ r.lhs
  if edgesContained consumed acc.avail then
    let ρExt : Fin (r.numBound + r.numFresh) → ℕ := fun i =>
      if h : i.val < r.numBound then ρ ⟨i.val, h⟩
      else baseFresh + acc.offset + (i.val - r.numBound)
    let produced : ExecHG ℕ := mapPattern ρExt r.rhs
    { avail := removeEdges acc.avail consumed
      produced := acc.produced ++ produced
      offset := acc.offset + r.numFresh
      fired := acc.fired ++ [(ri, consumed, produced)] }
  else acc

theorem fireIfFree_avail_of_contained (r : ExecRule) (ri baseFresh : ℕ)
    (acc : StepAcc) (ρ : Fin r.numBound → ℕ)
    (h : edgesContained (mapPattern ρ r.lhs) acc.avail = true) :
    (fireIfFree r ri baseFresh acc ρ).avail
      = removeEdges acc.avail (mapPattern ρ r.lhs) := by
  simp [fireIfFree, h]

theorem fireIfFree_produced_of_contained (r : ExecRule) (ri baseFresh : ℕ)
    (acc : StepAcc) (ρ : Fin r.numBound → ℕ)
    (h : edgesContained (mapPattern ρ r.lhs) acc.avail = true) :
    (fireIfFree r ri baseFresh acc ρ).produced
      = acc.produced ++ mapPattern
          (fun i : Fin (r.numBound + r.numFresh) =>
            if h : i.val < r.numBound then ρ ⟨i.val, h⟩
            else baseFresh + acc.offset + (i.val - r.numBound)) r.rhs := by
  simp [fireIfFree, h]

/-- A match whose consumed edges are not available is skipped. -/
theorem fireIfFree_of_not_contained (r : ExecRule) (ri baseFresh : ℕ)
    (acc : StepAcc) (ρ : Fin r.numBound → ℕ)
    (h : edgesContained (mapPattern ρ r.lhs) acc.avail = false) :
    fireIfFree r ri baseFresh acc ρ = acc := by
  simp [fireIfFree, h]

/-- The fold of one single-way step over all rules and matches. -/
def stepFold (sys : ExecSystem) (H : ExecHG ℕ) : StepAcc :=
  let baseFresh := nextFresh H
  (sys.rules.zipIdx.foldl (fun (acc : StepAcc) (rp : ExecRule × ℕ) =>
    (allMatches rp.1 H).foldl (fireIfFree rp.1 rp.2 baseFresh) acc)
    ⟨H, [], 0, []⟩)

/-- One single-way step: the unconsumed edges of `H` followed by the
edges produced by the fired matches. -/
def singleWayStep (sys : ExecSystem) (H : ExecHG ℕ) : ExecHG ℕ :=
  let acc := stepFold sys H
  acc.avail ++ acc.produced

/-- `n` iterations of `singleWayStep`. -/
def singleWayEvolve (sys : ExecSystem) (H : ExecHG ℕ) : Nat → ExecHG ℕ
  | 0 => H
  | n+1 => singleWayStep sys (singleWayEvolve sys H n)

/-! ## Fire-all step

`fireAllStep` applies every match of every rule found in the input state
`H`, including matches that share edges. Each match removes its consumed
edges from the running state where they are still present (`List.erase`
does nothing on an absent edge) and appends its produced edges. When two
matches share an edge, the result is not a single-way Wolfram model
step, and the edge count of a conservative rule can change. Results
stated with `fireAllStep` are results about this operator. -/

/-- One fire-all step. -/
def fireAllStep (sys : ExecSystem) (H : ExecHG ℕ) : ExecHG ℕ :=
  let baseFresh := nextFresh H
  let processed := sys.rules.foldl (fun (acc : ExecHG ℕ × Nat) r =>
    (allMatches r H).foldl (fun (acc' : ExecHG ℕ × Nat) ρ =>
      let (state, offset) := acc'
      let consumed : ExecHG ℕ := mapPattern ρ r.lhs
      let ρExt : Fin (r.numBound + r.numFresh) → ℕ := fun i =>
        if h : i.val < r.numBound then ρ ⟨i.val, h⟩
        else baseFresh + offset + (i.val - r.numBound)
      let produced : ExecHG ℕ := mapPattern ρExt r.rhs
      (removeEdges state consumed ++ produced, offset + r.numFresh)
    ) acc
  ) (H, 0)
  processed.fst

/-- Iterated `fireAllStep`. -/
def fireAllEvolve (sys : ExecSystem) (H : ExecHG ℕ) : Nat → ExecHG ℕ
  | 0 => H
  | n+1 => fireAllStep sys (fireAllEvolve sys H n)

/-! ## Edge and vertex counts of the multiway evolution -/

/-- Edge count of `H`. -/
def hgEdgeCount (H : ExecHG ℕ) : Nat := H.length

/-- Vertex count of `H` (after dedup). -/
def hgVertexCount (H : ExecHG ℕ) : Nat := (vertexList H).length

/-- The triple of the number of states at step `n` of `multiwayEvolve`, the sum of their edge counts
and
the sum of their vertex counts. -/
def stepSignature (sys : ExecSystem) (H : ExecHG ℕ) (n : Nat) :
    Nat × Nat × Nat :=
  let states := multiwayEvolve sys H n
  (states.length,
    (states.map hgEdgeCount).foldr (· + ·) 0,
    (states.map hgVertexCount).foldr (· + ·) 0)

end MultiwayExec
end InfraFormalization
