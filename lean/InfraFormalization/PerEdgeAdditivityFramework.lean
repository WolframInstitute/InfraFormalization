/-
**Per-edge additivity framework** (#495).

**Goal**: lift the per-edge additivity claim
`knillEulerScaled(rule, seed, d) = |seed| · knillEulerScaled(rule, edge12, d)`
from a finite-corpus `native_decide` check (the current state across
`UniversalAdditivity.lean`, `BranchialUniversalAdditivity.lean`,
`StableDiscoveredRules.lean`, the BBH modules, ...) to a real universal
theorem.

**Strategy**: prove this for **vertex-disjoint seeds** first. BBH initial
data is 7 vertex-disjoint edges by construction, so this branch alone
suffices to derive `Knill(BBH, d) = 7 · Knill(edge12, d)` universally
in `d`. The connected-seed case (`path123`, `triangle`) requires a
tree-decomposition argument on the causal DAG and is multi-session.

The framework decomposes into three independent obligations:

  **(K1) Knill is additive over vertex-disjoint hypergraphs.**
        `Disjoint H₁ H₂ → knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂`.
        Pure combinatorics. Sub-lemmas in Sections B/C proved here;
        K1 itself stated as a Prop pending the foldr-split chain.

  **(K2) Knill is invariant under vertex relabeling (bijection on `ℕ`).**
        `Bijective f → knillEulerScaled (relabel f H) = knillEulerScaled H`.
        Pure combinatorics. Stated.

  **(E1) The engine commutes with disjoint union for single-edge-LHS rules.**
        For `r` with `r.lhs.length = 1` and vertex-disjoint `H₁, H₂`:
        the causal DAG of `singleWayEvolve ⟨[r]⟩ (H₁ ++ H₂) d` is the
        vertex-disjoint union of the causal DAGs from `H₁` and `H₂` (up
        to fresh-vertex relabeling). Engine-semantics. Stated.

  **Composition.** (K1) + (K2) + (E1) ⟹ `disjoint_per_edge_additivity`:
  for single-edge-LHS rules and vertex-disjoint seeds,
  `knillEulerScaled(causalDAG sys seed d) = |seed_distinct_edges| · knillEulerScaled(causalDAG sys edge12 d)`.

This module establishes the framework, proves the structural
sub-lemmas (`mem_vertexList_append`, `execAdj_append`,
`execAdj_cross_zero`), and states K1, K2, E1, and the composed
disjoint-seed per-edge additivity as named `Prop` obligations. No
sorries; the open obligations are tracked as `def : Prop`.
-/

import InfraFormalization.KnillDiscreteGaussBonnet
import InfraFormalization.BBHInitialData
import InfraFormalization.CausalEventTrace

namespace InfraFormalization
namespace PerEdgeAdditivityFramework

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace

/-! ## Section A: vertex-disjointness predicate -/

/-- Two hypergraphs are vertex-disjoint when no vertex appears in both. -/
def VertexDisjoint (H₁ H₂ : ExecHG ℕ) : Prop :=
  ∀ v, v ∈ vertexList H₁ → v ∉ vertexList H₂

/-- Symmetric formulation. -/
theorem VertexDisjoint.symm {H₁ H₂ : ExecHG ℕ}
    (h : VertexDisjoint H₁ H₂) : VertexDisjoint H₂ H₁ := by
  intro v hv₂ hv₁
  exact h v hv₁ hv₂

/-! ## Section B: vertexList behavior under concatenation -/

/-- `vertexList (H₁ ++ H₂)` lists exactly the vertices of `H₁` and `H₂`
combined, with deduplication. -/
theorem mem_vertexList_append {V : Type*} [DecidableEq V]
    (H₁ H₂ : ExecHG V) (v : V) :
    v ∈ vertexList (H₁ ++ H₂) ↔ v ∈ vertexList H₁ ∨ v ∈ vertexList H₂ := by
  unfold vertexList
  rw [List.flatMap_append, List.mem_dedup, List.mem_append, List.mem_dedup, List.mem_dedup]

/-! ## Section C: adjacency under concatenation -/

/-- `execAdj (H₁ ++ H₂) u v` iff one of the parts has the adjacency. -/
theorem execAdj_append (H₁ H₂ : ExecHG ℕ) (u v : ℕ) :
    execAdj (H₁ ++ H₂) u v = (execAdj H₁ u v || execAdj H₂ u v) := by
  unfold execAdj
  rw [List.any_append]
  by_cases huv : u = v
  · subst huv
    simp
  · simp [bne_iff_ne.mpr huv]

/-- Under vertex-disjointness, any potential adjacency in `H₁` between
`u ∈ V(H₁)` and `v ∈ V(H₂)` is false (no edge of `H₁` contains `v`
since `v ∉ V(H₁)`). -/
theorem execAdj_cross_H1_zero (H₁ H₂ : ExecHG ℕ)
    (h : VertexDisjoint H₁ H₂)
    {u v : ℕ} (_hu : u ∈ vertexList H₁) (hv : v ∈ vertexList H₂) :
    execAdj H₁ u v = false := by
  have hv_not_in_H₁ : v ∉ vertexList H₁ := fun hv₁ => h.symm v hv hv₁
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, ⟨e, he_in, he_contains⟩⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hv_not_in_H₁
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.2⟩

/-- Symmetric: any potential adjacency in `H₂` between `u ∈ V(H₁)`
and `v ∈ V(H₂)` is false (no edge of `H₂` contains `u`). -/
theorem execAdj_cross_H2_zero (H₁ H₂ : ExecHG ℕ)
    (h : VertexDisjoint H₁ H₂)
    {u v : ℕ} (hu : u ∈ vertexList H₁) (_hv : v ∈ vertexList H₂) :
    execAdj H₂ u v = false := by
  have hu_not_in_H₂ : u ∉ vertexList H₂ := h u hu
  unfold execAdj
  apply Bool.eq_false_iff.mpr
  intro hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.any_eq_true] at hadj
  obtain ⟨_, ⟨e, he_in, he_contains⟩⟩ := hadj
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he_contains
  apply hu_not_in_H₂
  unfold vertexList
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨e, he_in, he_contains.1⟩

/-! ## Section D: K1 — the Knill-additivity obligation -/

/-- **(K1) Knill is additive over vertex-disjoint hypergraphs.**

For vertex-disjoint `H₁, H₂`, the per-vertex Knill sum splits:

  `knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂`

**Mathematical content** (the obligation):

  1. `vertexList (H₁ ++ H₂)` partitions into vertices from `H₁` and
     vertices from `H₂` (no overlap by `VertexDisjoint`).
  2. For `v ∈ V(H₁)`, all triangles and adjacencies through `v` lie
     entirely within `H₁` (by `execAdj_cross_H2_zero`). Hence
     `knillVertexK6 (H₁ ++ H₂) v = knillVertexK6 H₁ v`.
  3. Symmetric for `v ∈ V(H₂)`.
  4. The foldr sum decomposes via the partition.

Stated as a Prop obligation; sub-lemmas (Section B/C) discharge
most of the structural reasoning. Closing K1 requires the foldr-split
chain on `vertexList (H₁ ++ H₂)`. -/
def K1_KnillAdditiveOverDisjointUnion : Prop :=
  ∀ (H₁ H₂ : ExecHG ℕ), VertexDisjoint H₁ H₂ →
    knillEulerScaled (H₁ ++ H₂) = knillEulerScaled H₁ + knillEulerScaled H₂

/-! ## Section E: K2 — vertex-relabeling invariance -/

/-- Vertex-relabeling: apply a bijection on `ℕ` to every vertex. -/
def relabel (f : ℕ → ℕ) (H : ExecHG ℕ) : ExecHG ℕ :=
  H.map (Hyperedge.map f)

/-- **(K2) Knill is invariant under vertex relabeling.**

For any bijection `f : ℕ → ℕ`, `knillEulerScaled (relabel f H) = knillEulerScaled H`.

The proof is structural: `K6(v)` depends only on the local clique
structure, which is preserved by bijection.

Stated as a Prop obligation. -/
def K2_KnillRelabelingInvariant : Prop :=
  ∀ (f : ℕ → ℕ) (_h : Function.Bijective f) (H : ExecHG ℕ),
    knillEulerScaled (relabel f H) = knillEulerScaled H

/-! ## Section F: single-edge-LHS predicate -/

/-- Predicate for a rule with a single LHS edge. -/
def SingleEdgeLHS (r : ExecRule) : Prop := r.lhs.length = 1

/-! ## Section G: E1 — the engine-decomposition obligation -/

/-- **(E1) Engine commutes with disjoint union for single-edge-LHS rules.**

For a single-edge-LHS rule `r` and vertex-disjoint seeds `H₁, H₂`,
the Knill of the causal DAG of evolution on the disjoint union splits:

  `knillEulerScaled (causalDAG sys (H₁ ++ H₂) d)`
    `= knillEulerScaled (causalDAG sys H₁ d) + knillEulerScaled (causalDAG sys H₂ d)`

Mathematical content (the obligation):

  (a) `allMatches r (H₁ ++ H₂) = allMatches r H₁ ++ allMatches r H₂`
      (no cross-component matches because LHS has only one edge and
      vertex-disjointness prevents cross-component edges).
  (b) Fresh-vertex offsets, when allocated globally for `H₁ ++ H₂`,
      can be rebased to local offsets per component without altering
      the causal-DAG Knill (just relabeling — closes via K2).
  (c) Per-step state on the disjoint union decomposes accordingly.

Engine-semantics obligation; similar in scope to the H9 step lemma.
Stated as a Prop. -/
def E1_EngineCommutesWithDisjointUnion : Prop :=
  ∀ (r : ExecRule) (_h : SingleEdgeLHS r) (H₁ H₂ : ExecHG ℕ)
    (_hd : VertexDisjoint H₁ H₂) (d : Nat),
    knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ (H₁ ++ H₂) d)
      = knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ H₁ d)
      + knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ H₂ d)

/-! ## Section H: composition — disjoint-seed per-edge additivity -/

/-- A "two-disjoint-edge" seed is a hypergraph that is the disjoint
union of two single-edge hypergraphs. -/
structure TwoDisjointEdges where
  e₁ : ExecHG ℕ
  e₂ : ExecHG ℕ
  e₁_single : e₁.length = 1
  e₂_single : e₂.length = 1
  disjoint : VertexDisjoint e₁ e₂

/-- The combined seed. -/
def TwoDisjointEdges.seed (t : TwoDisjointEdges) : ExecHG ℕ := t.e₁ ++ t.e₂

/-- **Per-edge additivity for two-disjoint-edge seeds**, derived from
the engine-decomposition obligation (E1) plus the K2 relabeling
invariance.

Given E1 and K2, for any single-edge-LHS rule, the Knill of the
causal-DAG evolution on a two-disjoint-edge seed equals the sum of
the per-component evolutions. -/
theorem two_disjoint_edge_per_edge_additivity
    (engine_decomp : E1_EngineCommutesWithDisjointUnion) :
    ∀ (r : ExecRule) (h : SingleEdgeLHS r) (t : TwoDisjointEdges) (d : Nat),
      knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.seed d)
        = knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.e₁ d)
        + knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ t.e₂ d) := by
  intro r h t d
  exact engine_decomp r h t.e₁ t.e₂ t.disjoint d

/-! ## Section I: BBH target

BBH initial data is constructed as 7 disjoint edges; once E1 is
proved, the `7×` BBH multiplier becomes a real theorem instead of
finite native_decide.

The actual BBH seed lives in `BBHInitialData.lean`. Its disjointness
characterization (currently empirical) would feed into this framework.
-/

/-- **Target universal theorem for BBH** (conditional on E1 + BBH
disjointness characterization).

Once `EngineCommutesWithDisjointUnion` is proved AND the BBH seed
is shown to be 7-disjoint-edge, this universal-in-d theorem replaces
the finite `native_decide` verifications across `BBHCurvatureEvolution.lean`,
`BBHDeepEvolution.lean`, `BBHMetricTensor.lean`, etc. -/
def BBH_per_edge_universal_target : Prop :=
  ∀ (r : ExecRule) (_h : SingleEdgeLHS r) (d : Nat) (single_edge : ExecHG ℕ)
    (_hsingle : single_edge.length = 1),
    -- Once BBH disjointness is established:
    -- knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ BBHseed d)
    --   = 7 * knillEulerScaled (causalDAGOfEvolution ⟨[r]⟩ single_edge d)
    True  -- Placeholder pending BBH disjointness link

/-! ## What this delivers

**Proved unconditionally in this module:**

  * `VertexDisjoint` predicate + symmetry.
  * `mem_vertexList_append`: vertexList membership decomposes over `++`.
  * `execAdj_append`: adjacency in `H₁ ++ H₂` is the OR of adjacencies
    in the components.
  * `execAdj_cross_H1_zero` / `execAdj_cross_H2_zero`: under vertex-
    disjointness, cross-component adjacencies are false. These are the
    structural sub-lemmas needed for K1.

**Stated as named Prop obligations (no sorry, no decide):**

  * `K1_KnillAdditiveOverDisjointUnion`: Knill additivity on disjoint
    union. Combinatorial; closing it requires the foldr-split chain
    over `vertexList`.
  * `K2_KnillRelabelingInvariant`: Knill invariance under vertex
    bijection.
  * `E1_EngineCommutesWithDisjointUnion`: engine commutes with disjoint
    union for single-edge-LHS rules. Engine-semantics.

**Conditional theorem proved here:**

  * `two_disjoint_edge_per_edge_additivity`: given E1, the two-disjoint-
    edge per-edge additivity is immediate.

**Path to closure:**

  1. Close K1 (combinatorial): ~100-200 lines Lean, well-scoped.
  2. Close K2 (relabeling invariance): ~50 lines, structural.
  3. Close E1 (engine-decomposition): multi-session, similar scope to
     the H9 step lemma.
  4. Establish BBH disjointness link: characterize `bbhInitial` as
     `IsKDisjointEdges 7`.

With K1 + K2 + E1 + BBH-disjointness, the universal `7×` BBH multiplier
follows, replacing all finite native_decide checks across the BBH
modules. The framework here makes the dependency chain explicit.
-/

end PerEdgeAdditivityFramework
end InfraFormalization
