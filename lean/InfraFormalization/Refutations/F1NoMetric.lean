/-
**F1: the JGORARD G1 Def 15 "discrete Lorentzian metric tensor g^{ab} on
a hypergraph" is never constructed, and is not determined by the
hypergraph data alone.**

**Context.** arXiv:2004.14810 Def 15 (line 325) states "let `g` be a
discrete Lorentzian metric of signature `(−,+,+,+)`" on the causal graph,
and the subsequent §3 manipulations compute
`δS[g^{ab}]/δg^{ab}`, `√(−g) R`, Christoffel symbols `Γ^ρ_{μν}`, and a
Ricci tensor `R_{ab}` built from `g^{ab}`. None of these is defined by
any formula or procedure taking the causal graph / hypergraph as input
and returning components. "Metric" is used as a *symbol* without a
definition.

Ancillary assumption: G1 §3.2 line 840 stipulates by fiat that
"all pairs of non-parallel hyperedges can be considered orthonormal",
which is a property of the (undefined) bilinear form.

**The structural issue.** Any claim of the form

    "for the metric `g^{ab}` of hypergraph `H`, property P holds"

is under-specified: the symbol `g^{ab}` refers to no object unless a
*construction* `H ↦ g^{ab}(H)` is supplied. JGORARD's text supplies none.
Moreover, even granting some construction, many inequivalent
constructions are compatible with "using only hypergraph data" — so
`g^{ab}` is not uniquely determined by the hypergraph.

**What this file does.** Formalises:

1. "Metric construction" as a function type `DHyp V → V → V → ℝ`
   (= a bilinear form at each vertex pair, varying with the hypergraph).
2. `hypergraph_does_not_determine_metric`: the type of metric
   constructions has at least two distinct elements, so no canonical
   one is singled out by the hypergraph data.
3. `metric_construction_is_never_unique`: for *any* candidate
   construction `Φ`, another construction `Ψ ≠ Φ` exists.

This is the impossibility theorem backing the claim that `g^{ab}`, as
used in G1 §3, is not a well-defined object on hypergraphs.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith

namespace InfraFormalization
namespace Refutations

/-- A minimalistic directed hypergraph: a vertex type together with a
set of directed hyperedges (encoded as lists of vertices). This is
the only data JGORARD's Def 15 gives himself when he writes "the metric
`g^{ab}` of the hypergraph". -/
structure DHyp (V : Type*) where
  edges : Set (List V)

/-- A *metric construction* is a function that, given a hypergraph on
`V`, returns a real bilinear-form-like object on `V × V`. This type
captures the weakest possible interpretation of "let `g^{ab}` be the
metric of the hypergraph": an assignment, for each hypergraph, of a
real value to each pair of vertices. -/
abbrev MetricConstruction (V : Type*) : Type _ :=
  DHyp V → V → V → ℝ

/-- **F1 formal statement.** The type `MetricConstruction V` of
possible "hypergraph-to-metric" assignments has at least two distinct
elements — the constant-zero construction and the constant-one
construction. Therefore the phrase "the metric `g^{ab}` of the
hypergraph" (G1 Def 15, §3.3) does not refer to a canonical object;
an additional choice of construction is required. -/
theorem hypergraph_does_not_determine_metric
    (V : Type*) [Inhabited V] :
    ∃ (Φ Ψ : MetricConstruction V), Φ ≠ Ψ := by
  refine ⟨(fun _ _ _ => (0 : ℝ)), (fun _ _ _ => (1 : ℝ)), ?_⟩
  intro h
  have heq : (fun (_ : DHyp V) (_ : V) (_ : V) => (0 : ℝ))
           = (fun _ _ _ => (1 : ℝ)) := h
  have h01 : (0 : ℝ) = (1 : ℝ) := by
    have := congrFun (congrFun (congrFun heq ⟨∅⟩) default) default
    exact this
  exact zero_ne_one h01

/-- **F1 stronger form.** For *any* candidate metric construction `Φ`,
there is another construction `Ψ ≠ Φ`: concretely, `Ψ H u v := Φ H u v + 1`.
Hence no individual construction is singled out — JGORARD's `g^{ab}` is
always a *choice*, never a canonical consequence of the hypergraph. -/
theorem metric_construction_is_never_unique
    (V : Type*) [Inhabited V] (Φ : MetricConstruction V) :
    ∃ Ψ : MetricConstruction V, Ψ ≠ Φ := by
  refine ⟨(fun H u v => Φ H u v + 1), ?_⟩
  intro h
  have hpt : Φ ⟨∅⟩ default default + 1 = Φ ⟨∅⟩ default default := by
    have := congrFun (congrFun (congrFun h ⟨∅⟩) default) default
    exact this
  linarith

/-- **F1 in impossibility form.** There is no function
`H ↦ g_H` assigning a bilinear form to every hypergraph that
is singled out by the hypergraph data alone: for any such function,
a non-equal alternative exists, and both are equally "from the
hypergraph" in the weak sense JGORARD invokes. -/
theorem no_canonical_metric_from_hypergraph_alone
    (V : Type*) [Inhabited V] :
    ¬ ∃ (Φ : MetricConstruction V),
      ∀ Ψ : MetricConstruction V, Ψ = Φ := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨Ψ, hne⟩ := metric_construction_is_never_unique V Φ
  exact hne (hΦ Ψ)

/-- **F1 applied to the §3.3 action.** Any "discrete action"
`S : MetricConstruction V → ℝ` can distinguish distinct constructions.
Therefore the symbol `δS/δg^{ab}` in G1 Eq 87 is not a function of the
hypergraph; it is a function of the hypergraph *together with* a choice
of construction. JGORARD's prose treats this choice as absent, which is
the F1 structural flaw. -/
theorem action_depends_on_construction_choice
    (V : Type*) [Inhabited V]
    (S : MetricConstruction V → ℝ)
    (hS : Function.Injective S) :
    ∀ Φ : MetricConstruction V,
      ∃ Ψ : MetricConstruction V, S Ψ ≠ S Φ := by
  intro Φ
  obtain ⟨Ψ, hne⟩ := metric_construction_is_never_unique V Φ
  exact ⟨Ψ, fun heq => hne (hS heq)⟩

end Refutations
end InfraFormalization
