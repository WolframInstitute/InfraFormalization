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

These theorems are statements about the function type
`DHyp V → V → V → ℝ`: it has more than one element. They do not
mention arXiv:2004.14810. The finding about the paper, that Def 15
(`papers/gorard_2004.14810.txt` line 786) gives no construction of
`g^{ab}` from the hypergraph, is a
reading of the paper text and is not a Lean theorem.

**Sharpening (2026-05, macro-observer note; see
`notes/phajek_macro_observer_notes.txt`).** The non-uniqueness is not
merely "many constructions are possible" — it is unavoidable in
principle. A graph determines a *moduli of Riemannian manifolds*, not
one manifold. By the Nash embedding theorem every Riemannian manifold
embeds isometrically in some `ℝⁿ`, so the assumption "graph
shortest-path distance = geodesic distance of the assigned metric" is
satisfied by a positive-dimensional family of manifolds. Discrete
invariants (clique size → embedding-dimension bound, discrete
curvature → curvature constraints, clique complex → topology) act as
obstructions narrowing that moduli but never collapse it to a point
without large-scale / Gromov coarse-graining data. The two-element
witness below is the minimal Lean expression of a phenomenon that is
genuinely a positive-dimensional moduli.

**Sharpening (2026-05-30, paclet-design note).** The moduli observation
is now structural in PHAJEK's `SyntheticInfrageometry` paclet:
primitive synthetic operations come as one-parameter families of
inequivalent definitions, exposed via an explicit `Method` argument.
- `InfraPerpendicularQ` admits Schoenberg, Centroid (balanced-feet
  test), and four-corner-wedge methods
  (`resources/SyntheticInfrageometry/Kernel/InfraEquality.wl`).
- `FindInfraShellCenter` admits bisector, chord, and equidistant
  methods (`resources/SyntheticInfrageometry/Kernel/InfraShell.wl`).
- `FindLineStructure` / `InfraLineStructure` treats a line as a
  *consistent path system*, with multiple T1–T5 methods and an
  explicit tie-break study
  (`resources/SyntheticInfrageometry/Kernel/InfraLineStructure.wl`).

These primitives realize F1 at the synthetic level: every basic
geometric construct admits a moduli of inequivalent realisations.
JGORARD's `g^{ab}` is not the only object without a canonical
definition — perpendicularity, the centre of a shell, and the notion
of a line are all of the same kind. Any derivation that silently fixes
one representative (as G1 Def 15 does for the metric) is choosing a
point in a moduli; competing equally-valid derivations exist on the
alternative methods.
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
construction. -/
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
-/
theorem metric_construction_is_never_unique
    (V : Type*) [Inhabited V] (Φ : MetricConstruction V) :
    ∃ Ψ : MetricConstruction V, Ψ ≠ Φ := by
  refine ⟨(fun H u v => Φ H u v + 1), ?_⟩
  intro h
  have hpt : Φ ⟨∅⟩ default default + 1 = Φ ⟨∅⟩ default default := by
    have := congrFun (congrFun (congrFun h ⟨∅⟩) default) default
    exact this
  linarith

/-- **F1 in impossibility form.** No element of `MetricConstruction V`
is equal to every element of `MetricConstruction V`. -/
theorem no_canonical_metric_from_hypergraph_alone
    (V : Type*) [Inhabited V] :
    ¬ ∃ (Φ : MetricConstruction V),
      ∀ Ψ : MetricConstruction V, Ψ = Φ := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨Ψ, hne⟩ := metric_construction_is_never_unique V Φ
  exact hne (hΦ Ψ)

/-- For an injective `S : MetricConstruction V → ℝ` and any
construction `Φ`, some construction `Ψ` has `S Ψ ≠ S Φ`. -/
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
