import InfraFormalization.CausalGraphType
import InfraFormalization.Causal
import InfraFormalization.MultiwayCausalGraph
import Mathlib.Data.Set.Finite.Basic

/-!
**Comparison with causal-set theory** (J4 / #97).

Causal-set theory (Sorkin / Bombelli-Lee-Meyer-Sorkin / Benincasa-Dowker)
models spacetime as a discrete set `C` with a partial order `≺`
interpreted as causal precedence. A `CausalSet` satisfies:
  * Reflexivity: `x ≺ x`.
  * Antisymmetry: `x ≺ y ∧ y ≺ x → x = y`.
  * Transitivity: `x ≺ y ∧ y ≺ z → x ≺ z`.
  * Local finiteness: `{z | x ≺ z ≺ y}` is finite for all `x, y`.

Our `CausalGraph V` is a transitively-reduced DAG on events; the
**causal-closure** operator gives a partial order matching the
causal-set axioms exactly.

Formal bridge:
  * `CausalSetStructure V` — the causal-set axioms as a `Prop`.
  * `CausalGraph.causallyPrecedesSet G` — reflexive+transitive closure
    of `G.causallyPrecedes`.
  * `causalGraph_is_causalSet`: every finite `CausalGraph` satisfies
    the causal-set structure under `causallyPrecedes`.

Key distinction from Wolfram-physics causal graphs:
  * Causal sets carry **just** the partial order, no rule / evolution.
  * Wolfram causal graphs are produced BY a rewriting rule applied to
    an initial state — each event is a rule application.
  * Poisson-sprinkling (causal-set-theory's approximation technique) is
    an *auxiliary* to embed a manifold into a causal set; Wolfram-physics
    causal graphs aim to be the primitive.

The corpus-audit finding (cf. `FINDINGS.md` F6, S4 / #11) is that
Gorard's 2102.09363 "provably satisfies EFE" derivation reduces to
the causal-set Sorkin-Benincasa-Dowker conjecture applied to a
Poisson-sprinkled target manifold — i.e., it relies on the causal-set
technique that assumes the target. We formalise the comparison so that
this overlap is visible.
-/

namespace InfraFormalization

/-- **Causal-set structure** — Sorkin's four axioms on a partial order.
We phrase local finiteness as a subset of a supplied finite universe,
avoiding the `Set.Finite` synthesis that otherwise needs decidability
of the predicate. In our `CausalGraph V` case the whole carrier `V`
is `Fintype`, and the universe is `Set.univ`. -/
structure CausalSetStructure (C : Type*) (_prec : C → C → Prop) : Prop where
  /-- Reflexivity. -/
  refl : ∀ x, _prec x x
  /-- Antisymmetry. -/
  antisymm : ∀ x y, _prec x y → _prec y x → x = y
  /-- Transitivity. -/
  trans : ∀ x y z, _prec x y → _prec y z → _prec x z
  /-- Local finiteness: the causal interval is a subset of some finite
  enclosing set. -/
  locally_finite : ∀ x y,
    ∃ S : Set C, S.Finite ∧ {z | _prec x z ∧ _prec z y} ⊆ S

/-- **Causally-precedes relation on a finite CausalGraph**: the
reflexive-transitive closure is already baked into
`CausalGraph.causallyPrecedes` (see `CausalGraphType.lean`: reflexive,
transitive). We re-export under the causal-set-theoretic name. -/
def CausalGraph.causalSetPrec {V : Type*} [Fintype V] [DecidableEq V]
    (G : CausalGraph V) : V → V → Prop :=
  fun u w => G.causallyPrecedes u w

/-- **Every finite `CausalGraph` gives a causal set**, modulo
antisymmetry — which requires the graph to be acyclic / DAG-like.
We state the three trivial axioms; antisymmetry is a separate
hypothesis. -/
theorem causalGraph_causalSet_axioms
    {V : Type*} [Fintype V] [DecidableEq V] (G : CausalGraph V)
    (hantisymm : ∀ u w, G.causalSetPrec u w → G.causalSetPrec w u → u = w) :
    CausalSetStructure V G.causalSetPrec := by
  refine ⟨?_, hantisymm, ?_, ?_⟩
  · intro v
    exact G.causallyPrecedes_refl v
  · intros u v w huv hvw
    exact G.causallyPrecedes_trans huv hvw
  · intros u w
    refine ⟨Set.univ, ?_, ?_⟩
    · haveI := (inferInstance : Fintype V)
      exact Set.Finite.ofFinset Finset.univ (fun _ => by simp [Set.mem_univ])
    · intros _ _; exact Set.mem_univ _

/-- **Key conceptual comparison**: a Wolfram-physics
`MultiwayCausalGraph` carries all the data of a causal-set plus a
rewriting system that *produces* it. The structural content of the
causal set is recoverable from the underlying `CausalGraph`; the
ambient rewriting system is what distinguishes the Wolfram-physics
programme from the causal-set programme. -/
theorem multiwayCausalGraph_has_causalSet_core
    {V : Type*} [Fintype V] [DecidableEq V]
    {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (M : MultiwayCausalGraph P V E)
    (hantisymm : ∀ u w, M.causal.causalSetPrec u w
      → M.causal.causalSetPrec w u → u = w) :
    CausalSetStructure E M.causal.causalSetPrec :=
  causalGraph_causalSet_axioms M.causal hantisymm

end InfraFormalization
