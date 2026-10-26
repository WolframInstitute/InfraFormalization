import InfraFormalization.CausalGraphType
import InfraFormalization.Causal
import InfraFormalization.MultiwayCausalGraph
import Mathlib.Data.Set.Finite.Basic

/-!
Causal-set axioms for causal graphs.

This module defines `CausalSetStructure C prec`: `prec` is reflexive,
antisymmetric, transitive and locally finite (Bombelli, Lee, Meyer, Sorkin).
It proves that the precedence relation `causallyPrecedes` of a finite
`CausalGraph V` satisfies these axioms when antisymmetry is assumed, and
states the same for the causal graph of a `MultiwayCausalGraph`.
`FINDINGS.md` F6 compares the argument of G3 (arXiv:2102.09363) with the
Benincasa–Dowker construction; this module does not formalise that
comparison.
-/

namespace InfraFormalization

/-- The causal-set axioms for `_prec`: reflexivity, antisymmetry,
transitivity, and local finiteness, stated as containment of each interval
`{z | x ≺ z ≺ y}` in some finite set. -/
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

/-- `G.causallyPrecedes`, under a second name. -/
def CausalGraph.causalSetPrec {V : Type*} [Fintype V] [DecidableEq V]
    (G : CausalGraph V) : V → V → Prop :=
  fun u w => G.causallyPrecedes u w

/-- For a finite causal graph whose precedence relation is antisymmetric,
`causalSetPrec` satisfies `CausalSetStructure`. Antisymmetry is a
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

/-- For a `MultiwayCausalGraph` whose causal precedence relation is
antisymmetric, that relation satisfies `CausalSetStructure`. This is
`causalGraph_causalSet_axioms` applied to `M.causal`. -/
theorem multiwayCausalGraph_has_causalSet_core
    {V : Type*} [Fintype V] [DecidableEq V]
    {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]
    (M : MultiwayCausalGraph P V E)
    (hantisymm : ∀ u w, M.causal.causalSetPrec u w
      → M.causal.causalSetPrec w u → u = w) :
    CausalSetStructure E M.causal.causalSetPrec :=
  causalGraph_causalSet_axioms M.causal hantisymm

end InfraFormalization
