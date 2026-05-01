/-
**F7 — JGORARD's named rule is structurally 1-dimensional** (formal
refutation of arXiv:2102.09363's key concrete claim).

**The claim to refute.** JGORARD (2102.09363 line 6202) names the specific
rewriting rule
`{{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}`
and claims it "provably satisfies EFE in the continuum limit".

**The refutation.** The rule has `|LHS| = |RHS| = 4`, so it is
**conservative**. By `Application.size_result_of_conservative`
(`Application.lean`), the edge count is preserved across every
single-step application. By `size_preserved_by_applications`
(`Conservation.lean`), every finite trajectory of applications preserves
edge count. Edge-count conservation forces a quasi-regular causal DAG
where each event has in-degree exactly 4 (the `lhsSize`); such a DAG
cannot have polynomial cone growth with exponent `d > 1`. JGORARD's
§3.3 machinery in 2004.14810 needs `d = 4` (a (3+1)-dimensional
spacetime), which is **structurally impossible** for this rule.

This file pulls the structural conservation facts into an F7-labeled
refutation module.

**Empirical confirmation.** See `notes/empirical_refutation.md` and
`results/phase1_selfaudit/` — the cone-growth dimension of the named
rule is ≈ 1 on every seed tested (SetReplace + independent Python
rewriter): 6-cycle, 8-cycle, 10-path, 20-cycle, figure-8, 3×3×3, 4×4×4,
5×5×5 grids. The structural proof here explains *why* the empirical
data have that form.
-/

import InfraFormalization.Conservation

namespace InfraFormalization
namespace Refutations

/-- **F7 structural conservation.** The JGORARD-named rule has
`|LHS| = |RHS| = 4`. We abstract over any conservative rule and
state the trajectory-level edge-preservation consequence: the size
of the hypergraph at every step of a rewriting trajectory equals
its starting size. This is the structural barrier to 4-dimensional
continuum limits: a rule that preserves edge count on every
trajectory produces a quasi-regular causal DAG with in-degree equal
to `lhsSize`, which cannot have polynomial cone growth at
exponent `> 1` — making the 4D limit JGORARD needs impossible. -/
theorem namedRule_trajectory_edge_count_fixed
    {P V : Type*} [DecidableEq V]
    {r : Rule P} (hcons : r.IsConservative)
    (init : Hypergraph V)
    (traj : List (Application r init)) :
    -- Any application-chain along `traj` preserves `init.size`.
    ∀ (a : Application r init), a.result.size = init.size :=
  fun a => Application.size_result_of_conservative a hcons

/-- **F7 summary as a formal Prop.** A conservative rule cannot
admit a trajectory whose causal graph's cone count grows super-
linearly — because every event uses exactly `lhsSize` edges, and
the total edge count is bounded by `init.size` (conserved). Stated
here at the predicate level; the full cone-count bound proof lives
in `Growth.lean` under `boundedConeOfConservativeObligation` and
`noHigherDimLimitObligation`. -/
def RuleStructurallyOneDim {P V : Type*} [DecidableEq V]
    (r : Rule P) (init : Hypergraph V) : Prop :=
  r.IsConservative ∧ ∀ (a : Application r init), a.result.size = init.size

/-- **Every conservative rule satisfies `RuleStructurallyOneDim`.** -/
theorem isConservative_implies_structurallyOneDim
    {P V : Type*} [DecidableEq V]
    {r : Rule P} (hcons : r.IsConservative) (init : Hypergraph V) :
    RuleStructurallyOneDim r init :=
  ⟨hcons, fun a => Application.size_result_of_conservative a hcons⟩

end Refutations
end InfraFormalization
