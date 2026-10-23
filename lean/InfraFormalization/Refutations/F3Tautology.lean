/-
**F3: the JGORARD §3.3 "asymptotic dim preservation ⇒ Einstein
equations" argument is a tautology.**

**Context.** arXiv:2004.14810 §3.3 (equations 86–91) proceeds as
follows:

  Eq 86:  S[g^ab] := Σ d μ_g · R                  (discrete "action")
  Eq 87:  "asymptotic dim preservation" := δS/δg^ab → 0
  Eq 88:  "in the continuum limit, S becomes ∫ d⁴x √(−g) R"
  Eq 89:  L_G := √(−g) R                          (Einstein-Hilbert density)
  Eq 90:  δS_EH/δg^ab = √(−g) (R_ab − ½R g_ab)
  Eq 91:  R_ab − ½R g_ab = 0                       (vacuum Einstein)

JGORARD summarises: "for any set of hypergraph updating rules that are
both causal-invariant and asymptotically dimensionality preserving
… the limiting manifold must satisfy the vacuum Einstein field
equations."

**Paper text.** `papers/gorard_2004.14810.txt` lines 2203-2206 state
that asymptotic dimensionality preservation "corresponds to the
statement" that `δS/δg^{ab} → 0` (Eq 87). The Euler-Lagrange equation
of `S` is the same condition. The step from there to the vacuum
Einstein equations rests on Eq 88, the claim that the sum becomes the
Einstein-Hilbert integral (see F5).

**What this file proves.** The file encodes both conditions as
`P.variation g = 0` and proves they are equivalent. The equivalence
holds by `Iff.rfl` because the two definitions have the same body. The
reading of Eq 87 that justifies this encoding is a reading of the
paper text and is not a Lean theorem.
-/

import Mathlib.Data.Real.Basic

namespace InfraFormalization
namespace Refutations

/-- An abstract variational setup: a type `M` of "metric-like
configurations" and a `variation` operator that, at each `g : M`,
returns a real number interpreted as the `δS/δg` residue. -/
structure VariationalSetup (M : Type*) where
  variation : M → ℝ

/-- JGORARD's `AsymptoticDimPreservation` (from arXiv:2004.14810
Eq 87): the condition that the variation of the action vanishes. -/
def AsymptoticDimPreservation {M : Type*} (P : VariationalSetup M) (g : M) : Prop :=
  P.variation g = 0

/-- The Euler-Lagrange equation for the same action at the same
point: the condition that the variation vanishes. -/
def EulerLagrange {M : Type*} (P : VariationalSetup M) (g : M) : Prop :=
  P.variation g = 0

/-- `AsymptoticDimPreservation P g` and `EulerLagrange P g` are
equivalent, by `Iff.rfl`: both are defined as `P.variation g = 0`. -/
theorem asymptoticDimPreservation_iff_eulerLagrange
    {M : Type*} (P : VariationalSetup M) (g : M) :
    AsymptoticDimPreservation P g ↔ EulerLagrange P g :=
  Iff.rfl

end Refutations
end InfraFormalization
