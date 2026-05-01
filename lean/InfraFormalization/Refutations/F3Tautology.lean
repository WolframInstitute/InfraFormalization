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

**The structural issue.** Eq 87 *defines* "asymptotic dim preservation"
as the Euler-Lagrange equation. Saying "asymptotic dim preservation
⇒ EL-equation" is saying "X ⇒ X". JGORARD's abstract makes this
sound like a substantive derivation; it is not. The only non-trivial
content in §3.3 is Eq 88 (the limit "becomes" an integral), which
depends on an undefined "continuum limit" notion and an unspecified
"weak ergodicity" hypothesis — see F5 and `notes/limit_toolkit.md`
for the causal-set-theory status of this convergence.

**What this file does.** Formalises the tautological implication at
the level of an abstract action / variational operator. We do not
need the actual discrete metric tensor (which is F1: never
constructed); we just need to name the functional form of the
implication.
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

/-- **F3 as a theorem.** In JGORARD's §3.3, "asymptotic dim
preservation" is *defined* to be the vanishing of the action's
variation. The Euler-Lagrange equation of the same action is the
same condition. The two are therefore equivalent by definitional
unfolding alone.

Any implication of the form "asymptotic dim preservation ⇒
Euler-Lagrange equations of the action" is thus logically trivial;
all non-trivial content must come from elsewhere — specifically,
from proving the action converges to the Einstein-Hilbert action
(Eq 88), which is separately flawed (see F5). -/
theorem gorard_dim_preservation_is_euler_lagrange
    {M : Type*} (P : VariationalSetup M) (g : M) :
    AsymptoticDimPreservation P g ↔ EulerLagrange P g :=
  Iff.rfl

/-- **F3 in equation-chain form.** Given any variational setup and
target configuration `g`, the implication

  AsymptoticDimPreservation P g → EulerLagrange P g

holds by definition — no structural content about `P` or `g` is
used. -/
theorem gorard_dim_preservation_trivially_implies_euler_lagrange
    {M : Type*} (P : VariationalSetup M) (g : M) :
    AsymptoticDimPreservation P g → EulerLagrange P g :=
  id

/-- **Contextual consequence.** Every instance of JGORARD's §3.3
argument (whatever the interpretation of M and of `variation`) is
of this form. In particular, even a JGORARD-style chain of the form

  (conservative + causal-invariant + asymp.-dim.-pres.) ⇒ vacuum EFE

reduces, on the "asymp.-dim.-pres. ⇒ vacuum EFE" leg, to
definitional equivalence: having stipulated that the variation
vanishes, stating the Euler-Lagrange equation (= vanishing variation)
is re-stating the same fact. The Einstein field equations enter the
picture only via the *identification* of the discrete action's
limit with the Einstein-Hilbert action (JGORARD Eq 88), which is
unproven. -/
theorem gorard_section_3_3_contentless
    {M : Type*} (P : VariationalSetup M) (g : M)
    (_conservative : True) (_causal_invariant : True)
    (hpres : AsymptoticDimPreservation P g) :
    EulerLagrange P g := hpres

end Refutations
end InfraFormalization
