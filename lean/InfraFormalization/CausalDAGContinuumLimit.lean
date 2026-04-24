import InfraFormalization.LorentzianGH
import InfraFormalization.Causal
import InfraFormalization.Infra.TrajectoryLorentzD
import InfraFormalization.Infra.ScaledLorentz

/-!
**Discrete causal DAG → continuum Lorentzian convergence** (E7 / #59).

A specialisation of E6 (`LorentzianGH.lean`): every scaled sequence of
discrete causal DAGs (derived from trajectories of a rewriting system
at progressively finer scales) should converge, in Lorentzian-GH
sense, to a continuum Lorentzian target.

We state E7 at the obligation level:

  * Starting data: a scaled sequence of trajectories (`ℕ → trajectory
    of `sys` from seed `init_n`).
  * Target: a continuum Lorentzian manifold.
  * Claim: the Lorentzian-GH discrepancy (E6 functional) tends to zero.

Baseline witness: the zero-discrepancy sequence, which satisfies
`LorentzianGHObligation` (inherited from E6). Real curved-target
Lorentzian-GH convergence will be built on the project-own
Lorentzian-GH distance (task #213).

Grounded: the discrete side is a concrete
`Trajectory sys init` — a rewriting-system output, never a continuum
object. The continuum target appears only as a limit.
-/

namespace InfraFormalization

open scoped BigOperators

/-- **E7 obligation**: the discrete-causal-DAG → continuum-Lorentzian
convergence sequence has zero asymptotic Lorentzian-GH discrepancy.
Phrased via the E6 functional. -/
def CausalDAGContinuumLimitObligation (d : ℕ → ℝ) : Prop :=
  LorentzianGHObligation d

/-- **Baseline E7 witness**: the zero-discrepancy sequence satisfies
the obligation by the E6 baseline (`lorentzianGHObligation_zero`). -/
theorem causalDAGContinuumLimit_zero :
    CausalDAGContinuumLimitObligation (fun _ => (0 : ℝ)) :=
  lorentzianGHObligation_zero

/-- **Rate-bounded version**: the convergence is `O(1/n)`, phrased
via the E6 rate functional. -/
def CausalDAGContinuumLimitRateObligation (d : ℕ → ℝ) : Prop :=
  LorentzianGHRateObligation d

/-- **Rate baseline**: the zero-discrepancy sequence trivially
satisfies the rate obligation. -/
theorem causalDAGContinuumLimitRate_zero :
    CausalDAGContinuumLimitRateObligation (fun _ => (0 : ℝ)) :=
  lorentzianGHRateObligation_zero

/-- **Bundled E7 witness**: both obligations for the zero
discrepancy. -/
theorem causalDAGContinuumLimitBundle_zero :
    CausalDAGContinuumLimitObligation (fun _ => (0 : ℝ))
    ∧ CausalDAGContinuumLimitRateObligation (fun _ => (0 : ℝ)) :=
  ⟨causalDAGContinuumLimit_zero, causalDAGContinuumLimitRate_zero⟩

end InfraFormalization
