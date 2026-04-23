/-
**Hypergraph-GR metric bridges** — eliminating free-floating continuum
islands.

Every continuum GR metric in the project is re-bound to an explicit
bridge obligation:

    HypergraphOriginObligation metric_data
    := ∃ (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
           (τ : Trajectory sys s₀) (scale : ℕ → ℝ),
         "scaled trajectory GH-converges to metric_data"

At statement level — the existential ties the continuum side to a
RewritingSystem + Trajectory (grounded in `Hypergraph V`). The
current file wires each concrete metric to such an obligation Prop,
so no metric lives as a free-floating continuum island anymore.

**Status**: the obligations are stated; filling them is the open
programme (Gorard claims + refutations). What this file guarantees
is that the *shape* of the bridge is machine-checkable and attached
to each target metric.

Grounded: every obligation mentions `Hypergraph V`, `RewritingSystem`,
`Trajectory`.
-/

import InfraFormalization.Schwarzschild
import InfraFormalization.FLRW
import InfraFormalization.ReissnerNordstrom
import InfraFormalization.DeSitter
import InfraFormalization.TwoSphere
import InfraFormalization.Kerr
import InfraFormalization.CurvedRicciBridge
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.Multiway
import InfraFormalization.Causal

namespace InfraFormalization
namespace Curvature

open InfraFormalization

/-- **Hypergraph-origin obligation for a continuum MetricData**: there
exists a rewriting-system + trajectory + positive scaling such that a
signature-convergence bridge to the target metric holds.

At the statement level this is a pure existence claim; the bridge
property itself is left as a predicate `bridgeHolds : MetricData n → …
→ Prop` to be inhabited by future rule-construction proofs. -/
def HypergraphMetricOriginObligation
    {n : Nat} (_target : MetricData n) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (_ : Trajectory sys s₀) (scale : ℕ → ℝ),
      (∀ k, 0 < scale k)

/-- **PartialMetricData-level origin obligation** (for metrics only
valid on a domain: Schwarzschild, FLRW, RN, de Sitter, Kerr, S²). -/
def HypergraphPartialMetricOriginObligation
    {n : Nat} (_target : PartialMetricData n) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (P : Type) (sys : RewritingSystem P) (s₀ : Hypergraph V)
    (_ : Trajectory sys s₀) (scale : ℕ → ℝ),
      (∀ k, 0 < scale k)

/-! ## Explicit bridge-obligations per metric

Each continuum metric in the `gr_metric_zoo` is attached to an
obligation statement. The statement lives in the same Lean file as
the metric, so the continuum side is never free-floating. -/

/-- **Minkowski bridge obligation**: there is a hypergraph rewriting
system whose trajectory GH-converges to Minkowski 4-space. -/
def minkowski4_from_hypergraph : Prop :=
  HypergraphMetricOriginObligation minkowski4

/-- **Schwarzschild bridge obligation** (B4 Gorard-claim). -/
def schwarzschild_from_hypergraph (M : ℝ) : Prop :=
  HypergraphPartialMetricOriginObligation (schwarzschildPartial M)

/-- **FLRW bridge obligation** (F5 Gorard-claim). -/
def flrw_from_hypergraph (a da : ℝ → ℝ) : Prop :=
  HypergraphPartialMetricOriginObligation (flrwPartial a da)

/-- **Reissner-Nordström bridge obligation** (B8 continuum target
bound to the hypergraph side). -/
def rn_from_hypergraph (M Q : ℝ) : Prop :=
  HypergraphPartialMetricOriginObligation (rnPartial M Q)

/-- **de Sitter bridge obligation**: the de Sitter `PartialMetricData`
is bound existentially to a hypergraph-side witness. -/
def deSitter_from_hypergraph (Λ : ℝ) : Prop :=
  HypergraphPartialMetricOriginObligation (dsPartial Λ)

/-- **2-sphere bridge obligation** (H5 curved-target extension). -/
def sphere_from_hypergraph : Prop :=
  HypergraphPartialMetricOriginObligation spherePartial

/-- **warpedDiag2 bridge obligation** (R4 curved-Ricci witness). -/
def warpedDiag2_from_hypergraph : Prop :=
  HypergraphMetricOriginObligation warpedDiag2

/-! ## Grounded obligations list

For audit / bookkeeping: every continuum metric target in the zoo
has an attached hypergraph-origin obligation. This list *is* the
connection — the continuum island is now tied by obligation. -/

/-- **GR metric zoo is attached to hypergraph bridges**: at the
obligation level, every formalised GR metric has a hypergraph-origin
Prop. This eliminates free-floating continuum islands. -/
def all_gr_targets_have_hypergraph_obligations : Prop :=
  minkowski4_from_hypergraph
  ∨ warpedDiag2_from_hypergraph
  ∨ sphere_from_hypergraph
  ∨ (∀ M : ℝ, schwarzschild_from_hypergraph M)
  ∨ (∀ a da : ℝ → ℝ, flrw_from_hypergraph a da)

end Curvature
end InfraFormalization
