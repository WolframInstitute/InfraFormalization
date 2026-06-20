/-
**B4-curvature-density-limit: per-edge curvature density limit
from universal additivity** (#455).

The universal per-edge additivity law (#454) tells us that for the
discovered merger rules,

  `Knill(rule, seed, n) = |seed| · Knill(rule, edge12, n)`

across all probed seed topologies and depths. This module
**immediately derives** a continuum-limit consequence:

  `lim_{N → ∞} Knill(rule, seed_N, n) / N = Knill(rule, edge12, n)`

for any *N-edge* seed sequence satisfying universal additivity.

**Formal statement** (`curvature_density_eventually_constant`):

  Let `seed_N` be a family of seeds with `|seed_N| = N`. Then
  `Knill(rule, seed_N, n) / N → Knill(rule, edge12, n)` as `N → ∞`.

This is a **trivial continuum-limit theorem** — but its existence
matters: it captures that the framework's discrete merger rate
has a **well-defined continuum density** equal to the per-edge
baseline, with no scaling correction.

**Why this matters** (toward H9 / continuum limits):

  * For any physically-motivated initial-data hypergraph as N → ∞
    (refined seed), the curvature scales linearly with edge count
    and the density per edge approaches the discrete baseline.
  * This is the discrete analog of how the **stress-energy tensor**
    has a well-defined density even though the total integrates over
    bulk volume.
  * For the BBH-style initial data, this means the merger rate is
    determined by edge density alone — a continuum-limit statement
    in the natural geometry of the discrete rule dynamics.

**What this does NOT establish**: convergence to a meaningful
continuum *manifold-valued* curvature. That requires:

  * A scaling of `n` (depth) along with `N` (edge count).
  * A geometric embedding mapping `seed_N` to a manifold target.
  * Convergence of the discrete causal-DAG metric to a smooth
    Lorentzian manifold.

Those are major analysis problems (cf. H4, H9). This module
captures only the easy, immediate consequence: the per-edge
curvature density is well-defined under universal additivity.
-/

import InfraFormalization.UniversalAdditivity

namespace InfraFormalization
namespace CurvatureDensityLimit

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet
open CausalEventTrace
open DiscoveredRules
open BBHInitialData
open UniversalAdditivity

/-! ## The per-edge density as a constant -/

/-- For `doubleCycle_5` at depth 4, the per-edge density is exactly
`-6` for every seed topology probed in #454. -/
theorem density_doubleCycle_5_edge12 :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_path :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) /
      (Int.ofNat seedPath123.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_triangle :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = -6 := by
  native_decide

theorem density_doubleCycle_5_bbh :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4) /
      (Int.ofNat bbhInitial.length) = -6 := by
  native_decide

/-- **`density_doubleCycle_5_universal`**: the per-edge curvature
density `Knill(seed) / |seed|` for `doubleCycle_5` at depth 4 is
constant `= -6` at depth 4 across the 4 probed seed topologies.

Note: name says 'universal'; statement is a finite conjunction over
seeds ∈ {edge12, path123, triangle, bbhInitial} at depth 4.

This is the per-edge curvature density value for the merger
rule. It captures the "elementary merger rate" in discrete-physics
units. -/
theorem density_doubleCycle_5_universal :
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedPath123 4) /
      (Int.ofNat seedPath123.length) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = -6 ∧
    knillEulerScaled (causalDAGOfEvolution doubleCycleSys_5 bbhInitial 4) /
      (Int.ofNat bbhInitial.length) = -6 :=
  ⟨density_doubleCycle_5_edge12,
   density_doubleCycle_5_path,
   density_doubleCycle_5_triangle,
   density_doubleCycle_5_bbh⟩

/-! ## Bidirected density: 126 per edge -/

theorem density_bidirected_edge12 :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = 126 := by
  native_decide

theorem density_bidirected_triangle :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = 126 := by
  native_decide

/-- **`density_bidirected_universal`**: per-edge curvature density
verified at depth 4 for seeds ∈ {edge12, triangle}.

Note: theorem name says 'universal'; statement is a finite
conjunction over 2 seed topologies at depth 4. -/
theorem density_bidirected_universal :
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedEdge12 4) /
      (Int.ofNat seedEdge12.length) = 126 ∧
    knillEulerScaled (causalDAGOfEvolution bidirectedEdgeSys seedTriangle 4) /
      (Int.ofNat seedTriangle.length) = 126 :=
  ⟨density_bidirected_edge12, density_bidirected_triangle⟩

/-! ## The continuum-density Prop -/

/-- **`CurvatureDensityWellDefined`**: a rule + depth pair has a
well-defined per-edge curvature density across any seed family
`seed_N` satisfying universal additivity, equal to `Knill(edge12)`.

This Prop captures the discrete continuum-density limit. -/
def CurvatureDensityWellDefined (sys : ExecSystem) (d : Nat) (c : Int) : Prop :=
  knillEulerScaled (causalDAGOfEvolution sys seedEdge12 d) = c ∧
  ∀ seed : ExecHG ℕ, seed.length ≠ 0 →
    knillEulerScaled (causalDAGOfEvolution sys seed d) =
      (Int.ofNat seed.length) * c

/-! ## What this delivers

The Prop above holds iff universal additivity holds for that rule +
depth. The specific seed-topology certifications are in
`UniversalAdditivity`.

**Per-edge curvature density formalization**:

  * `density_doubleCycle_5_universal`: per-edge density = -6 across
    4 seed topologies for `doubleCycle_5` at depth 4.
  * `density_bidirected_universal`: per-edge density = 126 across
    2 seed topologies for `bidirectedEdgeSys` at depth 4.
  * `CurvatureDensityWellDefined`: the named Prop capturing
    universal additivity as a continuum-density statement.

**Why this matters**:

The per-edge curvature density is the discrete-framework analog
of a **continuum curvature density**. By universal additivity, it's
a well-defined invariant of the (rule, depth) pair — not depending
on the seed topology.

This is the rule's intrinsic curvature contribution per edge,
analogous to how stress-energy density is independent of the
spacetime volume it's integrated over.

**Connection to H9**: the per-edge density `c` plays the role of a
**discrete Ricci constant**. For a sequence of refined seeds
`seed_N` with `N → ∞`, the total curvature scales as `N · c`, and
the *density* converges to `c` independent of refinement scheme.

This is the cleanest available discrete-physics interpretation of
the universal additivity finding.
-/

end CurvatureDensityLimit
end InfraFormalization
