/-
Bridge: discrete Forman-Ricci on the cycle ↔ continuum Ricci on the
circle.

**The grounding-principle obligation.** Per `BRIDGE_MACHINERY.md`,
every continuum-curvature object must be paired with a discrete-side
object plus a relating theorem. This file is the first such bridge:

  Forman-Ricci on `Fin n` cycle (a 2-regular graph)
       =  0
       =  continuum Ricci on `S¹` (a 1-dim manifold)

The circle's continuum Ricci is computed using the local-coordinate
framework: `MetricData 1` with `g₀₀ ≡ 1`, flat connection, Ricci ≡ 0
(via `flatConnection_ricci_zero`).

The match is not a coincidence: the circle is the GH-limit of the
scaled cycle (`Infra.cycle_circle_gh_bound`), and Forman-Ricci is a
combinatorial invariant that vanishes precisely when degrees are 2,
i.e., when the graph is locally 1-dim — which is what a 1-dim
manifold limit requires.

This is the prototype for the broader statement we want eventually:
**discrete-Ricci on a hypergraph → continuum-Ricci on its GH-limit**.
For the cycle case it is trivially `0 = 0`, but the formalisation
makes the bridge mechanically checkable, and provides the template
for higher-curvature cases (sphere → positive Ricci, etc.).
-/

import InfraFormalization.DiscreteRicci
import InfraFormalization.CurvatureLocalCoord
import InfraFormalization.CurvatureRiemann

namespace InfraFormalization

/-- **Circle as a `MetricData 1`.** Single-coordinate `x` with constant
metric `g₀₀(x) = 1` (Euclidean line, equivalently the unit-arc-length
parameterisation of the circle). Inverse `g^{00} ≡ 1`; partial
derivatives ≡ 0. -/
noncomputable def circleMetric : Curvature.MetricData 1 where
  g := fun _ _ _ => 1
  ginv := fun _ _ _ => 1
  dg := fun _ _ _ _ => 0
  g_symm := by intros; rfl
  ginv_symm := by intros; rfl
  ginv_mul := by
    intros x μ ν
    -- For Fin 1, all elements are equal, so μ = ν always; sum has one summand.
    have hμν : μ = ν := Subsingleton.elim μ ν
    rw [Finset.sum_const, Finset.card_univ]
    have : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
    rw [this]
    simp [hμν]
  dg_symm := by intros; rfl

/-- **Continuum Ricci of the circle vanishes.** Using the flat
connection on `circleMetric`, the Ricci tensor is zero everywhere. -/
theorem circle_ricci_zero (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    (Curvature.flatConnection 1).ricci x σ ν = 0 :=
  Curvature.flatConnection_ricci_zero 1 x σ ν

/-- **Continuum scalar curvature of the circle vanishes.** -/
theorem circle_scalar_zero (x : Fin 1 → ℝ) :
    Curvature.ConnectionData.scalarCurvature circleMetric
      (Curvature.flatConnection 1) x = 0 :=
  Curvature.flatConnection_scalar_zero circleMetric x

/-- **Discrete Forman-Ricci of the cycle vanishes.** Any
neighbourhood structure on `Fin n` in which every vertex has degree
exactly 2 yields zero Forman-Ricci on every edge. -/
theorem cycleForman_zero {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2) (v w : Fin n) :
    formanRicciEdge N v w = 0 :=
  formanRicciEdge_zero_of_two_regular N h2reg v w

/-- **The bridge.** For any 2-regular neighbourhood structure on
`Fin n` (the discrete-side avatar of a 1-dim cyclic spatial slice),
the Forman-Ricci on every edge equals the continuum Ricci of the
circle at every point — both being zero.

This is the first formalised case of the discrete-Ricci ↔
continuum-Ricci correspondence under our grounding principle: the
continuum object (Ricci tensor on `circleMetric`) is paired with a
discrete-side object (Forman-Ricci on a 2-regular graph) and an
explicit relating theorem (both vanish identically). -/
theorem forman_ricci_matches_continuum_on_cycle
    {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2)
    (v w : Fin n) (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    (formanRicciEdge N v w : ℤ) = 0
    ∧ (Curvature.flatConnection 1).ricci x σ ν = 0 := by
  refine ⟨?_, ?_⟩
  · exact cycleForman_zero N h2reg v w
  · exact circle_ricci_zero x σ ν

/-- **Bridge in numerical form.** Cast both sides to ℝ and use the
fact that both are zero. The casting bridges integer-valued discrete
Ricci and real-valued continuum Ricci. -/
theorem forman_ricci_real_matches_continuum_on_cycle
    {n : Nat} (N : Neighbourhood (Fin n))
    (h2reg : ∀ v : Fin n, N.degree v = 2)
    (v w : Fin n) (x : Fin 1 → ℝ) (σ ν : Fin 1) :
    ((formanRicciEdge N v w : ℤ) : ℝ)
    = (Curvature.flatConnection 1).ricci x σ ν := by
  rw [cycleForman_zero N h2reg v w, circle_ricci_zero x σ ν]
  simp

end InfraFormalization
