/-
End-to-end bridge: trajectory → Lorentz lattice → continuum Minkowski.

Composes the two upstream bridges:
  1. `TrajectoryLorentzD.fullEmbed τ φ`:
     trajectory events → `Event d`  (time = level, space = φ),
     preserves causal order under `LightConeCompatible` hypothesis.

  2. `ScaledLorentz.lorentzIntEmbed`:
     `Event d` → `ContinuumEvent d`  (int-to-ℝ cast),
     preserves causal order in the forward direction.

The composition gives the full chain:

  `causallyPrecedes τ i j`
    ⇒  under `LightConeCompatible τ φ`,
  `ContinuumCausalPrecedes d
     (lorentzIntEmbed (fullEmbed τ φ i))
     (lorentzIntEmbed (fullEmbed τ φ j))`.

This is the machine-checked statement a rule-search pipeline (see
`RULE_SEARCH.md`) would use to certify that a candidate rule +
candidate spatial embedding yields a Lorentzian-causal structure
consistent with continuum Minkowski.

The `Timelike` refinement is also provided: under the stronger
`StrictlyTimelikeCompatible` hypothesis, the causal pair lands in the
strict interior of the continuum light cone.
-/

import InfraFormalization.Infra.TrajectoryLorentzD
import InfraFormalization.Infra.ScaledLorentz

namespace InfraFormalization
namespace Infra

variable {P V : Type*} [DecidableEq V]

/-- The full composed embedding: trajectory event i → continuum event. -/
noncomputable def fullContinuumEmbed {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i : Nat) : ContinuumEvent d :=
  lorentzIntEmbed (fullEmbed τ φ i)

/-- **End-to-end bridge (causal).** Under the light-cone compatibility
hypothesis on the spatial embedding `φ`, the trajectory's
`causallyPrecedes` relation implies `ContinuumCausalPrecedes` in the
continuum Minkowski lattice under the full embedding. -/
theorem causallyPrecedes_gives_continuum {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    ContinuumCausalPrecedes d (fullContinuumEmbed τ φ i)
                              (fullContinuumEmbed τ φ j) := by
  unfold fullContinuumEmbed
  exact lorentzIntEmbed_preserves_causal _ _
    (fullEmbed_preserves_causal τ φ hcompat i j h)

/-- **End-to-end bridge (timelike, strict interior).** Under the
strictly-timelike compatibility hypothesis, the continuum embedding
lands in the strict interior of the forward Minkowski light cone. -/
theorem causallyPrecedes_gives_continuum_timelike {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hstrict : StrictlyTimelikeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    ContinuumTimelike d (fullContinuumEmbed τ φ i)
                        (fullContinuumEmbed τ φ j) := by
  unfold fullContinuumEmbed
  exact lorentzIntEmbed_preserves_timelike _ _
    (fullEmbed_timelike τ φ hstrict i j h)

/-- **Time-coordinate extraction.** The time coordinate in the
continuum embedding is simply `(level τ i : ℝ)`. -/
theorem fullContinuumEmbed_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i : Nat) :
    (fullContinuumEmbed τ φ i) 0 = ((level τ i : ℤ) : ℝ) := by
  unfold fullContinuumEmbed lorentzIntEmbed
  simp [fullEmbed_time]

/-- **Same-level events share continuum time.** -/
theorem same_level_continuum_same_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i j : Nat)
    (hlevel : level τ i = level τ j) :
    (fullContinuumEmbed τ φ i) 0 = (fullContinuumEmbed τ φ j) 0 := by
  rw [fullContinuumEmbed_time, fullContinuumEmbed_time, hlevel]

end Infra
end InfraFormalization
