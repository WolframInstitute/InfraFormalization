/-
Composition of the trajectory-to-lattice and lattice-to-continuum embeddings.

`fullContinuumEmbed τ φ` is `lorentzIntEmbed ∘ fullEmbed τ φ`: event `i` of the trajectory
is sent to the real point with time coordinate `level τ i` and spatial coordinates `φ`.
Under the hypothesis `LightConeCompatible τ φ`, `causallyPrecedes τ i j` implies
`ContinuumCausalPrecedes` of the images. Under `StrictlyTimelikeCompatible τ φ`, it implies
`ContinuumTimelike` of the images. Both results are composites of the corresponding
results in `TrajectoryLorentzD` and `ScaledLorentz`; the compatibility hypotheses are
assumptions on `φ`.
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

/-- If `LightConeCompatible τ φ` holds and `causallyPrecedes τ i j`, then the images of
`i` and `j` under `fullContinuumEmbed τ φ` satisfy `ContinuumCausalPrecedes`. -/
theorem causallyPrecedes_gives_continuum {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    ContinuumCausalPrecedes d (fullContinuumEmbed τ φ i)
                              (fullContinuumEmbed τ φ j) := by
  unfold fullContinuumEmbed
  exact lorentzIntEmbed_preserves_causal _ _
    (fullEmbed_preserves_causal τ φ hcompat i j h)

/-- If `StrictlyTimelikeCompatible τ φ` holds and `causallyPrecedes τ i j`, then the
images of `i` and `j` under `fullContinuumEmbed τ φ` satisfy `ContinuumTimelike`. -/
theorem causallyPrecedes_gives_continuum_timelike {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hstrict : StrictlyTimelikeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    ContinuumTimelike d (fullContinuumEmbed τ φ i)
                        (fullContinuumEmbed τ φ j) := by
  unfold fullContinuumEmbed
  exact lorentzIntEmbed_preserves_timelike _ _
    (fullEmbed_timelike τ φ hstrict i j h)

/-- The time coordinate of `fullContinuumEmbed τ φ i` equals `level τ i`. -/
theorem fullContinuumEmbed_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i : Nat) :
    (fullContinuumEmbed τ φ i) 0 = ((level τ i : ℤ) : ℝ) := by
  unfold fullContinuumEmbed lorentzIntEmbed
  simp [fullEmbed_time]

/-- Events with equal level have equal time coordinate under `fullContinuumEmbed`. -/
theorem same_level_continuum_same_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i j : Nat)
    (hlevel : level τ i = level τ j) :
    (fullContinuumEmbed τ φ i) 0 = (fullContinuumEmbed τ φ j) 0 := by
  rw [fullContinuumEmbed_time, fullContinuumEmbed_time, hlevel]

end Infra
end InfraFormalization
