/-
Embedding of a trajectory's events into the (d+1)-dimensional Lorentz lattice with a supplied
spatial map.

The time coordinate of event `i` is `level τ i` and the spatial coordinates are `φ i` for a given
`φ : ℕ → Fin d → ℤ`. The predicate `LightConeCompatible τ φ` requires the spatial L∞ distance of
every causally related pair to be at most their level difference. Under this hypothesis, causal
precedence in the trajectory implies `CausalPrecedes` between the image events. The module also
proves that two events of equal level with distinct spatial images are `Spacelike`.
-/

import InfraFormalization.CausalLevel
import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.TrajectoryLorentz

namespace InfraFormalization
namespace Infra

variable {P V : Type*} [DecidableEq V]

/-- A spatial map of trajectory events into `Fin d → ℤ`, indexed by event number. -/
abbrev SpatialEmbedding (d : Nat) : Type := Nat → Fin d → ℤ

/-- The lattice event with time coordinate `level τ i` and spatial coordinates `φ i`. -/
noncomputable def fullEmbed {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) {d : Nat} (φ : SpatialEmbedding d)
    (i : Nat) : Event d :=
  fun k =>
    if hk : k.val = 0 then
      (level τ i : ℤ)
    else
      φ i ⟨k.val - 1, by
        have : k.val < d + 1 := k.isLt
        omega⟩

@[simp] theorem fullEmbed_time {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (i : Nat) :
    (fullEmbed τ φ i) 0 = (level τ i : ℤ) := by
  unfold fullEmbed
  simp

/-- For every pair with `causallyPrecedes τ i j`, the spatial L∞ distance between `fullEmbed τ φ i`
and `fullEmbed τ φ j` is at most `level τ j - level τ i`. -/
def LightConeCompatible {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) {d : Nat} (φ : SpatialEmbedding d) : Prop :=
  ∀ i j, causallyPrecedes τ i j →
    (spaceDist d (fullEmbed τ φ i) (fullEmbed τ φ j) : ℤ)
    ≤ (level τ j : ℤ) - (level τ i : ℤ)

/-- If `LightConeCompatible τ φ` and `causallyPrecedes τ i j`, then
`CausalPrecedes d (fullEmbed τ φ i) (fullEmbed τ φ j)`. -/
theorem fullEmbed_preserves_causal {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    CausalPrecedes d (fullEmbed τ φ i) (fullEmbed τ φ j) := by
  unfold CausalPrecedes
  rw [fullEmbed_time, fullEmbed_time]
  have := hcompat i j h
  linarith

/-- If `LightConeCompatible τ φ` and `causallyPrecedes τ i j`, then `fullEmbed τ φ j` lies in
`forwardCone d (fullEmbed τ φ i)`. -/
theorem fullEmbed_forward_cone {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    fullEmbed τ φ j ∈ forwardCone d (fullEmbed τ φ i) :=
  fullEmbed_preserves_causal τ φ hcompat i j h

/-- For every pair with `causallyPrecedes τ i j`, the spatial L∞ distance between `fullEmbed τ φ i`
and `fullEmbed τ φ j` is strictly less than `level τ j - level τ i`. -/
def StrictlyTimelikeCompatible {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) : Prop :=
  ∀ i j, causallyPrecedes τ i j →
    (spaceDist d (fullEmbed τ φ i) (fullEmbed τ φ j) : ℤ)
    < (level τ j : ℤ) - (level τ i : ℤ)

/-- If `StrictlyTimelikeCompatible τ φ` and `causallyPrecedes τ i j`, then
`Timelike d (fullEmbed τ φ i) (fullEmbed τ φ j)`. -/
theorem fullEmbed_timelike {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hstrict : StrictlyTimelikeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    Timelike d (fullEmbed τ φ i) (fullEmbed τ φ j) := by
  unfold Timelike
  rw [fullEmbed_time, fullEmbed_time]
  exact hstrict i j h

/-- If `level τ i = level τ j` and the spatial distance between `fullEmbed τ φ i` and
`fullEmbed τ φ j` is positive, then the two image events are `Spacelike`. -/
theorem same_level_spacelike_of_spatial_distinct
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) {d : Nat} (φ : SpatialEmbedding d)
    (i j : Nat)
    (hlevel : level τ i = level τ j)
    (hsp : 0 < spaceDist d (fullEmbed τ φ i) (fullEmbed τ φ j)) :
    Spacelike d (fullEmbed τ φ i) (fullEmbed τ φ j) := by
  apply spacelike_of_equal_time
  · rw [fullEmbed_time, fullEmbed_time]
    exact_mod_cast hlevel
  · exact hsp

end Infra
end InfraFormalization
