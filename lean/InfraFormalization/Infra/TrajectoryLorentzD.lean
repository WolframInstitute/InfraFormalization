/-
d-dim bridging theorem: trajectory causal DAG → (d+1)-dim Lorentz lattice
via level-as-time + a *chosen* spatial embedding.

**Why this file exists.** The 1+0-dim bridging (`TrajectoryLorentz.lean`)
uses `level τ i` as a canonical time coordinate, but has no spatial
structure — all same-level events collapse to a single point. For a
higher-dim bridging we need spatial coordinates, and F1/F2 show that
no canonical spatial embedding is determined by the rewriting data
alone.

This file formalises the next-best thing: a **parameterised** bridging
theorem. Given *any* chosen spatial embedding
`φ : ℕ → Fin d → ℤ`, we can ask whether `causallyPrecedes τ i j`
implies `CausalPrecedes d (fullEmbed φ τ i) (fullEmbed φ τ j)`. The
answer depends on the chosen `φ`: this cannot be a theorem about `φ`
alone, but becomes one under a compatibility hypothesis.

The compatibility hypothesis is:

  **(compat)** for all `i, j` with `causallyPrecedes τ i j`,
              the spatial L∞ distance between `φ i` and `φ j` is
              ≤ the level-gap `level τ j - level τ i`.

Equivalently: the embedding places causally-related events inside each
other's light cones at the speed of one lattice-spacing-per-level-step.

Under (compat), the d-dim bridging theorem holds automatically. The
F1/F2 structural flaw is now *precisely the failure of (compat) to be
automatic* — any candidate rule for a Wolfram-to-GR bridge must come
with an embedding `φ` that satisfies (compat) by *construction*, not
by happy accident. This file gives the formal ground for that
requirement.

This is the form used in the rule-search pipeline (see
`RULE_SEARCH.md`): step 4 searches for `φ`, step 5 verifies (compat)
via the Lean machinery here.
-/

import InfraFormalization.CausalLevel
import InfraFormalization.Infra.LorentzLattice
import InfraFormalization.Infra.TrajectoryLorentz

namespace InfraFormalization
namespace Infra

variable {P V : Type*} [DecidableEq V]

/-- A **spatial embedding** of trajectory events into the lattice
`Fin d → ℤ`. This data is not determined by the trajectory and must be
supplied externally — F1/F2 state that no canonical choice exists. -/
abbrev SpatialEmbedding (d : Nat) : Type := Nat → Fin d → ℤ

/-- The full spacetime embedding: time = `level τ`, spatial = the
supplied `φ`. -/
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

/-- **Light-cone compatibility** of a spatial embedding with a
trajectory: whenever event `i` causally precedes event `j`, the
spatial L∞ distance between their `φ`-images is at most the level-gap
(equivalently: one lattice-step-per-level-tick bound, i.e., light
speed = 1). -/
def LightConeCompatible {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) {d : Nat} (φ : SpatialEmbedding d) : Prop :=
  ∀ i j, causallyPrecedes τ i j →
    (spaceDist d (fullEmbed τ φ i) (fullEmbed τ φ j) : ℤ)
    ≤ (level τ j : ℤ) - (level τ i : ℤ)

/-- **d-dim bridging theorem (conditional).** Under `LightConeCompatible`,
a trajectory's causal-precedence relation is faithfully embedded into
the (d+1)-dim Lorentz lattice's `CausalPrecedes` relation. -/
theorem fullEmbed_preserves_causal {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    CausalPrecedes d (fullEmbed τ φ i) (fullEmbed τ φ j) := by
  unfold CausalPrecedes
  rw [fullEmbed_time, fullEmbed_time]
  have := hcompat i j h
  linarith

/-- **Strengthened d-dim bridging.** Under `LightConeCompatible`, every
causally-related pair lands in the forward (possibly null) light cone.
Whether the image is strictly `Timelike` or `Null` depends on whether
the spatial L∞ distance strictly matches the level-gap — which is a
per-rule, per-embedding question. -/
theorem fullEmbed_forward_cone {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hcompat : LightConeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    fullEmbed τ φ j ∈ forwardCone d (fullEmbed τ φ i) :=
  fullEmbed_preserves_causal τ φ hcompat i j h

/-- **Timelike (strict) bridging.** If the spatial L∞ distance is
*strictly less* than the level-gap on every causal pair, then the
embedding maps causal precedence into strict `Timelike` separation —
the image lands in the *interior* of each forward light cone. -/
def StrictlyTimelikeCompatible {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) : Prop :=
  ∀ i j, causallyPrecedes τ i j →
    (spaceDist d (fullEmbed τ φ i) (fullEmbed τ φ j) : ℤ)
    < (level τ j : ℤ) - (level τ i : ℤ)

theorem fullEmbed_timelike {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) {d : Nat}
    (φ : SpatialEmbedding d) (hstrict : StrictlyTimelikeCompatible τ φ)
    (i j : Nat) (h : causallyPrecedes τ i j) :
    Timelike d (fullEmbed τ φ i) (fullEmbed τ φ j) := by
  unfold Timelike
  rw [fullEmbed_time, fullEmbed_time]
  exact hstrict i j h

/-- **Consequence for rule search.** If a spatial embedding `φ`
additionally maps same-level events to spatially *distinct* positions,
then same-level events become `Spacelike` in the Lorentz lattice — the
1+0-dim lossiness (`trajectoryToEvent_lossy`) is overcome.

This is the concrete criterion a candidate `φ` must satisfy in the
rule-search pipeline (step 4 in `RULE_SEARCH.md`): compatibility with
causal order (above) **plus** injectivity on same-level events. -/
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
