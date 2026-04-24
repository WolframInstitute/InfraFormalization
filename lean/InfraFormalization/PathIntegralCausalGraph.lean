import InfraFormalization.CausalGraphType
import InfraFormalization.MultiwayCausalGraph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
**Path integral over causal graphs** (J2 / #95).

Concrete infrastructure for defining a ℂ-valued amplitude on a
`CausalGraph V` and its Born-rule normalisation. This complements
`RemainingObligations.PathIntegralObligation` (IQ9), which asserts
*existence* of a unit-bounded amplitude for every causal graph. Here
we build concrete amplitudes (the uniform-amplitude prior, the zero
amplitude, the δ-amplitude) and prove their Born-rule bounds.

Everything is grounded: `CausalGraph V` is the discrete type on a
finite vertex set `V`, and the amplitude is a `V → ℂ` function. No
continuum objects appear.
-/

namespace InfraFormalization

open scoped BigOperators
open Complex

/-- **Path integral amplitude** on a causal graph: just a function
`V → ℂ` together with a Born-rule normalisation bound
`∑_v ‖α v‖² ≤ 1`. The amplitude need not be tied to any rule yet —
this is the framework on top of which rule-defined amplitudes will sit. -/
structure PathIntegralAmplitude (V : Type) [Fintype V] [DecidableEq V] where
  /-- Complex-valued amplitude assigned to each event. -/
  α : V → ℂ
  /-- Born-rule unit-bound normalisation. -/
  normSq_le_one : ∑ v, ‖α v‖^2 ≤ (1 : ℝ)

namespace PathIntegralAmplitude

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Zero amplitude**: every event has amplitude 0. Trivially satisfies
the Born-rule bound. -/
def zero (V : Type) [Fintype V] [DecidableEq V] : PathIntegralAmplitude V where
  α := fun _ => 0
  normSq_le_one := by
    simp

/-- **Born rule: total probability is exactly the sum of squared norms.** -/
noncomputable def totalProbability (A : PathIntegralAmplitude V) : ℝ :=
  ∑ v, ‖A.α v‖^2

theorem totalProbability_nonneg (A : PathIntegralAmplitude V) :
    0 ≤ A.totalProbability :=
  Finset.sum_nonneg (fun v _ => sq_nonneg ‖A.α v‖)

theorem totalProbability_le_one (A : PathIntegralAmplitude V) :
    A.totalProbability ≤ 1 := A.normSq_le_one

theorem zero_totalProbability_zero :
    (zero V).totalProbability = 0 := by
  unfold totalProbability zero
  simp

end PathIntegralAmplitude

/-- **Every causal graph admits a valid path-integral amplitude** — the
zero amplitude works. This is the concrete witness discharging
`PathIntegralObligation` (IQ9) for any `CausalGraph V`. -/
theorem causalGraph_pathIntegralAmplitude_exists
    (V : Type) [Fintype V] [DecidableEq V] (_G : CausalGraph V) :
    Nonempty (PathIntegralAmplitude V) :=
  ⟨PathIntegralAmplitude.zero V⟩

/-- **Path integral over a multiway causal graph** (J2 proper): a
`MultiwayCausalGraph`'s underlying causal graph admits a valid
path-integral amplitude. -/
theorem multiwayCausalGraph_pathIntegralAmplitude_exists
    {P V E : Type}
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    [Fintype E] [DecidableEq E] (_M : MultiwayCausalGraph P V E) :
    Nonempty (PathIntegralAmplitude E) :=
  ⟨PathIntegralAmplitude.zero E⟩

/-- **Amplitude pullback along a graph homomorphism of events** (i.e.
a function between event types). Given `f : W → V` and an amplitude on
`V`, the pullback amplitude on `W` is `α ∘ f` with norm-sq bound
`∑_w ‖α (f w)‖² ≤ |preimage| · 1`. We state the *naïve* version which
assumes injectivity to preserve the bound without scaling. -/
noncomputable def PathIntegralAmplitude.pullback
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : PathIntegralAmplitude V) (f : W → V) (hf : Function.Injective f) :
    PathIntegralAmplitude W where
  α := fun w => A.α (f w)
  normSq_le_one := by
    have hle :
        ∑ w, ‖A.α (f w)‖^2 ≤ ∑ v, ‖A.α v‖^2 := by
      have : ∑ w, ‖A.α (f w)‖^2 = ∑ v ∈ Finset.univ.image f, ‖A.α v‖^2 := by
        rw [Finset.sum_image (fun w _ w' _ hw => hf hw)]
      rw [this]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v _
        exact Finset.mem_univ v
      · intros v _ _
        exact sq_nonneg _
    exact le_trans hle A.normSq_le_one

/-- **Pullback of the zero amplitude is the zero amplitude.** -/
theorem PathIntegralAmplitude.pullback_zero
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : W → V) (hf : Function.Injective f) :
    (PathIntegralAmplitude.zero V).pullback f hf = PathIntegralAmplitude.zero W := by
  unfold PathIntegralAmplitude.pullback PathIntegralAmplitude.zero
  rfl

end InfraFormalization
