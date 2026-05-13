/-
**Per-slice signature screener** (#224, Phase B).

Builds on `RuleSignature` (state-level signature functor),
`DiscreteRicci.formanRicciHypergraph` (Forman-Ricci scalar), and the
generic `ConvergenceRateObligation` framework from `WassersteinRate`.

The *trajectory signature* of a rewriting trajectory `τ` is the
sequence of state-level signatures `(σₙ)ₙ` indexed by step. A
*screener* is a `ConvergenceRateObligation` on a numerical projection
of that trajectory: e.g.

  * `formanRicciTrajectory τ : ℕ → ℝ` — total Forman-Ricci scalar of
    each state, viewed as a real-valued function of step.
  * `formanRicciDeviation τ target : ℕ → ℝ` — pointwise distance
    between the trajectory's Forman-Ricci and a target.
  * `vertexBallVolumeTrajectory τ v r : ℕ → ℝ` — ball volume at a
    fixed `(v, r)` along the trajectory.

These projections plug into `ConvergenceRateObligation` so we get
discardable obligations: "this rule's curvature converges to the
target at rate `r(n)`". A failed screener disqualifies a rule from
discharging the corresponding curved-target origin obligation.

This is the Phase B foundation for #224 (per-slice screener) and feeds
the eventual #190 empirical rule search and #225 multi-way bridge.

Grounded: every metric extracted is a function of the trajectory
states, which are `Hypergraph V` data — no continuum islands.
-/

import InfraFormalization.RuleSignature
import InfraFormalization.WassersteinRate
import InfraFormalization.RuleDimensionBounds

namespace InfraFormalization

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {P : Type*}

/-! ## Per-slice signature trajectory -/

/-- **Per-slice signature**: the `RuleSignature` of the n-th state of
trajectory `τ`. Out-of-range indices return the signature of the
last state (saturating); concrete clamping keeps total-functions and
avoids needing `Decidable` membership predicates. -/
noncomputable def signatureTrajectory {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (n : ℕ) : RuleSignature V :=
  if h : n < τ.states.length then
    hypergraphSignature (τ.states.get ⟨n, h⟩)
  else
    hypergraphSignature init

@[simp] theorem signatureTrajectory_zero {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (h0 : 0 < τ.states.length) :
    signatureTrajectory τ 0 = hypergraphSignature init := by
  unfold signatureTrajectory
  rw [dif_pos h0]
  congr 1
  exact trajectory_states_zero τ h0

@[simp] theorem signatureTrajectory_oob {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) {n : ℕ} (h : ¬ n < τ.states.length) :
    signatureTrajectory τ n = hypergraphSignature init := by
  unfold signatureTrajectory
  rw [dif_neg h]

/-- **Edge-count projection** of the trajectory signature: a real-valued
sequence `n ↦ |edges of state n|`. Suitable for plugging into a
`ConvergenceRateObligation`. -/
noncomputable def edgeCountTrajectory {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) : ScaledDiscrepancy :=
  fun n => ((signatureTrajectory τ n).edgeCount : ℝ)

/-- **Vertex-count projection** is the constant `Fintype.card V`. -/
noncomputable def vertexCountTrajectory {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) : ScaledDiscrepancy :=
  fun n => ((signatureTrajectory τ n).vertexCount : ℝ)

theorem vertexCountTrajectory_const {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (n : ℕ) :
    vertexCountTrajectory τ n = (Fintype.card V : ℝ) := by
  unfold vertexCountTrajectory signatureTrajectory
  by_cases hn : n < τ.states.length
  · rw [dif_pos hn]; rfl
  · rw [dif_neg hn]; rfl

/-! ## Conservation lifts to bounded edge-count trajectory -/

/-- **Conservation ⇒ edge-count trajectory is constant.** Lifts
`RuleSignature.edgeCount_invariant_of_conservative` to the trajectory
projection. -/
theorem edgeCountTrajectory_const_of_conservative
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (n : ℕ) :
    edgeCountTrajectory τ n = (init.size : ℝ) := by
  unfold edgeCountTrajectory signatureTrajectory
  by_cases hn : n < τ.states.length
  · rw [dif_pos hn]
    have :=
      RuleSignature.edgeCount_invariant_of_conservative τ hstep hcons n hn
    show ((hypergraphSignature (τ.states.get ⟨n, hn⟩)).edgeCount : ℝ) = _
    rw [this]
    rfl
  · rw [dif_neg hn]; rfl

/-- **Conservative-trajectory edge-count discrepancy from initial size
is identically zero.** Direct corollary of
`edgeCountTrajectory_const_of_conservative`. -/
theorem edgeCountTrajectory_deviation_zero_of_conservative
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (n : ℕ) :
    edgeCountTrajectory τ n - (init.size : ℝ) = 0 := by
  rw [edgeCountTrajectory_const_of_conservative τ hstep hcons n]
  ring

/-! ## ConvergenceRate plugs for trajectory projections -/

/-- **Conservative edge-count discrepancy satisfies any rate**: the
deviation `|edgeCountTrajectory τ n − init.size|` is identically zero
along a conservative trajectory, so it satisfies every
`ConvergenceRateObligation r` with `r ≥ 0`. -/
theorem edgeCountTrajectory_satisfies_any_rate_of_conservative
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    ConvergenceRateObligation
      (fun n => |edgeCountTrajectory τ n - (init.size : ℝ)|) r := by
  refine ⟨1, one_pos, 0, ?_⟩
  intros n _
  show |edgeCountTrajectory τ n - (init.size : ℝ)| ≤ 1 * r n
  rw [edgeCountTrajectory_deviation_zero_of_conservative τ hstep hcons n]
  rw [abs_zero, one_mul]
  exact hr_nonneg n

/-! ## Forman-Ricci trajectory -/

/-- **Forman-Ricci trajectory**: real-valued sequence
`n ↦ formanRicciHypergraph (state n)`. The fundamental curvature
projection used for the per-slice screener. -/
noncomputable def formanRicciTrajectory {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) : ScaledDiscrepancy :=
  fun n =>
    if h : n < τ.states.length then
      ((formanRicciHypergraph (τ.states.get ⟨n, h⟩) : ℤ) : ℝ)
    else
      ((formanRicciHypergraph init : ℤ) : ℝ)

@[simp] theorem formanRicciTrajectory_zero {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (h0 : 0 < τ.states.length) :
    formanRicciTrajectory τ 0 = ((formanRicciHypergraph init : ℤ) : ℝ) := by
  unfold formanRicciTrajectory
  rw [dif_pos h0]
  congr 1
  congr 1
  exact trajectory_states_zero τ h0

@[simp] theorem formanRicciTrajectory_oob {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    {n : ℕ} (h : ¬ n < τ.states.length) :
    formanRicciTrajectory τ n = ((formanRicciHypergraph init : ℤ) : ℝ) := by
  unfold formanRicciTrajectory
  rw [dif_neg h]

/-- **Forman-Ricci deviation trajectory**: pointwise distance between
the rule's Forman-Ricci scalar trajectory and a target value
`κ : ℝ`. This is the discrepancy that plugs into a
`ConvergenceRateObligation` to express "this rule's curvature
converges to `κ`". -/
noncomputable def formanRicciDeviation {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (κ : ℝ) : ScaledDiscrepancy :=
  fun n => |formanRicciTrajectory τ n - κ|

/-- **Forman-Ricci screener obligation**: the trajectory's Forman-Ricci
scalar converges to target curvature `κ` at rate `r`. -/
def FormanRicciScreener {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (κ : ℝ) (r : ℕ → ℝ) : Prop :=
  ConvergenceRateObligation (formanRicciDeviation τ κ) r

/-! ## Triangle-corrected Forman-Ricci trajectory (1D Forman on the clique skeleton)

The standard 1D Forman with the triangle-correction term — finer than
the bare `formanRicciHypergraph` (which sums `k(2−k)` over hyperedges
and vanishes on simple graphs). Per edge `(v, w)` in the
clique-expansion graph,
  `F(v, w) = 4 − deg(v) − deg(w) + 3 · #triangles_through(v, w)`.

The trajectory value is `Hypergraph.formanRicciTriangleDoubled` — the
double sum that equals `2 · F_total`. The factor of two is absorbed by
the rate constant in `ConvergenceRateObligation`, so the screener is
unchanged in meaning. Aligns with `Infrageometry/Graph.wl`'s
`FormanRicciCurvature[g, "OnCells" -> 1]` (PHAJEK 2026-05). -/

noncomputable def formanRicciTriangleTrajectory {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) : ScaledDiscrepancy :=
  fun n =>
    if h : n < τ.states.length then
      (((τ.states.get ⟨n, h⟩).formanRicciTriangleDoubled : ℤ) : ℝ)
    else
      ((init.formanRicciTriangleDoubled : ℤ) : ℝ)

@[simp] theorem formanRicciTriangleTrajectory_zero {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (h0 : 0 < τ.states.length) :
    formanRicciTriangleTrajectory τ 0 = ((init.formanRicciTriangleDoubled : ℤ) : ℝ) := by
  unfold formanRicciTriangleTrajectory
  rw [dif_pos h0]
  congr 1
  congr 1
  exact trajectory_states_zero τ h0

@[simp] theorem formanRicciTriangleTrajectory_oob {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    {n : ℕ} (h : ¬ n < τ.states.length) :
    formanRicciTriangleTrajectory τ n = ((init.formanRicciTriangleDoubled : ℤ) : ℝ) := by
  unfold formanRicciTriangleTrajectory
  rw [dif_neg h]

/-- **Triangle-Forman deviation**: pointwise distance from target. -/
noncomputable def formanRicciTriangleDeviation {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init) (κ : ℝ) : ScaledDiscrepancy :=
  fun n => |formanRicciTriangleTrajectory τ n - κ|

/-- **Triangle-Forman screener obligation**: the trajectory's
triangle-corrected Forman scalar converges to `κ` at rate `r`. -/
def FormanRicciTriangleScreener {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (κ : ℝ) (r : ℕ → ℝ) : Prop :=
  ConvergenceRateObligation (formanRicciTriangleDeviation τ κ) r

/-- **Constant-trajectory triangle-Forman screener**: a trajectory
whose triangle-Forman scalar is identically equal to the initial value
passes the screener at the initial target for any non-negative rate. -/
theorem formanRicciTriangleScreener_const_self {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hconst : ∀ n, formanRicciTriangleTrajectory τ n =
      ((init.formanRicciTriangleDoubled : ℤ) : ℝ))
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    FormanRicciTriangleScreener τ ((init.formanRicciTriangleDoubled : ℤ) : ℝ) r := by
  refine ⟨1, one_pos, 0, ?_⟩
  intros n _
  unfold formanRicciTriangleDeviation
  rw [hconst n, sub_self, abs_zero, one_mul]
  exact hr_nonneg n

/-- **Length-1-trajectory triangle-Forman screener**: a trajectory with
only the initial state passes the triangle-Forman screener at the
initial target with any non-negative rate. -/
theorem formanRicciTriangleScreener_initial_state_const {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hlen : τ.states.length = 1)
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    FormanRicciTriangleScreener τ ((init.formanRicciTriangleDoubled : ℤ) : ℝ) r := by
  refine formanRicciTriangleScreener_const_self τ ?_ r hr_nonneg
  intro n
  unfold formanRicciTriangleTrajectory
  by_cases hn : n < τ.states.length
  · rw [dif_pos hn]
    have h0 : 0 < τ.states.length := by rw [hlen]; exact one_pos
    have hn_zero : n = 0 := by
      have : n < 1 := by rw [hlen] at hn; exact hn
      omega
    subst hn_zero
    have := trajectory_states_zero τ h0
    rw [this]
  · rw [dif_neg hn]

/-- **Negative discharge** for the triangle-Forman screener: a
trajectory whose triangle-Forman deviation has a cofinal positive
lower bound `δ` fails any rate eventually less than `δ`. -/
theorem formanRicciTriangleScreener_fails_of_persistent_gap
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (κ : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (hgap : ∀ N, ∃ n, N ≤ n ∧ δ ≤ formanRicciTriangleDeviation τ κ n)
    (r : ℕ → ℝ) (hC : ∀ C : ℝ, 0 < C → ∃ N₀, ∀ n, N₀ ≤ n → C * r n < δ) :
    ¬ FormanRicciTriangleScreener τ κ r := by
  intro ⟨C, hC_pos, N, hN⟩
  obtain ⟨N₀, hN₀⟩ := hC C hC_pos
  obtain ⟨n, h_Nmax, h_gap⟩ := hgap (max N N₀)
  have h_N_le : N ≤ n := le_of_max_le_left h_Nmax
  have h_N₀_le : N₀ ≤ n := le_of_max_le_right h_Nmax
  have h_d_le : formanRicciTriangleDeviation τ κ n ≤ C * r n := hN n h_N_le
  have h_Cr_lt : C * r n < δ := hN₀ n h_N₀_le
  have h_d_lt : formanRicciTriangleDeviation τ κ n < δ := lt_of_le_of_lt h_d_le h_Cr_lt
  exact absurd h_gap (not_le.mpr h_d_lt)

/-! ## Trivial / baseline screener witnesses -/

/-- **Self-screener**: a constant trajectory (every state has the same
Forman-Ricci scalar) trivially passes the screener at the appropriate
target with any rate. Used as a baseline rule-discharge witness. -/
theorem formanRicciScreener_const_self {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hconst : ∀ n, formanRicciTrajectory τ n = ((formanRicciHypergraph init : ℤ) : ℝ))
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    FormanRicciScreener τ ((formanRicciHypergraph init : ℤ) : ℝ) r := by
  refine ⟨1, one_pos, 0, ?_⟩
  intros n _
  unfold formanRicciDeviation
  rw [hconst n, sub_self, abs_zero, one_mul]
  exact hr_nonneg n

/-- **Empty-trajectory screener**: a length-1 trajectory (only the
initial state, no applications) has constant Forman-Ricci, so passes
the screener at the initial-state target with any rate. -/
theorem formanRicciScreener_initial_state_const {sys : RewritingSystem P}
    {init : Hypergraph V} (τ : Trajectory sys init)
    (hlen : τ.states.length = 1)
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    FormanRicciScreener τ ((formanRicciHypergraph init : ℤ) : ℝ) r := by
  refine formanRicciScreener_const_self τ ?_ r hr_nonneg
  intro n
  unfold formanRicciTrajectory
  by_cases hn : n < τ.states.length
  · rw [dif_pos hn]
    have h0 : 0 < τ.states.length := by rw [hlen]; exact one_pos
    have hn_zero : n = 0 := by
      have hnle : n < 1 := by rw [hlen] at hn; exact hn
      omega
    subst hn_zero
    have := trajectory_states_zero τ h0
    rw [this]
  · rw [dif_neg hn]

/-! ## Multi-screener: combined edge + curvature signature -/

/-- **Combined screener**: a trajectory passes the multi-screener for
`(target_edgeCount, target_κ, r)` iff its edge-count is constantly
`target_edgeCount` (within the rate, with `r ≥ 0` enforcing
non-negative bounds) AND its Forman-Ricci converges to `target_κ` at
rate `r`. The conjunction is the structurally minimal "rule passes
for this target curvature" statement. -/
def MultiScreener {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (target_edgeCount : ℝ) (target_κ : ℝ) (r : ℕ → ℝ) : Prop :=
  ConvergenceRateObligation
    (fun n => |edgeCountTrajectory τ n - target_edgeCount|) r
  ∧ FormanRicciScreener τ target_κ r

/-- **Conservative + initial-state target ⇒ multi-screener passes**:
along a conservative trajectory of length 1, both the edge-count and
the Forman-Ricci agree exactly with the initial values, so the
multi-screener at `(init.size, formanRicciHypergraph init)` passes
with any non-negative rate. -/
theorem multiScreener_self_of_conservative_initial
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (hstep : τ.StepConsistent)
    (hcons : ∀ i (hi : i < τ.applications.length),
      (τ.applications.get ⟨i, hi⟩).2.1.IsConservative)
    (hlen : τ.states.length = 1)
    (r : ℕ → ℝ) (hr_nonneg : ∀ n, 0 ≤ r n) :
    MultiScreener τ (init.size : ℝ)
      ((formanRicciHypergraph init : ℤ) : ℝ) r := by
  refine ⟨?_, ?_⟩
  · exact edgeCountTrajectory_satisfies_any_rate_of_conservative τ hstep hcons r hr_nonneg
  · exact formanRicciScreener_initial_state_const τ hlen r hr_nonneg

/-! ## Negative screener: deviation lower bound rules a rule out -/

/-- **Screener-failure lower bound** (negative rule discharge): if for
infinitely many `n`, the rule's Forman-Ricci deviates from `target_κ`
by at least `δ > 0`, then no `ConvergenceRateObligation` with rate
function eventually less than `δ` can hold — the rule **fails** the
screener for `target_κ` and is disqualified.

Concretely: if the deviation has a uniform positive lower bound on a
cofinal subset, no convergent rate can witness the screener. -/
theorem formanRicciScreener_fails_of_persistent_gap
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (κ : ℝ) (δ : ℝ) (_hδ : 0 < δ)
    (hgap : ∀ N, ∃ n, N ≤ n ∧ δ ≤ formanRicciDeviation τ κ n)
    (r : ℕ → ℝ) (hC : ∀ C : ℝ, 0 < C → ∃ N₀, ∀ n, N₀ ≤ n → C * r n < δ) :
    ¬ FormanRicciScreener τ κ r := by
  intro ⟨C, hC_pos, N, hN⟩
  obtain ⟨N₀, hN₀⟩ := hC C hC_pos
  obtain ⟨n, h_Nmax, h_gap⟩ := hgap (max N N₀)
  have h_N_le : N ≤ n := le_of_max_le_left h_Nmax
  have h_N₀_le : N₀ ≤ n := le_of_max_le_right h_Nmax
  have h_d_le : formanRicciDeviation τ κ n ≤ C * r n := hN n h_N_le
  have h_Cr_lt : C * r n < δ := hN₀ n h_N₀_le
  have h_d_lt : formanRicciDeviation τ κ n < δ := lt_of_le_of_lt h_d_le h_Cr_lt
  exact absurd h_gap (not_le.mpr h_d_lt)

/-! ## Angular-deviation screener (AT7)

Parallel to `formanRicciDeviation` / `FormanRicciScreener` above.
Each trajectory state has an *elementary angle profile* at a chosen
basepoint and radius (AT0): pick equidistant `A, B ∈ S(O, r)` and read
off `H.elementaryAngle O A B`. The screener: does the trajectory's
angle deviation from a target angle `κ_ang` decay at a given rate?

Lives next to the Forman-Ricci screener so a multi-screener can stack
both curvature and angular obligations.
-/

/-- **Per-step angular sample**: at trajectory state `n`, pick the
*first* witnessing equidistant pair `(A, B)` at radius `r` from a
fixed basepoint `O` (whichever the underlying decidability finds first;
out-of-range states fall back to the initial state). Returns `0` if no
equidistant pair exists at radius `r` in the given state. -/
noncomputable def elementaryAngleSample {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (O : V) (r : ℕ) (n : ℕ) : ℝ :=
  let H : Hypergraph V :=
    if h : n < τ.states.length then τ.states.get ⟨n, h⟩ else init
  -- Sum of elementary angles over all equidistant pairs at radius r
  -- (a one-vertex-pair witness is enough, but summing is a stable
  -- aggregator that matches Bishop-Gromov style accumulation).
  let sphere : Finset V := Finset.univ.filter (fun v => H.dist O v = r)
  ∑ A ∈ sphere, ∑ B ∈ sphere, H.elementaryAngle O A B

/-- **Angular-deviation discrepancy**: pointwise distance between the
trajectory's per-step angle sample at `(O, r)` and a target angle
aggregate `κ_ang`. Plugs into `ConvergenceRateObligation` to express
"this rule's angular profile converges to `κ_ang` at rate `r`". -/
noncomputable def angularDeviation {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (O : V) (r : ℕ) (κ_ang : ℝ) : ScaledDiscrepancy :=
  fun n => |elementaryAngleSample τ O r n - κ_ang|

/-- **Angular-deviation screener obligation**: the trajectory's angular
profile at basepoint `O`, radius `r`, converges to target `κ_ang` at
convergence rate `rate`. -/
def AngularScreener {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (O : V) (r : ℕ) (κ_ang : ℝ) (rate : ℕ → ℝ) : Prop :=
  ConvergenceRateObligation (angularDeviation τ O r κ_ang) rate

/-! ## Combined curvature + angular multi-screener -/

/-- **Multi-screener: edge-count + Forman-Ricci + angular**. A trajectory
passes the combined screener iff (a) its edge-count discrepancy from
`target_edgeCount` satisfies `rate`; (b) its Forman-Ricci converges to
`target_κ_curv` at `rate`; (c) its angular profile at `(O, r)`
converges to `target_κ_ang` at `rate`. The combined-discharge form is
the structurally minimal "rule produces correct geometry" obligation. -/
def CombinedScreener {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init)
    (target_edgeCount : ℝ) (target_κ_curv : ℝ)
    (O : V) (r : ℕ) (target_κ_ang : ℝ) (rate : ℕ → ℝ) : Prop :=
  ConvergenceRateObligation
    (fun n => |edgeCountTrajectory τ n - target_edgeCount|) rate
  ∧ FormanRicciScreener τ target_κ_curv rate
  ∧ AngularScreener τ O r target_κ_ang rate

/-- **Negative discharge** for the angular screener: persistent gap from
target `κ_ang` rules out any rate function eventually less than `δ`.
Sibling of `formanRicciScreener_fails_of_persistent_gap`. -/
theorem angularScreener_fails_of_persistent_gap
    {sys : RewritingSystem P} {init : Hypergraph V}
    (τ : Trajectory sys init) (O : V) (r : ℕ) (κ_ang : ℝ)
    (δ : ℝ) (_hδ : 0 < δ)
    (hgap : ∀ N, ∃ n, N ≤ n ∧ δ ≤ angularDeviation τ O r κ_ang n)
    (rate : ℕ → ℝ)
    (hC : ∀ C : ℝ, 0 < C → ∃ N₀, ∀ n, N₀ ≤ n → C * rate n < δ) :
    ¬ AngularScreener τ O r κ_ang rate := by
  intro ⟨C, hC_pos, N, hN⟩
  obtain ⟨N₀, hN₀⟩ := hC C hC_pos
  obtain ⟨n, h_Nmax, h_gap⟩ := hgap (max N N₀)
  have h_N_le : N ≤ n := le_of_max_le_left h_Nmax
  have h_N₀_le : N₀ ≤ n := le_of_max_le_right h_Nmax
  have h_d_le : angularDeviation τ O r κ_ang n ≤ C * rate n := hN n h_N_le
  have h_Cr_lt : C * rate n < δ := hN₀ n h_N₀_le
  have h_d_lt : angularDeviation τ O r κ_ang n < δ := lt_of_le_of_lt h_d_le h_Cr_lt
  exact absurd h_gap (not_le.mpr h_d_lt)

end InfraFormalization
