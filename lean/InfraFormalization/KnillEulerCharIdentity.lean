/-
**Universal Knill = 6·χ identity** (task #496).

The empirical certificates in `KnillDiscreteGaussBonnet.lean`,
`KnillHigherGenus.lean`, and `KnillThreeManifold.lean` discharge
`knillEulerScaled H = 6·χ` at specific triangulations
(tetrahedron, octahedron, icosahedron, triangulated tori at
`n ∈ {4,5,6}`, `∂Δ⁴ = K₅`) by `native_decide`.

This module lifts those certificates to a **single universal-in-`H`
theorem** — Knill's discrete Gauss-Bonnet (arxiv 1009.2292, Theorem 1)
formalized inside the executable-hypergraph framework:

    knillEulerScaled H = 6 · eulerChar H

where `eulerChar H := V − E + T` (`V` = vertex count, `E` =
1-skeleton edge count, `T` = 3-clique count).

The proof is the standard combinatorial telescoping. Linearity of
sum + two double-counting identities (degree → edges; triangle
incidences → triangles) suffice. Both identities are proved via a
Fubini-style swap on lists combined with the symmetry / irreflexivity
of `execAdj` and the trichotomy on `ℕ`.

The general theorem uses no `native_decide`. The specific corollaries
that replace the original closed-form certificates compute `eulerChar`
on concrete triangulations by `native_decide` — its intended use:
discharging an arithmetic fact about a fixed concrete object, while
the algebraic step `knillEulerScaled = 6 · eulerChar` is universal.
-/

import InfraFormalization.KnillDiscreteGaussBonnet

namespace InfraFormalization
namespace KnillEulerCharIdentity

open MultiwayExec
open RuleSignatureExecMetrics
open KnillDiscreteGaussBonnet

/-! ## 1. Definitions: 1-skeleton edges, 3-cliques, Euler characteristic -/

/-- Ordered pair `(u, v)` with `u < v` and adjacent in `H`. -/
def oneSkeletonEdges (H : ExecHG ℕ) : List (ℕ × ℕ) :=
  (vertexList H).flatMap (fun u =>
    ((vertexList H).filter (fun v => decide (u < v) && execAdj H u v)).map (Prod.mk u))

def oneSkeletonEdgeCount (H : ExecHG ℕ) : ℕ := (oneSkeletonEdges H).length

/-- Ordered triple `(u, v, w)` with `u < v < w` and all pairs adjacent. -/
def threeCliques (H : ExecHG ℕ) : List (ℕ × ℕ × ℕ) :=
  (vertexList H).flatMap (fun u =>
    (vertexList H).flatMap (fun v =>
      ((vertexList H).filter (fun w =>
        decide (u < v) && decide (v < w) &&
        execAdj H u v && execAdj H u w && execAdj H v w)).map (fun w => (u, v, w))))

def threeCliqueCount (H : ExecHG ℕ) : ℕ := (threeCliques H).length

/-- Discrete Euler characteristic `V − E + T`. -/
def eulerChar (H : ExecHG ℕ) : ℤ :=
  ((vertexList H).length : ℤ) - oneSkeletonEdgeCount H + threeCliqueCount H

/-! ## 2. Symmetry and irreflexivity of `execAdj` -/

theorem execAdj_irrefl (H : ExecHG ℕ) (v : ℕ) :
    execAdj H v v = false := by
  unfold execAdj
  rw [bne_self_eq_false]
  rfl

theorem execAdj_symm (H : ExecHG ℕ) (u v : ℕ) :
    execAdj H u v = execAdj H v u := by
  unfold execAdj
  have hbne : (u != v) = (v != u) := by
    rcases eq_or_ne u v with rfl | hne
    · rfl
    · have h1 : (u != v) = true := by simp [bne_iff_ne, hne]
      have h2 : (v != u) = true := by simp [bne_iff_ne, Ne.symm hne]
      rw [h1, h2]
  have hany :
      (List.any H fun e => e.verts.contains u && e.verts.contains v)
        = (List.any H fun e => e.verts.contains v && e.verts.contains u) := by
    apply congrArg (List.any H)
    funext e
    exact Bool.and_comm _ _
  rw [hbne, hany]

/-! ## 3. Generic distribution / Fubini swap for list sums -/

lemma sum_map_add_nat (l : List ℕ) (f g : ℕ → ℕ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- Filter-length = sum of indicator. -/
lemma length_filter_eq_sum_indicator (l : List ℕ) (P : ℕ → Bool) :
    (l.filter P).length = (l.map (fun x => if P x = true then 1 else 0)).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    cases hb : P hd with
    | true =>
      have hcons : (hd :: tl).filter P = hd :: tl.filter P := by
        rw [List.filter_cons]; simp [hb]
      rw [hcons]
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [ih]
      simp [hb]; omega
    | false =>
      have hcons : (hd :: tl).filter P = tl.filter P := by
        rw [List.filter_cons]; simp [hb]
      rw [hcons]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      simp [hb]

/-- The Fubini swap: `Σ_u Σ_v f(u, v) = Σ_v Σ_u f(u, v)` on lists. -/
lemma sum_map_sum_swap (vs ws : List ℕ) (f : ℕ → ℕ → ℕ) :
    (vs.map (fun u => (ws.map (fun v => f u v)).sum)).sum
      = (ws.map (fun v => (vs.map (fun u => f u v)).sum)).sum := by
  induction vs with
  | nil =>
    -- LHS = 0; RHS = (ws.map (fun _ => 0)).sum
    simp only [List.map_nil, List.sum_nil]
    induction ws with
    | nil => rfl
    | cons w ws' ihw =>
      simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
      omega
  | cons hd tl ih =>
    -- After step:
    -- LHS = (ws.map (fun v => f hd v)).sum + (tl.map (fun u => (ws.map (fun v => f u v)).sum)).sum
    -- RHS = (ws.map (fun v => f hd v + (tl.map (fun u => f u v)).sum)).sum
    --     = (ws.map (fun v => f hd v)).sum + (ws.map (fun v => (tl.map (fun u => f u v)).sum)).sum
    --       (by sum_map_add_nat)
    -- Apply IH to second term.
    have lhs_eq :
        ((hd :: tl).map (fun u => (ws.map (fun v => f u v)).sum)).sum
          = (ws.map (fun v => f hd v)).sum
            + (tl.map (fun u => (ws.map (fun v => f u v)).sum)).sum := by
      simp [List.map_cons, List.sum_cons]
    have rhs_eq :
        (ws.map (fun v => ((hd :: tl).map (fun u => f u v)).sum)).sum
          = (ws.map (fun v => f hd v)).sum
            + (ws.map (fun v => (tl.map (fun u => f u v)).sum)).sum := by
      have hpw : ∀ v, ((hd :: tl).map (fun u => f u v)).sum
                        = f hd v + (tl.map (fun u => f u v)).sum := by
        intro v; simp [List.map_cons, List.sum_cons]
      rw [show (ws.map (fun v => ((hd :: tl).map (fun u => f u v)).sum))
            = (ws.map (fun v => f hd v + (tl.map (fun u => f u v)).sum)) from by
              apply List.map_congr_left; intros v _; exact hpw v]
      exact sum_map_add_nat ws (fun v => f hd v) (fun v => (tl.map (fun u => f u v)).sum)
    rw [lhs_eq, rhs_eq, ih]

/-- Fubini for filter-lengths. -/
lemma sum_swap_filter (vs ws : List ℕ) (P : ℕ → ℕ → Bool) :
    (vs.map (fun u => (ws.filter (fun v => P u v)).length)).sum
      = (ws.map (fun v => (vs.filter (fun u => P u v)).length)).sum := by
  have l1 : (vs.map (fun u => (ws.filter (fun v => P u v)).length)).sum
              = (vs.map (fun u => (ws.map (fun v => if P u v = true then 1 else 0)).sum)).sum := by
    apply congrArg
    apply List.map_congr_left
    intros u _
    exact length_filter_eq_sum_indicator ws (fun v => P u v)
  have r1 : (ws.map (fun v => (vs.filter (fun u => P u v)).length)).sum
              = (ws.map (fun v => (vs.map (fun u => if P u v = true then 1 else 0)).sum)).sum := by
    apply congrArg
    apply List.map_congr_left
    intros v _
    exact length_filter_eq_sum_indicator vs (fun u => P u v)
  rw [l1, r1]
  exact sum_map_sum_swap vs ws (fun u v => if P u v = true then 1 else 0)

/-! ## 4. Sum of degrees = 2 · |E| -/

lemma execAdjDegree_eq_filter_length (H : ExecHG ℕ) (v : ℕ) :
    execAdjDegree H v = ((vertexList H).filter (execAdj H v)).length := rfl

/-- Per-vertex degree splits by trichotomy on `u` vs `v`. -/
lemma execAdjDegree_split (H : ExecHG ℕ) (v : ℕ) :
    execAdjDegree H v
      = ((vertexList H).filter (fun u => decide (u < v) && execAdj H v u)).length
      + ((vertexList H).filter (fun u => decide (v < u) && execAdj H v u)).length := by
  rw [execAdjDegree_eq_filter_length]
  induction vertexList H with
  | nil => simp
  | cons hd tl ih =>
    by_cases hadj : execAdj H v hd = true
    · have hne : v ≠ hd := by
        intro heq
        rw [← heq, execAdj_irrefl] at hadj
        exact absurd hadj (by decide)
      rcases Nat.lt_or_ge hd v with hlt | hge
      · -- hd < v
        have hd1 : decide (hd < v) = true := by simp [hlt]
        have hd2 : decide (v < hd) = false := by
          simp [Nat.not_lt.mpr (Nat.le_of_lt hlt)]
        simp [List.filter_cons, hadj, hd1, hd2, List.length_cons]
        omega
      · have hlt : v < hd := lt_of_le_of_ne hge hne
        have hd1 : decide (hd < v) = false := by
          simp [Nat.not_lt.mpr (Nat.le_of_lt hlt)]
        have hd2 : decide (v < hd) = true := by simp [hlt]
        simp [List.filter_cons, hadj, hd1, hd2, List.length_cons]
        omega
    · have hadj' : execAdj H v hd = false := by
        cases hb : execAdj H v hd with
        | false => rfl
        | true => exact absurd hb hadj
      simp [List.filter_cons, hadj']
      exact ih

/-- `Σ_v |{u : v < u ∧ adj v u}| = E`. -/
lemma sum_split_above_eq_E (H : ExecHG ℕ) :
    ((vertexList H).map (fun v =>
        ((vertexList H).filter (fun u => decide (v < u) && execAdj H v u)).length)).sum
      = oneSkeletonEdgeCount H := by
  unfold oneSkeletonEdgeCount oneSkeletonEdges
  rw [List.length_flatMap]
  simp only [List.length_map]

/-- `Σ_v |{u : u < v ∧ adj v u}| = E` by Fubini swap + adj symmetry. -/
lemma sum_split_below_eq_E (H : ExecHG ℕ) :
    ((vertexList H).map (fun v =>
        ((vertexList H).filter (fun u => decide (u < v) && execAdj H v u)).length)).sum
      = oneSkeletonEdgeCount H := by
  have step1 :
      ((vertexList H).map (fun v =>
          ((vertexList H).filter (fun u => decide (u < v) && execAdj H v u)).length)).sum
        = ((vertexList H).map (fun v =>
            ((vertexList H).filter (fun u => decide (u < v) && execAdj H u v)).length)).sum := by
    apply congrArg
    apply List.map_congr_left
    intros v _
    apply congrArg
    apply List.filter_congr
    intros u _
    rw [execAdj_symm]
  rw [step1]
  rw [← sum_swap_filter (vertexList H) (vertexList H)
        (fun u v => decide (u < v) && execAdj H u v)]
  exact sum_split_above_eq_E H

theorem sum_degree_eq_twice_edges (H : ExecHG ℕ) :
    ((vertexList H).map (execAdjDegree H)).sum
      = 2 * oneSkeletonEdgeCount H := by
  have hmap : ((vertexList H).map (execAdjDegree H)).sum
                = ((vertexList H).map (fun v =>
                    ((vertexList H).filter (fun u => decide (u < v) && execAdj H v u)).length
                    + ((vertexList H).filter (fun u => decide (v < u) && execAdj H v u)).length)).sum := by
    apply congrArg
    apply List.map_congr_left
    intros v _
    exact execAdjDegree_split H v
  rw [hmap, sum_map_add_nat, sum_split_below_eq_E, sum_split_above_eq_E]
  ring

/-! ## 5. Sum of triangle counts = 3 · |T|

We work with the canonical "triangle incidence" expression:

    triangleIncidenceCount H
      := Σ_v Σ_x Σ_y [adj v x ∧ adj v y ∧ x < y ∧ adj x y]

(suppressing the redundant `x ≠ v`, `y ≠ v` conditions, which `adj`
already enforces). We show:

  (a) `Σ_v tri(v) = triangleIncidenceCount H`;
  (b) `triangleIncidenceCount H = 3 · threeCliqueCount H`. -/

/-- Canonical triangle-incidence predicate. -/
def triPred (H : ExecHG ℕ) (v x y : ℕ) : Bool :=
  execAdj H v x && execAdj H v y && decide (x < y) && execAdj H x y

/-- Triple-indexed incidence count. -/
def triangleIncidenceCount (H : ExecHG ℕ) : ℕ :=
  ((vertexList H).map (fun v =>
    ((vertexList H).map (fun x =>
      ((vertexList H).filter (fun y => triPred H v x y)).length)).sum)).sum

/-- Step (a): per-vertex triangle count summed = triple-indexed count. -/
lemma sum_triangleCount_eq_incidenceCount (H : ExecHG ℕ) :
    ((vertexList H).map (execTriangleCountAtVertex H)).sum
      = triangleIncidenceCount H := by
  unfold triangleIncidenceCount
  apply congrArg
  apply List.map_congr_left
  intros v _
  unfold execTriangleCountAtVertex
  set vs := vertexList H
  -- Convert nbrs.foldr to (nbrs.map ...).sum (general lemma).
  have hfoldr_sum : ∀ (l : List ℕ) (f : ℕ → ℕ),
      l.foldr (fun x acc => acc + f x) 0 = (l.map f).sum := by
    intros l f
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
      ring
  rw [hfoldr_sum]
  -- (nbrs.map ...).sum where nbrs = vs.filter Qv
  -- Convert (filter Qv).map g .sum → vs.map (Qv-guarded g) .sum
  have hmap_filter : ∀ (l : List ℕ) (Q : ℕ → Bool) (g : ℕ → ℕ),
      ((l.filter Q).map g).sum = (l.map (fun x => if Q x = true then g x else 0)).sum := by
    intros l Q g
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      by_cases h : Q hd = true
      · simp [h, ih]
      · have h' : Q hd = false := by
          cases hb : Q hd with
          | false => rfl
          | true => exact absurd hb h
        simp [h', ih]
  rw [hmap_filter vs (fun x => decide (x ≠ v) && execAdj H v x)
        (fun x => ((vs.filter (fun x' => decide (x' ≠ v) && execAdj H v x')).filter
                     (fun y => x < y && execAdj H x y)).length)]
  apply congrArg
  apply List.map_congr_left
  intros x _
  by_cases hQ : (decide (x ≠ v) && execAdj H v x) = true
  · rw [if_pos hQ]
    rw [List.filter_filter]
    -- Goal: |{y : (Qv y) && (x < y && adj x y)}| = |{y : triPred v x y}|
    have hxnev : decide (x ≠ v) = true := by
      rcases (Bool.and_eq_true _ _).mp hQ with ⟨h1, _⟩; exact h1
    have hadjvx : execAdj H v x = true := by
      rcases (Bool.and_eq_true _ _).mp hQ with ⟨_, h2⟩; exact h2
    apply congrArg
    apply List.filter_congr
    intros y _
    unfold triPred
    rw [hadjvx]
    -- LHS: (decide (y ≠ v) && adj v y) && (decide (x < y) && adj x y)
    -- RHS: true && adj v y && decide (x < y) && adj x y
    by_cases hAdjvy : execAdj H v y = true
    · have hynev : decide (y ≠ v) = true := by
        have : y ≠ v := by
          intro heq; rw [heq, execAdj_irrefl] at hAdjvy
          exact absurd hAdjvy (by decide)
        simp [this]
      rw [hAdjvy, hynev]
      simp
    · have hAdjvy' : execAdj H v y = false := by
        cases hb : execAdj H v y with
        | false => rfl
        | true => exact absurd hb hAdjvy
      rw [hAdjvy']
      simp
  · rw [if_neg hQ]
    -- triPred starts with adj v x. If hQ false, then adj v x = false (or x = v).
    have hQ' : (decide (x ≠ v) && execAdj H v x) = false := by
      cases hb : (decide (x ≠ v) && execAdj H v x) with
      | false => rfl
      | true => exact absurd hb hQ
    have hadjvx_false : execAdj H v x = false := by
      rcases Bool.and_eq_false_iff.mp hQ' with h | h
      · have hxv : x = v := by
          by_contra hne
          have : decide (x ≠ v) = true := by simp [hne]
          rw [this] at h; exact absurd h (by decide)
        rw [hxv, execAdj_irrefl]
      · exact h
    -- Length = 0.
    symm
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intros y _
    unfold triPred
    rw [hadjvx_false]
    simp

/-! ### Step (b): the canonical triangle-incidence count equals `3 · T`. -/

/-- "v is smallest" predicate. -/
def pred1 (H : ExecHG ℕ) (v x y : ℕ) : Bool :=
  decide (v < x) && decide (x < y) && execAdj H v x && execAdj H v y && execAdj H x y

/-- "v is middle" predicate. -/
def pred2 (H : ExecHG ℕ) (v x y : ℕ) : Bool :=
  decide (x < v) && decide (v < y) && execAdj H v x && execAdj H v y && execAdj H x y

/-- "v is largest" predicate. -/
def pred3 (H : ExecHG ℕ) (v x y : ℕ) : Bool :=
  decide (x < y) && decide (y < v) && execAdj H v x && execAdj H v y && execAdj H x y

/-- Per-element trichotomy split of `triPred`. -/
lemma triPred_split_count (H : ExecHG ℕ) (vs : List ℕ) (v x : ℕ) :
    (vs.filter (fun y => triPred H v x y)).length
      = (vs.filter (fun y => pred1 H v x y)).length
        + (vs.filter (fun y => pred2 H v x y)).length
        + (vs.filter (fun y => pred3 H v x y)).length := by
  induction vs with
  | nil => simp
  | cons hd tl ih =>
    by_cases hAvx : execAdj H v x = true
    · by_cases hAvy : execAdj H v hd = true
      · by_cases hAxy : execAdj H x hd = true
        · by_cases hxlt : x < hd
          · -- All adjs true and x < hd. triPred holds for hd.
            have hvnex : v ≠ x := by
              intro heq; rw [heq, execAdj_irrefl] at hAvx
              exact absurd hAvx (by decide)
            have hvnehd : v ≠ hd := by
              intro heq; rw [heq, execAdj_irrefl] at hAvy
              exact absurd hAvy (by decide)
            have htri : triPred H v x hd = true := by
              unfold triPred; simp [hAvx, hAvy, hxlt, hAxy]
            rcases Nat.lt_or_gt_of_ne hvnex with hvltx | hxltv
            · -- v < x < hd
              have h1 : pred1 H v x hd = true := by
                unfold pred1; simp [hvltx, hxlt, hAvx, hAvy, hAxy]
              have h2 : pred2 H v x hd = false := by
                unfold pred2
                have : ¬ (x < v) := Nat.not_lt.mpr (Nat.le_of_lt hvltx)
                simp [this]
              have h3 : pred3 H v x hd = false := by
                unfold pred3
                have : ¬ (hd < v) := by omega
                simp [this]
              simp [List.filter_cons, htri, h1, h2, h3, List.length_cons]
              omega
            · -- x < v
              by_cases hvlt : v < hd
              · -- x < v < hd
                have h1 : pred1 H v x hd = false := by
                  unfold pred1
                  have : ¬ (v < x) := Nat.not_lt.mpr (Nat.le_of_lt hxltv)
                  simp [this]
                have h2 : pred2 H v x hd = true := by
                  unfold pred2; simp [hxltv, hvlt, hAvx, hAvy, hAxy]
                have h3 : pred3 H v x hd = false := by
                  unfold pred3
                  have : ¬ (hd < v) := by omega
                  simp [this]
                simp [List.filter_cons, htri, h1, h2, h3, List.length_cons]
                omega
              · -- hd < v
                have hhdv : hd < v := lt_of_le_of_ne (Nat.not_lt.mp hvlt) hvnehd.symm
                have h1 : pred1 H v x hd = false := by
                  unfold pred1
                  have : ¬ (v < x) := Nat.not_lt.mpr (Nat.le_of_lt hxltv)
                  simp [this]
                have h2 : pred2 H v x hd = false := by
                  unfold pred2
                  have : ¬ (v < hd) := Nat.not_lt.mpr (Nat.le_of_lt hhdv)
                  simp [this]
                have h3 : pred3 H v x hd = true := by
                  unfold pred3; simp [hxlt, hhdv, hAvx, hAvy, hAxy]
                simp [List.filter_cons, htri, h1, h2, h3, List.length_cons]
                omega
          · -- ¬ x < hd. triPred false.
            have htri : triPred H v x hd = false := by unfold triPred; simp [hxlt]
            have h1 : pred1 H v x hd = false := by unfold pred1; simp [hxlt]
            have h3 : pred3 H v x hd = false := by unfold pred3; simp [hxlt]
            have h2 : pred2 H v x hd = false := by
              unfold pred2
              by_cases hxv : x < v
              · by_cases hvhd : v < hd
                · exact absurd (lt_trans hxv hvhd) hxlt
                · have : ¬ (v < hd) := Nat.not_lt.mpr (Nat.not_lt.mp hvhd)
                  simp [this]
              · have : ¬ (x < v) := Nat.not_lt.mpr (Nat.not_lt.mp hxv)
                simp [this]
            simp [List.filter_cons, htri, h1, h2, h3]
            exact ih
        · have hAxy' : execAdj H x hd = false := by
            cases hb : execAdj H x hd with
            | false => rfl
            | true => exact absurd hb hAxy
          have htri : triPred H v x hd = false := by unfold triPred; simp [hAxy']
          have h1 : pred1 H v x hd = false := by unfold pred1; simp [hAxy']
          have h2 : pred2 H v x hd = false := by unfold pred2; simp [hAxy']
          have h3 : pred3 H v x hd = false := by unfold pred3; simp [hAxy']
          simp [List.filter_cons, htri, h1, h2, h3]
          exact ih
      · have hAvy' : execAdj H v hd = false := by
          cases hb : execAdj H v hd with
          | false => rfl
          | true => exact absurd hb hAvy
        have htri : triPred H v x hd = false := by unfold triPred; simp [hAvy']
        have h1 : pred1 H v x hd = false := by unfold pred1; simp [hAvy']
        have h2 : pred2 H v x hd = false := by unfold pred2; simp [hAvy']
        have h3 : pred3 H v x hd = false := by unfold pred3; simp [hAvy']
        simp [List.filter_cons, htri, h1, h2, h3]
        exact ih
    · have hAvx' : execAdj H v x = false := by
        cases hb : execAdj H v x with
        | false => rfl
        | true => exact absurd hb hAvx
      have htri : triPred H v x hd = false := by unfold triPred; simp [hAvx']
      have h1 : pred1 H v x hd = false := by unfold pred1; simp [hAvx']
      have h2 : pred2 H v x hd = false := by unfold pred2; simp [hAvx']
      have h3 : pred3 H v x hd = false := by unfold pred3; simp [hAvx']
      simp [List.filter_cons, htri, h1, h2, h3]
      exact ih

/-- The triangle-incidence count splits into three pieces. -/
lemma triangleIncidenceCount_split (H : ExecHG ℕ) :
    triangleIncidenceCount H
      = ((vertexList H).map (fun v =>
          ((vertexList H).map (fun x =>
            ((vertexList H).filter (fun y => pred1 H v x y)).length)).sum)).sum
      + ((vertexList H).map (fun v =>
          ((vertexList H).map (fun x =>
            ((vertexList H).filter (fun y => pred2 H v x y)).length)).sum)).sum
      + ((vertexList H).map (fun v =>
          ((vertexList H).map (fun x =>
            ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum)).sum := by
  unfold triangleIncidenceCount
  -- Distribute split through both sums.
  have sum_add3 : ∀ (F G K : ℕ → ℕ) (l : List ℕ),
      (l.map (fun x => F x + G x + K x)).sum
        = (l.map F).sum + (l.map G).sum + (l.map K).sum := by
    intros F G K l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  have step_inner : ∀ v x,
      ((vertexList H).filter (fun y => triPred H v x y)).length
        = ((vertexList H).filter (fun y => pred1 H v x y)).length
          + ((vertexList H).filter (fun y => pred2 H v x y)).length
          + ((vertexList H).filter (fun y => pred3 H v x y)).length :=
    fun v x => triPred_split_count H (vertexList H) v x
  -- Lift to middle level.
  have step_middle : ∀ v,
      ((vertexList H).map (fun x => ((vertexList H).filter (fun y => triPred H v x y)).length)).sum
        = ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred1 H v x y)).length)).sum
          + ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred2 H v x y)).length)).sum
          + ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum := by
    intro v
    have heq : (vertexList H).map (fun x => ((vertexList H).filter (fun y => triPred H v x y)).length)
                = (vertexList H).map (fun x =>
                    ((vertexList H).filter (fun y => pred1 H v x y)).length
                    + ((vertexList H).filter (fun y => pred2 H v x y)).length
                    + ((vertexList H).filter (fun y => pred3 H v x y)).length) := by
      apply List.map_congr_left
      intros x _
      exact step_inner v x
    rw [heq, sum_add3]
  -- Lift to outer level.
  have heq2 : (vertexList H).map (fun v =>
                ((vertexList H).map (fun x =>
                  ((vertexList H).filter (fun y => triPred H v x y)).length)).sum)
              = (vertexList H).map (fun v =>
                ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred1 H v x y)).length)).sum
                + ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred2 H v x y)).length)).sum
                + ((vertexList H).map (fun x => ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum) := by
    apply List.map_congr_left
    intros v _
    exact step_middle v
  rw [heq2, sum_add3]

/-- `pred1` count equals `T`: same iteration structure as `threeCliques`. -/
lemma pred1_count_eq_T (H : ExecHG ℕ) :
    ((vertexList H).map (fun v =>
        ((vertexList H).map (fun x =>
          ((vertexList H).filter (fun y => pred1 H v x y)).length)).sum)).sum
      = threeCliqueCount H := by
  unfold threeCliqueCount threeCliques
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros u _
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros v _
  simp only [List.length_map]
  apply congrArg
  apply List.filter_congr
  intros y _
  unfold pred1
  -- pred1 v u y vs threeCliques inner predicate. Both should be the same.
  rfl

/-- `pred2` count equals `T`: swap outer two sums, then use adj symmetry. -/
lemma pred2_count_eq_T (H : ExecHG ℕ) :
    ((vertexList H).map (fun v =>
        ((vertexList H).map (fun x =>
          ((vertexList H).filter (fun y => pred2 H v x y)).length)).sum)).sum
      = threeCliqueCount H := by
  rw [sum_map_sum_swap (vertexList H) (vertexList H)
        (fun v x => ((vertexList H).filter (fun y => pred2 H v x y)).length)]
  unfold threeCliqueCount threeCliques
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros u _
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros v _
  simp only [List.length_map]
  apply congrArg
  apply List.filter_congr
  intros y _
  unfold pred2
  rw [execAdj_symm H v u]
  -- Goal: (u < v) && (v < y) && adj u v && adj v y && adj u y
  --     = (u < v) && (v < y) && adj u v && adj u y && adj v y
  -- Reorder the last three with Bool.and_right_comm or by cases.
  cases h1 : decide (u < v) <;> cases h2 : decide (v < y) <;>
    cases h3 : execAdj H u v <;> cases h4 : execAdj H v y <;>
    cases h5 : execAdj H u y <;> rfl

/-- `pred3` count equals `T`: two Fubini swaps + adj symmetry. -/
lemma pred3_count_eq_T (H : ExecHG ℕ) :
    ((vertexList H).map (fun v =>
        ((vertexList H).map (fun x =>
          ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum)).sum
      = threeCliqueCount H := by
  rw [sum_map_sum_swap (vertexList H) (vertexList H)
        (fun v x => ((vertexList H).filter (fun y => pred3 H v x y)).length)]
  -- Goal: (vs.map fun x => (vs.map fun v => |{y : pred3 v x y}|).sum).sum = T.
  -- Now swap inner two (v, y) per x.
  have inner_swap : ∀ x,
      ((vertexList H).map (fun v =>
        ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum
        = ((vertexList H).map (fun y =>
          ((vertexList H).filter (fun v => pred3 H v x y)).length)).sum := by
    intro x
    exact sum_swap_filter (vertexList H) (vertexList H) (fun v y => pred3 H v x y)
  have heq : (vertexList H).map (fun x =>
                ((vertexList H).map (fun v =>
                  ((vertexList H).filter (fun y => pred3 H v x y)).length)).sum)
              = (vertexList H).map (fun x =>
                ((vertexList H).map (fun y =>
                  ((vertexList H).filter (fun v => pred3 H v x y)).length)).sum) := by
    apply List.map_congr_left
    intros x _
    exact inner_swap x
  rw [heq]
  unfold threeCliqueCount threeCliques
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros u _
  rw [List.length_flatMap]
  apply congrArg
  apply List.map_congr_left
  intros v _
  simp only [List.length_map]
  apply congrArg
  apply List.filter_congr
  intros w _
  unfold pred3
  -- Goal: pred3 w u v = clique predicate (u, v, w)
  -- pred3 w u v = decide (u < v) && decide (v < w) && adj w u && adj w v && adj u v
  -- threeCliques (u, v, w) inner: decide (u < v) && decide (v < w) && adj u v && adj u w && adj v w
  -- adj w u = adj u w (sym), adj w v = adj v w (sym), adj u v same.
  rw [execAdj_symm H w u, execAdj_symm H w v]
  cases h1 : decide (u < v) <;> cases h2 : decide (v < w) <;>
    cases h3 : execAdj H u v <;> cases h4 : execAdj H u w <;>
    cases h5 : execAdj H v w <;> rfl

theorem sum_triangle_count_eq_thrice_triangles (H : ExecHG ℕ) :
    ((vertexList H).map (execTriangleCountAtVertex H)).sum
      = 3 * threeCliqueCount H := by
  rw [sum_triangleCount_eq_incidenceCount,
      triangleIncidenceCount_split,
      pred1_count_eq_T, pred2_count_eq_T, pred3_count_eq_T]
  ring

/-! ## 6. The main identity: `knillEulerScaled H = 6 · eulerChar H` -/

lemma foldr_add_int_eq_sum_map (vs : List ℕ) (f : ℕ → ℤ) :
    vs.foldr (fun v (acc : ℤ) => acc + f v) 0
      = (vs.map f).sum := by
  induction vs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
    ring

lemma knillEulerScaled_expand (H : ExecHG ℕ) :
    knillEulerScaled H
      = 6 * ((vertexList H).length : ℤ)
        - 3 * ((((vertexList H).map (execAdjDegree H)).sum : ℕ) : ℤ)
        + 2 * ((((vertexList H).map (execTriangleCountAtVertex H)).sum : ℕ) : ℤ) := by
  unfold knillEulerScaled
  rw [foldr_add_int_eq_sum_map (vertexList H) (knillVertexK6 H)]
  have aux : ∀ (vs : List ℕ),
      (vs.map (knillVertexK6 H)).sum
        = 6 * (vs.length : ℤ)
          - 3 * ((vs.map (execAdjDegree H)).sum : ℤ)
          + 2 * ((vs.map (execTriangleCountAtVertex H)).sum : ℤ) := by
    intro vs
    induction vs with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      unfold knillVertexK6
      push_cast
      ring
  rw [aux]

/-- **Knill's discrete Gauss-Bonnet identity** (arxiv 1009.2292):
the scaled per-vertex defect sum equals `6 · χ` of the 2-skeleton. -/
theorem knill_eq_six_euler_char (H : ExecHG ℕ) :
    knillEulerScaled H = 6 * eulerChar H := by
  rw [knillEulerScaled_expand]
  have hdeg : (((vertexList H).map (execAdjDegree H)).sum : ℤ)
                = 2 * (oneSkeletonEdgeCount H : ℤ) := by
    have := sum_degree_eq_twice_edges H
    exact_mod_cast this
  have htri : (((vertexList H).map (execTriangleCountAtVertex H)).sum : ℤ)
                = 3 * (threeCliqueCount H : ℤ) := by
    have := sum_triangle_count_eq_thrice_triangles H
    exact_mod_cast this
  rw [hdeg, htri]
  unfold eulerChar
  ring

/-! ## 7. Corollaries -/

theorem tetrahedron_eulerChar : eulerChar SphereTriangulationAudit.tetrahedronHG = 2 := by
  native_decide

theorem tetrahedron_knillEuler_via_universal :
    knillEulerScaled SphereTriangulationAudit.tetrahedronHG = 12 := by
  rw [knill_eq_six_euler_char, tetrahedron_eulerChar]; rfl

theorem octahedron_eulerChar : eulerChar SphereTriangulationAudit.octahedronHG = 2 := by
  native_decide

theorem octahedron_knillEuler_via_universal :
    knillEulerScaled SphereTriangulationAudit.octahedronHG = 12 := by
  rw [knill_eq_six_euler_char, octahedron_eulerChar]; rfl

theorem icosahedron_eulerChar : eulerChar SphereTriangulationAudit.icosahedronHG = 2 := by
  native_decide

theorem icosahedron_knillEuler_via_universal :
    knillEulerScaled SphereTriangulationAudit.icosahedronHG = 12 := by
  rw [knill_eq_six_euler_char, icosahedron_eulerChar]; rfl

/-- **Universal certificate**: three S² Knill values, all instances of one universal theorem. -/
theorem knill_S2_via_universal :
    knillEulerScaled SphereTriangulationAudit.tetrahedronHG = 12 ∧
    knillEulerScaled SphereTriangulationAudit.octahedronHG = 12 ∧
    knillEulerScaled SphereTriangulationAudit.icosahedronHG = 12 :=
  ⟨tetrahedron_knillEuler_via_universal,
   octahedron_knillEuler_via_universal,
   icosahedron_knillEuler_via_universal⟩

/-! ## What this delivers

Universal `knillEulerScaled H = 6 · eulerChar H` proved without
`native_decide`. Standard combinatorial telescoping: linearity of
sum + two double-counting identities (degree → edges, triangle-
incidence → triangles), via Fubini swap + adjacency symmetry +
trichotomy.

The previous per-triangulation certificates remain decidable
specializations of the universal identity, with the per-instance
work reduced to computing `eulerChar` of a fixed concrete object —
the appropriate use of `native_decide`. -/

end KnillEulerCharIdentity
end InfraFormalization
