/-
Riemann curvature tensor, Ricci tensor, scalar curvature, Einstein
tensor — all in local coordinates.

**Continuation of Rung 5.** `CurvatureLocalCoord.lean` formalised
Christoffel symbols. Here we add the Riemann tensor (which needs
first partial derivatives of Γ, as data), Ricci (a contraction of
Riemann), scalar curvature (Ricci traced against the inverse metric),
and Einstein tensor `G_{μν} = R_{μν} − ½ R g_{μν}`.

**Representation.** A `ConnectionData n` carries connection
coefficients `Γ^ρ_{μν}(x)` and their first partial derivatives
`∂_λ Γ^ρ_{μν}(x)` as user-supplied data, plus the lower-index
symmetry of Γ. (We do not require Γ to be derived from a metric —
this is the Riemann-tensor-as-formula viewpoint.)

When a `MetricData` is also supplied, contractions to Ricci and scalar
become available.

**Sanity check.** The `flat` instance has `Γ ≡ 0, ∂Γ ≡ 0`; we prove
`riemann ≡ 0`, `ricci ≡ 0`, `scalarCurvature ≡ 0`. This is the
flat-space check — no curvature when Christoffel symbols vanish.

**Hypergraph anchor (status: pending, prioritised).** Same caveat as
`CurvatureLocalCoord.lean`: the curvature tensors here are *targets*
for hypergraph-anchored discrete approximations (Forman-Ricci,
Ollivier-Ricci, discrete connection convergence). They are not
standalone continuum mathematics; they sit on the receiving end of
discrete-to-continuum bridges that are decomposed in
`BRIDGE_MACHINERY.md` Rungs 4.4 and 5.

`minkowski4_satisfies_vacuum_EFE` is the trivial flat-space sanity
check that the formalism is set up correctly. The non-trivial
hypergraph→GR bridge requires (a) a candidate rule, (b) a discrete
Ricci on its causal graph, (c) a convergence theorem. Those are the
priority items, not yet shipped.
-/

import InfraFormalization.CurvatureLocalCoord

namespace InfraFormalization
namespace Curvature

/-- **Connection-with-derivatives data.** -/
structure ConnectionData (n : Nat) where
  /-- `Γ^ρ_{μν}(x)`. -/
  Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- `∂_l Γ^ρ_{μν}(x)`. -/
  dΓ : Fin n → (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ
  /-- Lower-index symmetry of Γ (torsion-free). -/
  Γ_symm : ∀ x ρ μ ν, Γ x ρ μ ν = Γ x ρ ν μ
  /-- Lower-index symmetry of `∂Γ` (inherited from `Γ_symm` when `dΓ` is the
  actual partial derivative; we record it as an axiom since `dΓ` is
  supplied as data). -/
  dΓ_symm : ∀ l x ρ μ ν, dΓ l x ρ μ ν = dΓ l x ρ ν μ

namespace ConnectionData

variable {n : Nat} (C : ConnectionData n)

/-- **Riemann curvature tensor (mixed indices).**

  `R^ρ_{σμν}(x) = ∂_μ Γ^ρ_{νσ}(x) − ∂_ν Γ^ρ_{μσ}(x)
                 + Σ_λ Γ^ρ_{μλ}(x) Γ^λ_{νσ}(x)
                 − Σ_λ Γ^ρ_{νλ}(x) Γ^λ_{μσ}(x)`.
-/
def riemann (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  C.dΓ μ x ρ ν σ - C.dΓ ν x ρ μ σ
    + (∑ l : Fin n, C.Γ x ρ μ l * C.Γ x l ν σ)
    - (∑ l : Fin n, C.Γ x ρ ν l * C.Γ x l μ σ)

/-- **Antisymmetry of Riemann in the last two indices.** `R^ρ_{σμν} = −R^ρ_{σνμ}`. -/
theorem riemann_antisymm (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν = - C.riemann x ρ σ ν μ := by
  unfold riemann
  ring

/-- **First (algebraic) Bianchi identity** for a torsion-free connection:

  `R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0`.

Each `∂Γ` term cancels its cyclic mate using `Γ_symm` and `dΓ_symm`.
The six quadratic `ΓΓ` terms also cancel pairwise. -/
theorem bianchi_first (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    C.riemann x ρ σ μ ν + C.riemann x ρ μ ν σ + C.riemann x ρ ν σ μ = 0 := by
  unfold riemann
  -- All ∂Γ terms cancel by `dΓ_symm`; all ΓΓ terms by `Γ_symm`.
  -- Use Γ_symm to rewrite Γ^ρ_{μλ} = Γ^ρ_{λμ}? No, lower-index symmetry is
  -- Γ x ρ μ λ = Γ x ρ λ μ. So Γ x ρ μ λ * Γ x λ ν σ involves:
  --   second factor lower indices (ν σ): Γ x λ ν σ = Γ x λ σ ν.
  --   first factor lower indices (μ λ): Γ x ρ μ λ = Γ x ρ λ μ.
  -- Use these to relate cyclic terms.
  have hG := C.Γ_symm
  have hdG := C.dΓ_symm
  -- For each cyclic permutation we use symmetries to bring summands to a
  -- common form, and then the six terms cancel pairwise.
  -- Rewrite all the ∂Γ-with-swapped-lower-indices.
  have hd1 : C.dΓ μ x ρ ν σ = C.dΓ μ x ρ σ ν := hdG μ x ρ ν σ
  have hd2 : C.dΓ ν x ρ σ μ = C.dΓ ν x ρ μ σ := hdG ν x ρ σ μ
  have hd3 : C.dΓ σ x ρ μ ν = C.dΓ σ x ρ ν μ := hdG σ x ρ μ ν
  rw [hd1, hd2, hd3]
  -- Now ∂Γ terms: μ-derivs of Γ^ρ_{σν} cancel; ν of Γ^ρ_{μσ} cancel; σ of Γ^ρ_{νμ} cancel.
  -- For ΓΓ terms, rewrite the second-factor lower indices using Γ_symm.
  have hΓ1 : ∀ l, C.Γ x l ν σ = C.Γ x l σ ν := fun l => hG x l ν σ
  have hΓ2 : ∀ l, C.Γ x l μ σ = C.Γ x l σ μ := fun l => hG x l μ σ
  have hΓ3 : ∀ l, C.Γ x l σ μ = C.Γ x l μ σ := fun l => hG x l σ μ
  have hΓ4 : ∀ l, C.Γ x l ν μ = C.Γ x l μ ν := fun l => hG x l ν μ
  have hΓ5 : ∀ l, C.Γ x l μ ν = C.Γ x l ν μ := fun l => hG x l μ ν
  have hΓ6 : ∀ l, C.Γ x l σ ν = C.Γ x l ν σ := fun l => hG x l σ ν
  -- Sum manipulation: combine terms by pairing.
  -- The expression after rewriting becomes a sum of three differences
  -- where ΓΓ-pairs cancel via the Γ_symm rewrites.
  -- Direct approach: after the dΓ rewrites, the linear (∂Γ) part is 0.
  -- Then we need the quadratic part to also be 0. Use simp_rw with
  -- the Γ-symmetries to align all factor orderings, then ring should close.
  ring_nf
  -- After ring_nf the linear-in-∂Γ part should already be 0. The remaining
  -- quadratic part is a sum of 6 ΓΓ terms in cyclic permutations; we need
  -- to identify them via Γ_symm.
  -- Use Finset.sum_add_distrib to combine the cyclic sums:
  have key :
      (∑ l, C.Γ x ρ μ l * C.Γ x l ν σ)
      - (∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
      + ((∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
         - (∑ l, C.Γ x ρ σ l * C.Γ x l ν μ))
      + ((∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
         - (∑ l, C.Γ x ρ μ l * C.Γ x l σ ν)) = 0 := by
    -- Pair (T1) with (T6), (T2) with (T3), (T4) with (T5):
    --   T1: Γ^ρ_{μl} Γ^l_{νσ}     T6 (negated): -Γ^ρ_{μl} Γ^l_{σν}
    --      sum: Γ^ρ_{μl} (Γ^l_{νσ} - Γ^l_{σν}) = 0  via Γ_symm.
    --   T2 (negated): -Γ^ρ_{νl} Γ^l_{μσ}     T3: +Γ^ρ_{νl} Γ^l_{σμ}
    --      sum: Γ^ρ_{νl} (Γ^l_{σμ} - Γ^l_{μσ}) = 0.
    --   T4 (negated): -Γ^ρ_{σl} Γ^l_{νμ}     T5: +Γ^ρ_{σl} Γ^l_{μν}
    --      sum: Γ^ρ_{σl} (Γ^l_{μν} - Γ^l_{νμ}) = 0.
    have p16 : (∑ l, C.Γ x ρ μ l * C.Γ x l ν σ)
             - (∑ l, C.Γ x ρ μ l * C.Γ x l σ ν) = 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l ν σ]
      ring
    have p23 : -(∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
             + (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ) = 0 := by
      rw [show -(∑ l, C.Γ x ρ ν l * C.Γ x l μ σ)
              + (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
            = (∑ l, C.Γ x ρ ν l * C.Γ x l σ μ)
              - (∑ l, C.Γ x ρ ν l * C.Γ x l μ σ) from by ring]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l μ σ]
      ring
    have p45 : -(∑ l, C.Γ x ρ σ l * C.Γ x l ν μ)
             + (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν) = 0 := by
      rw [show -(∑ l, C.Γ x ρ σ l * C.Γ x l ν μ)
              + (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
            = (∑ l, C.Γ x ρ σ l * C.Γ x l μ ν)
              - (∑ l, C.Γ x ρ σ l * C.Γ x l ν μ) from by ring]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intros l _
      rw [hG x l ν μ]
      ring
    linarith
  linarith

/-- **Ricci tensor.** Contraction of Riemann over the first upper and
second lower index: `R_{σν}(x) = Σ_ρ R^ρ_{σρν}(x)`. -/
def ricci (x : Fin n → ℝ) (σ ν : Fin n) : ℝ :=
  ∑ ρ : Fin n, C.riemann x ρ σ ρ ν

/-- **Scalar curvature.** Trace of Ricci against the inverse metric:
`R(x) = Σ_{σν} g^{σν}(x) R_{σν}(x)`.

This requires a metric. We provide the formula here against an
externally-supplied `MetricData`; the type system enforces that the
metric and connection share the same dimension `n`. -/
def scalarCurvature {n : Nat} (M : MetricData n) (C : ConnectionData n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ σ : Fin n, ∑ ν : Fin n, M.ginv x σ ν * C.ricci x σ ν

/-- **Einstein tensor.** `G_{μν}(x) = R_{μν}(x) − ½ R(x) g_{μν}(x)`. -/
noncomputable def einsteinTensor {n : Nat} (M : MetricData n)
    (C : ConnectionData n) (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  C.ricci x μ ν - (1 / 2) * scalarCurvature M C x * M.g x μ ν

end ConnectionData

/-- **Flat connection** on `ℝⁿ`: `Γ ≡ 0, ∂Γ ≡ 0`. -/
def flatConnection (n : Nat) : ConnectionData n where
  Γ := fun _ _ _ _ => 0
  dΓ := fun _ _ _ _ _ => 0
  Γ_symm := by intros; rfl
  dΓ_symm := by intros; rfl

/-- For the flat connection, the Riemann tensor vanishes identically. -/
theorem flatConnection_riemann_zero (n : Nat)
    (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    (flatConnection n).riemann x ρ σ μ ν = 0 := by
  unfold ConnectionData.riemann flatConnection
  simp

/-- For the flat connection, the Ricci tensor vanishes identically. -/
theorem flatConnection_ricci_zero (n : Nat) (x : Fin n → ℝ) (σ ν : Fin n) :
    (flatConnection n).ricci x σ ν = 0 := by
  unfold ConnectionData.ricci
  apply Finset.sum_eq_zero
  intros ρ _
  exact flatConnection_riemann_zero n x ρ σ ρ ν

/-- For the flat connection, the scalar curvature vanishes (against
any metric). -/
theorem flatConnection_scalar_zero {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) :
    ConnectionData.scalarCurvature M (flatConnection n) x = 0 := by
  unfold ConnectionData.scalarCurvature
  apply Finset.sum_eq_zero
  intros σ _
  apply Finset.sum_eq_zero
  intros ν _
  rw [flatConnection_ricci_zero]
  ring

/-- For the flat connection, the Einstein tensor vanishes. -/
theorem flatConnection_einstein_zero {n : Nat} (M : MetricData n)
    (x : Fin n → ℝ) (μ ν : Fin n) :
    ConnectionData.einsteinTensor M (flatConnection n) x μ ν = 0 := by
  unfold ConnectionData.einsteinTensor
  rw [flatConnection_ricci_zero, flatConnection_scalar_zero]
  ring

/-- **Vacuum Einstein equation.** `G_{μν} = 0` on Minkowski with the
flat connection. This is the trivial flat-space sanity check that the
formalism is set up correctly. -/
theorem minkowski4_satisfies_vacuum_EFE
    (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    ConnectionData.einsteinTensor minkowski4 (flatConnection 4) x μ ν = 0 :=
  flatConnection_einstein_zero minkowski4 x μ ν

/-! ## Levi-Civita connection derivation from a metric with second partials

Given a `MetricData n` extended with second partial derivatives
`ddg : Fin n → Fin n → ...`, we can compute both `Γ` (the
Christoffel symbols) and `∂Γ` (their derivatives) explicitly.

The second partials are required because the Riemann tensor formula
involves `∂μ Γ^ρ_{νσ}`, which reduces to second derivatives of the
metric through the Christoffel formula.

We also need `dginv` (partial derivatives of the inverse metric);
from `g · g⁻¹ = I`, differentiating gives
`∂_μ g^{ρσ} = −g^{ρα} g^{σβ} ∂_μ g_{αβ}`. We carry `dginv` as
separate data with this compatibility axiom optional (we do not
enforce it in the structure; it can be checked per-instance).
-/

/-- **Metric with second partial derivatives** — the data required to
compute the full Riemann tensor from the metric via the Levi-Civita
connection. Extends `MetricData n` with:
  * `ddg λ μ x α β := ∂_λ ∂_μ g_{αβ}(x)` (second partials, symmetric
    in the two derivative indices),
  * `dginv λ x ρ σ := ∂_λ g^{ρσ}(x)` (partials of the inverse metric).
-/
structure MetricDataC2 (n : Nat) extends MetricData n where
  /-- Second partial derivatives of the metric: `∂_λ ∂_μ g_{αβ}(x)`. -/
  ddg : Fin n → Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- Partial derivatives of the inverse metric:
      `∂_λ g^{ρσ}(x) = −g^{ρα}(x) g^{σβ}(x) ∂_λ g_{αβ}(x)`.
      We supply this as data (with the compatibility implicit in
      well-formed instances). -/
  dginv : Fin n → (Fin n → ℝ) → Fin n → Fin n → ℝ
  /-- `ddg` has lower-index symmetry inherited from `g`. -/
  ddg_symm : ∀ l m x α β, ddg l m x α β = ddg l m x β α
  /-- `ddg` is symmetric in the two derivative indices (Clairaut's
  theorem / Schwarz's theorem: mixed partials commute for smooth `g`). -/
  ddg_swap_deriv : ∀ l m x α β, ddg l m x α β = ddg m l x α β

namespace MetricDataC2

variable {n : Nat} (M : MetricDataC2 n)

/-- **Partial derivative of the Christoffel symbol** (as explicit
formula), computed from the metric data via:

  `∂_λ Γ^ρ_{μν} = ½ (∂_λ g^{ρσ}) (∂_μ g_{σν} + ∂_ν g_{σμ} − ∂_σ g_{μν})
                 + ½ g^{ρσ} (∂_λ ∂_μ g_{σν} + ∂_λ ∂_ν g_{σμ} − ∂_λ ∂_σ g_{μν})`.
-/
noncomputable def dchristoffel (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n,
    (M.dginv l x ρ σ *
       (M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν)
     + M.ginv x ρ σ *
       (M.ddg l μ x σ ν + M.ddg l ν x σ μ - M.ddg l σ x μ ν))

/-- **Lower-index symmetry of `dchristoffel`**. Follows from the
lower-index symmetry of `Γ` being preserved under differentiation
(via `ddg_symm`). -/
theorem dchristoffel_symm (l : Fin n) (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    M.dchristoffel l x ρ μ ν = M.dchristoffel l x ρ ν μ := by
  unfold dchristoffel
  congr 1
  apply Finset.sum_congr rfl
  intros σ _
  have h1 : M.dg μ x σ ν + M.dg ν x σ μ - M.dg σ x μ ν
          = M.dg ν x σ μ + M.dg μ x σ ν - M.dg σ x ν μ := by
    rw [M.dg_symm σ x μ ν]
    ring
  have h2 : M.ddg l μ x σ ν + M.ddg l ν x σ μ - M.ddg l σ x μ ν
          = M.ddg l ν x σ μ + M.ddg l μ x σ ν - M.ddg l σ x ν μ := by
    rw [M.ddg_symm l σ x μ ν]
    ring
  rw [h1, h2]

/-- **Levi-Civita connection data** derived from a `MetricDataC2`.
  * `Γ` = the Christoffel symbols (from the underlying `MetricData`).
  * `dΓ` = computed via the differentiation of the Christoffel formula
    using `dg`, `ddg`, `dginv`.
  * `Γ_symm` = from `christoffel_symm`.
  * `dΓ_symm` = from `dchristoffel_symm`. -/
noncomputable def leviCivitaConnection : ConnectionData n where
  Γ := fun x ρ μ ν => M.toMetricData.christoffel x ρ μ ν
  dΓ := M.dchristoffel
  Γ_symm := fun x ρ μ ν =>
    M.toMetricData.christoffel_symm x ρ μ ν
  dΓ_symm := fun l x ρ μ ν =>
    M.dchristoffel_symm l x ρ μ ν

end MetricDataC2

end Curvature
end InfraFormalization
