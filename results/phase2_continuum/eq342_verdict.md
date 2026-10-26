# G3 eq. 342 and the tube-volume expansion

## Statement in G3

arXiv:2102.09363 eq. 342 (`papers/gorard_2102.09363.txt` line 5276, TeX `papers/tex_2102/NumericalRelativity.tex` line 2607, §6) and arXiv:2011.12174 eq. 126 (`papers/gorard_2011.12174.txt` line 2409, TeX `papers/tex_2011/CausalSetPaper.tex` line 1165) give the volume of a tube of radius ε around a geodesic segment of length δx with unit tangent δx̂ in a d-dimensional Riemannian manifold:
$$
\mathrm{Vol}(T_{\varepsilon, \delta x}(p)) = \frac{\pi^{(d-1)/2}}{\Gamma((d+1)/2)}\,\varepsilon^{d-1}\,\delta x\;\left(1 - \frac{d-1}{d+1}\Big(R - R_{ij}\hat{\delta x}^i\hat{\delta x}^j\Big)\varepsilon^2 + O(\varepsilon^3 + \varepsilon^2\delta x) + \dots\right).
$$

## Expansion from Fermi normal coordinates

References: Gray, *Tubes*, 2nd ed.; Manasse and Misner (1963); Misner, Thorne and Wheeler §8.7. In Fermi normal coordinates along the geodesic, with s the arc length and Greek indices for the d − 1 normal directions,
$$
g_{ss}(s,y) = 1 - R_{s\alpha s\beta}\,y^\alpha y^\beta + O(|y|^3),\qquad
g_{\alpha\beta}(s,y) = \delta_{\alpha\beta} - \tfrac{1}{3} R_{\alpha\gamma\beta\delta}\,y^\gamma y^\delta + O(|y|^3).
$$
Since Σ_α R_αγαδ over normal α equals R_γδ − R_sγsδ,
$$
\sqrt{\det g} = 1 - \tfrac{1}{3}R_{s\alpha s\beta}\, y^\alpha y^\beta - \tfrac{1}{6} R_{\alpha\beta}\, y^\alpha y^\beta + O(|y|^3),
$$
where R_αβ is the Ricci tensor at normal indices. The integral of y^α y^β over the (d−1)-ball of radius ε is ω_{d−1} ε^{d+1} δ^{αβ}/(d+1). With Σ_α R_sαsα = Ric(u,u) and Σ_α R_αα = R − Ric(u,u),
$$
\mathrm{Vol}(T_\varepsilon(\gamma)) = \omega_{d-1}\varepsilon^{d-1}L\left(1 - \frac{\varepsilon^2}{6(d+1)}\bigl(R + \mathrm{Ric}(u,u)\bigr) + O(\varepsilon^4)\right).
$$

## Checks on S² and S³

The tube of radius ε around a great circle (L = 2π) has volume 4π sin ε on the unit S² and 2π² sin² ε on the unit S³. The ratio to the flat value ω_{d−1} ε^{d−1} L has the series 1 − ε²/6 + ε⁴/120 on S² and 1 − ε²/3 + 2ε⁴/45 on S³ (`scripts/test_eq342.wl`, `Series[exact/flat, {eps, 0, 4}]`).

On S² the tube is the spherical zone between latitudes π/2 − ε and π/2 + ε, with area 2π ∫ sin θ dθ = 4π sin ε. The ratio to 4πε is 1 − ε²/6 + O(ε⁴).

| | S² (R = 2, Ric(u,u) = 1) | S³ (R = 6, Ric(u,u) = 2) |
|---|---|---|
| ε² coefficient of the exact series | 1/6 | 1/3 |
| (R + Ric(u,u))/(6(d+1)) | 1/6 | 1/3 |
| (d−1)(R − Ric(u,u))/(d+1), from eq. 342 | 1/3 | 2 |
| ratio eq. 342 / exact | 2 | 6 |

Ratio of the volume to the flat value at several ε (`scripts/test_eq342.wl`):

S²:

| ε | exact | 1 − ε²/6 | eq. 342 | relative difference of eq. 342 |
|---:|---:|---:|---:|---:|
| 0.05 | 0.99958 | 0.99958 | 0.99917 | 4.2e-4 |
| 0.10 | 0.99833 | 0.99833 | 0.99667 | 1.7e-3 |
| 0.15 | 0.99625 | 0.99625 | 0.99250 | 3.8e-3 |
| 0.20 | 0.99335 | 0.99333 | 0.98667 | 6.7e-3 |
| 0.30 | 0.98507 | 0.98500 | 0.97000 | 1.5e-2 |

S³:

| ε | exact | 1 − ε²/3 | eq. 342 | relative difference of eq. 342 |
|---:|---:|---:|---:|---:|
| 0.05 | 0.99917 | 0.99917 | 0.99500 | 4.2e-3 |
| 0.10 | 0.99667 | 0.99667 | 0.98000 | 1.7e-2 |
| 0.15 | 0.99252 | 0.99250 | 0.95500 | 3.8e-2 |
| 0.20 | 0.98674 | 0.98667 | 0.92000 | 6.8e-2 |
| 0.30 | 0.97036 | 0.97000 | 0.82000 | 1.5e-1 |

The ratio of the two coefficients is 2 on S² and 6 on S³, so the two expressions differ in form as well as by a constant factor.

Lean: `Infra.gray_vs_gorard_disagree_on_S2` (`lean/InfraFormalization/Infra/GrayTubeStatement.lean:39`) and `Infra.gray_vs_gorard_disagree_on_S3` (`:50`) compare the two leading coefficients on S² (1/6 and 1/3) and S³ (PROVED). Gray's formula is cited, not formalised.

Substituting (R + Ric(u,u))/(6(d+1)) for the coefficient of eq. 342 gives the expansion above.

## Use of eq. 342

- G2 eq. 126 states the same formula as G3 eq. 342.
- arXiv:2004.14810 does not contain the word "tube".
- G3 states after eq. 342 that "the growth rate of a small geodesic tube in a hypergraph allows us effectively to probe higher-order contractions of its limiting Riemann curvature tensor" (lines 5287-5291). A curvature estimate from tube growth calibrated by eq. 342 uses the coefficient (d−1)(R − Ric(u,u))/(d+1) in place of (R + Ric(u,u))/(6(d+1)).

## Reproducing

```
wolframscript -file scripts/test_eq342.wl
```

The script prints the exact series and the numerical values for S² and S³.
