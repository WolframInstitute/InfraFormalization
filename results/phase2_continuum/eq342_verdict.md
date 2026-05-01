# Phase 2B — Eq 342 audit verdict: ✗ REFUTED

**Claim (arXiv:2102.09363 Eq 342, = arXiv:2011.12174 Eq 126).** For a geodesic tube of radius $\varepsilon$ around a geodesic segment of length $\delta$ with unit tangent $\hat{\delta x}$ in a $d$-dim Riemannian manifold:
$$
\mathrm{Vol}(T_{\varepsilon, \delta x}(p)) = \frac{\pi^{(d-1)/2}}{\Gamma((d+1)/2)}\,\varepsilon^{d-1}\,\delta\;\left(1 - \frac{d-1}{d+1}\Big(R - R_{ij}\hat{\delta x}^i\hat{\delta x}^j\Big)\varepsilon^2 + O(\varepsilon^3 + \varepsilon^2\delta) + \dots\right).
$$

**Verdict.** Incorrect — both in algebraic structure and in overall scale. Verified by two exact closed-form test cases.

## Four-rail verification

### Rail A. Independent derivation from Fermi normal coordinates

Using Fermi normal coordinates along the geodesic (standard reference: Misner–Thorne–Wheeler §8.7; Manasse–Misner 1963; Gray, *Tubes* 2nd ed. §4), the metric expansion is:

$$
g_{ss}(s,y) = 1 - R_{s\alpha s\beta}(\gamma(s))\,y^\alpha y^\beta + O(|y|^3)
$$
$$
g_{\alpha\beta}(s,y) = \delta_{\alpha\beta} - \tfrac{1}{3} R_{\alpha\gamma\beta\delta}(\gamma(s))\,y^\gamma y^\delta + O(|y|^3)
$$

with $s$ tangential and Greek indices perpendicular. Then
$$
\det g = 1 - \tfrac{2}{3}R_{s\alpha s\beta} y^\alpha y^\beta - \tfrac{1}{3} R^\perp_{\alpha\beta} y^\alpha y^\beta + O(|y|^4),
$$
where $R^\perp_{\alpha\beta} = R_{\alpha\beta} - R_{s\alpha s\beta}$ is the Ricci tensor restricted to perpendicular indices.

Taking the square root and integrating $y^\alpha y^\beta$ over the $(d-1)$-ball (which yields $\omega_{d-1}\varepsilon^{d+1}\delta^{\alpha\beta}/(d+1)$):

$$
\int_{|y|\le\varepsilon}\sqrt{\det g}\,d^{d-1}y
= \omega_{d-1}\varepsilon^{d-1}\left[1 - \frac{\varepsilon^2}{d+1}\left(\tfrac{1}{3}\sum_{\alpha\perp u}R_{s\alpha s\alpha} + \tfrac{1}{6}\sum_{\alpha\perp u}R_{\alpha\alpha}\right)\right] + O(\varepsilon^{d+3}).
$$

Using $\sum_{\alpha\perp u} R_{s\alpha s\alpha} = \mathrm{Ric}(u,u)$ and $\sum_{\alpha\perp u} R_{\alpha\alpha} = R - \mathrm{Ric}(u,u)$:

$$
\boxed{\;\mathrm{Vol}(T_\varepsilon(\gamma)) = \omega_{d-1}\varepsilon^{d-1}L\left(1 - \frac{\varepsilon^2}{6(d+1)}\bigl(R + \mathrm{Ric}(u,u)\bigr) + O(\varepsilon^4)\right).\;}
$$

(Multiplication by $L$ simply integrates along the geodesic since $R, \mathrm{Ric}$ are approximately constant over an infinitesimal segment.)

### Rail B. Symbolic verification in Mathematica

Series expansion of the exact closed-form tube volume on $S^2$ and $S^3$ (around great circles, length $L=2\pi$) reproduces the Rail-A coefficient and disagrees with JGORARD's:

| Manifold | Closed-form volume | $\varepsilon^2$ coeff (series) |
|---|---|---|
| $S^2$ | $4\pi\sin\varepsilon$ | $1 - \varepsilon^2/6 + \varepsilon^4/120 - \ldots$ |
| $S^3$ | $2\pi^2\sin^2\varepsilon$ | $1 - \varepsilon^2/3 + 2\varepsilon^4/45 - \ldots$ |

See `scripts/test_eq342.wl`; the series are produced by `Series[exact/flat, {eps, 0, 4}]`.

### Rail C. Numerical test at several $\varepsilon$

Relative error in the tube-volume prediction versus the exact value:

**$S^2$:**

| $\varepsilon$ | exact ratio | Rail-A prediction | JGORARD Eq 342 | \|err\|/exact (JGORARD) |
|---:|---:|---:|---:|---:|
| 0.05 | 0.99958 | 0.99958 | 0.99917 | 4.2e-4 |
| 0.10 | 0.99833 | 0.99833 | 0.99667 | 1.7e-3 |
| 0.15 | 0.99625 | 0.99625 | 0.99250 | 3.8e-3 |
| 0.20 | 0.99335 | 0.99333 | 0.98667 | 6.7e-3 |
| 0.30 | 0.98507 | 0.98500 | 0.97000 | 1.5e-2 |

Rail-A prediction matches the exact value to O($\varepsilon^4$); JGORARD's error grows as $\varepsilon^2$, consistent with the coefficient being off by a factor of 2.

**$S^3$:**

| $\varepsilon$ | exact ratio | Rail-A prediction | JGORARD Eq 342 | \|err\|/exact (JGORARD) |
|---:|---:|---:|---:|---:|
| 0.05 | 0.99917 | 0.99917 | 0.99500 | 4.2e-3 |
| 0.10 | 0.99667 | 0.99667 | 0.98000 | 1.7e-2 |
| 0.15 | 0.99252 | 0.99250 | 0.95500 | 3.8e-2 |
| 0.20 | 0.98674 | 0.98667 | 0.92000 | 6.8e-2 |
| 0.30 | 0.97036 | 0.97000 | 0.82000 | 1.5e-1 |

At $\varepsilon = 0.3$, JGORARD's Eq 342 gives a 15 % relative error on $S^3$. For comparison, the correct Rail-A formula gives a $4 \times 10^{-4}$ relative error (the residual $\varepsilon^4$ term, exactly as predicted).

### Rail D. Hand-computation on $S^2$

At a great-circle belt of half-width $\varepsilon$ on the unit sphere: parametrize by latitude $\theta \in [\tfrac{\pi}{2}-\varepsilon, \tfrac{\pi}{2}+\varepsilon]$ and longitude $\phi \in [0, 2\pi)$. Area element $\sin\theta \, d\theta \, d\phi$. Integrating:
$$
A = 2\pi \int_{\pi/2-\varepsilon}^{\pi/2+\varepsilon}\sin\theta\, d\theta = 2\pi \bigl[\cos(\tfrac{\pi}{2}-\varepsilon) - \cos(\tfrac{\pi}{2}+\varepsilon)\bigr] = 4\pi \sin\varepsilon.
$$
Ratio to flat $(2\varepsilon)\cdot(2\pi) = 4\pi\varepsilon$: $\sin\varepsilon/\varepsilon = 1 - \varepsilon^2/6 + O(\varepsilon^4)$. Coefficient **1/6**, matching Rails A–C.

## Summary

| Rail | What it gives | Matches? |
|---|---|---|
| A — Independent derivation | $(R + \mathrm{Ric}(u,u))/(6(d+1))$ | ✓ |
| B — Symbolic series on $S^2, S^3$ | 1/6 and 1/3 | ✓ |
| C — Numerical at several $\varepsilon$ | agrees with A to $O(\varepsilon^4)$ | ✓ |
| D — Hand computation on $S^2$ | 1/6 | ✓ |

**All four rails agree** on the correct value. JGORARD's Eq 342 disagrees on both test manifolds:

| | $S^2$ | $S^3$ |
|---|---|---|
| Correct $\varepsilon^2$ coefficient | 1/6 | 1/3 |
| JGORARD Eq 342 coefficient | 1/3 | 2 |
| Ratio JGORARD/correct | 2 | 6 |

The ratio JGORARD/correct is not constant across $d$, so Eq 342 is not "off by an overall factor" — its algebraic structure is wrong: $(R - \mathrm{Ric}(u,u))\cdot(d-1)/(d+1)$ vs the correct $(R + \mathrm{Ric}(u,u))/(6(d+1))$.

## Propagation / downstream impact

- Eq 342 is the specialization of a formula given earlier in arXiv:2011.12174 Eq 126; the error thus traces back to that paper.
- The 2004.14810 main paper does not use the tube formula directly, so Eq 342's error does not invalidate the §3 Einstein-equations sketch there (which fails on other grounds — see `notes/2004.14810_close_reading.md`).
- Eq 342 is invoked in 2102.09363 §5 to probe "higher-order contractions of the Riemann curvature tensor" on hypergraphs; any hypergraph-dimension or hypergraph-Ricci inference drawn from the tube-volume growth rate using Eq 342 is calibrated against the wrong continuum formula and will systematically mis-estimate curvature in both magnitude and sign sensitivity.

## Reproducing

```
wolframscript -file scripts/test_eq342.wl
```

The script produces exact symbolic series, exact numerical values, and side-by-side comparisons for both $S^2$ and $S^3$.
