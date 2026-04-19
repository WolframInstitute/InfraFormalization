# Phase 2C — Eq 344 audit verdict: ✗ REFUTED

**Claim (arXiv:2102.09363 Eq 344, TeX line 2626).** For two points $p, q$ on a $d$-dim Riemannian manifold with $\delta = d(p,q)$, and $\varepsilon$-uniform-ball measures $m_p^\varepsilon, m_q^\varepsilon$:
$$
W(B_\varepsilon(p), B_\varepsilon(q)) \;=\; \delta \left(1 - \frac{\varepsilon^2}{2(d+2)}\,R + O(\varepsilon^3 + \varepsilon^2 \delta)\right),
$$
where $R$ is the scalar Ricci curvature at $p$.

**Verdict.** Incorrect. The correct statement, due to Ollivier — whom Gorard cites in the immediately preceding paragraph (TeX line 2628 cites `\cite{ollivier}` for the generalization to metric-measure spaces) — has the **directional** Ricci tensor $\mathrm{Ric}(v, v)$ (where $v$ is the unit vector from $p$ to $q$) in place of $R$.

This is a direct contradiction of the published theorem Gorard imports.

## Rail A — Statement of Ollivier's theorem

**Ollivier's Theorem** (Y. Ollivier, "Ricci curvature of Markov chains on metric spaces", *J. Funct. Anal.* 256 (2009) pp. 810–864, Example 7 + Theorem 4):

Let $(M,g)$ be a smooth $n$-dimensional Riemannian manifold and let $m_p^\varepsilon$ denote the normalized uniform probability measure on the geodesic ball $B_\varepsilon(p)$. For $p, q \in M$ with $d(p,q) = \delta$ small and $v \in T_pM$ the unit vector tangent to the minimizing geodesic from $p$ to $q$:
$$
\boxed{\;W_1(m_p^\varepsilon, m_q^\varepsilon) = \delta\left(1 - \frac{\varepsilon^2}{2(n+2)}\,\mathrm{Ric}(v,v) + O(\varepsilon^4 + \varepsilon^2 \delta^2)\right).\;}
$$
(Note: Ollivier writes this as an expansion of the Ollivier-Ricci curvature $\kappa = 1 - W_1/d$; we have re-solved for $W_1$.)

Here $\mathrm{Ric}(v,v) = R_{ij}v^i v^j$ is a **scalar** but a **directional** one, not the scalar curvature $R = g^{ij}R_{ij}$.

## Rail B — Algebraic comparison

| | Ollivier 2009 Thm | Gorard Eq 344 | Same formula? |
|---|---|---|---|
| Prefactor | $\delta$ | $\delta$ | ✓ |
| $\varepsilon^2$ correction | $\dfrac{\mathrm{Ric}(v,v)}{2(d+2)}$ | $\dfrac{R}{2(d+2)}$ | ✗ |

Identity iff $\mathrm{Ric}(v,v) = R$ for all unit $v$, which holds iff:
- $d = 1$: trivial, both sides equal 0.
- $d \ge 2$, Einstein manifold: then $\mathrm{Ric} = \tfrac{R}{d}g$, so $\mathrm{Ric}(v,v) = R/d$, giving equality only when $R = R/d$, i.e., $R = 0$ (flat).
- In general: $\mathrm{Ric}(v,v) \ne R$ whenever $R \ne 0$ and $d \ge 2$.

So Eq 344 disagrees with Ollivier on every nontrivial curved manifold.

## Rail C — Concrete disagreement on $S^2$

Unit round $S^2$: $d = 2$, $R = 2$, $\mathrm{Ric}(v,v) = 1$ for every unit $v$.

| | coefficient of $\varepsilon^2$ correction |
|---|---:|
| Ollivier's theorem | $1/8 = 0.125$ |
| Gorard Eq 344 | $2/8 = 0.250$ |

Gorard's prediction is **twice** the Ollivier value. At $\varepsilon = 0.3$: Ollivier $1 - 0.01125 \cdot \delta$, Gorard $1 - 0.0225 \cdot \delta$. Relative discrepancy $O(\varepsilon^2 \cdot \delta)$ – small in absolute terms but propagates through all downstream arguments.

## Rail D — Why we do not present a direct numerical verification

In a bounded-from-below direction: we attempted Monte Carlo estimation of $W_1(m_p^\varepsilon, m_q^\varepsilon)$ on $S^2$ with IID uniform samples on $B_\varepsilon(p)$ and $B_\varepsilon(q)$ and bipartite-matching (see `scripts/python/test_eq344.py`). The signal we wish to measure is $\Delta = \varepsilon^2/(2(d+2)) \cdot (R - \mathrm{Ric}(v,v)) \cdot \delta$, which on $S^2$ with $\varepsilon = 0.1, \delta = 0.1$ is $\approx 1.25 \times 10^{-3}$. Monte Carlo estimation of $W_1$ on a 2-dim space converges at rate $\log N / \sqrt{N}$ (Talagrand 1992; Dudley 1968; Ajtai–Komlós–Tusnády 1984), giving for $N = 600$ a noise floor of $\approx 0.06$ — **nearly 50× the signal**. Distinguishing the two predictions numerically would require $N$ of order $10^7$ or an analytical / deterministic approach.

The refutation nevertheless stands on Rails A–C above. We propose as Phase 2C follow-up work a deterministic analytical verification via the canonical parallel-transport plan, which at small $\varepsilon$ is known (Ollivier 2009, §5.1) to realize $W_1$ up to $O(\varepsilon^4)$; the canonical cost on $S^2$ can be computed exactly via Jacobi fields and would give a deterministic test. This is not required to establish the refutation but would be a useful auxiliary rail.

## Structural significance

The error in Eq 344 propagates into every use of the discrete Ollivier–Ricci curvature in 2102.09363 §5 that is motivated by "generalizing" this Riemannian identity. If the Riemannian identity is wrong, the discrete generalization inherits the mis-calibration: curvatures extracted from hypergraph ball-growth rates are being calibrated against the wrong continuum formula.

This is the **same error pattern** as in arXiv:2004.14810 Def 31 (see `notes/2004.14810_close_reading.md`, claim A3), where Gorard writes "the Ollivier-Ricci scalar curvature $\kappa(p,q)$ reduces to the standard Riemannian Ricci scalar curvature $R(p,q)$" — "$R(p,q)$" is not a standard object; Ollivier's theorem gives $\mathrm{Ric}(v,v)$ for $v$ the direction $p \to q$.

The pattern: **Gorard consistently conflates the directional Ricci tensor $\mathrm{Ric}(v,v)$ with the scalar curvature $R$**, both in 2004.14810 and in 2102.09363. On constant-curvature manifolds these are proportional but not equal; on general Riemannian manifolds they are independent quantities.

## Reproducing

- **Structural refutation (Rails A–C)** requires no computation; it is a literature comparison.
- **Numerical setup** (illustrating the MC difficulty) is in `scripts/python/test_eq344.py`; running `python3 test_eq344.py` produces the table showing $W_1/\delta$ scattered around 1 with $\sim 5\%$ noise, consistent with the predicted MC convergence rate.
