# G3 eq. 344 and Ollivier's theorem

## Statement in G3

arXiv:2102.09363 eq. 344 (`papers/gorard_2102.09363.txt` line 5340, TeX `papers/tex_2102/NumericalRelativity.tex` line 2626, §6) gives the average distance W between points of the ball B_ε(p) and the corresponding points of B_ε(q) after parallel transport:
$$
W(B_\varepsilon(p), B_\varepsilon(q)) \;=\; \delta \left(1 - \frac{\varepsilon^2}{2(d+2)}\,R + O(\varepsilon^3 + \varepsilon^2 \delta)\right),
$$
with δ = d(p, q) and R the scalar curvature. The paragraph that follows (TeX line 2628) cites Ollivier for the extension to metric measure spaces. G3 TeX line 2645 states that κ(p, q) "reduces to the usual Riemannian Ricci curvature scalar R(p, q) (up to a multiplicative constant)".

The same expansion with R appears in arXiv:2004.14810 as eq. 48 (`papers/gorard_2004.14810.txt` line 1468) and eq. 80 (lines 2045-2056), in arXiv:2011.12174 as eq. 197 (`papers/gorard_2011.12174.txt` line 3517), and in G3 again as eq. 373 (line 5868). G1 Definition 31 (lines 1521-1534) states that κ(p, q) "reduces (up to some arbitrary scaling factor) to the standard Riemannian Ricci scalar curvature R(p, q)". G2 (lines 3580-3582) and G3 (lines 5413-5416) state the same reduction.

## Statement in Ollivier (2009)

Y. Ollivier, "Ricci curvature of Markov chains on metric spaces", J. Funct. Anal. 256 (2009) 810-864, Example 7. Let (M, g) be a smooth n-dimensional Riemannian manifold and m_x^ε the uniform probability measure on B_ε(x). For y at distance δ from x and v the unit tangent vector at x towards y,
$$
\kappa(x,y) = 1 - \frac{W_1(m_x^\varepsilon, m_y^\varepsilon)}{\delta} = \frac{\varepsilon^2}{2(n+2)}\,\mathrm{Ric}(v,v) + O(\varepsilon^3 + \varepsilon^2 \delta),
$$
so that W_1 = δ(1 − ε² Ric(v,v)/(2(n+2)) + O(ε³ + ε²δ)).

## Comparison

| | Ollivier 2009 | G3 eq. 344 |
|---|---|---|
| Prefactor | δ | δ |
| ε² coefficient | Ric(v,v)/(2(d+2)) | R/(2(d+2)) |

Ric(v,v) = R_ij v^i v^j is the Ricci tensor evaluated on the direction from p to q. R = g^ij R_ij is its trace. The two coefficients agree for every unit v exactly when Ric(v,v) = R for every unit v. Taking the trace over an orthonormal basis gives R = dR, so for d ≥ 2 they agree only where R = 0 and Ric = 0.

On the unit sphere S²: R = 2 and Ric(v,v) = 1 for every unit v. The ε² coefficient is 1/8 in Ollivier's formula and 1/4 in eq. 344.

Lean (PROVED, axioms `propext`, `Classical.choice`, `Quot.sound`; Ollivier's theorem is cited, not formalised):

| Theorem | File:line | Statement |
|---|---|---|
| `Infra.ollivier_minus_gorard_leading` | `lean/InfraFormalization/Infra/OllivierStatement.lean:93` | The leading terms differ by δε²(R − Ric(v,v))/(2(n+2)) |
| `Infra.ollivier_gorard_agree_iff` | `Infra/OllivierStatement.lean:107` | For δ, ε ≠ 0 the leading terms agree iff R = Ric(v,v) |
| `Infra.s2_gorard_error` | `Infra/OllivierStatement.lean:137` | The discrepancy on S² |

Substituting Ric(v,v) for R in eq. 344 gives Ollivier's formula.

## Monte Carlo estimate

MEASURED with `scripts/python/test_eq344.py` (rerun 2026-10-23): W_1 between empirical uniform measures on two geodesic discs of S², by optimal assignment of N samples per disc, for δ ∈ {0.05, 0.10, 0.15} and ε ∈ {0.03, 0.05, 0.08, 0.10}. At N = 600 the ratio W_1/δ ranges from 0.953 to 1.050. The two formulas differ in W_1/δ by ε²/8, which is 1.25 × 10⁻³ at ε = 0.1. The sampling error at N = 600 is larger than this difference, so the run does not distinguish the two formulas. The comparison above rests on the statement of Ollivier's theorem.

## Use of eq. 344 in G3

G3 §6 uses eq. 344 to motivate the discrete Ollivier-Ricci curvature of hypergraphs that follows it (TeX lines 2628-2648), citing Forman, Ollivier, and Eidi and Jost. A discrete curvature whose continuum calibration is eq. 344 is compared against R where Ollivier's theorem gives Ric(v,v).

## Reproducing

- The comparison of coefficients needs no computation.
- `python3 scripts/python/test_eq344.py` prints the Monte Carlo table (NumPy and SciPy required).
