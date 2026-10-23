# I05: The Wasserstein expansion in G1-G3 and Ollivier's theorem

Result. G1-G3 state the expansion
$$W(B_\varepsilon(p), B_\varepsilon(q)) = \delta\bigl(1 - \tfrac{\varepsilon^2}{2(d+2)} R + O(\varepsilon^3 + \varepsilon^2\delta)\bigr)$$
with the scalar curvature R, at arXiv:2004.14810 eq. 48 (line 1468) and eq. 80 (line 2054), arXiv:2011.12174 eq. 197 (line 3517), and arXiv:2102.09363 eq. 344 (line 5340) and eq. 373 (line 5868) (READ). Ollivier (2009, Example 7), which G3 cites, gives the expansion with Ric(v,v), the Ricci curvature in the direction v from p to q. For d ≥ 2 the two agree for every direction only where the Ricci tensor vanishes. On the unit sphere S² the ε² coefficients are 1/4 and 1/8.

Lean (PROVED, arithmetic comparisons; Ollivier's theorem is cited, not formalised): `Infra.OllivierIdentityLeading` and `Infra.GorardMisstatedForm` state the two leading forms; `Infra.ollivier_gorard_agree_iff` proves that for δ, ε ≠ 0 the leading terms agree iff R = Ric(v,v); `Infra.ollivier_minus_gorard_leading` gives the difference δε²(R − Ric(v,v))/(2(n+2)); `Infra.s2_gorard_error` gives the value on S². Details: `results/phase2_continuum/eq344_verdict.md`.

Substituting Ric(v,v) for R gives Ollivier's expansion. G1 Definition 31 (lines 1521-1534), G2 (lines 3580-3582) and G3 (lines 5413-5416) state that κ(p, q) reduces to the scalar curvature R(p, q). The note records each location with the formula from the source.

Target venue: arXiv math.DG, math-ph, as a short note.

Length: 8-12 pages.

Open items: a Lean proof of Ollivier's theorem would replace the citation; it is not needed for the comparison.
