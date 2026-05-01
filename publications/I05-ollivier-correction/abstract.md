# I05 — Correcting the Ollivier–Ricci Identity in the Wolfram-Model Corpus

**Thesis.** The Wasserstein-vs-Ricci identity used throughout the JGORARD Wolfram-model corpus (arXiv:2004.14810 line 604, arXiv:2011.12174 lines 1668/1699/1882, arXiv:2102.09363 Eq 344), written in each case with the *scalar* Ricci curvature $R$,
$$W_1(m_p^\varepsilon, m_q^\varepsilon) = \delta\bigl(1 - \tfrac{\varepsilon^2}{2(d+2)} R + O(\varepsilon^3 + \varepsilon^2\delta)\bigr),$$
directly contradicts the Ollivier 2009 theorem (which JGORARD cites as the source), which has the *directional* Ricci $\mathrm{Ric}(v, v)$ in place of $R$. On $S^2$ the two forms differ by a factor of 2. We document the error, provide the correct form as a formally-stated Lean predicate `OllivierIdentityLeading`, contrast it with JGORARD's `GorardMisstatedForm`, and prove their algebraic non-equivalence in a theorem `ollivier_vs_gorard_equivalence_requires_ric_eq_scalar`.

**What is and is not claimed.** We do *not* claim the correct Ollivier identity is wrong. We claim that what appears in the JGORARD corpus is not the Ollivier identity but a scalar-Ricci variant that holds only on Einstein-flat manifolds. The correction is arithmetic-level and does not by itself rescue the program; several *structural* flaws remain (see the companion major paper M01).

**Target venue.** arXiv math.DG + math-ph, as a short *correction note*.

**Sufficient Lean support.** T27 (`OllivierIdentityLeading`), T28 (`ollivier_vs_gorard_equivalence_requires_ric_eq_scalar`), plus the full Ollivier 2009 theorem citation.

**Length target.** 8–12 pages.

**Dependencies on research not yet done.** Minor: a full Lean-proved version of Ollivier's 2009 theorem would strengthen this note but is not required.
