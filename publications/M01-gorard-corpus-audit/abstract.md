# M01 — A Machine-Checked Audit of the Wolfram-Model General-Relativity Programme

**Thesis.** The claim that general relativity has been derived from Wolfram-model hypergraph rewriting — as articulated across Gorard arXiv:2004.14810 (seminal), arXiv:2011.12174 (causal-sets link), arXiv:2102.09363 (Cauchy problem), arXiv:2303.07282 (singularity theorems) — is not established by the corpus. We provide an equation-level catalog of every continuum-limit claim, classify errors into six severity tiers (S1 false statements, S2 ill-defined objects, S3 tautologies, S4 unsupported bridges, S5 refuted specific claims, S6 title/abstract overclaims), expose eight major structural flaws (F1–F8) that are *not* reparable by arithmetic corrections, and empirically refute the single specific rule advertised as "provably satisfying the Einstein field equations in the continuum limit." All load-bearing structural observations are machine-verified in Lean 4 + Mathlib 4.29.1, with `#print axioms` establishing dependence only on Lean's three standard axioms.

**What we establish.** (1) Two specific arithmetic errors — the Ollivier directional/scalar Ricci conflation (S1 #1, appearing 6 times verbatim across 3 papers) and the Gray tube coefficient error (S1 #2, appearing in 2 papers) — contradict cited sources. (2) Several central constructions — a discrete metric tensor $g^{ab}$, a discrete functional derivative $\delta/\delta g^{ab}$, "fiat orthonormality" of non-parallel hyperedges — are declared rather than defined (F1, F2). (3) The central $\delta S/\delta g^{ab} \to 0 \Rightarrow $ Einstein's equations argument is tautological: the hypothesis is the Euler-Lagrange equation of the claimed action (F3). (4) The "provably satisfies EFE" claim in arXiv:2102.09363 is circular — the target manifold is Poisson-sampled into the hypergraph, then "recovered" by Benincasa–Dowker counting (F6). (5) The specific named rule is structurally incapable of producing a 3+1-dimensional causal graph (F7).

**What we do not claim.** We do not claim the underlying idea is worthless, nor that any data were fabricated. The pattern is best described as physics-style plausibility arguments written with the grammar of mathematical proof. The corpus contains genuine numerical-relativity content (CCZ4-on-mesh simulations) that is valid in its own right; those portions survive the audit unchanged.

**Companion positive work.** Companion incremental papers I01–I07 provide corrected versions of the specific errors documented here; companion major paper M02 lays the foundations of a genuine infrageometry programme that replaces Gorard's vacuous apparatus with rigorous discrete-to-continuum convergence theorems.

**Target venue.** arXiv math-ph + gr-qc + cs.LO, possibly submitted to the *Bulletin of the American Mathematical Society* (audit / exposition track) or *Complex Systems* (the journal that published the corpus under audit).

**Sufficient Lean support.** The full structural-theorem library (T1–T15 for Wolfram-model facts; T27–T31 for corrected continuum identities), plus the Python + SetReplace cross-check of the named-rule refutation.

**Length target.** 30–50 pages including Lean code listings in an appendix.

**Dependencies on research not yet done.** None for the audit portion. The positive-side-of-the-ledger claims cite M02 and the companion papers.
