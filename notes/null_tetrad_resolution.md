# Null tetrad in Gorard's papers — where it actually is, and what it's for

**Bottom line.** The null tetrad is NOT extracted from a hypergraph. It is built on the *continuum metric tensor* that the CCZ4/BSSN numerical relativity code computes on a hypergraph-as-adaptive-mesh. The hypergraph's only role in the tetrad construction is to provide grid points. This is standard numerical-relativity gravitational-wave extraction and has no novel content.

## Location in the papers
All null-tetrad / Newman–Penrose material is in arXiv:2102.09363, §6 (gravitational wave extraction / black-hole merger simulations):

- Line 3002 (`gorard_2102.09363.txt`): orthonormal tetrad introduced for numerical eigenvalue problems.
- Line 3960 onward: Newman–Penrose formalism, Weyl scalar Ψ₄ = C_αβγδ n^α m̄^β n^γ m̄^δ (Eq 267).
- Eqs 268–270 (lines 3973–3987): standard null-tetrad algebraic conditions (l·l = n·n = m·m = 0; l·n = −1; m·m̄ = 1; all other zero; g^ij = −l^i n^j − n^i l^j + m^i m̄^j + m̄^i m^j).
- Eqs 274–281: background Kinnersley tetrad in Boyer–Lindquist coordinates for Kerr — completely standard (Kinnersley 1969).
- Eqs 282–286 (lines 4105–4150): numerical construction of ℓ̃, ñ, m̃ from 3+1 basis (u, r, θ, φ) via Gram–Schmidt on the spatial metric γ_ij as given numerically.
- Eqs 298–301: null rotations + boost (Baker–Campanelli–Lousto 2002) rotating the computed tetrad into Kinnersley form.
- Eq 302: Ψ₄ computed by projecting the spatial Riemann tensor onto the tetrad.
- Eq 303: h = h_+ − i h_× obtained via double time-integral of Ψ₄.

## Why this does not answer "tetrad on a hypergraph"

The construction relies on:
- A four-velocity u^μ that is the normal to a spacelike hypersurface in a pseudo-Riemannian (M,g).
- A spatial metric γ_ij and an inverse three-metric γ^ij on that hypersurface.
- A 3+1 decomposition (lapse α, shift β^i).
- The Weyl curvature tensor C_ijkl (which requires a metric-compatible connection).

Every one of these is a continuum object. They exist in 2102.09363 only because the code runs CCZ4 — which is a reformulation of the Einstein PDEs — on values stored at hypergraph vertices. The hypergraph is a mesh, nothing more. If you strip the CCZ4 PDE layer, you get "pure Wolfram model evolution" and **none of these objects exist**: there is no metric, no lapse, no shift, no Weyl tensor, no tetrad.

## What Gorard's "pure Wolfram model evolution" actually does (companion claim)

On the "pure" side, Gorard does *not* build a tetrad. Instead, he cites a "hypergraph substitution rule that provably satisfies the Einstein field equations in the continuum limit" and compares its emergent spacetime to the CCZ4 one. That claim is traced (2102.09363 §5, around line 6000+) to the Benincasa–Dowker action from causal-set theory:

1. Define a discrete d'Alembertian B^(d) on a causal graph (Eqs 378, 379) — copied from Benincasa–Dowker 2010.
2. Under **uniform Poisson sampling** of events in (M,g), expected value of the smoothed B_k^(d) converges to □φ − (1/2) R(x) φ(x) (Eq 383) — Sorkin–Benincasa–Dowker conjecture, supported by numerical work of Cunningham.
3. Set φ ≡ 1; discrete action S^(4) = (4/√6)[n − N_0 + 9N_1 − 16N_2 + 8N_3] (Eq 386) becomes the expectation of a local curvature scalar.
4. Under further assumptions (zero surface terms, far-light-cone contributions vanish), S^(4) converges in expectation to the Einstein–Hilbert action S_EH(g) as Poisson density ρ_c → ∞ (Eq 387).

This chain is **three layers of conjecture/numerical support, not proof**, and every one of its steps is **about causal sets, not about the Wolfram model**. Nothing in the Wolfram-model rewriting dynamics is used — what is used is the statement "if the hyperedges/causal-graph edges look like a Poisson-sampled causal set in (M,g), then the Benincasa–Dowker counting functional reproduces the EH action in expectation."

So the "provably satisfies EFE in continuum limit" claim reduces to:
- **True content**: Benincasa–Dowker action on a Poisson causal set has expectation converging to EH (a conjecture in causal-set theory, not proven; partial numerical evidence).
- **What is not content**: the Wolfram-model substitution rule is never shown to produce causal graphs that converge in the required distributional sense. It is **assumed** they do.

## Two immediate consequences for this project

1. "The null tetrad question" — the one the user flagged — has a clean answer: **there is no hypergraph-native tetrad**, so there is nothing to formalise on the Lean side beyond ordinary Lorentzian NR. The question to flag upstream: does 2303.07282, which applies Raychaudhuri + singularity theorems, also work exclusively on the continuum side? (Check needed — preliminary grep shows Raychaudhuri language in the abstract but no "tetrad" in 2303.07282's text.)
2. The "pure Wolfram model rule that satisfies EFE in the continuum limit" claim is actually the Benincasa–Dowker convergence conjecture *applied to* a Poisson sampling assumption on causal graphs. Any Lean-side or mathematical attack on this claim goes through the causal-set literature, not through Gorard-specific machinery.
