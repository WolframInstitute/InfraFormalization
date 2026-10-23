# The null tetrad in arXiv:2102.09363

In arXiv:2102.09363 (G3, `papers/gorard_2102.09363.txt`) the null tetrad is built from the spatial metric that the CCZ4 code evolves at the vertices of a hypergraph. The tetrad construction uses the hypergraph only as the set of grid points. The construction follows the standard gravitational-wave extraction of numerical relativity (Baker, Campanelli and Lousto). All findings below are READ.

## Location in G3

The tetrad material is in §5 (Numerical Convergence Tests, lines 2530-4779). §6 (Comparison to Pure Wolfram Model Evolution) starts at line 4780.

- Line 3002 (§5.2, Kerr black hole): an orthonormal tetrad for the Kerr metric, used with the curvature invariant of eq. 205.
- Lines 3960-3967 (§5.4): the Newman-Penrose Weyl scalar Ψ4 = C_αβγδ n^α m̄^β n^γ m̄^δ (eq. 267).
- Eqs. 268-270 (lines 3973-3987): the null-tetrad conditions (l·l = n·n = m·m = 0, l·n = −1, m·m̄ = 1, other products zero) and g^ij = −l^i n^j − n^i l^j + m^i m̄^j + m̄^i m^j.
- Eqs. 274-281 (lines 4031-4102): the background Kinnersley tetrad for Kerr in Boyer-Lindquist coordinates (Kinnersley 1969).
- Eqs. 282-286 (lines 4105-4150): the numerical construction of the tetrad from a 3+1 basis by Gram-Schmidt orthonormalisation with respect to the spatial metric γ_ij.
- Eqs. 298-301 (lines 4276-4299): null rotations and a boost that bring the computed tetrad to Kinnersley form (Baker, Campanelli and Lousto 2002).
- Eq. 302 (line 4316): Ψ4 from the projection of the curvature onto the tetrad.
- Eq. 303 (line 4329): the strain h = h_+ − i h_× from a double time integral of Ψ4.

## Objects the construction uses

- A unit normal u^μ to a spacelike hypersurface of a Lorentzian manifold (M, g).
- The spatial metric γ_ij and its inverse γ^ij.
- The lapse α and shift β^i of a 3+1 decomposition.
- The Weyl tensor C_ijkl, which requires the Levi-Civita connection of the metric.

The CCZ4 code stores each of these as values at the hypergraph vertices. A hypergraph without these stored fields has a vertex set and a set of hyperedges, with no tangent space, metric, lapse, shift or Weyl tensor.

## The pure Wolfram model case in §6

G3 §6 evolves a hypergraph with the rule {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}} (line 6202) and reports the l = 2, m = 0 mode of rΨ4 "in the pure Wolfram model case" at resolutions of 200, 400 and 800 vertices (lines 6210-6216, Figure 78). G3 does not state how a tetrad, a Weyl tensor or Ψ4 is computed from the evolved hypergraph.

The abstract describes the rule as one "that provably satisfies the Einstein field equations in the continuum limit" (lines 50-52). The supporting argument in §6 is the Benincasa-Dowker action on causal sets:

1. The discrete d'Alembertian of Benincasa and Dowker on a causal graph (eqs. 378-379, lines 5984-6001, citing Benincasa and Dowker 2010 at line 5990).
2. The limit of its expectation as ρ_c → ∞ within the Riemann normal neighbourhood, □φ − R φ/2 (eq. 383, line 6071).
3. G3 replaces "the assumption of weak ergodicity of the causal graph dynamics with the much stronger assumption of uniform Poisson distribution of the rewrite events" (lines 6079-6081), and with φ constant obtains the Benincasa-Dowker action S^(4) = (4/√6)[n − N_0 + 9N_1 − 16N_2 + 8N_3] (eq. 386, line 6105).
4. "As proposed by Sorkin, Benincasa and Dowker, and demonstrated numerically by Cunningham", assuming zero surface terms and a vanishing contribution from outside the Riemann normal neighbourhood, the expectation of S^(4) converges to the Einstein-Hilbert action (eq. 387, lines 6110-6124).

Each step concerns a causal set obtained by Poisson sampling of (M, g). G3 gives no proof that the causal graph of the rule of line 6202 is distributed as such a causal set. The convergence in step 4 has numerical support in the cited work (Cunningham) and no proof.

## Consequences for this repository

1. The tetrad construction of G3 belongs to continuum numerical relativity on a mesh. The repository has no hypergraph construction of a tetrad to formalise.
2. G4 (`papers/gorard_2303.07282.txt`) does not contain the word "tetrad". It discusses the Raychaudhuri equation in its introduction (lines 195-213).
3. A statement that the rule of G3 line 6202 yields the Einstein-Hilbert action needs a theorem that its causal graphs are distributed as Poisson-sampled causal sets of a Lorentzian manifold, together with the Benincasa-Dowker convergence. Both are OPEN.
