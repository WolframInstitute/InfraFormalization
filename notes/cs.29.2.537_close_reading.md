# Close reading of J. Gorard, "Some Quantum Mechanical Properties of the Wolfram Model" (Complex Systems 29(2) 537-598, 2020)

The paper is called G5 in this repository. It is not on arXiv. The PDF is the one linked from https://www.complex-systems.com/abstracts/v29_i02_a02/ (https://content.wolfram.com/sites/13/2020/07/29-2-2.pdf, 62 pages). All line citations refer to `papers/gorard_complexsystems_29_2.txt` (2941 lines, `pdftotext -layout`). The PDF has no TeX source, and some symbols (square roots, hats, brackets) are lost in the text extraction. Equation numbers are the paper's.

Each claim is classified as:

- PROVED IN PAPER, proof holds: the paper gives a proof, and the proof was checked and holds.
- PROVED IN PAPER, proof fails: the paper gives a proof or calls its argument a proof, and a step does not follow. The failing step is named.
- STATED: stated without proof, including statements the paper calls conjectures.
- CITED: the paper attributes the statement to another work.
- CONTRADICTED: the statement is contradicted by the paper itself or by a computation recorded here. The evidence is given.

Computations: `scripts/python/pubreview/` (run with `run_capped.sh`, a 4 GB address-space cap; HGEvolve evolutions pass "MemoryLimit" at 0.8 of the cap). Engine: HGEvolve Python client at engine commit 6969681e. Outputs: `results/publication_review/qm_*.json`.

## 1. Section headings

- Abstract (lines 11-54)
- §1 Introduction (line 58)
- §2 Operators, Observables and the Uncertainty Principle (line 163): §2.1 abstract rewriting and causal invariance (line 165), §2.2 multiway evolution and Knuth-Bendix completion (line 355), §2.3 wavefunction collapse and the uncertainty principle (line 656), §2.4 mathematical and computational considerations (line 967)
- §3 Branchlike Foliations and Multiway Relativity (line 1148): §3.1 branchial geometry and multiway invariance (line 1150), §3.2 complex projective Hilbert space and multiway relativity (line 1482), §3.3 the multiway causal graph (line 1979), §3.4 Bell's theorem, particles and consequences (line 2287)
- §4 Concluding Remarks (line 2550), References (line 2602)

G5 has numbered definitions (Defs 1-50) and no numbered theorems, propositions or lemmas. The word "prove" and its forms occur in the abstract (lines 25, 33, 40) and at lines 145, 617, 801, 1131, 1339, 1483, 1504, 1689, 2025, 2087, 2426.

## 2. Claims

### C-1 Abstract and introduction: what the paper states it proves (lines 16-43, 133-160)

The abstract states that the paper shows the multiway evolution "is analogous to the evolution of a linear superposition" (lines 17-20), that completion is "compatible with a multiway analog of the uncertainty principle", which "we prove" (lines 25-26), that the paper "rigorously justif[ies] this correspondence by proving ... that the geometry of the multiway evolution graph converges to that of complex projective Hilbert space in the continuum limit" (lines 33-36), and that it derives the analog of the Einstein field equations (lines 37-38), the path integral, particle-like excitations, "the proof of compatibility with Bell's theorem and violation of the CHSH inequality", the discrete Schrödinger equation and the nonrelativistic propagator (lines 39-43).

The body states three of these as conjectures: the Einstein-equation analog (lines 1947-1949, "Our central conjecture ... is that this tensor plays the same role"), the propagator (lines 2515-2524, "Our central conjecture here (which we intend to explore more fully in a subsequent publication)"), and the twistor structure (line 2245). The CHSH violation is stated at lines 2426-2429 ("one is able to prove violation of the CHSH inequality in much the same way as one does for other ... interpretations") with no proof. Classification: CONTRADICTED by the paper itself for the Einstein-equation analog and the propagator (abstract "derive" against body "conjecture"). The other items are classified below.

### C-2 Standard rewriting definitions and lemmas (lines 174-264, 440-503, 806-831)

- Defs 1-8 (abstract rewriting system, confluence, local, semi- and strong confluence, strong diamond property) and the statements that local confluence is strictly weaker than confluence (line 214) and that semi-confluence is equivalent to confluence (lines 247-248) agree with the standard definitions [4-7]. CITED.
- The critical pair lemma (lines 443-445) and Newman's lemma (lines 494-499) are stated correctly for term rewriting and abstract rewriting systems. CITED ([12]).
- Hindley-Rosen commutative union (lines 813-824) and the commutativity lemma (lines 824-831). CITED ([24-26]).
- Def 8 (lines 258-264) quantifies over all b, c with a → b and a → c, including b = c. Read literally, it fails at every state whose successor is a normal form. The standard diamond property is stated for this quantifier and is still violated only in that degenerate case. No consequence below depends on this.
- Figure 6 (lines 297-300): AB → A, BA → B from ABA has two normal forms. MEASURED: the normal forms are A and AA (`qm_string_figures.py`). Figure 7 (lines 305-310): A → B, BB → B and AA → BA, AB → BA are confluent. MEASURED: both terminate and give one normal form from each of the 510 strings over {A, B} of length 1 to 8.

### C-3 Definitions of the hypergraph rule, the causal graph and causal invariance (lines 266-326)

- Def 9 (lines 266-278): a rule for a "finite, undirected hypergraph" replaces H₁ by H₂ "with identical symmetries and the same number of outgoing edges as H₁". This is G1 Def 3 (`2004.14810_close_reading.md` §2.1). "Outgoing" is not defined for undirected hypergraphs.
- Def 11 (lines 317-323): a causal edge exists when B "was only applicable as a consequence of the outcome of" A, i.e. "the input for event B has a nontrivial overlap with the output for event A". This is G1 Def 4. Neither form states whether the overlap is of hyperedge occurrences or values.
- Def 12 (lines 324-326): causal invariance is that "the causal graphs corresponding to all possible evolution histories eventually become isomorphic". This is G1 Def 9, with the same unstated sense of "eventually".

READ.

### C-4 Branch-pair convergence is necessary for causal invariance (lines 450-454)

> "In the general case of a multiway evolution, we can say that a necessary condition of causal invariance is that all branch pairs generated by the multiway system eventually converge to some common successor state"

CONTRADICTED. MEASURED (`qm_confluence_causal_invariance.py`, system E1): the rules {a} → {a,a} and {a} → {a,a,a} from {{1}} (the string system A → B, A → C) have two complete histories of one event each. Their causal graphs are isomorphic (one event, no edges), so the system is causal invariant under Def 12, and the two terminal states are distinct, so the branch pair does not converge.

### C-5 For terminating systems, branch-pair convergence is necessary and sufficient for causal invariance (lines 499-503)

> "Newman's lemma and the critical pair lemma together imply that, for a multiway system in which every branch eventually terminates, the convergence of all branch pairs is not only a necessary condition for causal invariance, but also a sufficient one."

CONTRADICTED. Necessity fails by C-4. Sufficiency, MEASURED (same script):

- E2: rules {a} → {a,a}, {a} → {a,a,a}, {a,a} → {a,a,a} from {{1}} (the string system A → B, A → D, B → D). Every branch terminates and every state reaches the one normal form {{1,1,1}}. The complete histories have 1 event and 2 events (with one causal edge). The causal graphs are not isomorphic.
- E3: rules {a} → {a,a}, {b,b,b} → {b,b,b,b}, {{a,a},{b,b,b}} → {{a,a},{b,b,b,b}} from {{1},{2,2,2}} (the string system A → X, B → Y, XB → XY from AB). Every branch terminates in the one normal form. The three complete histories have 2 events each. Two have no causal edge and one has a causal edge. The causal graphs are not isomorphic.

Newman's lemma concerns the reachable objects (confluence). Def 12 concerns the causal graphs of the histories. The paper gives no argument from the first to the second.

### C-6 Generalised Knuth-Bendix completion yields a causal invariant system with the same deductive closure (lines 504-526, 599-622, 688-717, 748-760)

- Lines 512-515 and 748-749 describe completion as adding "pairs of new rewrite rules of the form {x → y, y → x}" for each unresolved critical pair. Lines 516-526 state that the result is confluent "so long as the process also preserves the strong normalization property". A system that contains both x → y and y → x has the infinite rewrite sequence x → y → x → ..., so it is not strongly normalizing, and Newman's lemma no longer applies. Standard Knuth-Bendix completion orients each equation into one rule by a reduction order [14-15]. CONTRADICTED by the paper's own condition at lines 516-526.
- Lines 599-607: the completed multiway evolution "is nevertheless causal invariant". STATED. Confluence of the completed system would not give causal invariance (C-5, systems E2 and E3).
- Lines 615-618: "Our conjecture, which we formalize and prove in the following, is that this procedure is formally equivalent to wavefunction collapse". The following sections contain no statement of this equivalence as a proposition and no proof. STATED.
- Lines 637-644: completion "can have the effect of allowing new states of the multiway system to become reachable"; lines 645-654: these states "should correspond to quantum interference effects". STATED.

### C-7 Amplitudes and the Born rule (lines 657-717, 2434-2461)

- Eq. 25-27: states on distinct branches are orthonormal "by assumption" (line 681), and the hypersurface state is normalised (eq. 27). The amplitudes c_i are "a sum of the incoming path weights for the associated vertex in the multiway graph, where these path weights are computed using the discrete multiway norm, as defined below" (lines 677-680). Lines 2459-2461 state that the path-weight quantity takes values in the natural numbers. G5 gives no normalisation of these sums to Σ|c_i|² = 1 and no phase. With non-negative real amplitudes the sum of two contributions cannot cancel. STATED.
- Eq. 29: the "multiway Born rule" P_k = |c_k|². STATED.

### C-8 Rewrite relations as linear operators with every state an eigenvector (eqs. 37-40, lines 846-871)

> "for some eigenvalue a, which itself corresponds to the measured value of A; this fact follows immediately from the linearity of A"

PROVED IN PAPER, proof fails. Eq. 40 writes Âψ = Σ e_i Â_i ψ = Σ e_i a_i ψ, which uses eq. 38 (Â_i ψ = a_i ψ for every component) as a hypothesis. Linearity of Â does not imply that ψ is an eigenvector of Â. The linear operator with matrix [[0, 1], [1, 0]] on ℂ² is a counterexample at ψ = (1, 0).

### C-9 The multiway uncertainty principle (eqs. 41-47, lines 872-940; eq. 123, lines 1981-1999)

- Eq. 44: for ψ an eigenvector of both Â and B̂ with eigenvalues a and b, [Â, B̂]ψ = abψ − baψ = 0. This holds for every pair of operators with a common eigenvector ψ and does not use commutation. The step from eq. 44 to "quantities A and B can be measured simultaneously with infinite precision" (lines 902-903) is STATED.
- Eq. 46 prints ΔAΔB ≠ |⟨[A, B]⟩|/2. The Robertson relation is ΔAΔB ≥ |⟨[A, B]⟩|/2. The extraction of the PDF shows "≠" at line 926.
- Eq. 47, [Â, B̂] = iℏ, follows "if one now assumes the unit distance on branchlike hypersurfaces to be given by iℏ" (lines 928-929). The later justification (lines 1981-1999) identifies ℏ with the separation of global states by distinct multiway edges. STATED. The abstract (lines 25-26) states that the compatibility with the uncertainty principle is proved.

### C-10 Operator-state correspondence (eqs. 48-49, lines 941-964)

The paper states that the correspondence is "exceptionally easy to prove" in the multiway setting, and that it corresponds to the existence of an "ex-nihilo" event ∅ → x. No proof is given. The vacuum is stated to be invariant under SL(2, ℤ). In two-dimensional conformal field theory the vacuum is invariant under the global conformal group SL(2, ℂ), and SL(2, ℤ) is the modular group of the torus. STATED.

### C-11 Knuth-Bendix, the word problem and Buchberger's algorithm (lines 968-1028)

Completion as a semi-decision procedure for the word problem of finitely presented monoids, and Buchberger's algorithm as a specialisation of it. CITED ([13-18], [31-33]). In Def 26 the relation set of M = ⟨X | R⟩ is called "a finite relation set X" (line 973).

### C-12 Quantum and classical computation, P = BQP (lines 1029-1139)

- Lines 1033-1038: "a fundamental equivalence between the collapse of a multiway evolution corresponding to a quantum computation, and the solution to the word problem for the monoid of unitary automorphisms of Hilbert space". STATED.
- Lines 1107-1115: the "prediction" P = BQP after coarse-graining, restricted at lines 1116-1120 to rules "sufficiently close to causal invariance, in some suitably defined sense". Lines 1130-1139: "This statement can be proved rigorously by applying ... Knuth-Bendix completion ... to the finitely presented transition monoid of a quantum Turing machine", deferred to "a future publication". STATED.
- Def 27 (eq. 60) writes the transition relation as a subset of Q\F × F × Q × Γ × {L, S, R}. The second factor of the standard definition is Γ.

### C-13 Multiway lattice coordinates and the multiway norm (eqs. 62-67, Defs 29-31, lines 1168-1209)

The multiway graph is given "a layered graph embedding ... into the discrete multiway lattice ℤ^{1,n}" (lines 1169-1171), with coordinates (t, y). G5 gives no construction of the embedding, no statement of n and no uniqueness. The norm ‖(t, y)‖ = ‖y‖² − t² and the classification of Def 30 are defined on the embedding coordinates. STATED (object used without a construction, as G1 Def 15 for the causal graph, `2004.14810_close_reading.md` §2.3).

### C-14 Observers as foliations and multiway invariance (Defs 37-38, lines 1294-1336)

- Def 37: an observer is a sequence of non-intersecting branchlike hypersurfaces given by a time function t : ℳ → ℤ "such that t ≠ 0 everywhere" (eq. 71). The condition t ≠ 0 excludes the value 0 at every state, including the initial one.
- Lines 1333-1336: "Since Newman's lemma guarantees that critical pair convergence implies confluence for terminating rewriting systems, it follows that multiway invariance implies causal invariance for any non-infinite multiway evolution." CONTRADICTED. The step from confluence to causal invariance fails for terminating systems (C-5, systems E2 and E3).

### C-15 Complex branchlike distances (eqs. 73-81, lines 1356-1478)

- Lines 1368-1398: from Sylvester's law of inertia and Ikramov's generalisation to normal matrices, "the metric tensor for the multiway causal graph must have eigenvalues with at least three distinct signs, hence necessitating the use of complex numbers". The inertia laws concern one quadratic or Hermitian form up to congruence and do not state that three kinds of separation require complex eigenvalues. Two real forms, or a real form on a space with a distinguished splitting, separate three kinds of directions. PROVED IN PAPER (called "rigorous justification", line 1368), proof fails at this step.
- Eq. 79, ‖(t, x, y)‖ = ‖x‖² + i‖y‖² − (1 + i)t², with the classification of eq. 80. The five classes overlap: a separation with ℜ > 0 and ℑ > 0 is both spacelike and branchlike. Lines 1456-1458 state that there is "no mutual exclusivity". READ.
- Lines 1459-1464: spacelike separation "is, in general, a special case of branchlike separation". Lines 1464-1480: this "immediately impl[ies] the de Broglie hypothesis". STATED.
- Lines 1402-1406 call the use of both signs of imaginary numbers "four distinct eigenvalue signs" (line 1673) and identify it with the projectivity of the Hilbert space. STATED.

### C-16 Branchial distance as common-ancestor depth (lines 1504-1518)

> "if they are both elements of the same branch pair (i.e., if both follow directly from a common state via a single updating event), then they are separated by a distance of one, and otherwise they are separated by the number of levels back in the multiway hierarchy that one must traverse in order to find their common ancestor state. Disconnections in a branchial hypersurface therefore indicate a lack of common ancestry between states (which generally only happens if there was more than one initial condition for the system, or if the hypersurface grew faster than the maximum rate of entanglement)."

CONTRADICTED. MEASURED (`qm_branchial_distance.py`, one initial state in every run). The branchial graph at the final step joins two states that are one-step successors of a common state, the paper's branch pair. For each pair of final states the script compares their branchial distance with the least number of levels back to a common ancestor.

| Rule, initial state, steps | States | Final states | Pairs: distance = depth | Pairs: disconnected |
|---|---|---:|---:|---:|
| {{x,y},{x,z}} → {{x,y},{x,w},{y,w},{z,w}}, {{1,2},{1,3}}, 3 | Full | 6 | 7 | 8 |
| same | tree | 16 | 24 | 96 |
| {{x,y}} → {{x,y},{y,z}}, {{1,2},{2,3}}, 4 | Full | 20 | 190 | 0 |
| same | tree | 120 | 240 | 6900 |
| the G3 rule, directed 8-edge path, 3 | Full | 37 | 32 | 634 |
| same | tree | 71 | 92 | 2393 |

"Full" identifies isomorphic states ("CanonicalizeStates" -> "Full"); "tree" does not. No pair is connected at a distance different from its ancestor depth. Two states whose common ancestor lies two or more levels back are joined only through states that have common parents, and in a multiway tree they are never joined: the branchial graph of a tree at one step is a disjoint union of the sibling cliques. Every run has one initial condition, and the clause on the "maximum rate of entanglement" has no definition in G5 that can be checked.

### C-17 Convergence of branchlike hypersurfaces to complex projective Hilbert space (lines 1482-1689; abstract lines 33-36)

The paper calls this a proof ("Our principal goal for this subsection is to prove rigorously", line 1483; "which completes the proof", line 1689). The argument has four steps:

1. The branchial distance "is equivalent, at least up to some multiplicative constant, to the information distance metric from algorithmic complexity" (lines 1519-1528). STATED. The information distance (Def 42, eq. 82) is a minimum over programs of a fixed universal Turing machine. Lines 1540-1542 replace the universal machine by the rewrite rules of the multiway system, for which the minimum is the number of rewrites and not the information distance of [49]. C-16 shows that the branchial distance is not the common-ancestor depth.
2. "The standard continuum limit of the discrete information distance metric for a statistical manifold ... corresponds to the so-called Fisher information metric" (lines 1557-1562). STATED. The Fisher metric of eq. 87 is the second-order term of the Kullback-Leibler divergence between nearby distributions of a parametric family. G5 gives no family of distributions on branchial states, no parameters θ, and no relation between Kolmogorov information distance and the Kullback-Leibler divergence.
3. The Fisher metric "extends" to the Fubini-Study metric on ℂPⁿ (lines 1597-1609), and the Fubini-Study metric agrees with the Bures metric (lines 1647-1661). CITED ([53-56]).
4. Projectivity: causal and multiway graphs are "invariant under the conformal transformation g → Ω²g", and for a multiway graph "such a conformal rescaling is equivalent to modding out by the action of the multiplicative group ℂ*, which completes the proof" (lines 1677-1689). STATED. A real conformal factor Ω² acts by positive reals and does not give the phase part of ℂ* = ℝ_{>0} × U(1).

Line 1662 states "Having shown that the natural discrete metric on branchlike hypersurfaces converges to the Fisher information metric", which steps 1 and 2 do not show. G5 states no sequence of multiway systems, no limit object, and no mode of convergence. PROVED IN PAPER, proof fails at steps 1, 2 and 4.

### C-18 Modular lattices and causal invariance (lines 1732-1824)

- Lines 1804-1806: "a multiway evolution graph may be considered to be the Hasse diagram for a partially ordered set of global states". MEASURED (`qm_confluence_causal_invariance.py`): the multiway graph of E2 contains the edge A → D and the path A → B → D, so it is not a Hasse diagram (a Hasse diagram has no edge implied by transitivity), and the multiway graph of E1 is not a lattice (the two terminal states have no common upper bound).
- Lines 1812-1818: "the modularity condition for lattices is equivalent to the strong diamond property for rewriting systems, and hence modularity of the multiway lattice constitutes a provably sufficient condition for causal invariance". STATED for the equivalence. CONTRADICTED for sufficiency. MEASURED: the multiway graph of E3 (states AB, XB, AY, XY with the canonical identification of isomorphic states) is the four-element Boolean lattice, which is modular, and E3 is not causal invariant (C-5).
- Lines 1760-1788: the diamond isomorphism theorem and its characterisation of modular pairs. CITED ([61, 62]), stated correctly.

### C-19 Continuous geometry (lines 1825-1858)

Lines 1831-1834: "any lattice satisfying the properties of modularity, completeness, continuity, complementarity and irreducibility may be interpreted as a continuous geometry, and therefore as a lattice-theoretic model of complex projective space". CITED ([63-65]) for the definition. The step to complex projective space is STATED. Von Neumann's continuous geometries include geometries with a continuous dimension function that are not projective geometries, and an irreducible projective geometry of dimension at least 3 is a geometry over some division ring, which need not be ℂ. G5 does not show that any multiway lattice is complete, continuous, complemented or irreducible. The lattice of E3 is complemented and modular and is the product of two two-element chains, so it is reducible.

### C-20 Multiway Einstein equations from superrelativity (eqs. 114-122, lines 1865-1977)

- Eqs. 119-120 are the Fubini-Study metric in inhomogeneous coordinates and a deformation with a "density sphere" radius R, following Leifer [66]. CITED.
- Lines 1946-1949: "Our central conjecture, just as that of superrelativity, is that this tensor plays the same role in geometric quantum mechanics as the Einstein curvature tensor plays in general relativity." STATED as a conjecture. No field equation for the multiway system is written. The abstract (lines 37-38) states that the paper derives it (C-1).
- Lines 1957-1977: the connection of eq. 122 "defines an intrinsic gauge potential on multiway space", the hypergraph is the base of a fibre bundle, and "local gauge invariance in the multiway evolution therefore follows as an inevitable consequence of causal invariance". STATED.

### C-21 ℏ as the maximum entanglement rate and the path integral (lines 1981-2015)

The phase e^{iS} is "the dispersion angle of geodesic bundles", which is "trivially related to the density of causal edges", so that ℏ has units of action, "justifying (at least dimensionally) our interpretation of the multiway graph as a path integral". STATED. The abstract (line 39) lists "the derivation of the path integral". No path integral over multiway paths, measure or action on multiway paths is defined.

### C-22 Margolus-Levitin bound and the quantum Zeno effect (eqs. 125-138, lines 2016-2144)

- Eqs. 125-132 reproduce the Margolus-Levitin derivation for a Hamiltonian H with ⟨H⟩ ≥ 0, using cos x ≥ 1 − (2/π)(x + sin x) for x ≥ 0. PROVED IN PAPER, proof holds (continuum quantum mechanics, CITED [67, 68]).
- Lines 2084-2088: "our aforementioned result ... is therefore provably consistent with the Margolus-Levitin bound". The derivation uses no multiway object. STATED.
- Eqs. 133-138: the quantum Zeno effect for a Hamiltonian evolution with repeated projections. CITED ([69, 70]), standard. Its identification with time dilation is STATED.

### C-23 Normal forms, singularities, black holes and holography (lines 2145-2285)

- Normal forms of the rewriting system are "singularities in the multiway causal graph", "physical" ones are qubits and coordinate ones are measurement outcomes (lines 2145-2160). STATED.
- Eqs. 139-143: the Schwarzschild and Gullstrand-Painlevé metrics. With y the square root of c²r/2GM (the square root is lost in the text extraction), eq. 142 agrees with the standard transformation a(r) = 2M(−2y + log((y+1)/(y−1))) in units G = c = 1.
- Lines 2195-2224: a black hole has an "entanglement" horizon "strictly on the exterior" of the causal horizon, Hawking radiation is emitted from it, and this is "a possible resolution to the black hole information paradox". STATED.
- Lines 2230-2241: a toy model of holography and a bulk-boundary "duality ... just as in AdS/CFT". STATED.
- Lines 2245-2285: the limit of the multiway causal graph is conjectured to generalise the twistor correspondence space ("which we make no attempt to prove"). STATED. In the description of the twistor correspondence (lines 2248-2265), twistor space ℂP³ = Gr₁(ℂ⁴) is called "the Grassmannian of lines in complexified Minkowski space", and Gr₂(ℂ⁴) is said to correspond to "the massless Yang-Mills fields". In the standard correspondence (Ward and Wells [83]) Gr₁(ℂ⁴) is the space of lines in twistor space ℂ⁴, Gr₂(ℂ⁴) is compactified complexified Minkowski space, and the Penrose and Ward transforms relate cohomology classes and holomorphic bundles on regions of twistor space to massless free fields and self-dual Yang-Mills fields on Minkowski space. READ (differs from the standard statement of the cited source).

### C-24 Particles from forbidden minors (lines 2289-2390)

- Kuratowski's and Wagner's theorems, Defs 46-49, and the statement that a nonplanar trivalent graph contains a subdivision of K₃,₃ (lines 2315-2318). CITED ([84-86]), correct: a subdivision of K₅ needs four vertices of degree 4.
- Lines 2341-2343 call Wagner's theorem "a stronger variant" of Kuratowski's. Both characterise planarity. The relation between the minor and subdivision orders (lines 2352-2355) is stated correctly.
- The Robertson-Seymour theorem and the finiteness of forbidden minors for each surface (lines 2356-2379). CITED ([87, 88]), correct.
- Lines 2380-2390: the theorem "allows us to define a conserved graph quantity", and "may be interpreted as being a combinatorial analog of Noether's theorem". STATED. G5 gives no rule that preserves a minor-closed family and no symmetry of an action.

### C-25 CHSH violation (lines 2391-2429)

"Consequently, one is able to prove violation of the CHSH inequality in much the same way as one does for other standard deterministic and nonlocal interpretations" (lines 2425-2429). STATED. No correlation function E(a, b) is computed for a multiway system.

### C-26 Discrete Schrödinger operator (Def 50, eqs. 147-152, lines 2430-2489)

- Def 50 defines the discrete Laplacian for ϕ : V → R "taking values in a ring R", and lines 2459-2461 take "the ring R simply corresponding to the natural numbers ℕ". ℕ is not a ring, and (Δϕ)(v) = Σ(ϕ(v) − ϕ(w)) takes negative values for ϕ with values in ℕ. CONTRADICTED by the paper's own definition.
- H = Δ + P "has the form of the discrete Schrödinger operator" (lines 2477-2479). Lines 2487-2489: "Our diffusion equation assumes the form of a Schrödinger equation rather than a regular heat equation because of the presence of imaginary branchlike distances". No time-evolution equation for ϕ is written, and the potential P (eq. 149) is "the effect of these rival perturbations" with no definition. STATED. The abstract (line 42) lists "the derivation of the discrete Schrödinger equation".
- The repository's `BranchialSchrodinger.lean` proves conservation of Σ|ψ|² for i∂ₜψ = Aψ with A the adjacency operator of an arbitrary symmetric relation, not derived from a rewriting system (module header). It does not concern Def 50.

### C-27 Nonrelativistic propagator (eqs. 153-159, lines 2490-2546)

The resolvent G(v, w; λ) = ⟨δ_v|(H − λ)⁻¹|δ_w⟩ is defined. "Our central conjecture here ... is therefore that, in the continuum limit, this discrete Green's function is related to the standard propagator". STATED as a conjecture. The abstract (line 43) lists "the derivation of the nonrelativistic propagator".

### C-28 Reference [1] (lines 2604-2606)

Reference [1], cited for the relativistic results (lines 60, 170, 392, 1168), is "J. Gorard, 'Some Relativistic and Gravitational Properties of the Wolfram Model,' Complex Systems, 29(2), 2020 pp. 537-598. doi:10.25088/ComplexSystems.29.2.537". The page range and DOI are those of G5 itself (line 48 and the page footers). READ.

### C-29 Results of G1 restated (lines 98-116)

Lines 98-113 state that [1] "proved" causal invariance equivalent to discrete general covariance and "proved" that the condition that the causal graph limits to a manifold of fixed dimensionality is equivalent to the discrete Einstein field equations. The repository's reading of G1 finds neither proved there: the first equivalence identifies two descriptions of the same property (`STATUS_OF_GORARD_CLAIMS.md` Claim 4, `notes/severity_taxonomy.md` items 7 and 9), and the second rests on the Euler-Lagrange restatement of eq. 87 and an unproved continuum limit (Claim 3). CITED, to a source that does not supply the proof.

## 3. Counts

Each row lists the statements of §2 in the class. Items that are findings about definitions, notation or references (C-2 Def 8, C-3, C-12 Def 27, C-15 eq. 80, C-23 twistor description, C-28) are READ and not counted as claims.

| Class | Count | Statements |
|---|---:|---|
| PROVED IN PAPER, proof holds | 1 | C-22 (Margolus-Levitin derivation) |
| PROVED IN PAPER, proof fails | 4 | C-8; C-9 (eq. 44 as an argument for simultaneous measurability); C-15 (inertia law to complex numbers); C-17 |
| STATED | 26 | C-6 (causal invariance of the completion; equivalence with collapse; interference states); C-7 (amplitudes; Born rule); C-9 (eq. 47); C-10; C-12 (equivalence with the word problem; P = BQP); C-13; C-15 (de Broglie; projectivity); C-18 (modularity equals the strong diamond property); C-19; C-20 (Einstein-tensor conjecture; gauge invariance); C-21; C-22 (consistency with the bound); C-23 (normal forms as singularities; two horizons; holography; twistor conjecture); C-24 (Noether analog); C-25; C-26 (Schrödinger form); C-27 |
| CITED | 9 | C-2 (rewriting definitions; critical pair and Newman lemmas; Hindley-Rosen); C-11; C-20 (eqs. 119-120); C-22 (Zeno effect); C-24 (Kuratowski and Wagner; Robertson-Seymour); C-29 |
| CONTRADICTED | 10 | C-1 (Einstein-equation analog; propagator); C-4; C-5; C-6 (completion with both orientations); C-14; C-16; C-18 (Hasse diagram; sufficiency of modularity); C-26 (ℕ as a ring) |

## 4. Computational checks

| Check | Script | Result |
|---|---|---|
| Causal invariance without confluence (E1) | `qm_confluence_causal_invariance.py` | 2 histories, isomorphic causal graphs, 2 terminal states |
| Confluent, terminating, not causal invariant (E2) | same | 1 normal form; histories of 1 and 2 events |
| Modular multiway lattice, confluent, terminating, not causal invariant (E3) | same | 4-element Boolean lattice; 3 histories of 2 events, with 0 and 1 causal edges |
| Multiway graph with a transitive edge (E2) | same | 1 edge implied by transitivity |
| Figures 6 and 7 | `qm_string_figures.py` | Figure 6: normal forms A and AA. Figure 7: one normal form from each of 510 strings |
| Branchial distance against common-ancestor depth | `qm_branchial_distance.py` | disconnected pairs with a common ancestor in 5 of 6 runs (table in C-16) |

Output files: `results/publication_review/qm_confluence_causal_invariance.json`, `qm_string_figures.json`, `qm_branchial_distance.json`.
