# Reading guide to the audit of G1-G4

This guide answers three questions about the papers G1 = arXiv:2004.14810, G2 = arXiv:2011.12174, G3 = arXiv:2102.09363 and G4 = arXiv:2303.07282, and points to the files of this repository that support each answer. Line numbers refer to `papers/gorard_*.txt`. Status labels: PROVED (Lean, axiom-clean), MEASURED, READ (from the paper text), OPEN.

The three questions:

1. Do the papers contain statements that are false?
2. Which statements are new, as opposed to restatements of prior literature?
3. Does anything beyond a summary of discrete approaches to gravity and a simulation of one rule show that hypergraph evolutions match continuum solutions?

## 1. Statements that differ from their sources or are not established

- Two formulas differ from the sources the papers cite. G3 eq. 344 (line 5340, also G1 eq. 80, lines 2045-2056) has the scalar curvature R where Ollivier (2009) has Ric(v,v). G3 eq. 342 (line 5276, also G2 eq. 126, line 2409) has the tube-volume coefficient (d−1)(R − Ric(u,u))/(d+1) where Gray (1973) has (R + Ric(u,u))/(6(d+1)). PROVED as arithmetic comparisons in `Infra/OllivierStatement.lean` and `Infra/GrayTubeStatement.lean`; details in `results/phase2_continuum/`.
- G3 states that the rule of line 6202 "provably satisfies the Einstein field equations in the continuum limit" (lines 50-52). G3 gives no proof for this rule (READ).
- G1 §3.3 uses a discrete metric, a volume measure and orthonormal hyperedges without constructing them (READ, G1 line 786, lines 2061-2063, eqs. 86-88).
- G4's title names discrete singularity theorems; the abstract states such a theorem as a hope (READ, G4 lines 1-3, 77-79).

`MAJOR_FLAWS.md` gives findings F1-F8 with their lines, and `FINDINGS.md` gives one line per claim.

## 2. Statements that restate prior literature

READ. The papers cite the following sources for their technical ingredients: Forman (2003) and Ollivier (2009) for discrete Ricci curvature, Gray (1973) for the ball and tube volume expansions, Bombelli, Lee, Meyer and Sorkin (1987) and Benincasa and Dowker (2010) for causal sets and the discrete d'Alembertian, and the ADM, BSSN and CCZ4 formulations for the Cauchy problem. Where the papers restate these results for hypergraphs, the restatement is either a definition (for example, G1 eq. 65 at lines 1792-1796 transfers the Riemannian ball-volume expansion to vertex counts) or a formula that differs from the source (eqs. 342, 344). The statements specific to the Wolfram model are:

- Causal invariance corresponds to discrete general covariance (G1 lines 1066-1075). The two notions are defined as the same property; the project's encoding is PROVED by `Iff.rfl` (`Refutations/F4Tautology.lean`).
- Asymptotically dimension-preserving, causal-invariant rules satisfy the vacuum Einstein equations (G1 §3.3). The dimension condition is the Euler-Lagrange equation of the action (G1 lines 2203-2211); the encoding is PROVED by `Iff.rfl` (`Refutations/F3Tautology.lean`). The passage from sum to integral (line 2214) states no notion of convergence.
- The rule of G3 line 6202 satisfies the Einstein equations in the continuum limit. No proof is given (READ).

## 3. Evidence that evolutions match continuum solutions

READ. G3 §6 (lines 6146-6290) compares the evolution of the rule with a numerical solution of the Einstein equations for two black holes. The initial hypergraph is a Poisson sample of the Brill-Lindquist initial data (lines 6148-6152, 6179); the figures are coloured with the analytic conformal factor (lines 6185-6192); G3 reports second-order convergence of the Hamiltonian constraint (Table 6) and rΨ4 extractions (Figure 78). G3 does not state the link cut-off, the orientation of the edges, the update order, the number of events per unit of time, or the procedures that compute ψ, rΨ4 and the constraint from a hypergraph.

G1-G4 do not compute a Gromov-Hausdorff or Wasserstein distance between an evolution and a continuum target, and do not prove a convergence rate for any rule.

What the repository establishes about the rule of G3:

- PROVED: the rule conserves edge count (`Refutations.gorardNamedRule_applications_preserve_size`). In every evolution from N hyperedges, with any update order, every antichain of the causal graph has at most N/4 events (`CausalHistory.gorardNamedRule_antichain_card_le`) and at most 5^t events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_ball_card_le`).
- MEASURED: on cycles, paths and 3D grids of up to 300 edges and 2000 events, cone-growth exponents between 0.77 and 1.26, depending on the update order (`notes/empirical_refutation.md`).
- OPEN: linear cone growth of the causal graph (`CausalHistory.GorardNamedRuleConeGrowthLinear`). A proof would bound the causal-graph dimension of every evolution of the rule by 1.

## Files

| File | Content |
|---|---|
| `STATUS_OF_GORARD_CLAIMS.md` | Status per claim, with axiom lists, and the section on reproducing the experiment of G3 §6 |
| `MAJOR_FLAWS.md` | Findings F1-F8 |
| `FINDINGS.md` | One line per claim |
| `THEOREM_STATUS.md` | Status of every theorem cited in the documentation |
| `results/phase2_continuum/eq342_verdict.md`, `eq344_verdict.md` | The two coefficient comparisons |
| `notes/empirical_refutation.md` | Measurements of the G3 rule and the cause of the difference between the SetReplace and Python tables |
| `lean/InfraFormalization/Refutations/` | F1-F7. F3 and F4 hold by `Iff.rfl`; F1, F2, F5 and F6 are VACUOUS with respect to the papers; F7 proves edge-count conservation |
| `lean/InfraFormalization/CausalHistory.lean` | Causal graph with hyperedge identities; antichain and cone bounds |

## The positive part of the library

The library states continuum targets (Minkowski, Schwarzschild, FLRW, Reissner-Nordström, Kerr, de Sitter, S²) and attaches to each an origin obligation. The obligations do not depend on their target and hold for every target (`Curvature.any_metric_has_strong_obligation_witness`), and the milestone statements of `Milestone.lean` hold for every target (`Milestone.GR_emerges_from_hypergraph_holds`). These statements are VACUOUS: no theorem in the library states that a rewriting evolution converges to any of these geometries. The PROVED continuum limits concern fixed families of graphs (cycles to the circle, paths to the interval, tori, lattices to Minkowski space); see `THEOREM_STATUS.md` and `BRIDGE_MACHINERY.md`.
