# Publications

Each subfolder is a planned paper. A subfolder holds an `abstract.md` that lists the results the paper would report and their status. No manuscript exists yet. A paper is drafted when its Lean support is PROVED (axioms at most `propext`, `Classical.choice`, `Quot.sound`) and its contribution over the existing literature is stated.

Status labels follow `STATUS_OF_GORARD_CLAIMS.md`: PROVED, PROVED-WITH-NATIVE-DECIDE, MEASURED, READ, OPEN.


## Structure

- Short papers: one result each, such as a coefficient compared with its published source, a convergence bound for a discrete metric space, or a structural theorem about hypergraph rewriting.
- Longer papers: a collection of short-paper results.

Each folder is planned to contain `abstract.md`, a manuscript (`paper.md` or `paper.tex`), `lean-dependencies.md` with the Lean theorems used, `reviews/` and `figures/`. Only `abstract.md` exists at present.

## Folders

Short papers:

- [`I01-edge-conservation/`](I01-edge-conservation/): edge-count conservation for rules with |LHS| = |RHS|, and the antichain and cone bounds of the causal graph.
- [`I02-cycle-circle-gh/`](I02-cycle-circle-gh/): an isometric embedding of the scaled n-cycle into the unit circle with 1/(2n)-dense image.
- [`I05-ollivier-correction/`](I05-ollivier-correction/): the Wasserstein expansion in G1-G3 compared with Ollivier (2009).

Planned short papers without a folder: I03 (scaled path and unit interval), I04 (scaled lattice and flat 2-torus), I06 (the tube-volume coefficient of G2 eq. 126 and G3 eq. 342 compared with Gray), I07 (measurements of the rule of G3 line 6202).

Longer papers:

- [`M01-gorard-corpus-audit/`](M01-gorard-corpus-audit/): the findings on G1-G4, collecting I05, I06, I07 and the findings S1-S6 and F1-F8.
- [`M02-infrageometry-foundations/`](M02-infrageometry-foundations/): the `GHApproximation` structure and its instances for the cycle, the path and the torus, collecting I02, I03, I04.

Planned longer papers without a folder: M03 (a hypergraph rewriting rule with a proved general-relativistic limit; OPEN, see `MILESTONES.md`) and M04 (binary black hole evolution on hypergraphs; depends on M03).

## Steps per paper

1. Create the folder and write `abstract.md`.
2. List the Lean theorems used in `lean-dependencies.md`. Add missing theorems to `MILESTONES.md` and prove them before drafting.
3. Draft the manuscript.
4. Internal review by at least two reviewers, recorded in `reviews/`.
5. Typeset in LaTeX.
6. Submit.
