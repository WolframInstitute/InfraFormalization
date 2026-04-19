# I01 — Edge Conservation and Structural Bounds for Wolfram-Model Hypergraph Rewriting

**Thesis.** A rewriting rule $r$ on directed multi-hypergraphs with $|LHS(r)| = |RHS(r)|$ is *conservative*: its application preserves the multiset cardinality of the state. From conservation plus the definitional properties of the causal DAG, we derive: (i) every event has in-degree exactly $|LHS(r)|$ and out-degree exactly $|RHS(r)|$ (multi-counted); (ii) the trajectory-level causal DAG is "balanced" for conservative rules; (iii) the causal level function (length of longest causal chain) is strictly monotone along causal edges, giving the antichain property that events at the same causal level cannot be causally related. Every theorem is machine-verified in Lean 4 + Mathlib 4.29.1, depending only on Lean's three standard axioms.

**Consequences.** As a direct corollary, the specific rule
$$\{\{x,y\},\{y,z\},\{z,w\},\{w,v\}\} \to \{\{y,u\},\{u,v\},\{w,x\},\{x,u\}\}$$
claimed in arXiv:2102.09363 to satisfy the Einstein field equations in the continuum limit cannot produce a 3+1-dimensional causal graph on any initial condition tested (empirical: 9 independent seeds including 3D grids; structural: edge conservation implies bounded simultaneity width).

**Target venue.** arXiv cs.LO + math.CO; possibly Complex Systems.

**Sufficient Lean support.** T1, T2, T5–T15 in [`STATUS.md`](../../STATUS.md).

**Length target.** 15–20 pages.

**Dependencies on research not yet done.** None. Draftable now.
