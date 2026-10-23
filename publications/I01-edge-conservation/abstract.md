# I01: Edge conservation and causal-graph bounds for Wolfram model rules

Results. A rule r on directed multi-hypergraphs with |LHS(r)| = |RHS(r)| preserves the number of hyperedges of the state under every application and every chain of applications (PROVED: `Application.size_result_of_conservative`, `size_preserved_by_applications`, `trajectory_size_invariant`). In every trajectory, each event consumes |LHS| hyperedges and produces |RHS| hyperedges (PROVED: `in_degree_eq_lhsSize`, `out_degree_eq_rhsSize`, `balanced_of_conservative` in `ParallelSchedule.lean`). The causal level of an event, the length of the longest causal chain ending at it, increases by at least 1 along every causal edge, so events at the same level are not causally related (PROVED: `level_add_one_le_of_isCausalPred`, `no_causal_edge_within_level` in `CausalLevel.lean`). These trajectory results use the relation `causallyPrecedes` (`Causal.lean`), which compares hyperedge values.

`CausalHistory.lean` defines evolutions with hyperedge identities and their causal graph. For every update order (PROVED): an identity is consumed by at most one event (`CausalHistory.History.consumer_unique`); the out-degree of an event is at most the number of identities it creates (`CausalHistory.History.succ_card_le`); for a rule with |LHS| = |RHS| = k and N initial hyperedges, every antichain A of the causal graph satisfies k·|A| ≤ N (`CausalHistory.RuleHistory.antichain_card_le`).

Application to the rule {{x,y},{y,z},{z,w},{w,v}} → {{y,u},{u,v},{w,x},{x,u}}, which arXiv:2102.09363 describes as satisfying the Einstein field equations in the continuum limit (lines 50-52, rule at line 6202):

- PROVED: the rule preserves the edge count (`Refutations.gorardNamedRule_applications_preserve_size`); every antichain has at most N/4 events (`CausalHistory.gorardNamedRule_antichain_card_le`); at most 5^t events lie within directed distance t of an event (`CausalHistory.gorardNamedRule_ball_card_le`).
- MEASURED: on cycles, paths and 3D grids of up to 300 edges and 2000 events, the log-log cone-growth exponent lies between 0.77 and 1.26 and depends on the update order (`notes/empirical_refutation.md`, section 4).
- OPEN: linear cone growth, stated as `CausalHistory.GorardNamedRuleConeGrowthLinear`.

Target venue: arXiv cs.LO and math.CO; Complex Systems.

Length: 15-20 pages.

Open items before drafting: linear cone growth (O1 in `STATUS_OF_GORARD_CLAIMS.md`).
