"""Independent, minimal Wolfram-model single-way rewriter.

Purpose
-------
Independent re-implementation of the hypergraph rewriting semantics used by
SetReplace's single-way evolution. Used to cross-check the SetReplace runs
on Gorard's named "EFE-satisfying" rule
    {{x,y},{y,z},{z,w},{w,v}} -> {{y,u},{u,v},{w,x},{x,u}}
(arXiv:2102.09363, line 6202). No dependency on SetReplace / Wolfram.

Semantics
---------
* A **state** is a list of tuples of ints — an ordered multiset of directed
  hyperedges. (Elements of a hyperedge are vertex labels.)
* A **pattern** is a list of tuples where each entry is either an int
  (literal vertex) or a string (pattern variable). A pattern variable may
  appear more than once; different occurrences must match the same value.
* A **rule** is (LHS_pattern, RHS_pattern, fresh_vars) where fresh_vars is
  the set of pattern variables that appear on the RHS but not the LHS and
  must be instantiated to freshly-allocated vertices.
* A **match** of LHS in state: an injective map from LHS indices to state
  indices (each LHS edge consumes a distinct state edge), together with a
  binding of LHS pattern variables to vertex values, such that substituting
  the binding into each LHS edge produces the corresponding state edge.
* Firing consumes the matched edges and emits the RHS with `fresh_vars`
  rebound to new unique integers.

Matching is brute-force backtracking: finds the first match in the
lexicographic order given by the current state's edge sequence.

Causal graph
------------
Each fired event is a node. For events e_i (earlier), e_j (later): edge
`e_i -> e_j` exists iff event e_j consumes a state edge that e_i produced.
Event 0 is a virtual "seed" event; its outputs are the initial-state edges.

Verification goals
------------------
Match SetReplace on, at minimum:
* total events fired (within MaxEvents),
* final state size,
* causal graph |V|, |E|,
* cone growth C(r) = |{events within graph-distance r of event 0}|.

Run `python rewriter.py --help` for CLI.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Set, Iterable, Optional


# --- Types ---------------------------------------------------------------

Vertex = int
Edge = Tuple[Vertex, ...]
PatternAtom = object   # int (literal) or str (variable)
PatternEdge = Tuple[PatternAtom, ...]


@dataclass
class Rule:
    lhs: List[PatternEdge]
    rhs: List[PatternEdge]

    @property
    def lhs_size(self) -> int:
        return len(self.lhs)

    @property
    def rhs_size(self) -> int:
        return len(self.rhs)

    def pattern_vars_on_lhs(self) -> Set[str]:
        return {a for e in self.lhs for a in e if isinstance(a, str)}

    def pattern_vars_on_rhs(self) -> Set[str]:
        return {a for e in self.rhs for a in e if isinstance(a, str)}

    def fresh_vars(self) -> Set[str]:
        return self.pattern_vars_on_rhs() - self.pattern_vars_on_lhs()


@dataclass
class Event:
    index: int
    input_edge_ids: List[int]        # state-edge indices consumed
    output_edge_ids: List[int]       # state-edge indices produced


@dataclass
class History:
    events: List[Event] = field(default_factory=list)
    # All state edges ever created, indexed globally:
    all_edges: List[Edge] = field(default_factory=list)
    # For each state edge: the event index that created it, and the event
    # index that consumed it (-1 if never consumed).
    creator: List[int] = field(default_factory=list)
    consumer: List[int] = field(default_factory=list)

    def live_edge_ids(self) -> List[int]:
        return [i for i in range(len(self.all_edges)) if self.consumer[i] < 0]

    def live_edges(self) -> List[Edge]:
        return [self.all_edges[i] for i in self.live_edge_ids()]

    def state_size(self) -> int:
        return len(self.live_edge_ids())


# --- Matching ------------------------------------------------------------

def _match_edge(
    pedge: PatternEdge, sedge: Edge, binding: Dict[str, int]
) -> Optional[Dict[str, int]]:
    """Try to match a pattern edge against a state edge under a current
    binding. Returns extended binding or None on failure."""
    if len(pedge) != len(sedge):
        return None
    b = dict(binding)
    for pa, sa in zip(pedge, sedge):
        if isinstance(pa, int):
            if pa != sa:
                return None
        elif isinstance(pa, str):
            if pa in b:
                if b[pa] != sa:
                    return None
            else:
                b[pa] = sa
        else:
            raise TypeError(f"Unexpected pattern atom: {pa!r}")
    return b


def find_match(
    history: History, rule: Rule
) -> Optional[Tuple[List[int], Dict[str, int]]]:
    """Find the first match of `rule.lhs` in the live state.

    Returns (list of live-edge IDs consumed, binding) or None.

    Iterates live edges in their natural (creation) order and LHS edges in
    definition order. Backtracking search.
    """
    live_ids = history.live_edge_ids()
    live_edges = [history.all_edges[i] for i in live_ids]

    lhs = rule.lhs
    n = len(lhs)

    # Chosen live-edge indices (into live_ids), one per LHS edge.
    chosen: List[int] = []
    used: Set[int] = set()

    def backtrack(i: int, binding: Dict[str, int]) -> Optional[Tuple[List[int], Dict[str, int]]]:
        if i == n:
            return ([live_ids[c] for c in chosen], binding)
        for j, sedge in enumerate(live_edges):
            if j in used:
                continue
            extended = _match_edge(lhs[i], sedge, binding)
            if extended is None:
                continue
            chosen.append(j)
            used.add(j)
            result = backtrack(i + 1, extended)
            if result is not None:
                return result
            chosen.pop()
            used.remove(j)
        return None

    return backtrack(0, {})


# --- Application ---------------------------------------------------------

def apply_rule(history: History, rule: Rule, next_fresh_id: int) -> Tuple[Optional[Event], int]:
    """Apply one firing of `rule` to the history's live state.

    Returns (event, new_next_fresh_id). If no match exists, returns (None, ...).
    """
    found = find_match(history, rule)
    if found is None:
        return None, next_fresh_id

    input_ids, binding = found

    # Allocate fresh vertex ids for fresh variables.
    fresh_map: Dict[str, int] = {}
    for fv in rule.fresh_vars():
        fresh_map[fv] = next_fresh_id
        next_fresh_id += 1

    full_binding: Dict[str, int] = {**binding, **fresh_map}

    # Instantiate RHS edges.
    rhs_edges: List[Edge] = []
    for pedge in rule.rhs:
        edge = tuple(
            (a if isinstance(a, int) else full_binding[a])
            for a in pedge
        )
        rhs_edges.append(edge)

    # Book-keeping.
    new_event_idx = len(history.events)
    output_ids: List[int] = []
    for e in rhs_edges:
        history.all_edges.append(e)
        history.creator.append(new_event_idx)
        history.consumer.append(-1)
        output_ids.append(len(history.all_edges) - 1)

    for eid in input_ids:
        history.consumer[eid] = new_event_idx

    event = Event(
        index=new_event_idx,
        input_edge_ids=list(input_ids),
        output_edge_ids=output_ids,
    )
    history.events.append(event)
    return event, next_fresh_id


def run(initial_state: List[Edge], rule: Rule, max_events: int) -> History:
    """Run the rule on `initial_state` for up to `max_events` firings.

    The initial state is installed as the outputs of a virtual seed event
    (event 0) so the causal graph's rooting is uniform.
    """
    h = History()
    # Virtual seed event 0: outputs = initial edges.
    h.events.append(Event(index=0, input_edge_ids=[], output_edge_ids=[]))
    for e in initial_state:
        h.all_edges.append(e)
        h.creator.append(0)
        h.consumer.append(-1)
        h.events[0].output_edge_ids.append(len(h.all_edges) - 1)

    # Determine next fresh vertex id: start above all ints appearing in seed.
    max_seed_vertex = max((v for e in initial_state for v in e), default=0)
    next_fresh = max_seed_vertex + 1

    for _ in range(max_events):
        ev, next_fresh = apply_rule(h, rule, next_fresh)
        if ev is None:
            break

    return h


# --- SetReplace's event order --------------------------------------------
#
# SetReplace's "EventOrderingFunction" (libSetReplace/HypergraphMatcher.cpp, MatchComparator).
# A match is (rule index, input edge ids in pattern order). Each ordering name compares one list
# of two matches: the ids sorted ascending ("OldestEdge", reversed "LeastOldEdge"), sorted
# descending ("LeastRecentEdge", reversed "NewestEdge"), in pattern order ("RuleOrdering",
# reversed "ReverseRuleOrdering"), or the rule index ("RuleIndex", reversed "ReverseRuleIndex").
# Two lists compare by their first differing entry, and a prefix comes before a longer list. The
# first name that tells two matches apart decides. SetReplace's default order is
# ["LeastRecentEdge", "RuleOrdering", "RuleIndex"].

SETREPLACE_DEFAULT_ORDER = ["LeastRecentEdge", "RuleOrdering", "RuleIndex"]

_ORDER_KEYS = {
    "OldestEdge": (lambda r, ids: sorted(ids), False),
    "LeastOldEdge": (lambda r, ids: sorted(ids), True),
    "LeastRecentEdge": (lambda r, ids: sorted(ids, reverse=True), False),
    "NewestEdge": (lambda r, ids: sorted(ids, reverse=True), True),
    "RuleOrdering": (lambda r, ids: list(ids), False),
    "ReverseRuleOrdering": (lambda r, ids: list(ids), True),
    "RuleIndex": (lambda r, ids: [r], False),
    "ReverseRuleIndex": (lambda r, ids: [r], True),
}


def _compare_lists(a: List[int], b: List[int]) -> int:
    for x, y in zip(a, b):
        if x != y:
            return -1 if x < y else 1
    return (len(a) > len(b)) - (len(a) < len(b))


def setreplace_compare(ordering: List[str], a: Tuple[int, List[int]], b: Tuple[int, List[int]]) -> int:
    """-1, 0 or 1 as match a comes before, ties with, or comes after match b."""
    for name in ordering:
        f, reverse = _ORDER_KEYS[name]
        c = _compare_lists(f(*a), f(*b))
        if c != 0:
            return -c if reverse else c
    return 0


def all_matches(history: History, rule: Rule) -> List[Tuple[List[int], Dict[str, int]]]:
    """Every match of `rule.lhs` in the live state: (edge ids in pattern order, binding).

    The candidates for a pattern edge with a bound variable are the live edges at that variable's
    vertex. The candidates for any other pattern edge are all live edges."""
    live_ids = history.live_edge_ids()
    at_vertex: Dict[int, List[int]] = {}
    for i in live_ids:
        for v in set(history.all_edges[i]):
            at_vertex.setdefault(v, []).append(i)
    out: List[Tuple[List[int], Dict[str, int]]] = []
    chosen: List[int] = []

    def backtrack(k: int, binding: Dict[str, int]) -> None:
        if k == len(rule.lhs):
            out.append((list(chosen), binding))
            return
        bound = [binding[a] for a in rule.lhs[k] if isinstance(a, str) and a in binding]
        candidates = at_vertex.get(bound[0], []) if bound else live_ids
        for i in candidates:
            if i in chosen:
                continue
            extended = _match_edge(rule.lhs[k], history.all_edges[i], binding)
            if extended is None:
                continue
            chosen.append(i)
            backtrack(k + 1, extended)
            chosen.pop()

    backtrack(0, {})
    return out


def run_ordered(initial_state: List[Edge], rules: List[Rule], max_events: int,
                ordering: List[str]) -> Tuple[History, List[int]]:
    """Single history as SetReplace's WolframModel runs it: up to `max_events` events, each the
    match first in `ordering`, a list of SetReplace's "EventOrderingFunction" names that orders
    every two matches. Edge ids are creation order: the initial edges, then each event's outputs
    in right-hand-side order. Returns the history, whose event 0 is the virtual seed event, and
    the rule index of each event, counted from 1."""
    h = History()
    h.events.append(Event(index=0, input_edge_ids=[], output_edge_ids=[]))
    for e in initial_state:
        h.all_edges.append(tuple(e))
        h.creator.append(0)
        h.consumer.append(-1)
        h.events[0].output_edge_ids.append(len(h.all_edges) - 1)
    next_fresh = max((v for e in initial_state for v in e), default=0) + 1
    event_rules: List[int] = []
    for _ in range(max_events):
        best = None
        for r, rule in enumerate(rules):
            for ids, binding in all_matches(h, rule):
                if best is None or setreplace_compare(ordering, (r, ids), (best[0], best[1])) < 0:
                    best = (r, ids, binding)
        if best is None:
            break
        r, ids, binding = best
        rule = rules[r]
        full = dict(binding)
        for fv in sorted(rule.fresh_vars()):
            full[fv] = next_fresh
            next_fresh += 1
        index = len(h.events)
        outputs = []
        for pedge in rule.rhs:
            h.all_edges.append(tuple(a if isinstance(a, int) else full[a] for a in pedge))
            h.creator.append(index)
            h.consumer.append(-1)
            outputs.append(len(h.all_edges) - 1)
        for i in ids:
            h.consumer[i] = index
        h.events.append(Event(index=index, input_edge_ids=list(ids), output_edge_ids=outputs))
        event_rules.append(r + 1)
    return h, event_rules


# --- Causal graph --------------------------------------------------------

def causal_edges(
    h: History, *, multi: bool = True, drop_virtual_seed: bool = True
) -> List[Tuple[int, int]]:
    """Edges i -> j in the causal DAG.

    * `multi=True` (SetReplace default): each mediating expression
      contributes one edge, so parallel causal edges between the same
      event pair are counted with multiplicity.
    * `drop_virtual_seed=True` (SetReplace default): causal edges whose
      creator is the virtual seed event (event 0) are excluded, matching
      SetReplace's convention of not counting inputs to the first real
      events.
    """
    edges: List[Tuple[int, int]] = []
    for eid in range(len(h.all_edges)):
        i = h.creator[eid]
        j = h.consumer[eid]
        if j < 0 or i == j:
            continue
        if drop_virtual_seed and i == 0:
            continue
        edges.append((i, j))
    if multi:
        return sorted(edges)
    return sorted(set(edges))


def cone_distances_from(start: int, nodes: int, edges: List[Tuple[int, int]]) -> Dict[int, int]:
    """BFS shortest-path distances from `start` in the digraph.

    Multi-edges collapsed for BFS purposes (distance semantics).
    """
    adj: Dict[int, List[int]] = {i: [] for i in range(nodes)}
    seen_pairs: Set[Tuple[int, int]] = set()
    for u, v in edges:
        if (u, v) not in seen_pairs:
            adj[u].append(v)
            seen_pairs.add((u, v))
    dist = {start: 0}
    frontier = [start]
    while frontier:
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    nxt.append(v)
        frontier = nxt
    return dist


def cone_growth(h: History, start: int = 1) -> List[Tuple[int, int]]:
    """C(r) = |events at directed distance <= r from `start` along causal edges|.

    Uses full causal graph (virtual seed edges NOT dropped) so that BFS
    reaches every causally-reachable event. Default start = event 1, the
    first real rewriting event.
    """
    n = len(h.events)
    ce = causal_edges(h, multi=False, drop_virtual_seed=False)
    if start >= n:
        return []
    dists = cone_distances_from(start, n, ce)
    max_r = max(dists.values(), default=0)
    out = []
    for r in range(0, max_r + 1):
        out.append((r, sum(1 for v in dists.values() if v <= r)))
    return out


# --- Gorard's named rule -------------------------------------------------

def gorard_rule() -> Rule:
    """The rule Gorard names in arXiv:2102.09363, line 6202.
       LHS: {{x,y},{y,z},{z,w},{w,v}}
       RHS: {{y,u},{u,v},{w,x},{x,u}}  (u fresh)
    """
    return Rule(
        lhs=[("x", "y"), ("y", "z"), ("z", "w"), ("w", "v")],
        rhs=[("y", "u"), ("u", "v"), ("w", "x"), ("x", "u")],
    )


# --- Seeds matching SetReplace runs -------------------------------------

def seed(name: str) -> List[Edge]:
    if name == "4cycle":
        return [(1, 2), (2, 3), (3, 4), (4, 1)]
    if name == "5path" or name == "4path":  # original SetReplace misnamed it; 4 edges
        return [(1, 2), (2, 3), (3, 4), (4, 5)]
    if name == "6cycle":
        return [(i, (i % 6) + 1) for i in range(1, 7)]
    if name == "8cycle":
        return [(i, (i % 8) + 1) for i in range(1, 9)]
    if name == "10path":
        return [(i, i + 1) for i in range(1, 11)]
    if name == "20cycle":
        return [(i, (i % 20) + 1) for i in range(1, 21)]
    if name == "fig8":
        a = [(i, (i % 6) + 1) for i in range(1, 7)]
        b = [(i + 6, ((i - 1) % 6) + 7) for i in range(1, 7)]
        # Connector edges 1<->7 both directions
        return a + b + [(1, 7), (7, 1)]
    if name == "grid3_3":
        k = 3
    elif name == "grid3_4":
        k = 4
    elif name == "grid3_5":
        k = 5
    else:
        raise KeyError(name)
    out: List[Edge] = []
    def vid(i: int, j: int, l: int) -> int:
        return 1 + ((i - 1) * k + (j - 1)) * k + (l - 1)
    for i in range(1, k + 1):
        for j in range(1, k + 1):
            for l in range(1, k + 1):
                if i < k:
                    out.append((vid(i, j, l), vid(i + 1, j, l)))
                if j < k:
                    out.append((vid(i, j, l), vid(i, j + 1, l)))
                if l < k:
                    out.append((vid(i, j, l), vid(i, j, l + 1)))
    return out


# --- CLI -----------------------------------------------------------------

def _loglog_dim_fit(cone_pts: List[Tuple[int, int]]) -> Optional[float]:
    import math
    # Fit over the middle half to match the SetReplace analysis.
    if len(cone_pts) < 8:
        return None
    r_max = cone_pts[-1][0]
    r_lo = max(2, r_max // 4)
    r_hi = max(r_lo + 3, 3 * r_max // 4)
    pts = [(r, c) for r, c in cone_pts if r_lo <= r <= r_hi and c > 0]
    if len(pts) < 3:
        return None
    n = len(pts)
    xs = [math.log(r) for r, _ in pts]
    ys = [math.log(c) for _, c in pts]
    mx = sum(xs) / n
    my = sum(ys) / n
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = sum((x - mx) ** 2 for x in xs)
    return num / den if den > 0 else None


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Independent Python re-implementation of Gorard's named EFE rule.")
    p.add_argument("--seed", default="6cycle")
    p.add_argument("--max-events", type=int, default=500)
    p.add_argument("--json", action="store_true", help="Emit JSON summary")
    args = p.parse_args(argv)

    s = seed(args.seed)
    r = gorard_rule()
    h = run(s, r, args.max_events)

    ce = causal_edges(h)
    cg = cone_growth(h)
    dim = _loglog_dim_fit(cg)

    summary = {
        "seed": args.seed,
        "seed_size": len(s),
        "max_events": args.max_events,
        "events_fired": len(h.events) - 1,    # subtract virtual seed
        "final_state_size": h.state_size(),
        "causal_graph_vertices": len(h.events),
        "causal_graph_edges": len(ce),
        "cone_points": cg,
        "cone_log_log_dim_fit": dim,
    }
    if args.json:
        print(json.dumps(summary, indent=2))
    else:
        print(f"seed:                {args.seed}  (|E|={len(s)})")
        print(f"max events:          {args.max_events}")
        print(f"events fired:        {summary['events_fired']}")
        print(f"final state size:    {summary['final_state_size']}")
        print(f"causal graph: |V|={summary['causal_graph_vertices']}, |E|={summary['causal_graph_edges']}")
        if cg:
            print(f"C(r) for r=0..{min(15, len(cg) - 1)}: {cg[:16]}")
        print(f"cone log-log dim fit (middle half): {dim}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
