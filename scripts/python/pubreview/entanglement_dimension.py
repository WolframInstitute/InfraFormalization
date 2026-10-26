"""The cone-growth dimension estimate of arXiv:2301.12455 (papers/tex_2301_12455/
EntanglementEntropy.tex lines 955-975, Figures 10-13) on its two example rules.

G9 states that the causal graphs of {{x,y,y},{x,z,u}} -> {{u,v,v},{v,z,y},{x,y,v}} and
{{x,y,x},{x,z,u}} -> {{u,v,u},{v,u,z},{x,y,v}} have a "1+1-dimensional Lorentzian manifold-like
limiting structure", with the logarithmic difference estimator
  Delta_t(p) = (log Vol(C_{t+1}(p)) - log Vol(C_t(p))) / (log(t+1) - log t)
"identifying the limiting dimension of two correctly in both cases". G9 does not state the initial
condition, the update order or the number of events. This script uses k copies of {0,0,0} (k = 2 by default, the second argument), the
"Generational" update (every non-overlapping match applied at each step), and the forward
causal cone C_t(p) = events within directed distance t of p, for p the first event and for the
events of generation 3. It prints Delta_t for each t and the event count. It also prints the
same estimator on the undirected spatial hypergraph of the final state (ball growth around the
vertex of largest degree)."""
import collections
import json
import math
import sys

from hg_env import evolve

RULES = {
    "flat_rule": ([["x", "y", "y"], ["x", "z", "u"]], [["u", "v", "v"], ["v", "z", "y"], ["x", "y", "v"]]),
    "curved_rule": ([["x", "y", "x"], ["x", "z", "u"]], [["u", "v", "u"], ["v", "u", "z"], ["x", "y", "v"]]),
}


def deltas(counts):
    out = []
    for t in range(1, len(counts) - 1):
        a, b = counts[t], counts[t + 1]
        if a > 0 and b > 0:
            out.append(round((math.log(b) - math.log(a)) / (math.log(t + 1) - math.log(t)), 3))
    return out


def cone_counts(succ, p, tmax):
    dist = {p: 0}
    q = collections.deque([p])
    while q:
        u = q.popleft()
        if dist[u] >= tmax:
            continue
        for v in succ[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                q.append(v)
    hist = collections.Counter(dist.values())
    cum, out = 0, []
    for t in range(tmax + 1):
        cum += hist[t]
        out.append(cum)
    return out


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    loops = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    init = [[0, 0, 0]] * loops
    report = {}
    for name, rule in RULES.items():
        r = evolve([rule], init, steps, generational=True,
                   canonicalize_states=None)
        succ = collections.defaultdict(list)
        for a, b in r.causal_edges.array[:, :2].tolist():
            succ[a].append(b)
        events = list(r.events.records())
        gen = {e["Id"]: e["OutputState"] for e in events}
        first = min(gen)
        cones = {"first_event": cone_counts(succ, first, steps)}
        early = sorted(e for e in gen if gen[e] == 3)[:3]
        for e in early:
            cones[f"event_{e}"] = cone_counts(succ, e, steps)
        recs = list(r.states.records())
        last = max(recs, key=lambda s: s["Step"])
        adj = collections.defaultdict(set)
        for edge in last["Edges"]:
            vs = edge[1:]
            for a in vs:
                for b in vs:
                    if a != b:
                        adj[a].add(b)
        centre = max(adj, key=lambda v: len(adj[v]))
        dist = {centre: 0}
        q = collections.deque([centre])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if v not in dist:
                    dist[v] = dist[u] + 1
                    q.append(v)
        hist = collections.Counter(dist.values())
        balls, cum = [], 0
        for t in range(max(hist) + 1):
            cum += hist[t]
            balls.append(cum)
        report[name] = {
            "steps": steps, "initial_self_loops": loops, "events": r.num_events, "causal_edges": r.num_causal_edges,
            "final_edges": len(last["Edges"]), "final_vertices": len(adj),
            "cone_counts": cones,
            "cone_deltas": {k: deltas(v) for k, v in cones.items()},
            "spatial_ball_counts": balls, "spatial_ball_deltas": deltas(balls)}
        print(name, json.dumps(report[name]), flush=True)
    with open(f"../../../results/publication_review/entanglement_dimension_{steps}_{loops}loops.json", "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
