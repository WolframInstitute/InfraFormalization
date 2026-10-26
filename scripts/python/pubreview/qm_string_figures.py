"""Normal forms of the string substitution systems of Figures 6 and 7 of Complex Systems 29(2)
537-598 (papers/gorard_complexsystems_29_2.txt lines 297-310).

Figure 6: AB -> A, BA -> B from ABA is stated to be non-confluent with two normal forms.
Figure 7: A -> B, BB -> B and AA -> BA, AB -> BA are stated to be confluent. The figure does not
give every initial condition, so every string over {A, B} of length 1 to 8 is checked: each
system terminates from it (no string repeats on a path and every path ends) and the set of
normal forms reachable from it is counted."""
import itertools
import json


def successors(s, rules):
    out = set()
    for lhs, rhs in rules:
        i = s.find(lhs)
        while i != -1:
            out.add(s[:i] + rhs + s[i + len(lhs):])
            i = s.find(lhs, i + 1)
    return out


def normal_forms(s, rules, limit=100000):
    seen, stack, nf = {s}, [s], set()
    while stack:
        t = stack.pop()
        nxt = successors(t, rules)
        if not nxt:
            nf.add(t)
        for u in nxt:
            if u not in seen:
                seen.add(u)
                stack.append(u)
                if len(seen) > limit:
                    raise RuntimeError("no termination bound")
    return nf


def terminates(s, rules):
    # Every system here is length non-increasing, so the reachable set is finite; a cycle in it
    # would be an infinite path.
    colour = {}

    def dfs(t):
        colour[t] = 1
        for u in successors(t, rules):
            c = colour.get(u, 0)
            if c == 1 or (c == 0 and not dfs(u)):
                return False
        colour[t] = 2
        return True

    return dfs(s)


def main():
    report = {"fig6_ABA": sorted(normal_forms("ABA", [("AB", "A"), ("BA", "B")]))}
    for name, rules in {"fig7_A_B__BB_B": [("A", "B"), ("BB", "B")],
                        "fig7_AA_BA__AB_BA": [("AA", "BA"), ("AB", "BA")]}.items():
        bad, nonterm, total = [], [], 0
        for n in range(1, 9):
            for w in itertools.product("AB", repeat=n):
                s = "".join(w)
                total += 1
                if not terminates(s, rules):
                    nonterm.append(s)
                elif len(normal_forms(s, rules)) != 1:
                    bad.append(s)
        report[name] = {"strings": total, "non_terminating": len(nonterm),
                        "more_than_one_normal_form": bad[:10], "count_bad": len(bad)}
    print(json.dumps(report, indent=1))
    with open("../../../results/publication_review/qm_string_figures.json", "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
