"""Collect theorem names cited in the repository's prose and write a Lean
file that prints the axioms of each.

1. Parse lean/InfraFormalization/**/*.lean, tracking `namespace`/`end`
   and `section`/`end`, and record the fully qualified name of every
   `theorem`/`lemma` declaration with its file and line.
2. Scan *.md files (repository root, notes/, results/, publications/,
   reports/) for backticked identifiers. An identifier is cited when it
   equals a full name, or the last one or two components of exactly one
   full name.
3. Write <out>.lean with `#print axioms` lines and <out>.tsv with
   full name, file:line, citing documents. Cited names that match no
   theorem are written to <out>.unresolved.

Usage: python3 cited_theorems.py <out-prefix>  (run by scripts/theorem_status.sh)
"""
import collections
import pathlib
import re
import sys

VACUOUS_DEFS = [
    "HypergraphMetricOriginObligation", "HypergraphPartialMetricOriginObligation",
    "HypergraphMetricOriginObligationWithRate", "HypergraphMetricOriginObligationStrong",
    "HypergraphPartialMetricOriginObligationStrong", "HypergraphQuantumOriginObligationStrong",
    "HypergraphBBHOriginObligationStrong", "ConnectionDataOriginObligation",
    "GR_emerges_from_hypergraph", "QM_emerges_from_hypergraph", "BBH_emerges_from_hypergraph",
    "GR_emerges_from_hypergraph_minkowski", "GR_emerges_from_some_hypergraph",
    "DistConvergesTo", "ConnectionConvergesTo", "RiemannTensorConvergesTo",
    "EinsteinFieldEquationsHold", "DiscreteStressEnergyEmerges", "InitialDataMatches",
    "Psi4Matches", "BornRuleEmerges", "subdivisionDiscrepancy", "formanTarget",
    "LocallyTrivial", "CircularReconstruction", "MetricConstruction",
]

REPO = pathlib.Path(__file__).resolve().parent.parent
LEAN = REPO / "lean" / "InfraFormalization"

decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:({\[]+)")
ns_re = re.compile(r"^namespace\s+(\S+)")
sec_re = re.compile(r"^section\b\s*(\S*)")
end_re = re.compile(r"^end\b\s*(\S*)")

decls = {}  # full name -> (file, line)
for f in sorted(LEAN.rglob("*.lean")):
    stack = []  # list of (kind, name)
    in_comment = 0
    lines = f.read_text().splitlines()
    for i, line in enumerate(lines, 1):
        s = line.strip()
        # crude block-comment tracking
        if in_comment:
            in_comment += s.count("/-") - s.count("-/")
            continue
        if s.startswith("/-"):
            in_comment = s.count("/-") - s.count("-/")
            if in_comment < 0:
                in_comment = 0
            continue
        m = ns_re.match(s)
        if m:
            stack.append(("ns", m.group(1)))
            continue
        m = sec_re.match(s)
        if m:
            stack.append(("sec", m.group(1)))
            continue
        m = end_re.match(s)
        if m and stack:
            stack.pop()
            continue
        m = decl_re.match(s)
        if m:
            name = m.group(2)
            prefix = ".".join(n for k, n in stack if k == "ns")
            full = name if name.startswith("_root_.") else (prefix + "." + name if prefix else name)
            full = full.replace("_root_.", "")
            stmt_lines = []
            for j in range(i - 1, min(i + 40, len(lines))):
                stmt_lines.append(lines[j])
                if ":=" in lines[j] or lines[j].strip().startswith("by"):
                    break
            decls[full] = (str(f.relative_to(REPO)), i, " ".join(stmt_lines))

suffix_index = collections.defaultdict(set)
for full in decls:
    parts = full.split(".")
    for k in range(1, len(parts) + 1):
        suffix_index[".".join(parts[-k:])].add(full)

docs = [p for p in REPO.glob("*.md")]
for sub in ("notes", "results", "publications", "reports"):
    docs += list((REPO / sub).rglob("*.md"))

cites = collections.defaultdict(set)
unresolved = collections.defaultdict(set)
tick_re = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*[A-Za-z0-9_'])`")
for d in docs:
    text = d.read_text(errors="replace")
    for tok in set(tick_re.findall(text)):
        cands = suffix_index.get(tok)
        rel = str(d.relative_to(REPO))
        if cands and len(cands) == 1:
            cites[next(iter(cands))].add(rel)
        elif cands:
            for c in cands:
                cites[c].add(rel)
        elif "_" in tok and tok[0].islower() and "." not in tok and len(tok) > 6:
            unresolved[tok].add(rel)

out = sys.argv[1]
with open(out + ".lean", "w") as fh:
    fh.write("import InfraFormalization\n")
    for full in sorted(cites):
        fh.write(f"#print axioms {full}\n")
with open(out + ".tsv", "w") as fh:
    for full in sorted(cites):
        f, l, stmt = decls[full]
        hits = sorted(n for n in VACUOUS_DEFS if re.search(r"\b" + re.escape(n) + r"\b", stmt))
        fh.write(f"{full}\t{f}:{l}\t{','.join(sorted(cites[full]))}\t{','.join(hits)}\n")
with open(out + ".unresolved", "w") as fh:
    for tok in sorted(unresolved):
        fh.write(f"{tok}\t{','.join(sorted(unresolved[tok]))}\n")
print(len(decls), "theorems in library;", len(cites), "cited;", len(unresolved), "unresolved tokens")
