"""Byte-identical figures across the TeX sources of the reviewed papers.

For each paper, every \\includegraphics on a line that is not commented out is resolved to a file
of its TeX directory (trying the extensions .png, .pdf, .jpg when none is given), and its MD5 is
taken. The script lists every MD5 that occurs in the included figures of two or more papers,
with the paper, the TeX line and the file name."""
import collections
import hashlib
import json
import os
import re

PAPERS = {
    "G1": "tex_2004/RelativityAndGravitation.tex",
    "G2": "tex_2011/CausalSetPaper.tex",
    "G3": "tex_2102/NumericalRelativity.tex",
    "G4": "tex_2303/GravitationalCollapsePaper.tex",
    "GI": "tex_2308/GravitasPaper.tex",
    "GII": "tex_2401/GravitasPaper2.tex",
    "GH": "tex_2402/AccretionPaper2.tex",
    "G6": "tex_2105/act21.tex",
    "G7": "tex_2111/homotopy1.tex",
    "G8": "tex_2301_04690/ComputationalIrreducibility.tex",
    "G9": "tex_2301_12455/EntanglementEntropy.tex",
}
ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "..", "papers")
INC = re.compile(r"\\includegraphics(?:\[[^\]]*\])?\{([^}]*)\}")


def resolve(d, name):
    for cand in (name, name + ".png", name + ".pdf", name + ".jpg"):
        p = os.path.join(d, cand)
        if os.path.isfile(p):
            return p
    return None


def main():
    seen = collections.defaultdict(list)
    missing = []
    for paper, rel in PAPERS.items():
        path = os.path.join(ROOT, rel)
        d = os.path.dirname(path)
        with open(path, encoding="utf-8", errors="replace") as f:
            for n, line in enumerate(f, 1):
                if line.lstrip().startswith("%"):
                    continue
                code = line.split("%")[0] if "\\%" not in line else line
                for name in INC.findall(code):
                    p = resolve(d, name.strip())
                    if p is None:
                        missing.append([paper, n, name])
                        continue
                    with open(p, "rb") as g:
                        h = hashlib.md5(g.read()).hexdigest()
                    seen[h].append([paper, n, os.path.basename(p)])
    shared = [v for v in seen.values() if len({x[0] for x in v}) > 1]
    shared.sort(key=lambda v: (sorted({x[0] for x in v}), v[0][1]))
    pairs = collections.Counter()
    for v in shared:
        ps = sorted({x[0] for x in v})
        for i in range(len(ps)):
            for j in range(i + 1, len(ps)):
                pairs[f"{ps[i]}-{ps[j]}"] += 1
    out = {"shared_figures": shared, "pair_counts": dict(pairs), "unresolved": missing}
    print(json.dumps({"pair_counts": dict(pairs), "unresolved": len(missing)}, indent=1))
    for v in shared:
        print(v)
    with open(os.path.join(ROOT, "..", "results", "publication_review", "figure_reuse.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
