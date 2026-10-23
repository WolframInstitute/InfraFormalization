#!/usr/bin/env bash
# Regenerate THEOREM_STATUS.md: collect the theorems cited in the .md files,
# print their axioms with the built library, and classify them.
# Requires a completed `lake build` in lean/.
set -euo pipefail
repo="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
python3 "$repo/scripts/cited_theorems.py" "$tmp/cited"
(cd "$repo/lean" && lake env lean "$tmp/cited.lean") > "$tmp/axioms.txt" 2>&1
python3 "$repo/scripts/classify_axioms.py" "$tmp/axioms.txt" "$tmp/cited.tsv" "$repo/THEOREM_STATUS.md"
cp "$tmp/cited.unresolved" "$repo/results/cited_names_unresolved.tsv"
rm -rf "$tmp"
