#!/usr/bin/env bash
# Write results/lean_inventory.tsv: every declaration of the library with its
# axiom class and the flags of scripts/inventory.lean, and print counts.
# Requires a completed `lake build` in lean/.
set -euo pipefail
repo="$(cd "$(dirname "$0")/.." && pwd)"
tmp="$(mktemp -d)"
export INVENTORY_OUT="$tmp/decls.tsv"
export INVENTORY_AXIOMS="$tmp/axioms.lean"
cd "$repo/lean"
lake env lean "$repo/scripts/inventory.lean"
lake env lean "$INVENTORY_AXIOMS" > "$tmp/axioms.txt" 2>&1 || true
python3 "$repo/scripts/merge_inventory.py" "$tmp/decls.tsv" "$tmp/axioms.txt" "$repo/results/lean_inventory.tsv"
rm -rf "$tmp"
