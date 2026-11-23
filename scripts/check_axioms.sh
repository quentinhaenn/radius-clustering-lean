#!/usr/bin/env bash
# Fails on any axiom outside propext / Classical.choice / Quot.sound; sorryAx fails only with STRICT=1.
set -euo pipefail
cd "$(dirname "$0")/.."

out=$(lake env lean scripts/CheckAxioms.lean)
echo "$out"

axioms=$(echo "$out" | tr '\n' ' ' | grep -o '\[[^]]*\]' | tr -d '[] ' | tr ',' '\n' | sort -u)
bad=$(echo "$axioms" | grep -Ev '^((propext|Classical\.choice|Quot\.sound|sorryAx))?$' || true)
if [ -n "$bad" ]; then
  echo "FAIL: forbidden axioms:" $bad
  exit 1
fi
if echo "$axioms" | grep -qx sorryAx; then
  if [ "${STRICT:-0}" = 1 ]; then
    echo "FAIL: some theorems still depend on sorryAx"
    exit 1
  fi
  echo "WARNING: some theorems still depend on sorryAx (pending proofs)"
fi
echo "OK"
