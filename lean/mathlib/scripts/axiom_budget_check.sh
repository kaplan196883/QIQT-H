#!/usr/bin/env bash
#
# axiom_budget_check.sh — CI guard for the QIQT-H axiom budget.
#
# GPT-5.5-pro audit recommendation: "automatically fail if public
# theorems regain dependence on deprecated axioms."  This script builds
# the QIQTH.AxiomAudit module (whose `#print axioms` directives emit the
# dependency list of every advertised theorem) and fails the build if:
#
#   1. any theorem depends on `sorryAx` (an unfinished proof), or
#   2. any theorem depends on one of the DELETED false/placeholder
#      Step-1 sub-axioms (a regression that would silently re-introduce
#      a literally-false axiom), or
#   3. the project-wide raw `axiom` count exceeds the agreed budget.
#
# Usage (from lean/mathlib/):
#   bash scripts/axiom_budget_check.sh
#
# Exit code 0 = clean; non-zero = budget violation (prints the offense).

set -euo pipefail

cd "$(dirname "$0")/.."   # -> lean/mathlib

# ── 1. Build the audit module and capture the #print axioms output ────
echo "[axiom-budget] building QIQTH.AxiomAudit ..."
AUDIT_LOG="$(mktemp)"
trap 'rm -f "$AUDIT_LOG"' EXIT
lake build QIQTH.AxiomAudit 2>&1 | tee "$AUDIT_LOG"

fail() { echo "[axiom-budget] FAIL: $1" >&2; exit 1; }

# ── 2. No sorryAx anywhere ────────────────────────────────────────────
if grep -q "sorryAx" "$AUDIT_LOG"; then
  grep -n "sorryAx" "$AUDIT_LOG" >&2
  fail "a theorem depends on sorryAx (unfinished proof)."
fi

# ── 3. No dependence on the DELETED false/placeholder Step-1 axioms ───
# These five were removed in the second strengthening pass; three were
# literally false as stated.  If any reappears in a dependency list, a
# regression has re-introduced it.
DELETED_AXIOMS=(
  "step1a_complex_linear_extension"
  "step1b_basis_preservation"
  "step1c_coefficient_unification"
  "step1d_hadamard_pins_form"
  "step1e_hermitian_restriction_real_coefficients"
)
for ax in "${DELETED_AXIOMS[@]}"; do
  if grep -q "$ax" "$AUDIT_LOG"; then
    grep -n "$ax" "$AUDIT_LOG" >&2
    fail "dependency on deleted/false axiom '$ax' has reappeared."
  fi
done

# ── 4. Project-wide raw axiom budget ─────────────────────────────────
# Budget is the count after the consolidation + Step-1 deletion passes.
# Raise this number ONLY with an accompanying audit note explaining the
# new axiom; never silently.
AXIOM_BUDGET=40
AXIOM_COUNT="$(grep -rhE '^axiom ' QIQTH/ | wc -l | tr -d ' ')"
echo "[axiom-budget] raw axiom count: $AXIOM_COUNT (budget $AXIOM_BUDGET)"
if [ "$AXIOM_COUNT" -gt "$AXIOM_BUDGET" ]; then
  echo "[axiom-budget] axioms by file:" >&2
  grep -rcE '^axiom ' QIQTH/ | grep -v ':0$' >&2 || true
  fail "raw axiom count $AXIOM_COUNT exceeds budget $AXIOM_BUDGET."
fi

echo "[axiom-budget] OK — no sorryAx, no deleted-axiom regressions, count within budget."
