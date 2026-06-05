#!/usr/bin/env bash
#
# vacuity_lint.sh — flag vacuous Prop bodies in the QIQTH development.
#
# The axiom-budget check (axiom_budget_check.sh) counts axiom declarations and
# catches `sorryAx`, but it CANNOT see the soundness-hole family that bit this
# project twice (IsTensorMultiplicative := ∀ρσ, True feeding step3; the
# ∀-Dd2 flagship hypothesis): a predicate whose body is vacuously `True`.
#
# This linter greps for predicate bodies that are syntactically `True`
# (`:= True`, `↦ True`, trailing `→ True` / `, True`).  It is INFORMATIONAL
# (exit 0) — each hit must be triaged by hand:
#
#   • vacuous CONCLUSION of an axiom/theorem      → content-free, but SOUND.
#   • vacuous HYPOTHESIS feeding an axiom whose
#     conclusion is concretely falsifiable         → SOUNDNESS HOLE (fix it).
#   • a structure/instance field (e.g. `le _ _ := True`) → usually harmless.
#
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/../QIQTH" && pwd)"

echo "[vacuity-lint] scanning $ROOT/*.lean for vacuous Prop bodies ..."
# Strip line comments FIRST (so a trailing `-- ...` cannot hide a `True` body),
# then match a definition / quantifier / implication body that is exactly `True`:
#   `:= True` , `↦ True` , `→ True` , `, True`  (the last catches `∀…,True` / `∃…,True`).
PAT=':=[[:space:]]*True\b|↦[[:space:]]*True\b|→[[:space:]]*True\b|,[[:space:]]*True[[:space:]]*$'
hits=""
for f in "$ROOT"/*.lean; do
  while IFS= read -r m; do
    hits="${hits}${f}:${m}"$'\n'
  done < <(sed -E 's/[[:space:]]*--.*$//' "$f" | grep -nE "$PAT")
done
hits=$(printf '%s' "$hits" | grep -E . || true)

if [ -z "$hits" ]; then
  echo "[vacuity-lint] OK — no vacuous Prop bodies found."
  exit 0
fi

n=$(printf '%s\n' "$hits" | grep -c .)
echo "[vacuity-lint] $n vacuous-body site(s) found — TRIAGE each (see header):"
printf '%s\n' "$hits" | sed 's/^/    /'
echo "[vacuity-lint] (informational; known continuum placeholders are documented in AXIOM_CONTRACTS.md)"
exit 0
