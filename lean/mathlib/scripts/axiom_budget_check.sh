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
#
# Audit note (2026-06, LorentzSelection +4 then −4 → net 0): the LorentzSelection
# module (Open Problem 3b skeleton) ORIGINALLY named 4 opaque AQFT *interface*
# axioms (`axiom _ : Prop`) for the Type III₁ / Tomita–Takesaki analytic inputs
# beyond current Mathlib (`record_presheaf_exists`, `boundary_reconstruction`,
# `decoherence_functional_measure`, `screen_local_marginal`).  DISCHARGE PASS:
# these four — which asserted nothing (opaque Props) and were used by no theorem —
# have been RETIRED and replaced by the explicit `RecordedHistoryNet` structure
# that WRITES DOWN the intended content as type-checked data + propositions
# (holographic finiteness bound, boundary-reconstruction natural iso, decoherence
# probability weights, projective/no-signaling marginal).  The covariance result
# is now the conditional theorems `covariant_selection_of_net` /
# `covariant_selection_exists`, and no-signaling is the THEOREM
# `net_no_signaling`.  This is the "interface-as-hypothesis, not axiom" pattern:
# the deep Type III₁ existence problem is NOT solved, but it is now a single
# precise, written-down conjecture ("does a RecordedHistoryNet exist for
# realistic QFT?") rather than four assumed axioms.  The module adds ZERO project
# axioms.  An earlier 5th axiom (`actSection_consistent`, transport bookkeeping)
# was likewise ELIMINATED by upgrading the diamond action to an `OrderIso`
# (inverse-monotonicity makes the consistency a theorem); `evaluation_covariance`
# depends only on standard axioms.  FiniteModularTheory and FreeFieldRecord add
# ZERO axioms (pure proof / standard analysis).
#
# Audit note (2026-06, GleasonSelector): the module originally named a FALSE
# axiom `effect_gleason_representation` (positivity-free; a Fin 2
# counterexample satisfies its premises but is not Born).  RETIRED.  In its
# place — after the THIRD GPT-5.5-pro review (discharge ray-support from
# positivity) — the genuine Gleason bridge is now PROVED:
# `support_of_positive_certain` (positivity + certainty ⇒ ray-support) and the
# capstone `positive_ray_certain_forces_born` (positivity + normalization +
# ray-certainty ⇒ Born).  These rest on TWO standard linear-algebra interface
# axioms.  DISCHARGE PASS — BOTH NOW PROVED: `positive_functional_hermitian`
# (polarization: realness of w((A+X)ᴴ(A+X)) and w((A+iX)ᴴ(A+iX)) ⇒ conjugate
# symmetry) AND `psd_null_radical` (Cauchy–Schwarz null-radical: first-slot
# conjugate-linearity from hconj, then the real-quadratic discriminant
# `quadratic_nonneg_forall_linear_zero` at c=t and c=it forces re=im=0 of
# B Q X).  The GleasonSelector module now adds ZERO project axioms; the
# capstone `positive_ray_certain_forces_born` ("Born follows from positivity")
# depends on the STANDARD Lean axioms only.  Net: 45 → 44.
#
# Audit note (2026-06, LorentzSelection AQFT discharge): the 4 opaque AQFT
# placeholder axioms retired (see the LorentzSelection note above).  Net: 44 → 40.
AXIOM_BUDGET=40
AXIOM_COUNT="$(grep -rhE '^axiom ' QIQTH/ | wc -l | tr -d ' ')"
echo "[axiom-budget] raw axiom count: $AXIOM_COUNT (budget $AXIOM_BUDGET)"
if [ "$AXIOM_COUNT" -gt "$AXIOM_BUDGET" ]; then
  echo "[axiom-budget] axioms by file:" >&2
  grep -rcE '^axiom ' QIQTH/ | grep -v ':0$' >&2 || true
  fail "raw axiom count $AXIOM_COUNT exceeds budget $AXIOM_BUDGET."
fi

echo "[axiom-budget] OK — no sorryAx, no deleted-axiom regressions, count within budget."
