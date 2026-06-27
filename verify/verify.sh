#!/usr/bin/env bash
#
# verify.sh — QIQT-H verification capsule (Stages 1-3 + claim card).
#
# Re-establishes, on YOUR machine, with minimal trust in the authors, that the
# capstone theorems in verify/config.json are accepted by the Lean kernel and
# depend only on the standard axioms. Trust collapses to: (a) the Lean kernel,
# (b) your reading of the rendered statement, (c) the labelled physical inputs.
#
#   Stage 1  clean-room rebuild of the project's own modules (deps pinned by
#            lake-manifest.json) — the kernel re-checks every project proof.
#   Stage 2  independent re-check with lean4checker, if installed — removes
#            trust in Lean's *elaborator*; only the kernel logic remains.
#   Stage 3  axiom / soundness audit (verify/audit.py): the COMPLETE transitive
#            axiom set must be a subset of {propext, Classical.choice, Quot.sound}
#            with no sorryAx / native_decide; fail-closed.
#   Card     verify/out/claim_card.md — formal statement, complete trusted base,
#            and the full hypothesis ledger (the honest residue).
#
# Usage (from anywhere):  bash verify/verify.sh
# Exit code 0 = certified clean; non-zero = a stage failed (see output).
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
MATHLIB="$REPO/lean/mathlib"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
[ -x "$LAKE" ] || LAKE="$(command -v lake || true)"
[ -n "$LAKE" ] || { echo "FATAL: lake not found (set \$LAKE or install elan)."; exit 2; }

hr() { printf '%s\n' "------------------------------------------------------------"; }

# ── Stage 0 — provenance pins ────────────────────────────────────────────────
hr; echo "[stage0] provenance"
echo "  project commit : $(git -C "$REPO" rev-parse --short HEAD 2>/dev/null || echo '?')"
echo "  lean toolchain : $(cat "$MATHLIB/lean-toolchain")"
MREV="$(grep -B2 '"name": "mathlib"' "$MATHLIB/lake-manifest.json" | grep -m1 '"rev"' | grep -oE '[0-9a-f]{40}' || true)"
echo "  mathlib rev    : ${MREV:-?}"
echo "  lake           : $LAKE"

# ── Stage 1 — clean-room rebuild of the project's own modules ────────────────
hr; echo "[stage1] clean-room rebuild of QIQTH (kernel re-checks every project proof)"
echo "  note: dependencies (Mathlib, …) are pinned by lake-manifest.json. For a FULL"
echo "        from-source clean room (Mathlib included), use the Docker recipe in README."
( cd "$MATHLIB"
  # drop the project's compiled artifacts so they are genuinely rebuilt + re-checked
  find .lake/build -path '*QIQTH*' \( -name '*.olean' -o -name '*.ilean' -o -name '*.c' \) -delete 2>/dev/null || true
  "$LAKE" build QIQTH
)
echo "[stage1] OK — project built; the kernel accepted every proof during the build."

# ── Stage 2 — independent re-check (lean4checker) ────────────────────────────
hr; echo "[stage2] independent kernel re-check (lean4checker)"
L4C=""
if command -v lean4checker >/dev/null 2>&1; then L4C="lean4checker"
elif ( cd "$MATHLIB" && "$LAKE" exe lean4checker --help >/dev/null 2>&1 ); then L4C="$LAKE exe lean4checker"
fi
if [ -n "$L4C" ]; then
  ( cd "$MATHLIB" && $L4C QIQTH )
  echo "[stage2] OK — lean4checker re-verified the environment independently of the elaborator."
else
  echo "[stage2] SKIPPED — lean4checker not installed."
  echo "         The independent re-check is the strongest anti-fraud step; install it for a"
  echo "         complete certificate (see verify/README.md → 'Stage 2'). Stage 1's build"
  echo "         already had the kernel check every proof; lean4checker additionally removes"
  echo "         trust in the elaborator."
fi

# ── Stage 3 + claim card — axiom audit (fail-closed) ─────────────────────────
hr; echo "[stage3] axiom / soundness audit + claim card"
( cd "$REPO" && PYTHONPATH=scripts python verify/audit.py )
STATUS=$?

hr
if [ "$STATUS" -eq 0 ]; then
  echo "RESULT: ✅ certified clean on this machine. See verify/out/claim_card.md"
else
  echo "RESULT: ❌ audit failed (exit $STATUS). See output above and verify/out/claim_card.md"
fi
exit "$STATUS"
