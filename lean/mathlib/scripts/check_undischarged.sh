#!/usr/bin/env bash
# Undischarged-hypothesis checker — lists each target capstone's Prop-hypotheses and probes each for
# auto-dischargeability (redundant ⇒ should be internalized).  Edit the `targets` list in
# scripts/check_undischarged.lean to choose which theorems to audit.
#
# Usage:  bash scripts/check_undischarged.sh
set -euo pipefail
cd "$(dirname "$0")/.."
exec ~/.elan/bin/lake env lean scripts/check_undischarged.lean
