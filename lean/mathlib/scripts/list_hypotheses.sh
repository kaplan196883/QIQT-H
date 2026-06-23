#!/usr/bin/env bash
# Lists all hypotheses (grouped by category) + data binders for each target theorem in
# scripts/list_hypotheses.lean.  Edit the `targets` list there to choose theorems.
#
# Usage:  bash scripts/list_hypotheses.sh
set -euo pipefail
cd "$(dirname "$0")/.."
exec ~/.elan/bin/lake env lean scripts/list_hypotheses.lean
