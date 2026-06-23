/-
# Undischarged-hypothesis checker

For each target theorem, lists its **Prop-hypotheses** (the labelled inputs — data/object binders are
skipped) and probes each one for *auto-dischargeability*: can it be proved from the OTHER binders in scope
plus the existing library?  If a heuristic tactic closes it, the hypothesis is REDUNDANT and should be
internalized (the `hC`/`hric_symm`/`hreg`/`conserv` pattern); otherwise it is a genuine assumed input.

Run:  ~/.elan/bin/lake env lean scripts/check_undischarged.lean   (or scripts/check_undischarged.sh)
Add targets to `targets` below.  Three verdicts per Prop-hypothesis:
  • `AUTO-DISCHARGEABLE ⇒ internalize` — SOUND: after removing this binder, the probe tactic actually CLOSED its
    goal from the remaining binders + library. It is redundant; supply it internally (the `hC`/`hric_symm` pattern).
  • `assumed (depended-on — not isolable)` — a LATER binder's type depends on this one, so it can't be cleared and
    tested; treated conservatively as assumed (typically genuine data, e.g. `mw`/`ff` feeding `hbridge`).
  • `assumed` — the probe did not close it. This is a ONE-WAY signal: it may still be dischargeable by a bespoke
    lemma the probe doesn't try, so `assumed` ⇏ irreducible — it flags what to look at, not a proof of irreducibility.
To make the probe smarter, extend `discharge_probe` with more closers / project lemmas.
-/
import QIQTH

open Lean Elab Command Meta

/-- Targets to audit. -/
def targets : List Name :=
  [ -- the whole QIQT→GR chain, abstract core → concrete capstones:
    ``QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms_complete,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_from_flux_complete,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_from_wedge_kms_raychaudhuri,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg_raychaudhuri,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg_lorentzian,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_freefield ]

/-- Heuristic discharge tactic: tries the cheap, sound closers + the project's curated discharge lemmas. -/
syntax "discharge_probe" : tactic
macro_rules
  | `(tactic| discharge_probe) =>
    `(tactic|
      first
        | assumption
        | fun_prop
        | positivity
        | (intros; first
             | rfl
             | assumption
             | positivity
             | fun_prop
             | (apply QIQTH.Curvature.christoffel_contDiff <;> assumption)
             | (apply QIQTH.Curvature.ricci_symm <;> assumption)))

/-- Try to discharge goal `g` (self-hypothesis already cleared); returns `true` iff fully closed. -/
def tryDischarge (g : MVarId) : TermElabM Bool := do
  try
    let rem ← Tactic.run g do
      Tactic.evalTactic (← `(tactic| discharge_probe))
    pure rem.isEmpty
  catch _ => pure false

run_cmd liftTermElabM do
  for tgt in targets do
    let info ← getConstInfo tgt
    forallTelescopeReducing info.type fun args _concl => do
      let mut propCount : Nat := 0
      let mut dischargeable : Nat := 0
      let mut lines : Array String := #[]
      for hi : i in [0:args.size] do
        let fv := args[i]!.fvarId!
        let ld ← fv.getDecl
        if (← isProp ld.type) then
          propCount := propCount + 1
          let tyStr := toString (← ppExpr ld.type)
          -- build the goal in-context, then DROP the binder itself so it cannot prove itself.
          -- If `clear` fails (a later binder's TYPE depends on this one — genuine data dependency),
          -- the probe is invalid, so report conservatively as assumed (not isolable).
          let mvar ← mkFreshExprMVar ld.type
          let clearedOpt ← (try pure (some (← mvar.mvarId!.clear fv)) catch _ => pure none)
          match clearedOpt with
          | none =>
              lines := lines.push s!"  [assumed (depended-on — not isolable)] {ld.userName} : {tyStr}"
          | some g =>
              let ok ← tryDischarge g
              if ok then dischargeable := dischargeable + 1
              let tag := if ok then "AUTO-DISCHARGEABLE ⇒ internalize" else "assumed"
              lines := lines.push s!"  [{tag}] {ld.userName} : {tyStr}"
      let header := s!"## {tgt}\n   Prop-hypotheses: {propCount}   auto-dischargeable: {dischargeable}   still assumed: {propCount - dischargeable}"
      logInfo (String.intercalate "\n" (header :: lines.toList))
