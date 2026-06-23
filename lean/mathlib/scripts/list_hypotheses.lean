/-
# Hypothesis lister for the QIQT→GR chain

For each target theorem, separates DATA binders (the objects: metric, field, modes, …) from the actual
HYPOTHESES (Props), and groups the hypotheses by category so the remaining assumption surface is legible.
Categories are a curated name→label map (the chain's hypothesis names are stable); anything unrecognised
falls under `other` (update `categorize` if a new hypothesis appears).

Run:  ~/.elan/bin/lake env lean scripts/list_hypotheses.lean   (or scripts/list_hypotheses.sh)
-/
import QIQTH

open Lean Elab Command Meta

def targets : List Name :=
  [ ``QIQTH.WedgeKMSToGR.qiqt_gr_freefield,
    ``QIQTH.WedgeKMSToGR.qiqt_gr_explicit_kg,
    ``QIQTH.QiqtToGR.qiqt_bekenstein_gives_gr ]

/-- Curated category for a hypothesis, keyed by its binder name. -/
def categorize (n : String) : String :=
  if n == "hKG" then "PHYSICS — matter EOM (Klein–Gordon)"
  else if n == "hbound" || n == "hsat" || n == "hDnn" || n == "hD0" then
    "PHYSICS — Clausius / area-saturation law (the thermodynamic floor)"
  else if n == "hFocus" then "PHYSICS — Raychaudhuri focusing (ad = R_kk)"
  else if n == "hTkk" || n == "hbridge" then "PHYSICS — localization map ξ_{x,v} (Gap 2, dynamical realization)"
  else if n == "hflux" || n == "hKMS" || n == "hFlux" then "PHYSICS — wedge-KMS / boost-flux (modular input)"
  else if n == "conserv" then "CONSISTENCY — stress-energy conservation ∇·(aT)=0"
  else if n == "hS" || n == "hK" || n == "hA" then "SETUP — per-generator derivative existence"
  else if n == "hVC" || n == "hgeo" || n == "hequil" || n == "hVval" || n == "harea" then
    "SETUP — null-congruence kinematics (Raychaudhuri form)"
  else if n == "hmw" || n == "hf2" || n == "hf_int" || n == "hF0_int" || n == "hfd"
          || n == "hf'_meas" || n == "hB" then "REGULARITY — localization mode (soft analytic data)"
  else if n == "hreg" then "REGULARITY — curvature/source smoothness (hreg)"
  else if n == "hsymm" || n == "hsymm_gi" || n == "hinv" || n == "hCg" || n == "hCgi"
          || n == "hPP" || n == "hPP'" || n == "hcong" || n == "hT_symm"
          || n == "hbar0" || n == "heta" || n == "ha" || n == "hφ" then
    "REGULARITY/BACKGROUND — metric, frame, smoothness, constants"
  else "OTHER (uncategorised — update categorize)"

/-- Fixed display order for categories. -/
def catOrder : List String :=
  [ "PHYSICS — matter EOM (Klein–Gordon)",
    "PHYSICS — Clausius / area-saturation law (the thermodynamic floor)",
    "PHYSICS — Raychaudhuri focusing (ad = R_kk)",
    "PHYSICS — localization map ξ_{x,v} (Gap 2, dynamical realization)",
    "PHYSICS — wedge-KMS / boost-flux (modular input)",
    "CONSISTENCY — stress-energy conservation ∇·(aT)=0",
    "SETUP — per-generator derivative existence",
    "SETUP — null-congruence kinematics (Raychaudhuri form)",
    "REGULARITY — localization mode (soft analytic data)",
    "REGULARITY — curvature/source smoothness (hreg)",
    "REGULARITY/BACKGROUND — metric, frame, smoothness, constants",
    "OTHER (uncategorised — update categorize)" ]

run_cmd liftTermElabM do
  for tgt in targets do
    let info ← getConstInfo tgt
    forallTelescopeReducing info.type fun args concl => do
      let mut dataNames : Array String := #[]
      -- (category, name, type) for each Prop hypothesis
      let mut hyps : Array (String × String × String) := #[]
      for h : i in [0:args.size] do
        let ld ← args[i]!.fvarId!.getDecl
        let nm := toString ld.userName
        if (← isProp ld.type) then
          hyps := hyps.push (categorize nm, nm, toString (← ppExpr ld.type))
        else
          dataNames := dataNames.push nm
      let mut out : Array String := #[]
      out := out.push s!"\n══════════════════════════════════════════════════════════════════════"
      out := out.push s!"## {tgt}"
      out := out.push s!"   {dataNames.size} data binders · {hyps.size} hypotheses"
      let dataStr := String.intercalate ", " dataNames.toList
      out := out.push s!"   DATA: {dataStr}"
      for cat in catOrder do
        let inCat := hyps.toList.filter (fun (c, _, _) => c == cat)
        if !inCat.isEmpty then
          out := out.push s!"\n  ▸ {cat}  ({inCat.length})"
          for (_, nm, ty) in inCat do
            out := out.push s!"      • {nm} : {ty}"
      logInfo (String.intercalate "\n" out.toList)
