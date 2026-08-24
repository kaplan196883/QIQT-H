/-
QIQTH/LocalizedBankedData.lean

  Phase 2 of the capstone-signature redesign plan
  (`docs/qg_roadmap/CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`, J4-1168, Sol's 38th consult), per the phase
  table's Phase 2 line: "Localize the two `_of_banked` consumers
  (`endpointData_of_banked_on_horizon`, `interchangeData_of_banked_on_horizon`) → D3/D4 green.
  STOP here if D4 fails genuinely".

  ══════════════════════════════════════════════════════════════════════════════════════════════
  D4 — Sol's flagged PRINCIPAL RISK, resolved precisely.

  The literal question: "does `InterchangeData` genuinely need unbounded-τ estimates internally, or
  only up to `t`?"  Structural audit of the actual definitions (NOT assumed, read line-by-line):

    • `EndpointData.hIntegrable`/`InterchangeData.hSeries` (`TruncatedDuhamelData.lean`) both demand
      `IterConvIntegrableW E 2 0 C`, whose OWN definition (`ParametrixHEboundWiring.lean:155`) is
      `∀ (t : ℝ), 0 < t → …` — i.e. it is *itself* a claim about EVERY outer time, not merely the one
      horizon a caller cares about.
    • The concrete producer used by the EXISTING (non-localized) `endpointData_of_banked` is
      `iterConvIntegrableW_of_bound_baseMeas` (`IterEMeasurable.lean:200`), which demands a *single
      FIXED-C* bound valid at *every* `τ > 0` (no `τ ≤ t'` cap at all).
    • So the answer to D4, taken literally, is YES: `IterConvIntegrableW` (hence both `EndpointData`
      and `InterchangeData`, which is built from it via the `LeviSeriesLocalData` package's `hInt`
      field) genuinely needs information about the residual's behaviour at arbitrarily large τ, not
      just `τ ≤ t`.  Sol's fear is structurally REAL — this is not a false alarm.

  BUT — and this is the finding that resolves the risk favourably — that "arbitrarily large τ" demand
  is ALREADY MET, for free, by data the `gatedWitnessN1_package_open` residual (J4-108/197) already
  produces.  Its `hbound` field is
      `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp g gi H τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`
  — quantified over EVERY `t' : ℝ`, not one fixed horizon.  This is *exactly* the "every-ceiling bound
  family" shape (`hlocal`/`hglobal` in `GatedWitnessMeas.iterConvIntegrableW_of_locally_bound_baseMeas`
  and `LeviSeriesLocalData.leviSeriesLocalData_of_windowBound`) that those two ALREADY-BANKED producers
  (J4-109, J4-205/206) consume to build the all-outer-time `IterConvIntegrableW`/`hInter` WITHOUT ever
  needing a single τ-uniform constant.  So: **no new analysis is required** — D4's local siblings below
  are pure re-assembly of already-banked machinery, feeding it the package's `hbound` reshaped (via one
  `fun T hT => ⟨C*(1+T), …, hbound T …⟩` closure, not a new proof) as the every-ceiling family.  The
  Phase-1 lead (`InterchangeLocalRebase.lean`/`IterEMeasurable.lean`) DOES pan out, with the honest
  correction that it does not eliminate the unbounded-τ *structural* need (which is real) — it shows
  that need is already discharged by the package's OWN `hbound`, not by any new estimate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE (Canaries D3 — EndpointLocal, D4 — InterchangeLocal, BOTH GREEN).

    • `endpointData_of_banked_on_horizon` — `EndpointData g gi Wit t (C*(1+t))` from the package's raw
      `hbound` (every-ceiling family, no `τ ≤ t` restriction baked in at the call site) + `hEzero` +
      `hEmeas`.  `hEbound` via Phase 1's `package_bound_on_horizon`; `hIntegrable` via the ALREADY-BANKED
      `GatedWitnessMeas.iterConvIntegrableW_of_locally_bound_baseMeas` (J4-109), fed `hbound` reshaped
      as the every-ceiling family.
    • `interchangeData_of_banked_on_horizon` — `InterchangeData g gi Wit t` the same way, via the
      ALREADY-BANKED `InterchangeLocalRebase.hInter_from_local_data` (J4-206).

  Every hypothesis of both theorems is EXACTLY the shape `gatedWitnessN1_package_open`/
  `gatedWitnessN1_horizon_bound` (`PackageHorizonBound.lean`, J4-1170) already produces — `hbound`,
  `hEzero`, `hEmeas` — so these are the genuine local siblings of `endpointData_of_banked`/
  `interchangeData_of_banked` (`TruncatedDuhamelData.lean`) the plan calls for, at the SAME output
  types (`EndpointData`, `InterchangeData`) the live capstone's proof body consumes.

  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  This file is pure re-plumbing: it introduces no new analytic estimate, only reassembles J4-109/109/
  205/206/1170's already-banked machinery at the shape D3/D4 need.
-/
import Mathlib
import QIQTH.PackageHorizonBound
import QIQTH.TruncatedDuhamelData
import QIQTH.InterchangeLocalRebase
import QIQTH.GatedWitnessMeas

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.TruncatedDuhamelData QIQTH.InterchangeLocalRebase QIQTH.PackageHorizonBound
open QIQTH.LeviSeriesLocalData
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.LocalizedBankedData

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### D3 — `endpointData_of_banked_on_horizon`. -/

/-- **★ J4-1171 (Phase 2, Canary D3 — EndpointLocal).**  The local sibling of
    `TruncatedDuhamelData.endpointData_of_banked`: builds `EndpointData g gi Wit t (C*(1+t))` from the
    package-shaped every-ceiling bound family `hbound` (no externally-fixed τ-uniform constant), plus
    `hEzero`/`hEmeas`.  `hEbound` is `package_bound_on_horizon` (Phase 1, D1) specialized to `t`;
    `hIntegrable` is the already-banked `iterConvIntegrableW_of_locally_bound_baseMeas` (J4-109) fed
    `hbound` reshaped as its `hlocal` family — no new analytic content, pure reassembly. -/
theorem endpointData_of_banked_on_horizon (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi Wit τ p q| ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hEmeas : StronglyMeasurable
        (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)) :
    EndpointData g gi Wit t (C * (1 + t)) where
  hEbound := package_bound_on_horizon g gi Wit C t hbound
  hIntegrable :=
    iterConvIntegrableW_of_locally_bound_baseMeas (heatOp g gi Wit) (C * (1 + t)) hEzero hEmeas
      (fun T hT => ⟨C * (1 + T), by positivity, fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩)

/-! ### D4 — `interchangeData_of_banked_on_horizon` (the plan's flagged principal risk). -/

/-- **★★ J4-1171 (Phase 2, Canary D4 — InterchangeLocal, the plan's flagged PRINCIPAL RISK).**  The
    local sibling of `TruncatedDuhamelData.interchangeData_of_banked`: builds
    `InterchangeData g gi Wit t` from the SAME package-shaped `hbound`/`hEzero`/`hEmeas` (plus `ht`),
    via the already-banked `InterchangeLocalRebase.hInter_from_local_data` (J4-206) at window `T := t`.
    Resolves D4: `InterchangeData` DOES structurally need an every-ceiling (unbounded-τ) family — but
    the package's own `hbound` already supplies it (see file header), so no new analytic estimate is
    needed here. -/
theorem interchangeData_of_banked_on_horizon (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t C : ℝ) (hC : 0 ≤ C) (ht : 0 < t)
    (hbound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi Wit τ p q| ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi Wit τ p q = 0)
    (hEmeas : StronglyMeasurable
        (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)) :
    InterchangeData g gi Wit t where
  hSeries :=
    hInter_from_local_data (heatOp g gi Wit) (C * (1 + t)) t (by positivity) ht
      (package_bound_on_horizon g gi Wit C t hbound) hEzero hEmeas
      (fun T hT => ⟨C * (1 + T), by positivity, fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩)
      t ht le_rfl 0 0

end QIQTH.LocalizedBankedData

section AxiomChecks
open QIQTH.LocalizedBankedData
#print axioms endpointData_of_banked_on_horizon
#print axioms interchangeData_of_banked_on_horizon
end AxiomChecks
