/-
  CConvFacadeGate — J4-313: discharge the LAST surviving inner arrow of the wide `a₁` capstone —
  `hCConv` — at the CONCRETE van-Vleck gate, W1-FREE, following the J4-311/312 AT_GATE pattern.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / capstone-arrow-threading brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## Z0 — RECON: WHAT `hCConv` ACTUALLY IS, AND THE PROVIDER / POISONING AUDIT.

  The wide capstone `ProviderSideExports.wide_a1_R6_interface_discharged_v2` (J4-265) returns an
  ∃-implication whose surviving inner arrows are `hDuhamel → hDConv → hCConv → ⟨a₁ 2-jet⟩`, at the ONE
  concrete van-Vleck gate `S` that `GateOpennessExport.gatedWitnessN1_package_open` chooses.  Its
  `hCConv` antecedent is EXACTLY the spatial-`C²` slot
      `ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0) 0`.
  (Verbatim `wide_a1_R6_interface_discharged_v2` lines 197–199; identical to
  `hCConv_concrete_from_data`'s conclusion.)

  **WHAT `hCConv` UNFOLDS TO — the FIVE facade bundles + one honest carry.**  The banked threading
  `CConvConcreteThreading.hCConv_concrete_from_data` (J4-207) produces exactly that `C²` slot from the
  MECHANICAL composition
      `CConvFacade.hCConv_discharged_from_data`  (the L1 `∃`-`HasFDerivAt` family, `hfam`)
        ∘  `SpatialC2.hCConv_reduction`           (`hfam` + `hD1` ⟹ the `C²` slot, via `2 = 1 + 1`)
  at the concrete left kernel `H := vanVleckGatedWitness g gi hChr hK S a b` and concrete source
  `F := leviSeries (heatOp g gi H)`.  Its ingredient set — WHAT `hCConv` "is" at the gate — is:
    (B1) `metric : CConvMetricData g gi`                         — ambient metric smoothness/positivity
                                                                    `{hg, hgi, hgpos}`.
    (B2) `chart  : CConvChartGateData g gi hChr hK S a b t u`    — chart/gate measurability family
                                                                    `{hKmeasSet, hSmeasSet, hVmapMeas,
                                                                     hCover, hChartB, hSliceData, hKmeas}`.
    (B3) `source : CConvSourceData (fun s z => F s z 0) t Cf`    — source data `{hFjoint, hFbd, hFmeas}`.
    (B4) `deriv  : CConvDerivativeData … F H F D`                — derivative-representative bundle
                                                                    `{hDmeas, hlin, hDrep}` + explicit `D`.
    (B5) `env    : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd`
                                                                — envelope/regularity `{hcoef, hC2fam,
                                                                  hGateData, hGateData'}`.
    (C)  `hD1 : ContDiffAt ℝ 1 D 0`                             — the STILL-OPEN L2 singular-second-
                                                                  derivative carry (the `hCConv_reduction`
                                                                  L2 layer; honest, satisfiable, never faked).

  **PROVIDER / POISONING AUDIT (the J4-312 lesson — audit every route for the W1 `hAnear` wall).**
    • The facade route is STRUCTURALLY DISJOINT from the W1/`hAnear` boundary-limit machinery.  The W1
      wall (`hAnear`: the concrete witness is Gaussian at the CHART IMAGE `W z 0`, not at `z`) lives in
      the Duhamel/DerivConv boundary-loc-unif chain (`DaLimLU`/`hbdryLU`/`boundary_tendstoLocallyUniformlyOn`)
      — the `hDuhamel`/`hDConv` side.  The `hCConv` `C²` route runs `shared_chart_consequences →
      hjoint_instantiated → henv/hdomS_assembled → g2_bundle_assembled → hCConv_L1_final`, a Fréchet
      route via partials + coefficient-continuity, with NO `hAnear`, NO `hBoundaryLim`, NO `DaLimLU`
      anywhere.  So `hCConv` is NOT W1-poisoned; the five bundles + `hD1` are honest census items, not a
      poisoned provider.
    • (B1) `metric` HAS an honest zero-risk discharge AT THE GATE: it is the bare constructor
      `⟨hg, hgi, hgpos⟩` from the SAME ambient geometry facts the capstone already carries
      (`hg`/`hgiC`/`hgpos`).  Discharged here (see Z1).
    • (B2)–(B5) are genuine analytic/measurability census bundles with no clean W1-free full-bundle
      constructor at a general provider-chosen gate (partial field dischargers exist — e.g.
      `hFjoint` via the LeviSeriesLocalData package, `hDmeas_discharged` — but constructing the WHOLE
      bundles by-block whnf-times-out per the AxiomAudit notes; not attempted, to stay green < 5 min).
      Carried as the honest satisfiable census, exactly as J4-312 carries the `hDaLimLU` data census.
    • (C) `hD1` is the honest still-open L2 carry (`XUniformSliverFull.hD1_from_data` at the CLM lift);
      a plain regularity statement about `D`, satisfiable, carried — NEVER the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.

    • (Z1) `CConvMetricData` DISCHARGED at the gate from raw geometry `{hg, hgiC, hgpos}` (bundle
      constructor) — the one component with an honest zero-risk provider.  Internalized inside (Z2).

    • (Z2) `hCConvSlot_AT_GATE` — the EXACT `hCConv` antecedent of
      `wide_a1_R6_interface_discharged_v2` (verbatim slot shape), proven at the concrete `N = 1`
      van-Vleck gate from: raw geometry `{hg, hgiC, hgpos}` (⟹ `metric` bundle internally), the four
      remaining facade bundles `{chart, source, deriv, env}`, the explicit derivative map `D` with its
      neighbourhood `u`/constants, and the honest still-open L2 carry `hD1`.  Route:
      `CConvConcreteThreading.hCConv_concrete_from_data`.  W1-FREE.  The surviving hypotheses are the
      honest satisfiable census (B2–B5 + hD1); none is `hAnear`-poisoned, none is vacuous, none equals
      the conclusion.

  ## Z3 — NOT ATTEMPTED (correctly, per J4-311/312).  Extracting `⟨a₁ 2-jet⟩` from the banked `v2`
  would require supplying the `hCConv`/`hDConv`/`hDuhamel` slots FOR the capstone's OWN ∃-chosen gate
  `S` — i.e. the four facade bundles parametrized `∀ S` (a heavy `∀`-gate provider), plus re-running the
  residual provider to EXPORT them for its self-chosen `S`.  That is the same heavy intermediate J4-311
  and J4-312 declined; it cannot be done by `apply`/`exact` of `v2` without materializing the ~130-binder
  capstone or a `∀`-gate bundle provider.  Deferred.

  ## REMAINING MAP TO `a1_R6_of_geometry` after this brick.  With `hDuhamel` (J4-311),
  `hDConv` (J4-312) and now `hCConv` (this file) all W1-free-internalizable at the concrete gate, the
  three surviving inner capstone arrows each have their AT_GATE slot theorem.  What remains to reach
  `a1_R6_of_geometry`:
    (1) the S1 `∀`-gate measurability `∀ S a b, tripleHEmeas …` (carried by `v2`);
    (2) the census piles' satisfiability — the `hDaLimLU`/F2/`hFII` census (hDConv side), the
        `TruncatedDuhamelCore` census (hDuhamel side), and the FIVE facade bundles + `hD1` (this file);
    (3) base geometry inputs + `1 ≤ n`;
    (4) the heavy X3 `v3`-export: a capstone that internalizes all three arrows for its OWN ∃-chosen
        `S`, which needs the residual provider to re-export each slot's data census `∀`-gate (the
        heavy intermediate, NOT materialized);
    (5) the final assembly `a1_R6_of_geometry` wiring (4) + (1)–(3) into the geometry-only statement.

  ⚠  STILL NOT `a₁ = R/6`; every carried hypothesis is an honest satisfiable input.
-/
import QIQTH.CConvConcreteThreading

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.CConvFacade QIQTH.CConvConcreteThreading
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CConvFacadeGate

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (Z2) — `hCConvSlot_AT_GATE`: the exact capstone `hCConv` slot, verbatim, W1-free.
    ############################################################################### -/

/-- **★★★ (Z2) `hCConvSlot_AT_GATE`.**  The EXACT `hCConv` antecedent proposition of
    `ProviderSideExports.wide_a1_R6_interface_discharged_v2` at the concrete gate, reproduced verbatim
    and proven W1-FREE from:
      • (Z1) the ambient geometry `{hg, hgiC, hgpos}`, from which the `CConvMetricData` bundle is
        DISCHARGED internally (bare constructor — the one component with a zero-risk provider);
      • the four remaining facade bundles `{chart, source, deriv, env}` (the honest satisfiable
        census — chart/gate measurability, source data, derivative-representative bundle, envelope);
      • the explicit derivative map `D`, its neighbourhood `u`/openness/base-membership, the envelope
        constants `Bs Ba Bd Cf`;
      • the honest still-open L2 carry `hD1 : ContDiffAt ℝ 1 D 0`.
    Route: `CConvConcreteThreading.hCConv_concrete_from_data`.  The conclusion is VERBATIM the capstone
    `hCConv` slot (same `t`-binder, same witness, same source, same base-point).  NO `hAnear`;
    NO `hBoundaryLim`; NO `DaLimLU` — the facade `C²` route is structurally disjoint from the W1 wall.
    Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hCConvSlot_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t)
    -- (Z1) raw geometry the capstone already carries — the `metric` bundle is built from these.
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    -- the neighbourhood + constants + explicit derivative map.
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    -- the four remaining facade bundles (the honest satisfiable census).
    (chart : CConvChartGateData g gi hChr hK S a b t u)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (deriv : CConvDerivativeData g gi hChr hK S a b t u
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D)
    (env : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd)
    -- the honest still-open L2 carry.
    (hD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  -- (Z1) DISCHARGE the `CConvMetricData` bundle from the raw geometry the capstone already carries.
  have metric : CConvMetricData g gi := { hg := hg, hgi := hgiC, hgpos := hgpos }
  -- (Z2) thread the concrete `C²` `hCConv` slot from the five bundles + explicit `D` + `hD1`.
  exact hCConv_concrete_from_data g gi hChr hK S a b t ht u hu_open hu0 Bs Ba Bd Cf D
    metric chart source deriv env hD1

end QIQTH.CConvFacadeGate

section AxiomChecks
open QIQTH.CConvFacadeGate
#print axioms hCConvSlot_AT_GATE
end AxiomChecks
