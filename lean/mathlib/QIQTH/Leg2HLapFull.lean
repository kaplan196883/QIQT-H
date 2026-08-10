/-
  Leg2HLapFull — J4-547.  The CURVED LEG-2 external `hLapFull` producer for the `a₁` two-jet capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## THE KEY QUESTION (J4-547) — ANSWERED: leg-2's `hLapFull` = J4-540's `MemLapFull` (cheap wire).

  The `a₁` two-jet curved capstones `A1R6FromLabelledCurved.a1_R6_from_labelled_curved` and
  `A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary` consume, as an EXTERNAL binder,
  the leg-2 (Duhamel-core) census member
      `hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)`
      `             (leviSeries (heatOp g gi (vanVleckGatedWitness …))) U`
      `             (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z)`.
  Direct type-comparison (confirmed by Sol, high): this is EXACTLY the `MemLapFull` object that J4-540's
  `DaLimLUCappedStep2.memLapFull_from_labelled_capped` produces for a GENERAL gate function `S`, taken at
  `S := constGate g gi hChr hK c`.  So the leg-2 `hLapFull` is NOT a distinct instance requiring the
  `CappedAdom2Audit.memLapFull_from_pairing_dominations` template — it is the SAME capped-census
  `MemLapFull` J4-540 already built, and the wiring is CHEAP.

  ## WHAT THIS BRICK ADDS.

  `curved_leg2_hLapFull` reproduces J4-540's `MemLapFull` producer at the constant-radius flow-ball gate
  `S := constGate g gi hChr hK c`, with ONE reduction over J4-540: the two gauge binders
  (`hgi : MemGaugeGi gi`, `hΓ : MemGaugeGamma g gi`) are DISCHARGED INTERNALLY from the four geometric
  inputs (`hK0`, `hframeK`, `hinvF`, `hdg0`) via `GlobalRawBoundFacade.gauge_from_geometry` — exactly the
  gauge move leg-1's capped capstone (`DaLimLUCappedStep3.hDaLimLU_from_labelled_capped`, J4-541) makes.
  For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`, `Ric(0) = (n−1)Kδ ≠ 0`) those four
  geometric inputs are the banked `CurvedRNCGaugeBundle.curvedRNC_geomGaugeBundle` members
  (`hg0`/`hinvF`/`hdg0`) at the singleton seed `{0}` — so the produced leg-2 `hLapFull` is directly the
  curved capstone's binder once the caller plugs `g := curvedRNCMetric K`, `gi := curvedRNCInv K`.
  `curved_leg2_hLapFull_curved_satisfiable` certifies the instance is genuinely curved (NOT secretly flat).

  ## WHAT IS CARRIED (honest residue — the SAME family leg-1 carries).

  The analytic dominations remain binders, verbatim from J4-540: the frozen-side interchange member
  `hInter`, the width-`wA` heat-operator Gaussian bound `hAdomHeat` (curved: J4-536
  `curvedRNC_heatOp_dom_pkg`), the per-`m` CAPPED second-`x`-derivative family `hAdom2cap` (curved:
  J4-537 `curvedRNC_witnessSecondXDeriv_dom_crude` capped via `hAdom2cap_grounded`), the Levi source
  envelope `hFdomW`/`hFzero`, the census measurabilities `hmeasLo`/`hmeasHi`/`hmeas2Lo`, the MATCHED-SLIVER
  HI-leg residual `hII_hi : MemAdjHi` (the honest `∫₀^{ε_m} τ⁻¹ = +∞` target — NOT from any pointwise
  domination), the √ε sliver amplitude bundle `D0`/`D1`/`hbnd`, and the atomic interchange carrier
  `hPd2conv`.  NONE is the conclusion; NONE is vacuous or `:= True`.

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Constructing the leg-2 `hLapFull` does
  NOT derive the coefficient.  Even with BOTH legs now capped-for-curved (leg 1 = J4-541
  `hDaLimLU_from_labelled_capped`; leg 2 = THIS via J4-540), the `a₁` capstone still carries the
  `MemAdjHi`/matched-sliver moment residuals (both legs), the convergence trio, and the Seeley–DeWitt
  geometric wiring (`transportCoeff`/`htr`).  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, no hypothesis equal to the conclusion, no existing file edited, nothing
  committed.  NOT `a₁ = R/6`. -/
import Mathlib
import QIQTH.DaLimLUCappedStep2
import QIQTH.GlobalRawBoundFacade
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.A1R6CoreAtGate

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open QIQTH.CappedAdom2Audit QIQTH.DaLimLUCapped QIQTH.DaLimLUCappedStep2
open QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Interval Topology BigOperators

namespace QIQTH.Leg2HLapFull

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-547 — `curved_leg2_hLapFull`.**  THE CURVED LEG-2 external `hLapFull` producer: the full
    capped-census `MemLapFull` binder at the constant-radius flow-ball gate `S := constGate g gi hChr hK c`
    — EXACTLY the leg-2 (Duhamel-core) `hLapFull` binder the curved `a₁` two-jet capstones consume.  It is
    J4-540's `memLapFull_from_labelled_capped` at `S := constGate g gi hChr hK c`, with the two gauge
    binders (`hgi`/`hΓ`) DISCHARGED INTERNALLY from the four geometric inputs (`hK0`/`hframeK`/`hinvF`/
    `hdg0`) via `gauge_from_geometry` — the same gauge move leg-1's J4-541 capstone makes.  Every analytic
    domination (`hInter`, `hAdomHeat`, per-`m` CAPPED `hAdom2cap`, `hFdomW`, `hFzero`, measurabilities,
    the matched-sliver residual `hII_hi : MemAdjHi`, the √ε sliver bundle, `hPd2conv`) is carried verbatim
    from J4-540 — none is the conclusion, none vacuous.  For `g = g^K` (`K < 0`) the four geometric inputs
    are the banked `curvedRNC_geomGaugeBundle` members at the singleton seed, so this stays non-vacuous off
    the flat metric.  NOT `a₁ = R/6`. -/
theorem curved_leg2_hLapFull (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (a b : ℝ)
    (U : Set ℝ) (T wA CA wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- gauge FROM GEOMETRY (replaces the `hgi`/`hΓ` binders of J4-540; discharged internally):
    (hK0 : (0 : Point n) ∈ K)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    (hdg0 : ∀ c d e, pd (fun y => g y c d) e (0 : Point n) = 0)
    -- the frozen-side interchange member (from the W2 family):
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    -- (strip legs) the uncapped heat-operator Gaussian bound (no `τ⁻¹` blow-up):
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    -- (LO leg) the PER-`m` CAPPED second-derivative family — NO uncapped whole-time `hAdom2`:
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z|
          ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdomW : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0 = 0)
    (hmeasLo : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hmeasHi : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (HI leg) ★ THE MATCHED-SLIVER RESIDUAL — CARRIED, NOT from any pointwise 2nd-derivative domination:
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    -- the √ε sliver amplitude bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z) := by
  -- gauge from geometry (identical move to leg-1's J4-541 capped capstone).
  obtain ⟨hgi, hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0
  -- thread into J4-540's capped `MemLapFull` producer at `S := constGate g gi hChr hK c`.
  exact memLapFull_from_labelled_capped g gi hChr hK (constGate g gi hChr hK c) a b U T wA CA wA2 wF CF CA2c
    hwA hCA hwA2 hCA2c hwF hCF hUpos hUT hgi hΓ hInter hAdomHeat hAdom2cap hFdomW hFzero
    hmeasLo hmeasHi hmeas2Lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv

/-- **★ J4-547 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The metric underlying the curved
    leg-2 `hLapFull` producer is genuinely curved: for `K ≠ 0` and `n ≥ 2` the diagonal metric-Hessian
    trace (`Ric(0)`) of `g^K = curvedRNCMetric K` is nonzero.  So when `curved_leg2_hLapFull` is
    instantiated at `g := curvedRNCMetric K` (with the four geometric inputs supplied by the banked
    `curvedRNC_geomGaugeBundle` at the singleton seed), the leg-2 `hLapFull` it produces is inhabited by a
    genuinely curved metric, NOT the flat `δ`.  Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curved_leg2_hLapFull_curved_satisfiable (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) K y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne K hK hn c

end QIQTH.Leg2HLapFull

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.Leg2HLapFull.curved_leg2_hLapFull
#print axioms QIQTH.Leg2HLapFull.curved_leg2_hLapFull_curved_satisfiable
