/-
  GrandAssemblyRecon — J4-222: THE GRAND ASSEMBLY RECON.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the
  RECON + ASSEMBLY brick: it TRACES the tonight-banked walls into the capstone and composes the
  deepest wall-free capstone that builds today — `a1_R6_assembled` — by discharging, INSIDE the
  capstone, every slot the tonight bricks can internally supply.  No new analysis; only compositions.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## (1) THE COMPOSITION TRACE — shape-match verdicts.

  (a) `ETailRateBound.hDaLimLU_from_data`  →  the `hDaLimLU` frontier slot / the `core` `hDaLim` slot.
      · `hDaLimLU_from_data` CONCLUDES `DaLimLUWallRecon.DaLimLUGoal g gi H F U`, which is the ABBREV
          `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
             (fun u => laplaceBeltrami g gi (heatConv H F u · 0) 0 + heatConv (heatOp g gi H) F u 0 0)
             atTop U`.
      · `CapstoneAssembly.a1_R6_of_geometry_and_frontier` EXPOSES the frontier slot
          `hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc Wit (leviSeries (heatOp g gi Wit)) m u)
             DaLim atTop U`   with `DaLim : ℝ → ℝ` a FREE binder.
      · VERDICT — DIRECT MATCH.  Instantiate `H := Wit`, `F := leviSeries (heatOp g gi Wit)` and
          `DaLim := (fun u => laplaceBeltrami … + heatConv …)`; then `DaLimLUGoal` is DEFEQ to the
          frontier slot.  Windows: `hDaLimLU_from_data` wants `U` open (`hUopen`), `aT ≤ u ≤ T`
          (`hUlb`/`hUT`); the capstone carries `hUopen`, `hUfloor` (→ `aT`, `hUlb`) and `hUT` — all
          present.  The gauge binders `hgi : MemGaugeGi gi` / `hΓ : MemGaugeGamma g gi` are ABBREVS
          for exactly the capstone's RNC facts `gi 0 = δ` / `Γ 0 = 0`, so they thread verbatim.
          This is the HEADLINE: it turns the SOLE surviving capstone WALL (`hDaLimLU`) into DATA.
      · The `core` bundle's `hDaLim` slot (inside `truncatedDuhamelCore_of_daLim`) is the POINTWISE
          `Tendsto (fun m => DaTrunc Wit (leviSeries …) m t) atTop (𝓝 (laplaceBeltrami … + heatConv …))`
          at the single `t`.  It is the loc-unif goal EVALUATED at `t`, obtained by
          `TendstoLocallyUniformlyOn.tendsto_at htU`.  Build-checked below as
          `daLimLU_reduces_to_pointwise` (F general; specialize `F := leviSeries (heatOp g gi Wit)`).
          NOTE the capstone consumes `hDaLimLU` and `core` at SEPARATE slots (frontier `hDConv` block
          vs. the Duhamel identity), so discharging `hDaLimLU` does NOT collapse `core`.

  (b) `ChartJetHessianMixed.tripleHEmeas_concrete`  →  the `hEmeas` slots.
      · `tripleHEmeas_concrete` at `Wit := vanVleckGatedWitness g gi hChr hK S a b` CONCLUDES
          `HEmeasBorelAudit.tripleHEmeas g gi Wit`, which is DEFINITIONALLY
          `StronglyMeasurable (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2)`.
      · `TruncatedDuhamelData.interchangeData_of_banked` and `.endpointData_of_banked` each take the
          SINGLE slot `hEmeas : StronglyMeasurable (fun q => heatOp g gi Wit q.1 q.2.1 q.2.2)`.
      · VERDICT — DEFINITIONAL MATCH, SAME concrete witness.  Build-checked below as
          `tripleHEmeas_is_hEmeas_slot` (`Iff.rfl`).  So `tripleHEmeas_concrete` feeds BOTH bundle
          builders' `hEmeas` at `vanVleckGatedWitness g gi hChr hK S a b`.

  (c) STRONGEST base:  v7 (`HD1CLMLift.a1_R6_of_residue_inf_v7`, flat, `n` scalar `hgD1`) vs.
      `geometry_and_frontier` (bundles + expanded `hDConv` residue block ending in `hDaLimLU`).
      · The two improvements are ORTHOGONAL:
          – v7 (built on v5) replaces the CLM `hD1 : ContDiffAt ℝ 1 Dmap 0` binder by the SCALAR
            family `hgD1 i` and re-derives the CLM lift via `hD1_concrete_from_scalar`; but v5 keeps
            `hDConv` as a black-box `DifferentiableAt` and the four raw Levi/Duhamel slots.
          – `geometry_and_frontier` (built on v6) EXPANDS `hDConv` into the residue block ending in the
            loc-unif WALL `hDaLimLU`, and RE-GROUPS the four Levi slots into the three
            `TruncatedDuhamelData` bundles; but it keeps `hD1` CLM.
      · BOTH combine: build on `geometry_and_frontier` (v6: exposes `hDaLimLU`), then additionally
          apply v7's `hD1_concrete_from_scalar` in place.  That is `a1_R6_assembled` below.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## (2) LEAF ENUMERATION of `a1_R6_assembled` (the maximal composition).  Tags:
       GEOMETRY = RNC/Ricci input the theorem is ABOUT (load-bearing, never discharged);
       CONCRETE-DISCHARGEABLE (CD) = a banked lemma at the concrete witness exists (named);
       INSTANTIATION (INST) = a routine brick at the concrete witness (named);
       DATA = satisfiable analytic fact (no single-shot re-plumb);
       GENUINE-GAP = real open mathematical content.

    LEAF                                     TAG        PROVIDER / BRICK
    ─────────────────────────────────────────────────────────────────────────────────────────────
    g,gi,Ric,t,ht,C,hCnn,hChr,K,hK,S,a,b     GEOMETRY   —
      ha,hab,hK0,hS0,hg,hg0,hgi,hΓ,hdg0       GEOMETRY   RNC gauge (hgi = MemGaugeGi, hΓ = MemGaugeGamma)
    htr  (Σ∂∂g = -(2/3)Ric)                   GEOMETRY   Ricci source (banked: L3 source, VanVleckRadial)
    hsrc (transport-coeff C^∞)                GEOMETRY   transport smoothness
    endpoint : EndpointData                   CD         `endpointData_of_banked` (hEmeas ← tripleHEmeas_concrete;
                                                          hEbound ← EboundWiringHD1.hEboundW_from_geometry)
    core     : TruncatedDuhamelCore           CD/DATA    `truncatedDuhamelCore_of_daLim` — residue = 3 pointwise
                                                          limits {hBoundaryLim, hDaLim, hDerivConv};
                                                          hDaLim ← hDaLimLU_from_data via `.tendsto_at htU`;
                                                          hBoundaryLim ← BoundaryAssembly (loc-unif → tendsto_at);
                                                          hDerivConv ← hDerivLU_discharge (loc-unif → tendsto_at)
    inter    : InterchangeData                CD         `interchangeData_of_banked` (hEmeas ← tripleHEmeas_concrete)
    hCH  (ContDiffAt 2 witness)               DATA       banked 2-jet regularity family
    uu,hu_open,hu0,Bs,Ba,Bd,Cf,Dmap           DATA       CConv facade scaffolding
    metric/chart/source/derivData/env         DATA       `CConvFacade.hCConv_discharged_from_data`
    hgD1 i (n scalar C¹ jets)                 CD         `XUniformSliverFull.hD1_from_data` at gcoef i
                                                          (→ hD1 via `hD1_concrete_from_scalar`, this file)
    T,hT,U,hUopen,htU,hUpos,hUT               DATA       window / nbhd
    r₀,τ₀,…,hAnear,…,hu₁bdd                    DATA       near-diagonal parametrix (gaussDdim·(u₀+τu₁))
    A₀,A₁,C_L,hA*,hAdom,hAzero,hBdom          DATA       Gaussian dominations
    hBcont,hAmeas,hBmeas,hu₀meas,hu₁meas       DATA       continuity / measurability
    hMeasFII,hUfloor,hInnerCont               DATA       base s-measurability, floor, inner continuity
    nb,hnb,hFmeas,hFint,hF'meas,boundD,        DATA       C3ε under-∫ engine
      hbdd,hbound,hpardiff
    L,hLnn,hCross                              DATA       cross-Lipschitz mixed-2nd-difference
    ── the tonight WALL→DATA carries (from `hDaLimLU_from_data`) ──
    pdpdH                                      DATA       the 2nd-field-pd representative
    hInterchange : MemInterchange              CD         `SecondOrderInterchange.hInterchange_discharge`
    hLapFull     : MemLapFull                  CD         `InterchangeThreading.hLapFull_of_lims`
    hII_lo,hII_hi : MemAdjLo/MemAdjHi          DATA       strip integrabilities of pdpdH·F
    D0,D1,hD0,hD1nn,hbnd (√ε sliver)           CD         `witness_sliver2_concrete` amplitudes (banked)
    E₀,E₁,hE₀,hE₁,hEdom (residual E-domination) DATA      residual-operator Gaussian envelope
    hEzeroE (heatOp = 0, τ≤0)                  DATA       support-in-positive-time
    hFzero (leviSeries = 0, s≤0)               DATA       support-in-positive-time
    hIlo,hIhi (strip integrabilities)          DATA       inner-slice interval integrability
    hEcomb : MemECombine                       CD         `TruncatedDuhamel.hE_combination`

    GENUINE-GAP:  NONE at the a₁ = R/6 CONDITIONAL level.  The residue is entirely GEOMETRY +
      CONCRETE-DISCHARGEABLE + DATA.  The one PHYSICS input carried unconditionally is `htr`
      (the L3 Ricci source Σ∂∂g = -(2/3)Ric) which is itself banked in the constant-curvature /
      VanVleckRadial thread; it is GEOMETRY here (the coordinate normalization the theorem is ABOUT).
      The `pdpdH → Ric` geometric wiring is NOT open at this level: `htr` already delivers the Ricci
      trace, and `pdpdH` enters only as the interchange representative (bounded by the √ε sliver).

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## (3) ★ `a1_R6_assembled` — the deepest wall-free capstone that builds today.
     Base = `a1_R6_of_geometry_and_frontier` (v6: bundles + expanded `hDConv` residue), with:
       · `hDaLimLU`  DISCHARGED internally by `ETailRateBound.hDaLimLU_from_data` (WALL → DATA);
       · `hD1` (CLM) DISCHARGED internally by `HD1CLMLift.hD1_concrete_from_scalar` from `hgD1` (v7 route).
     Net: the ONLY named WALL (`hDaLimLU`) is gone, and the CLM regularity black box is gone; the
     surface is now GEOMETRY + banked bundles + satisfiable DATA.  Strictly smaller (wall-free) than
     both v7 (still black-box `hDConv`) and `geometry_and_frontier` (still has the `hDaLimLU` WALL).
     `endpoint`/`core`/`inter` kept as bundle inputs — per the CapstoneAssembly REJECTED-note,
     unbundling their `{hEbound(∀τ>0), hEzero, hEmeas}` ENLARGES the surface (a documented size
     choice, not a shape block); shape composition of `hEmeas` IS build-checked below.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## (4) THE ORDERED INSTANTIATION LADDER to the final `a₁ = R/6` theorem.
     Each rung = one concrete brick at `Wit := vanVleckGatedWitness g gi hChr hK S a b`.  Sizes honest.

     R1  [SMALL]  hEmeas ← `ChartJetHessianMixed.tripleHEmeas_concrete` (banked) — feeds
                  endpoint/inter; its own carries = measurable-supplier existentials (hcarTau/hcarField/
                  hcarField2/hgi/hchr/hKmeasSet), continuity-free.  Unbundle endpoint/inter to expose it.
     R2  [SMALL]  hInterchange/hLapFull/hEcomb ← the banked per-u dischargers (already named CD).
     R3  [MED]    core's hBoundaryLim/hDerivConv ← BoundaryAssembly loc-unif + hDerivLU_discharge, each
                  reduced to the pointwise-at-t via `.tendsto_at htU`; then `truncatedDuhamelCore_of_daLim`.
     R4  [MED]    the CConv facade bundles ← `CConvFacade.hCConv_discharged_from_data` at the concrete
                  chart/metric/source/deriv/env data.
     R5  [MED]    hgD1 i ← `XUniformSliverFull.hD1_from_data` at gcoef i (its sliver/continuity carries).
     R6  [MED]    the DATA dominations (hAdom/hEdom/hBdom/hAzero/hEzeroE/hFzero) + integrabilities
                  ← the Gaussian-envelope banked bounds at the gated witness.
     R7  [SMALL]  htr ← the L3 Ricci source (banked, constant-curvature thread) — or keep as the ONE
                  labelled GEOMETRY input (option (b), per the heat-kernel-gap plan).
     ⇒ FINAL  `a1_R6_of_geometry` (all-concrete): `heatOp … = 0 ∧ trueHeatKernel …` with the R/6
              coefficient, every leaf a named concrete brick.  Because hEmeas no longer needs a
              q-regularity WALL (S1 continuity-free, tripleHEmeas_concrete), the OLD
              `…_of_geometry_and_heatOp_qregularity` shape is superseded: the honest final shape is
              `a1_R6_of_geometry` with NO q-regularity hypothesis.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CapstoneAssembly
import QIQTH.HD1CLMLift
import QIQTH.ETailRateBound
import QIQTH.HEmeasBorelAudit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open QIQTH.HDConvThreading QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound QIQTH.HD1CLMLift
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.GrandAssemblyRecon

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### TRACE BUILD-CHECKS — (a) loc-unif → pointwise, (b) tripleHEmeas → hEmeas.
    ############################################################################### -/

/-- **(a) BUILD-CHECK.**  The `DaLimLUGoal` loc-uniform limit (the conclusion of
    `ETailRateBound.hDaLimLU_from_data`) reduces, at each `t ∈ U`, to the POINTWISE `Tendsto` in the
    EXACT `hDaLim` slot shape of `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim` — via
    `TendstoLocallyUniformlyOn.tendsto_at`.  Specialize `F := leviSeries (heatOp g gi Wit)` to hit the
    `core` bundle's `hDaLim` verbatim.  NOT `a₁ = R/6`. -/
theorem daLimLU_reduces_to_pointwise (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (t : ℝ) (htU : t ∈ U)
    (h : QIQTH.DaLimLUWallRecon.DaLimLUGoal g gi H F U) :
    Filter.Tendsto (fun m => DaTrunc H F m t) Filter.atTop
      (𝓝 (laplaceBeltrami g gi (fun x => heatConv H F t x 0) 0
            + heatConv (heatOp g gi H) F t 0 0)) :=
  h.tendsto_at htU

/-- **(b) BUILD-CHECK.**  `HEmeasBorelAudit.tripleHEmeas g gi Wit` is DEFINITIONALLY the single
    `hEmeas` slot of `interchangeData_of_banked` / `endpointData_of_banked`.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_is_hEmeas_slot (g gi : Point n → Fin n → Fin n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) :
    QIQTH.HEmeasBorelAudit.tripleHEmeas g gi Wit ↔
      StronglyMeasurable (fun q : ℝ × Point n × Point n => heatOp g gi Wit q.1 q.2.1 q.2.2) :=
  Iff.rfl

/-! ###############################################################################
    ### ★ `a1_R6_assembled` — the deepest wall-free capstone that builds today.
    ############################################################################### -/

/-- **★★★ J4-222 — `a1_R6_assembled`.**  `CapstoneAssembly.a1_R6_of_geometry_and_frontier` with the
    two tonight discharges folded IN:
      · the SOLE WALL `hDaLimLU` is discharged internally by `ETailRateBound.hDaLimLU_from_data`
        (fixing `DaLim` to the `DaLimLUGoal` limit; windows from `hUfloor`/`hUT`; gauge from
        `hgi`/`hΓ` = `MemGaugeGi`/`MemGaugeGamma`);
      · the CLM `hD1` slot is discharged internally by `HD1CLMLift.hD1_concrete_from_scalar` from the
        `n` scalar jets `hgD1` (the v7 route).
    Same conclusion as v6/geometry_and_frontier; strictly WALL-FREE surface.  Pure composition — no
    new analysis.  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    -- (i) RNC / Ricci geometric data (flat):
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- (iii) Levi/Duhamel interface as the three `TruncatedDuhamelData` bundles:
    (endpoint : EndpointData g gi (vanVleckGatedWitness g gi hChr hK S a b) t C)
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
    (inter : InterchangeData g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- (ii) the CConv `C²` facade bundles (v6, verbatim):
    (uu : Set (Point n)) (hu_open : IsOpen uu) (hu0 : (0 : Point n) ∈ uu)
    (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t uu)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (derivData : CConvDerivativeData g gi hChr hK S a b t uu
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      Dmap)
    (env : CConvEnvelopeData g gi hChr hK S a b t uu Bs Ba Bd)
    -- ★ v7 route: the CLM `hD1` REPLACED by the per-coordinate SCALAR jets.
    (hgD1 : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n))) (0 : Point n))
    -- (v) the `hDConv` analytic residue block (v6 residue, verbatim — MINUS `DaLim`/`hDaLimLU`):
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a')
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ★ NEW: the `hDaLimLU_from_data` DATA carries (the WALL, turned into data).
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1nn : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzeroE : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) ) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- WALL → DATA: extract the `aT` window from `hUfloor` (kept intact for the capstone).
  obtain ⟨aT, haT, hUlb⟩ := id hUfloor
  -- discharge the loc-unif WALL from pure data.
  have hDaLimLU := QIQTH.ETailRateBound.hDaLimLU_from_data g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    T U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1nn hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT
    hEdom hEzeroE hBdom hFzero hIlo hIhi hEcomb
  -- discharge the CLM `hD1` from the per-coordinate scalar jets (v7 route).
  have hD1 : ContDiffAt ℝ 1 Dmap (0 : Point n) :=
    QIQTH.HD1CLMLift.hD1_concrete_from_scalar g gi hChr hK S a b t uu hu_open hu0
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      Dmap derivData hgD1
  -- feed `geometry_and_frontier` with the two slots discharged; everything else verbatim.
  exact QIQTH.CapstoneAssembly.a1_R6_of_geometry_and_frontier
    g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc endpoint core inter hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross _ hDaLimLU

end QIQTH.GrandAssemblyRecon

section AxiomChecks
open QIQTH.GrandAssemblyRecon
#print axioms daLimLU_reduces_to_pointwise
#print axioms tripleHEmeas_is_hEmeas_slot
#print axioms a1_R6_assembled
end AxiomChecks
