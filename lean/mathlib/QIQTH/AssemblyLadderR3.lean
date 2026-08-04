/-
  AssemblyLadderR3 — J4-224: LADDER BRICK R3 — the `core` UNBUNDLE.

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  RE-PLUMBING brick on top of `AssemblyLadderR1R2.a1_R6_assembled_v2` (J4-223): it UNBUNDLES the last
  opaque `: Prop` data structure in that capstone's surface — `core : TruncatedDuhamelCore` — building
  it INTERNALLY from its deeper 3-limit residue via
  `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim`.  No new analysis; only compositions.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R3 — `a1_R6_assembled_v3`.  DONE (builds; std-3).
     `a1_R6_assembled_v2` with the bundle binder
        `core : TruncatedDuhamelCore g gi Wit t`
     REPLACED by the deeper 3-pointwise-limit residue those bundles are built from, via
        `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim`,
     whose residue is `{hBoundaryLim, hDaLim, hDerivConv}`.  TWO of the three limits are discharged
     INTERNALLY from data ALREADY carried by v2 (net-neutral / FREE); the third is CARRIED as an
     explicit pointwise-limit binder (SIZE-REJECTED, see verdict below):

       · `hDaLim`  (`DaTrunc → Δ_g(Wit*F) + E*F`, at `t`)  —  ★ FREE.  v2 already carries the FULL
         `hDaLimLU_from_data` DATA pile (gauge `hgi`/`hΓ`, the interchange trio, the strip
         integrabilities, the `√ε` sliver amplitudes, the two Gaussian dominations, `hUfloor`/`hUT`).
         Compose it through `ETailRateBound.hDaLimLU_from_data` (WALL → DATA) →
         `GrandAssemblyRecon.daLimLU_reduces_to_pointwise` (`.tendsto_at htU` at `t ∈ U`) to get the
         pointwise `hDaLim` with NO new binders.  This is the SAME composition `a1_R6_assembled` used
         one level up (for the frontier `hDConv` slot), now reused for the `core` `hDaLim` slot.

       · `hBoundaryLim`  (`BoundaryTrunc → F t 0 0`, at `t`)  —  ★ FREE (net-neutral).  Discharged by
         `HeatResidualBound.boundaryTrunc_tendsto` (W1) = pointwise-at-`t` of the landed loc-unif
         boundary discharge `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`.  SIZE VERDICT: EVERY
         carry of `boundaryTrunc_tendsto` (`T,hT,U,hUopen,hUpos,hUT,r₀,τ₀,hr₀,hτ₀,u₀,u₁,hAnear,`
         `hu₀cont,hu₀one,C₀,C₁,hu₀bdd,hu₁bdd,A₀,A₁,hA₀,hA₁,hAdom,C_L,hC_L,hBdom,hBcont,hAmeas,hBmeas,`
         `hu₀meas,hu₁meas,t,htU`) is ALREADY a v2 binder (with `A := Wit`, `B := leviSeries` fixed).
         So threading `hBoundaryLim` adds ZERO new binders — strictly better than keeping it a binder
         (which would be +1).  Thread it.

       · `hDerivConv`  (`DaTrunc + BoundaryTrunc → deriv (heatConv Wit F · 0 0)`, at `t`)  —  KEPT as an
         explicit binder (SIZE-REJECTED).  SIZE VERDICT: the provider
         `HeatResidualBound.derivConv_tendsto` (W3) needs `hderiv` (⟸ `hpar`/`htime`/`hR`, the F2
         truncated-`HasDerivAt` family), a loc-unif `hDerivLU` (⟸ `hDerivLU_discharge`, itself FREE
         from `hDaLimLU` + the boundary loc-unif), and `hfg` (⟸ `heatConv_tail_tendsto`, needing
         `hFII` the `Wit*F` strip integrability on `[0,u]`).  Of these, `hpar`/`htime`/`hR`/`hFII` are
         NOT v2 binders (v2 carries `hIlo`/`hIhi` for the residual `E = heatOp g gi Wit`, NOT the F2
         partials nor the `Wit*F` `hFII`).  Threading ⟹ ≥4 NEW binder families (the F2 regularity
         family + the tail integrability).  NET ENLARGE.  REJECT — carry `hDerivConv` as ONE clean
         pointwise-limit DATA binder (a satisfiable analytic fact, not the conclusion, not vacuous).

     ⚠ SIZE/DEPTH NOTE (honest).  v3 trades the OPAQUE `core : TruncatedDuhamelCore` bundle for ONE
       explicit pointwise-limit binder `hDerivConv` (net binder count: −1 core, +1 hDerivConv = 0),
       with the other two limits (`hBoundaryLim` + `hDaLim`) FULLY discharged from already-present
       data.  The value is DEPTH: the last opaque `: Prop` data bundle in the v2 surface is GONE; the
       surface now bottoms out in the geometry + measurable-suppliers + DATA piles + this single
       transparent pointwise limit.  Under the all-concrete ladder target this is genuine progress.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## POST-R3 LEAF ENUMERATION (the surface of `a1_R6_assembled_v3`, toward R4–R7).
     Relative to `a1_R6_assembled_v2`, the DELTA is:
       REMOVED : `core : TruncatedDuhamelCore`                 (the last opaque `: Prop` data bundle).
       ADDED   : `hDerivConv` (ONE pointwise limit `DaTrunc + BoundaryTrunc → deriv (heatConv)`).
     UNCHANGED (still open toward the final `a1_R6_of_geometry`):
       GEOMETRY   g,gi,Ric,…,hgi,hΓ,hdg0,htr,hsrc              (RNC/Ricci input the theorem is ABOUT)
       DATA       the CConv facade scaffolding + 5 bundles     (R4: hCConv_discharged_from_data)
       CD         `hgD1 i`                                      (R5: XUniformSliverFull.hD1_from_data)
       CD         `hInterchange`/`hLapFull`/`hEcomb`           (R2 size-REJECTED — kept as members)
       DATA       the whole hDConv analytic residue pile       (dominations/integrabilities/sliver…)
       DATA       `hEboundFull`, `hAdom`/`hEdom`/…             (R6: Gaussian-envelope banked bounds)
       CD         `hn`/`hKmeasSet`/`hcar*`/`hgiMeas`/`hchrMeas`(R1½: discharge suppliers from smoothness)
       DATA       `hDerivConv` (NEW; the ONE F2-family limit)  (R3½ / R6: needs F2 partials + hFII)
     GENUINE-GAP: NONE at the a₁ = R/6 CONDITIONAL level.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## NEXT BRICK (R4, refined).  Discharge the CConv facade bundles
     `metric`/`chart`/`source`/`derivData`/`env` via `CConvFacade.hCConv_discharged_from_data`, from
     the concrete chart/metric/source/deriv/env DATA.  Assess size: the facade's own data carries vs.
     the five bundle binders (likely a net enlarge unless the concrete data reuses the CConv envelope
     pile already present).

  NO `sorry`.  NO new axioms.  NO `:= True`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AssemblyLadderR1R2
import QIQTH.TruncatedDuhamelData
import QIQTH.DuhamelLimitWiring

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
open QIQTH.GrandAssemblyRecon QIQTH.ChartJetHessianMixed
open QIQTH.AssemblyLadderR1R2
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.AssemblyLadderR3

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ R3 — `a1_R6_assembled_v3`: the `core` bundle UNBUNDLED.
    ############################################################################### -/

/-- **★★★ J4-224 — `a1_R6_assembled_v3`.**  `AssemblyLadderR1R2.a1_R6_assembled_v2` with the bundle
    binder `core : TruncatedDuhamelCore …` REPLACED by its deeper 3-pointwise-limit residue, via
    `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim`:
      · `hDaLim`       ← `ETailRateBound.hDaLimLU_from_data` composed with
                         `GrandAssemblyRecon.daLimLU_reduces_to_pointwise` (`.tendsto_at htU`), REUSING
                         the `hDaLimLU`-data ALREADY carried by v2 (FREE, net-neutral);
      · `hBoundaryLim` ← `HeatResidualBound.boundaryTrunc_tendsto`, whose carries are ALL already v2
                         binders (FREE, net-neutral);
      · `hDerivConv`   ← the NEW carried pointwise-limit binder (SIZE-REJECTED: threading via
                         `derivConv_tendsto` needs the F2 partials + `hFII`, ≥4 non-v2 families).
    Same conclusion as `a1_R6_assembled_v2`; NO `TruncatedDuhamelCore` bundle in the surface.  Pure
    composition — no new analysis.  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v3 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
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
    -- the `tripleHEmeas_concrete` measurable-supplier block (v2):
    (hn : 0 < n) (hKmeasSet : MeasurableSet K)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hEboundFull : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    -- ★ R3 NEW: the `core` bundle's THIRD limit residue (was `core : TruncatedDuhamelCore`).
    (hDerivConv : Filter.Tendsto
        (fun m => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t
          + BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m t) Filter.atTop
        (𝓝 (deriv (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t)))
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
    -- v7 route: per-coordinate SCALAR jets.
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
    -- the `hDaLimLU_from_data` DATA carries (the WALL, turned into data) — R2 trio KEPT (size-rejected).
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
  -- R3: extract the `aT` window from `hUfloor` (kept intact for the capstone below).
  obtain ⟨aT, haT, hUlb⟩ := id hUfloor
  -- `hDaLim` (FREE): the WALL → DATA loc-unif, reduced to the pointwise-at-`t`.  Same composition as
  -- `a1_R6_assembled` used one level up; reused here for `core`'s `hDaLim` slot.
  have hDaLimLU := QIQTH.ETailRateBound.hDaLimLU_from_data g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    T U hUopen hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi
    D0 D1 hD0 hD1nn hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT
    hEdom hEzeroE hBdom hFzero hIlo hIhi hEcomb
  have hDaLim := QIQTH.GrandAssemblyRecon.daLimLU_reduces_to_pointwise g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    U t htU hDaLimLU
  -- `hBoundaryLim` (FREE, net-neutral): W1 pointwise-at-`t` boundary discharge; ALL carries are
  -- already v2 binders (`A := Wit`, `B := leviSeries`).
  have hBoundaryLim := QIQTH.HeatResidualBound.boundaryTrunc_tendsto
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    T hT U hUopen hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas t htU
  -- build the `core` bundle internally from its 3-limit residue.
  have core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t :=
    truncatedDuhamelCore_of_daLim g gi (vanVleckGatedWitness g gi hChr hK S a b) t
      hBoundaryLim hDaLim hDerivConv
  -- feed `a1_R6_assembled_v2` with the internally-built `core`; everything else verbatim.
  exact QIQTH.AssemblyLadderR1R2.a1_R6_assembled_v2
    g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc
    hn hKmeasSet hcarTau hcarField hcarField2 hgiMeas hchrMeas hEboundFull
    core hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.AssemblyLadderR3

section AxiomChecks
open QIQTH.AssemblyLadderR3
#print axioms a1_R6_assembled_v3
end AxiomChecks
