/-
QIQTH/CapstoneLocalAssembly.lean

  Phase 3 of the capstone-signature redesign plan
  (`docs/qg_roadmap/CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`, J4-1168, Sol's 38th consult), per the phase
  table's Phase 3 line: "Extract `a1_R6_assembled_local` (Layer A) + rebuild `v2'` as wrapper (Layer B)
  → D5 green".

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS.

    • `a1_R6_assembled_local` (Layer A) — a COPY of `RightInverseGeneral.a1_R6_assembled_v2'` with
      ONLY `(C, hCnn, hEboundFull)` replaced by `(CT, hCTnn, hEbound_t)`, where `hEbound_t` is the
      every-ceiling-affine-in-`t'` family
        `∀ t' τ p q, 0 < τ → τ ≤ t' → |heatOp g gi Wit τ p q| ≤ (CT * (1+t')) * baseKernelW 2 0 τ p q`
      — EXACTLY the shape `LocalizedBankedData.endpointData_of_banked_on_horizon`/
      `interchangeData_of_banked_on_horizon` (J4-1171, Phase 2) consume, and EXACTLY the shape
      `GateOpennessExport.gatedWitnessN1_package_open`'s own `hbound` field already has (no new bound
      shape invented here).  All ~50 other hypotheses of `a1_R6_assembled_v2'` are copied UNCHANGED —
      not generalized, not transported.  The `C` fed to the final `GrandAssemblyRecon.a1_R6_assembled`
      call is `CT * (1 + t)`, matching the `EndpointData`/`InterchangeData` output type the two `_on_horizon`
      producers actually build.

    • `a1_R6_assembled_v2'_via_local` (Layer B, Canary D5 — BackCompat) — a REGRESSION-TEST WRAPPER with
      the EXACT SAME signature as `a1_R6_assembled_v2'` (same `C`/`hCnn`/`hEboundFull`, same ~50 other
      hypotheses), proving the SAME conclusion by restricting the global `hEboundFull` to the local
      `hEbound_t` shape (`C ≤ C*(1+t')` since `C ≥ 0`, `t' ≥ 0`, and `baseKernelW 2 0 τ p q ≥ 0` since
      `τ^0 = 1` and `gaussDdim ≥ 0`) and invoking `a1_R6_assembled_local` with `CT := C`.  This is the
      literal D5 canary: `a1_R6_assembled_v2'` reproved as a thin wrapper around `a1_R6_assembled_local`.
      `RightInverseGeneral.lean` itself is NOT edited (new-files-only discipline) — this is a standalone
      regression check that Layer A did not silently weaken anything, not a replacement of the banked
      theorem.

  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  This
  file is pure re-plumbing: it introduces no new analytic estimate (the `C ≤ C*(1+t')` / `baseKernelW ≥ 0`
  facts used in Layer B are elementary), only reassembles J4-1170/1171's already-banked local machinery at
  the shape `a1_R6_assembled_v2'`'s proof body needs.
-/
import QIQTH.RightInverseGeneral
import QIQTH.LocalizedBankedData

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.ChartRepConstruction
open QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open QIQTH.HDConvThreading QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound QIQTH.HD1CLMLift
open QIQTH.GrandAssemblyRecon QIQTH.ChartJetHessianMixed
open QIQTH.LocalizedBankedData
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.CapstoneLocalAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Layer A — `a1_R6_assembled_local`: the `(0,t]`-local sibling of `a1_R6_assembled_v2'`.
    ############################################################################### -/

/-- **★★★ (Layer A, J4-1172) `a1_R6_assembled_local`.**  `RightInverseGeneral.a1_R6_assembled_v2'`
    with `(C, hCnn, hEboundFull)` replaced by `(CT, hCTnn, hEbound_t)`, where `hEbound_t` is the
    every-ceiling-affine-in-`t'` family (the SAME shape `LocalizedBankedData`'s two `_on_horizon`
    producers consume, and the SAME shape `gatedWitnessN1_package_open`'s own `hbound` field has). All
    other ~50 hypotheses are copied verbatim. NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_local (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (CT : ℝ) (hCTnn : 0 ≤ CT)
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
    -- ★ the chart-measurability supplier is a SINGLE `tripleHEmeas` handle (unchanged from `v2'`).
    (htriple : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    -- ★ (Layer A): the local every-ceiling family, replacing `hEboundFull`.
    (hEbound_t : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (CT * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    -- core kept (R3), `hCH`:
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
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
  have hEmeas := htriple
  have endpoint : EndpointData g gi (vanVleckGatedWitness g gi hChr hK S a b) t (CT * (1 + t)) :=
    endpointData_of_banked_on_horizon g gi (vanVleckGatedWitness g gi hChr hK S a b) t CT hCTnn
      hEbound_t hEzeroE hEmeas
  have inter : InterchangeData g gi (vanVleckGatedWitness g gi hChr hK S a b) t :=
    interchangeData_of_banked_on_horizon g gi (vanVleckGatedWitness g gi hChr hK S a b) t CT hCTnn ht
      hEbound_t hEzeroE hEmeas
  exact QIQTH.GrandAssemblyRecon.a1_R6_assembled
    g gi Ric t ht (CT * (1 + t)) (mul_nonneg hCTnn (by linarith)) hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc endpoint core inter hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

/-! ###############################################################################
    ### Layer B — `a1_R6_assembled_v2'_via_local`: Canary D5, the regression-test wrapper.
    ############################################################################### -/

/-- **★★★ (Layer B, J4-1172, Canary D5 — BackCompat) `a1_R6_assembled_v2'_via_local`.**  The EXACT SAME
    signature and conclusion as `RightInverseGeneral.a1_R6_assembled_v2'`, proved as a thin wrapper
    around `a1_R6_assembled_local`: restrict the global `hEboundFull` to the local `hEbound_t` shape
    (`C ≤ C*(1+t')` since `C ≥ 0` and `t' ≥ τ > 0`, combined with `baseKernelW 2 0 τ p q ≥ 0`) and invoke
    `a1_R6_assembled_local` with `CT := C`.  A pure regression check that Layer A did not silently weaken
    anything — does NOT edit `RightInverseGeneral.lean` (new-files-only discipline). NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v2'_via_local (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (htriple : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (hEboundFull : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
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
    (hgD1 : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n))) (0 : Point n))
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
  have hbaseNN : ∀ (τ : ℝ) (p q : Point n), (0:ℝ) ≤ baseKernelW (2:ℝ) (0:ℝ) τ p q := by
    intro τ p q
    show (0:ℝ) ≤ τ ^ (0:ℝ) * gaussDdim (2 * τ) (p - q)
    rw [Real.rpow_zero, one_mul]
    exact gaussDdim_nonneg _ _
  have hEbound_t : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro t' τ p q hτ hτt'
    have ht' : 0 < t' := lt_of_lt_of_le hτ hτt'
    have hb := hEboundFull τ p q hτ
    have hmul : C * baseKernelW (2:ℝ) (0:ℝ) τ p q ≤ (C * (1 + t')) * baseKernelW (2:ℝ) (0:ℝ) τ p q :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCnn ht'.le]) (hbaseNN τ p q)
    exact hb.trans hmul
  exact a1_R6_assembled_local g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc htriple hEbound_t core hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.CapstoneLocalAssembly

section AxiomChecks
open QIQTH.CapstoneLocalAssembly
#print axioms a1_R6_assembled_local
#print axioms a1_R6_assembled_v2'_via_local
end AxiomChecks
