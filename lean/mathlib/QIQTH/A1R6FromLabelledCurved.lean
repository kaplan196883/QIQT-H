/-
  A1R6FromLabelledCurved — J4-519: the CURVED-VALID hraw-channel rewire of the final facade
  `A1R6FromLabelled.a1_R6_from_labelled`.  VERBATIM copy of that capstone with EXACTLY ONE binder
  swapped: the step (vii) flat-only LINEAR residual label
      `hraw : GlobalGatedRawBound g gi H_G P`   (width-1 LINEAR: |heatOp| ≤ P·((r²/τ + 1)·gaussDdim τ))
  — which is curved-UNSATISFIABLE (the true curved residual carries a QUADRATIC (r²/τ)² term from the
  metric deviation g⁻¹−δ = O(r²)) — is replaced by the HONEST curved-VALID on-gate width-4/3 QUADRATIC
  carry
      `hgate : ∀ τ>0 ∀ q∈K ∀ p∈closure(S q), |heatOp| ≤ P·(((r²/τ)²+r²/τ+1)·gaussDdim((4/3)τ))`.
  The `hDa` production is routed through the banked `LabelledRethreadV2.hDaLimLU_from_hgate` (J4-364)
  instead of `GlobalRawBoundFacade.hDaLimLU_from_labelled`; every other binder and every downstream
  brick is byte-identical.  The `hEdom` ∃-object both routes ultimately feed is the SAME.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It is a ONE-BINDER RE-THREAD removing ONE
  flat-only channel from the capstone, coefficient-neutral (the R/6 lives solely in
  `transportCoeff`/`htr`, untouched).  It does NOT by itself derive curved a₁: the other flat-only /
  pending capstone items (`hframeK` — banked curved swap `DaLimCurvedGauge.gauge_from_pointwise` not yet
  literally threaded; `hBoundaryLim`; the iterE/htr/hGauss curved bridges; a genuine RNC curved witness)
  remain.  `hgate` is the NAMED, SATISFIABLE, curved-VALID carry (J4-362): a width-4/3 QUADRATIC on the
  gate, NOT the conclusion.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, no existing
  file edited, nothing committed.
-/
import Mathlib
import QIQTH.A1R6FromLabelled
import QIQTH.LabelledRethreadV2

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.LeviSeriesLocalData QIQTH.GaussianWidthTolerant QIQTH.HeatKernelA1
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.VanVleck
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open QIQTH.A1R6SlotAdapters QIQTH.HDerivConvComposition
open QIQTH.RadialDistance QIQTH.LabelledRethreadV2 QIQTH.A1R6FromLabelled
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromLabelledCurved

variable {n : ℕ}

set_option maxHeartbeats 4000000

/-- **J4-519 — `a1_R6_from_labelled_curved` — THE CURVED-VALID hraw-CHANNEL FACADE.**  Identical
    to `A1R6FromLabelled.a1_R6_from_labelled` with the step (vii) flat-only LINEAR residual label
    (curved-unsatisfiable) replaced by the HONEST curved-VALID on-gate width-4/3 QUADRATIC carry
    `hgate`, routed through `LabelledRethreadV2.hDaLimLU_from_hgate`.  Same conclusion (the a₁ two-jet
    at the constant-radius gate).  Coefficient-neutral swap.  ⚠ NOT `a₁ = R/6` (still CONDITIONAL;
    other flat-only/pending capstone items remain — see file header). -/
theorem a1_R6_from_labelled_curved
    -- ═══ SECTION A — base geometry, gate, window, and window parameters (shared everywhere) ═══
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (t T : ℝ) (ht : 0 < t) (hT : 0 < T) (hn : 1 ≤ n)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ═══ SECTION B — gauge / smoothness (core + `htr_adapter`); `hGauss` is LABELLED ═══
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i))  -- ★ LABELLED
    -- ═══ SECTION C — the constant-radius package facts (satisfiable via `constRadius_package_and_S1`) ═══
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
    -- ═══ SECTION D — the geometry-raw gauge facts for `hDaLimLU_from_labelled` ═══
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hinvF : ∀ y c d, (∑ σ, g y c σ * gi y σ d) = if c = d then 1 else 0)
    -- ═══ SECTION E — the W2 differentiation-under-∫ family (SHARED: labelled-Da AND Duhamel-FULL) ═══
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) y z
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hFmeas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
            (Function.update (0 : Point n) i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) (0 : Point n) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound_W2 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
            ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK (constGate g gi hChr hK c) a b i (u - s)
              (Function.update (0 : Point n) i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) w)
    -- ═══ SECTION F — residual window floor (SHARED: `hDaLimLU_from_labelled` `aa` + `…_FULL` `aT`) ═══
    (aa : ℝ) (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u)
    -- ═══ SECTION G — `hDaLimLU_from_labelled` analytic piles (Levi source, dominations, sliver) ═══
    (CLevi : ℝ) (dataLevi : QIQTH.LeviSeriesLocalData.LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) CLevi T)
    (wA CA wA2 CA2 : ℝ) (hwA : 0 < wA) (hCA : 0 ≤ CA) (hwA2 : 0 < wA2) (hCA2 : 0 ≤ CA2)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hAdom2 : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z| ≤ CA2 * gaussDdim (wA2 * τ) (0 - z))
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
    (hmeas2Hi : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (τ0A : ℝ)
    (dataAmp : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK (constGate g gi hChr hK c) a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) i T τ0A)  -- ★ hard field = hD2Hexpand (LABELLED)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ0A : ∀ m : ℕ, epsSeq m ≤ τ0A)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))  -- ★ CURVED-VALID quadratic width-4/3 gate carry
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) i y) i 0)))  -- ★ LABELLED
    (hDaEq : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u
        = ∫ s in (0)..(u - epsSeq m), ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z,
            laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) x z) 0
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        volume 0 (u - epsSeq m))
    -- ═══ SECTION H — `truncatedDuhamelCore_AT_GATE_FULL` specific census ═══
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m t) atTop
        (𝓝 (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0)))
    (hgiMem : MemGaugeGi (n := n) gi) (hΓMem : MemGaugeGamma (n := n) g gi)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (u - s) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))))
    -- ═══ SECTION I — the F2 / `hDConv` regularity family (SHARED: `…_FULL` AND `a1_R6_slots_AT_GATE`) ═══
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ cc, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ cc ∈ nb m u,
      HasDerivAt (fun cc => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (cc - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b r 0 z) (cc - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0) cc)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- ═══ SECTION J — frozen/moving envelope list (SHARED: `…_FULL` AND `hbdryLU_CONCRETE`) ═══
    (ρ lam CW Cf τ0fr : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ0fr : 0 < τ0fr)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z,
        |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop,
        ∫ z, |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.ball (0 : Point n) δ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) (u - epsSeq m) z (0 : Point n)
            - leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    -- ═══ SECTION K — the `hCConv` sliver census for `a1_R6_slots_AT_GATE` ═══
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK (constGate g gi hChr hK c) a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- ── brick 2: the `htr` binder at `Ric := fun cc d => ricci g gi cc d 0`, from the labelled `hGauss`.
  have htr := htr_adapter g gi hg hgsymm hgiC hgi hdg0 hGauss
  -- ── J4-337: the loc-unif `Da`-limit from the labelled census, at `S := constGate g gi hChr hK c`.
  have hDa :
      DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U :=
    hDaLimLU_from_hgate g gi hChr hK (constGate g gi hChr hK c) a b T U hUopen hn
      hK0 hframeK hinvF hdg0
      V hVopen hV0 snb hsnb hQ1 hFmeas_W2 hFint_W2 hF'meas_W2 bnd hbdd_W2 hbound_W2 hdiff
      aa haa hau hUT
      CLevi dataLevi
      wA CA wA2 CA2 hwA hCA hwA2 hCA2 hAdomHeat hAdom2 hmeasLo hmeasHi hmeas2Lo hmeas2Hi
      τ0A dataAmp hεaa hετ0A
      P hP hgate
      hPd2conv
      hDaEq hLap hLapZ hEZ hLapS hES
  -- ── J4-311: the truncated-Duhamel core at the gate, from its FULL concrete census.
  have core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) t :=
    truncatedDuhamelCore_AT_GATE_FULL g gi hChr hK (constGate g gi hChr hK c) a b
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) rfl
      t T hT U hUopen htU hUT hn
      hBoundaryLim
      hgiMem hΓMem V hVopen hV0 snb hsnb hQ1 hFmeas_W2 hFint_W2 hF'meas_W2 bnd hbdd_W2 hbound_W2 hdiff
      hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
      E₀ E₁ C_L aa hE₀ hE₁ hC_L haa hau hEdom hFdom hFzero hIlo hIhi hEcomb
      A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
      nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
      ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
      hWDom hmass hmassone hmod hsup hUsub
  -- ── J4-310: the W1-free boundary loc-unif slot, from the frozen/moving lists.
  have hbdry : QIQTH.LocUnifDerivConv.hbdryLUTarget
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U :=
    hbdryLU_CONCRETE (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U
      ρ lam CW Cf τ0fr ta tb hρ hlam hCW hτ0fr
      hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd hWDom hmass hmassone hmod hsup hUsub
  -- ── brick 4: the three per-gate analytic slots.
  have slots := a1_R6_slots_AT_GATE g gi hChr hK c a b t T hT U hUopen htU hUpos hUT
    (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) rfl rfl
    core
    A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hFdom hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    hDa hbdry
    uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
    hbulkderiv hbulk_tendsto hsliver hcont
  -- ── brick 1: the pre-∃ core, at `Ric := fun cc d => ricci g gi cc d 0`.
  exact wide_a1_R6_core_AT_CONSTRADIUS g gi (fun cc d => ricci g gi cc d 0) t ht hn
    hChr hK hK0 hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    htr hpkgBound hmemS0 hopenS0 hS1
    slots.hDuhamel slots.hDConv slots.hCConv

end QIQTH.A1R6FromLabelledCurved

/-! ## Axiom check -- the curved-hraw facade is std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6FromLabelledCurved
#print axioms a1_R6_from_labelled_curved
end AxiomChecks
