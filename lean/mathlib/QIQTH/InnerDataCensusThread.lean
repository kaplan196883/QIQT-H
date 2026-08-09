/-
  InnerDataCensusThread — J4-463: SWAP `hInnerData` FOR ITS REDUCED CORE INSIDE THE CENSUS.

  `HdiffGrounding.v2Census_phase5` (J4-462) grounded the `hdiff` carry onto the ALREADY-PRESENT z-level
  bundle `hInnerData` (the 7-conjunct differentiation-under-∫ existential).  With `hdiff` gone, the
  remaining diff-under-∫ opacity in the census surface IS `hInnerData` itself.  This brick attacks it:
  `v2Census_phase6` = `v2Census_phase5` with the opaque `hInnerData` bundle REMOVED and supplied
  INTERNALLY from the strictly-lighter phase-2 gate/amplitude/envelope core `hGateCore`, via the banked
  supplier `InnerDataEnvelope.innerData_phase2` (J4-427, chaining `innerData_reducedCore_of_gateData`
  into `innerData_phase1`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE  (phase-2 OUTPUT vs phase-5 `hInnerData` BINDER — shape comparison + verdict).

  DEMANDED (`v2Census_phase5`'s `hInnerData` binder, verbatim):
      `∀ (m) (i), ∀ u ∈ U, ∀ᵐ s, s ∈ uIoc 0 (u−εₘ) → ∀ w ∈ snb, ∃ znb bnd,`
      `  znb ∈ 𝓝 w ∧ (∀ w', AEStronglyMeasurable (dH(w')·Lev)) ∧ Integrable (dH(w)·Lev) ∧`
      `  AEStronglyMeasurable (dHH(w)·Lev) ∧ Integrable bnd ∧`
      `  (∀ᵐ z, ∀ w'∈znb, ‖dHH(w')·Lev‖ ≤ bnd z) ∧ (∀ᵐ z, ∀ w'∈znb, HasDerivAt (dH-slice·Lev) …).`

  SUPPLIED (`InnerDataEnvelope.innerData_phase2`'s OUTPUT): the SAME quantifier prefix
  `∀ m i, ∀ u ∈ U, ∀ᵐ s, … → ∀ w ∈ snb, ∃ znb bnd, …`, and the SAME seven conjuncts in the SAME order,
  with the SAME `(m,i,u)` indexing, the SAME a.e.-`s` truncation `uIoc 0 (u−εₘ)`, the SAME centre
  `update 0 i w`, and the SAME kernels `dH = witnessFieldDeriv`, `dHH = witnessFieldDeriv2`,
  `Lev z = leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0`.

  VERDICT.  ★ EXACT VERBATIM MATCH — NO BRIDGE NEEDED.  `innerData_phase2 g gi hChr hK S a b U snb
  hGateCore` inhabits `v2Census_phase5`'s `hInnerData` binder DEFINITIONALLY (the only difference between
  the two source files is the LOCAL bound-variable name `hC` vs `hChr` for the `ContDiff` argument, which
  is irrelevant to the type).  So `hInnerData` is REPLACED by the phase-2 core `hGateCore` — the seven
  NAMED ATOMIC carries: (a) bare z-slice measurabilities of `dH`/`Lev`/`dHH`; (b) positive Gaussian
  width `σ`; (c) `C₁ ≥ 0`; (d) `C₂ ≥ 0`; (e) `C_L ≥ 0`; (f) nbhd `znb ∈ 𝓝 w`; (g) the per-`z` GATE
  DICHOTOMY, plus the Levi domination `|Lev| ≤ C_L·G_σ` and the first/second-order on-gate sups.

  ── THE SUP-CONVERGENCE AUDIT (C₁/C_L via the grounded sup family?).  `SupFamilyFirstOrder.
  baseSlotAmpDeriv1_grounded` (J4-436) delivers `∃ M₁ ≥ 0, ∀ τ z, collarRegime … → |−2·pd(chartAmp …)
  i 0| ≤ M₁`, and `SupConstantFamily.levi_C_L_grounded` (J4-431) delivers
  `|leviSeries E τ p q| ≤ C_L·baseKernelW 2 0`.  These are NOT verbatim matches for `hGateCore`'s C₁/C_L
  slots, which are the ON-GATE (`z ∈ K`) sup of `witnessFieldDeriv … (update 0 i w) z` (C₁) and the
  `|Lev| ≤ C_L·gaussDdim σ z` domination (C_L).  Bridging would require the germ↔`chartAmp`-derivative
  identity + the `collarRegime → z ∈ K` restriction (for C₁) and the `baseKernelW 2 0 = gaussDdim (2s) z`
  identity + the large `leviSeries_gatedWitnessN1_dominated` standing carries (for C_L).  Per the
  J4-440/441 base-compatibility lessons this is a genuine PRESENTATION MISMATCH, not a drop-in: the
  grounded sups live in the `chartAmp`/`collarRegime`/`baseKernelW` presentation, `hGateCore` in the
  witness/gate/`gaussDdim` presentation.  ⟹  C₁/C_L stay as NAMED atomic carries at THIS surface; the
  grounding bridge is a separate downstream brick.  (Base check: the grounded C₁ is at field point `0`;
  `hInnerData`/`hGateCore` are base-`0` — compatible in POINT, mismatched in PRESENTATION.)

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It re-threads
  the census surface: `hInnerData` (the opaque 7-conjunct bundle) is replaced by the strictly-lighter
  NAMED atomic carries of `hGateCore`, with `hInnerData` supplied internally by the banked
  `innerData_phase2`.  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack AND on the surviving envelope/box/scaffold/gate/amplitude inputs.  `hGateCore` is genuine,
  satisfiable, non-vacuous, strictly lower-level than `hInnerData`, and never the conclusion.  NO `sorry`
  (header prose excepted), NO `:= True`, NO new axioms, NO existing file edited, nothing wired into
  `AxiomAudit`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HdiffGrounding
import QIQTH.InnerDataEnvelope

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.DuhamelCoreThreaded QIQTH.PerUCensusTuple QIQTH.W2Finish
open QIQTH.HDuhamelExportRethread QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.V2CensusInstantiation QIQTH.WallAInstantiation QIQTH.WallAThreading
open QIQTH.HInterGrounding QIQTH.HAdom2capGrounding
open QIQTH.InnerDataInstantiation QIQTH.InnerDataEnvelope QIQTH.HdiffGrounding
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.InnerDataCensusThread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★★ `v2Census_phase6` — `v2Census_phase5` with `hInnerData` SUPPLIED FROM `hGateCore`.
    ############################################################################### -/

/-- **★★★★ `v2Census_phase6`.**  THE innerData-REDUCED TERMINAL CROSS-CHECK.  It is `v2Census_phase5`
    with the opaque z-level bundle `hInnerData` REMOVED from the carried surface and supplied INTERNALLY
    from the strictly-lighter phase-2 gate/amplitude/envelope core `hGateCore` via the banked supplier
    `InnerDataEnvelope.innerData_phase2` (J4-427).  So its binder list is `v2Census_phase5`'s with the
    single opaque `hInnerData` carry TRADED for the seven NAMED ATOMIC carries of `hGateCore` (bare
    z-slice measurabilities, a positive Gaussian width `σ`, the three nonnegative sups `C₁`/`C₂`/`C_L`,
    the Levi Gaussian domination, the first/second-order on-gate sups, the per-`z` gate dichotomy).  The
    conclusion is the SAME v3-core `TruncatedDuhamelCore`.

    THAT THIS TYPECHECKS certifies `hInnerData` is no longer an independent carry — it collapses onto the
    banked `innerData_phase2` engine fed by the named gate/amplitude/envelope atoms.  ⚠ Pure surface
    reduction at the differentiation-under-∫ leg; closes NOTHING deeper.  NOT `a₁ = R/6`. -/
theorem v2Census_phase6 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ)
    (hFeq : F = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
    (t T : ℝ) (hT : 0 < T) (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUT : ∀ u ∈ U, u ≤ T) (hn : 1 ≤ n)
    (hBoundaryLim : Tendsto
        (fun m => BoundaryTrunc (vanVleckGatedWitness g gi hChr hK S a b) F m t) atTop
        (𝓝 (F t 0 0)))
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
          (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ c, AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z * F s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas_d : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd_d : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound_d : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0‖
        ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (c - s) * F s z 0) c)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (ρ lam CW Cf τ₀ : ℝ) (ta tb : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z) volume)
    (hffro_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hfmov_meas : ∀ m u, AEStronglyMeasurable (fun z => F (u - epsSeq m) z (0 : Point n)) volume)
    (hffro_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hfmov_bdd : ∀ m u z, |F (u - epsSeq m) z (0 : Point n)| ≤ Cf)
    (hWDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hChr hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto
        (fun m => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    (τc wA2 : ℝ)
    (hwA2 : 0 < wA2)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (Cdata : ℝ)
    (data : LeviSeriesLocalData
        (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) Cdata T)
    (hSecBoxes : ∀ i : Fin n, ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hBBoxes : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (Ccrude : ℝ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z))
    (Lc Bcomp Q Sconst : ℝ) (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0)
    (hGateCore : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
        ∃ (znb : Set ℝ) (σ C₁ C₂ C_L : ℝ),
          znb ∈ 𝓝 w ∧ 0 < σ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C_L ∧
          (∀ w' : ℝ, AEStronglyMeasurable
            (fun z => witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z) volume) ∧
          AEStronglyMeasurable
            (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            volume ∧
          AEStronglyMeasurable
            (fun z => witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z) volume ∧
          (∀ᵐ z ∂volume,
            |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
              ≤ C_L * gaussDdim σ z) ∧
          (∀ᵐ z ∂volume, z ∈ K →
            |witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w) z| ≤ C₁) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb, z ∈ K →
            |witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
                (Function.update (0 : Point n) i w') z| ≤ C₂) ∧
          (∀ᵐ z ∂volume, ∀ w' ∈ znb,
            z ∉ K ∨ PdiffAt (fun x' : Point n =>
                witnessFieldDeriv g gi hChr hK S a b i (u - s) x' z) i
              (Function.update (0 : Point n) i w')))
    (nbP : ℝ → Set (Point n)) (hnbP_open : ∀ u ∈ U, IsOpen (nbP u))
    (hnbP0 : ∀ u ∈ U, (0 : Point n) ∈ nbP u)
    (hProvP : ∀ u ∈ U, ∀ x ∈ nbP u, ∀ i : Fin n,
      ∃ (snbx : Set ℝ) (bound : ℝ → ℝ),
        snbx ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snbx,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGintP : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) :
    TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t := by
  -- ★ SUPPLY `hInnerData` INTERNALLY from the phase-2 gate/amplitude/envelope core `hGateCore`.
  have hInnerData := QIQTH.InnerDataEnvelope.innerData_phase2 g gi hChr hK S a b U snb hGateCore
  exact QIQTH.HdiffGrounding.v2Census_phase5 g gi hChr hK S a b F hFeq
    t T hT U hUopen htU hUT hn hBoundaryLim hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas
    bnd hbdd hbound D0 D1 hD0 hD1 hbnd E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hIlo hIhi
    hEcomb A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmassone hmod hsup hUsub
    τc wA2 hwA2 hεU Cdata data hSecBoxes hBBoxes
    Ccrude hCcrude hcrude
    Lc Bcomp Q Sconst hLc hBcomp hQ hSconst hslot hcap hEndpoint
    hInnerData
    nbP hnbP_open hnbP0 hProvP fderivBulk gderiv C₀ C₁ C₂ hGintP hbulkderiv hsliver hcont hfrozen_pd1

end QIQTH.InnerDataCensusThread

/-! ## THE CENSUS SURFACE LEDGER — the v3-core surface after this brick.

  With `v2Census_phase6`, the opaque z-level bundle `hInnerData` (the 7-conjunct differentiation-under-∫
  existential) is REMOVED from the carried census surface and supplied INTERNALLY from the strictly-
  lighter phase-2 gate/amplitude/envelope core `hGateCore`, via the banked supplier
  `InnerDataEnvelope.innerData_phase2` (J4-427, = `innerData_reducedCore_of_gateData` ∘
  `innerData_phase1`).  Combined with J4-461 (block-B ZERO genuine atoms) and J4-462 (`hdiff` grounded
  onto `hInnerData`), the differentiation-under-∫ leg of the wall-A census now rests on the following
  NAMED ATOMIC CARRIES ONLY (no opaque bundle left):

    census leg                         carried atoms (post J4-463)
    ────────────────────────────────   ─────────────────────────────────────────────────────────────
    differentiation-under-∫            `hGateCore` — per `(m,i,u)`, a.e.-`s`, `∀ w ∈ snb`:
    (was `hInnerData`, now `hGateCore`)   (a) bare z-slice measurabilities of `dH`/`Lev`/`dHH`;
                                          (b) positive Gaussian width `σ`;
                                          (c) `C₁ ≥ 0` — first-order on-gate sup `|dH(w)| ≤ C₁` (z∈K);
                                          (d) `C₂ ≥ 0` — second-order on-gate sup `|dHH(w')| ≤ C₂` (z∈K);
                                          (e) `C_L ≥ 0` — Levi domination `|Lev| ≤ C_L·G_σ`;
                                          (f) nbhd `znb ∈ 𝓝 w`;
                                          (g) the per-`z` GATE DICHOTOMY (`z∉K ∨ on-gate C¹ PdiffAt`).
    envelope / amplitude               `hEdom` `hFdom` `hAdom` `hWDom` `hslot` `hcrude` `hbnd` `hbound`
                                       `hsliver` …  (Gaussian envelopes + collar sups, named scalars).
    box / scaffold                     `hSecBoxes` `hBBoxes` `data` (`LeviSeriesLocalData`) `hProvP`
                                       `hbulkderiv` `hcont` `hfrozen_pd1` `hQ1` `hCross` …
    boundary / limit                   `hBoundaryLim` `hmassone` `hmass` `hmod` `hsup` `hUsub` …

  ── THE SUP-CONVERGENCE STATUS (C₁/C_L grounding).  AUDITED, DEFERRED.  The grounded sup family
  (`SupFamilyFirstOrder.baseSlotAmpDeriv1_grounded` for `C₁`, `SupConstantFamily.levi_C_L_grounded` for
  `C_L`) lives in the `chartAmp`-derivative / `collarRegime` / `baseKernelW` presentation, whereas
  `hGateCore`'s C₁/C_L slots are the on-gate (`z∈K`) sup of `witnessFieldDeriv` and the `gaussDdim σ`
  Levi domination.  These are a genuine PRESENTATION mismatch (germ↔`chartAmp` + `baseKernelW`↔`gaussDdim`
  bridges needed), NOT a census-level drop-in — consistent with the J4-440/441 base-compatibility
  lessons (the grounded C₁ is base-`0`, matching `hGateCore`'s base-`0` POINT, but the FUNCTIONAL
  presentation differs).  So C₁/C_L remain named atomic carries at this surface; their grounding is a
  separate downstream brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ v3-CORE SURFACE AFTER THIS BRICK.  The wall-A leg carries ONLY named atomic gate/amplitude/envelope/
  box/scaffold inputs — NO opaque differentiation-under-∫ bundle survives.  ⚠ THIS IS **NOT** `a₁ = R/6`:
  the surviving inputs are INPUTS, not theorems, and the DEEP convergence-trio + geometric-wiring content
  OUTSIDE the census is NEVER claimed closed.  Reducing `hInnerData` to `hGateCore` closes NOTHING deeper.
-/

section AxiomChecks
open QIQTH.InnerDataCensusThread
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms v2Census_phase6
end AxiomChecks
