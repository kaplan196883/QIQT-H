/-
  AssemblyV7Rethread — J4-233: the CORRECTED (satisfiable-S1) capstone re-thread `a1_R6_assembled_v7`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PURE RE-PLUMBING brick: it takes the R1 capstone `RightInverseGeneral.a1_R6_assembled_v2'` (whose
  single measurable-supplier slot is the direct handle `htriple : HEmeasBorelAudit.tripleHEmeas …`) and
  SOURCES that handle INTERNALLY from the VACUITY-FIXED, all-hypotheses-satisfiable S1 supplier
  `GatedRepSFix.tripleHEmeas_concrete_v4`.  No `sorry` (prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY v7 (the correction over v6).
  `a1_R6_assembled_v6` sources its `htriple` from `GatedChartMeasAudit.tripleHEmeas_concrete_v3`, i.e.
  the GATED (regional `Gc` + guarded `hWG`) chart route.  Its supplier existentials carry the S-membership
  as a CONCLUSION (`∀ w, w.2.2 ∈ K → 0 < w.1 → … w.2.1 ∈ S w.2.2 …`), which — since `w.2.1` ranges over
  ALL field points with no guard — FORCES `S q = univ` (`HgateSatAudit.hcar*_unsat`), i.e. the v3/v2 hcar
  block is UNSATISFIABLE for the concrete proper flow-ball gate with `K ≠ ∅`.

  `a1_R6_assembled_v7` (this file) replaces that whole `htriple` supplier block by
  `GatedRepSFix.tripleHEmeas_concrete_v4`, whose EVERY carried existential is SATISFIABLE at the concrete
  flow-ball gate:  S-membership is a HYPOTHESIS (conditional `hgate` form `… → w.2.1 ∈ S w.2.2 → …`),
  `hKSmeas` is the (open flow-ball ∩ compact-`K`) product-preimage `MeasurableSet`, and the off-`S`
  vanishings `hOffS`/`hOffS2` are the radialCutoff-support facts — NONE forces `K = ∅`.  All the analytic
  `a₁ = R/6` residue (`hEboundFull`, `core`, `hCH`, the CConv facade, the `hDConv` pile, the R2 trio) is
  threaded VERBATIM into `a1_R6_assembled_v2'`.  Same conclusion.  This is the credited concrete-closable
  path: ONE capstone whose S1 / measurability story is fully satisfiable.

  ## BINDER DIFF vs `a1_R6_assembled_v6` (supplier block only; everything else verbatim).
    * REMOVED  : `hKmeasSet : MeasurableSet K`, `Gc : Point² → Point`, `hGmeas : Measurable Gc`.
    * REPLACED : the v2/v3-form `hcarTau`/`hcarField`/`hcarField2` (with `… = Gc (…)` chart-substitution
                 conjuncts and the CONCLUSION-form `w.2.1 ∈ S w.2.2`) by the v4-form ones (RAW
                 `uniformInverseChart` measurability conjunct + CONDITIONAL `… → w.2.1 ∈ S w.2.2 → …`
                 hgate + the off-`S` vanishing conjuncts `hOffS`/`hOffS2`).
    * ADDED    : `hKSmeas : MeasurableSet {w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`.
    * KEPT     : `hn`, `hgiMeas`, `hchrMeas` (verbatim).

  NOT `a₁ = R/6`.
-/
import QIQTH.RightInverseGeneral
import QIQTH.GatedRepSFix

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
open QIQTH.RightInverseGeneral QIQTH.GatedRepSFix QIQTH.HgateSatAudit
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.AssemblyV7Rethread

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (B) `a1_R6_assembled_v7` — chart-measurability FULLY INTERNAL from the VACUITY-FIXED
    ###      (all-hypotheses-satisfiable) S1 supplier `GatedRepSFix.tripleHEmeas_concrete_v4`.
    ############################################################################### -/

/-- **★★★ (B) `a1_R6_assembled_v7`.**  `RightInverseGeneral.a1_R6_assembled_v2'` with its `tripleHEmeas`
    handle SOURCED INTERNALLY from the CORRECTED, all-hypotheses-satisfiable S1 supplier
    `GatedRepSFix.tripleHEmeas_concrete_v4`.  The v4 supplier block (`hn`, `hKSmeas`, the conditional-
    `hgate` + off-`S`-vanishing `hcarTau`/`hcarField`/`hcarField2`, `hgiMeas`, `hchrMeas`) becomes the new
    supplier binders — every one SATISFIABLE at the concrete flow-ball gate, so `K` NEED NOT be empty.
    All the analytic `a₁ = R/6` residue is threaded VERBATIM.  Same conclusion as `a1_R6_assembled_v2'`
    / `a1_R6_assembled_v6`.  Pure composition — the S1 / measurability story is now internal AND
    satisfiable.  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v7 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
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
    -- ★ (B) v7: the VACUITY-FIXED (all-hypotheses-satisfiable) `tripleHEmeas_concrete_v4` supplier block.
    (hn : 0 < n)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            witnessFieldDeriv g gi hChr hK S a b k w.1 w.2.1 w.2.2 = 0))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) j y) i w.2.1
              = 0))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
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
  -- (B) v7: build the `tripleHEmeas` handle from the VACUITY-FIXED, all-satisfiable S1 supplier.
  have htriple : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b) :=
    QIQTH.GatedRepSFix.tripleHEmeas_concrete_v4 hn g gi hChr hK S a b hKSmeas
      hcarTau hcarField hcarField2 hgiMeas hchrMeas
  exact QIQTH.RightInverseGeneral.a1_R6_assembled_v2'
    g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc htriple hEboundFull core hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.AssemblyV7Rethread

/-! ## Axiom check — the public capstone is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AssemblyV7Rethread
#print axioms a1_R6_assembled_v7
end AxiomChecks
