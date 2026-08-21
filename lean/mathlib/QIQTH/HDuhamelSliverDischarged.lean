/-
  HDuhamelSliverDischarged — eliminate the √ε matched-sliver amplitude carry `{D0, D1, hD0, hD1, hbnd}`
  from the LIVE order-1 `hDuhamel` slot, in favour of the moment-aware τ⁻¹ᐟ² pairing carry `hGpow`
  ALREADY present on that surface.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / dependency-normalization brick — the missing wiring step between two ALREADY
  banked results on the `hDuhamel` surface, exactly analogous to J4-979 (which eliminated the
  approximate-identity limit `hmassone`) and J4-980 (which eliminated the four bundled interchange
  census binders).  This time it eliminates the √ε matched-sliver amplitude carry.

    • `HDuhamelDataCensusDischarged.hDuhamelSlot_datacensus_discharged` (J4-980): the LIVE order-1
      `hDuhamel` slot identity at the concrete van-Vleck gated witness, with `hmassone` and the four
      bundled interchange census binders already discharged, but STILL carrying the √ε matched-sliver
      amplitude bound as RAW hypotheses `D0 D1 : Fin n → ℝ`, `hD0`/`hD1` (nonnegativity) and
          `hbnd : ∀ i m, ∀ u ∈ U, |∫ s in (u−ε_m)..u, ∫ z, W''(u−s) z · F s z 0|
                     ≤ D0 i · (2√ε_m) + D1 i · ε_m`
      alongside the moment-aware τ⁻¹ᐟ² pairing carry
          `hGpow : ∀ m i, ∀ u ∈ U, ∀ s ∈ uIoc (u−ε_m) u, |∫ z, W''(u−s) z · F s z 0| ≤ Cpair·(u−s)^{-1/2}`.

    • `SliverAmplitudeFromHGpow.hbnd_from_hGpow` (J4-921): DERIVES exactly the `hbnd` predicate — with
      the canonical constants `D0 := fun _ => Cpair`, `D1 := fun _ => 0` (the `D1·ε_m` slot is genuinely
      absent: the pure τ⁻¹ᐟ² profile pays no `ε_m` term) — FROM `hGpow` together with the SAME
      sliver-continuity carries `hUT`/`hεU`/`hSecCont`/`hBcont`/`hCpair` that the slot ALREADY carries.
      Route: integrate the pointwise τ⁻¹ᐟ² pairing bound over the matched sliver `[u−ε_m, u]`, using
      `∫ s in (u−ε_m)..u, (u−s)^{-1/2} ds = 2√ε_m`.

  This file COMPOSES them: it derives the √ε sliver amplitude bound `hbnd` (with `D0 := fun _ => Cpair`,
  `D1 := fun _ => 0`) from the `hGpow` carry already present in the slot's surface, and feeds it into the
  J4-980 slot, whose remaining surface is reproduced verbatim.  Net effect: the sliver carry
  `{D0, D1, hD0, hD1, hbnd}` is GONE from the live `hDuhamel` surface, traded for the τ⁻¹ᐟ² pairing carry
  `hGpow` — a dependency-frontier reduction (two named amplitude carries collapse onto the single one
  already present), NOT a new analytic result and NOT a logical weakening.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.
    • `hDuhamelSlot_sliver_discharged` — the EXACT `hDuhamel` slot identity of the LIVE order-1 capstone
      at the concrete van-Vleck gate (`heatOp g gi (H*L) t 0 0 = L t 0 0 + heatConv (heatOp g gi H) L t
      0 0`, `L := leviSeries (heatOp g gi H)`), now a THEOREM whose antecedent surface NO LONGER carries
      the √ε matched-sliver amplitude carry `{D0, D1, hD0, hD1, hbnd}` (nor `hmassone`, gone in J4-979,
      nor the four bundled interchange census binders, gone in J4-980).  The sliver `hbnd` is DERIVED
      internally from `SliverAmplitudeFromHGpow.hbnd_from_hGpow` (J4-921) fed the `hGpow` carry that was
      already present.

  ⚠  STILL NOT `a₁ = R/6`.  The remaining census members (the `RadialNormalCoordinateGauge`
  centre-identity leg + its geodesic-pullback bridge `hpull` — the opaque-chart wall — the Gaussian
  dominations `hEdom`/`hFdom`/`hAdom`/`hWDom`/`hAdom2cap`, the τ⁻¹ᐟ² pairing carry `hGpow` itself, and
  the single W1-free `hBoundaryLim` slot) are NOT discharged here.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`; this brick only NORMALIZES the `hDuhamel` dependency further by
  eliminating the √ε sliver amplitude carry in favour of the τ⁻¹ᐟ² pairing carry already present — the
  `hDuhamel`-slot analogue of J4-921's `hbnd_from_hGpow` reduction, now actually WIRED into the live
  slot identity.
-/
import QIQTH.HDuhamelDataCensusDischarged
import QIQTH.SliverAmplitudeFromHGpow

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelSliverDischarged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDuhamelSlot_sliver_discharged`.**  The EXACT `hDuhamel` slot identity of the LIVE order-1
    capstone at the concrete van-Vleck gated witness — the parametrix Duhamel identity
    `heatOp g gi (H*L) t 0 0 = L t 0 0 + heatConv (heatOp g gi H) L t 0 0`
    (`L := leviSeries (heatOp g gi H)`) — with the √ε matched-sliver amplitude carry
    `{D0, D1, hD0, hD1, hbnd}` ELIMINATED from the antecedent surface (alongside `hmassone`, gone in
    J4-979, and the four bundled interchange census binders, gone in J4-980).  The sliver `hbnd`
    (with canonical constants `D0 := fun _ => Cpair`, `D1 := fun _ => 0`) is DERIVED internally from
    `SliverAmplitudeFromHGpow.hbnd_from_hGpow` (J4-921), fed the moment-aware τ⁻¹ᐟ² pairing carry
    `hGpow` already present on the slot's surface (with the SAME sliver-continuity carries
    `hUT`/`hεU`/`hSecCont`/`hBcont`/`hCpair`).  Every remaining binder is verbatim from
    `HDuhamelDataCensusDischarged.hDuhamelSlot_datacensus_discharged` (J4-980).  Pure composition; NONE
    of the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hDuhamelSlot_sliver_discharged (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
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
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hsup : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
          |F (u - epsSeq m) z (0 : Point n) - F u z (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    (hgCD : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiCD : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hgdet0 : Matrix.det (g 0) = 1)
    (ha : 0 < a) (hab : a < b)
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (wA2 : ℝ) (hwA2 : 0 < wA2) (CA2c : ℕ → ℝ) (hCA2c : ∀ m, 0 ≤ CA2c m)
    (hεU : ∀ (m : ℕ), ∀ u ∈ U, epsSeq m ≤ u)
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hmeasJ : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)))
    (hSecCont : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ × Point n => witnessSecondXDeriv g gi hChr hK S a b i p.1 p.2)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hBcont : ContinuousOn
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (Cpair : ℝ) (hCpair : 0 ≤ Cpair)
    (hGpow : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2))
    (hDa : ∀ (m : ℕ) (u : ℝ),
        DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
          = ∫ s in (0)..(u - epsSeq m), ∫ z,
              deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLap : ∀ (m : ℕ) (u : ℝ),
        LapTrunc g gi (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u
          = ∫ s in (0)..(u - epsSeq m), ∫ z,
              laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
                * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    (hLapZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hEZ : ∀ (u : ℝ), ∀ s : ℝ, Integrable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume)
    (hLapS : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m))
    (hES : ∀ (m : ℕ) (u : ℝ), IntervalIntegrable
        (fun s => ∫ z, heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume 0 (u - epsSeq m)) :
    heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0 := by
  subst hFeq
  -- Derive the √ε matched-sliver amplitude bound `hbnd` (with `D0 := fun _ => Cpair`, `D1 := fun _ => 0`)
  -- from the moment-aware τ⁻¹ᐟ² pairing carry `hGpow` already present on the slot surface (J4-921).
  have hbnd := QIQTH.SliverAmplitudeFromHGpow.hbnd_from_hGpow g gi hChr hK S a b T U
    hUT hεU hSecCont hBcont Cpair hCpair hGpow
  -- Feed the derived sliver amplitude into the J4-980 slot; every other binder is verbatim.
  exact QIQTH.HDuhamelDataCensusDischarged.hDuhamelSlot_datacensus_discharged
    g gi hChr hK S a b _ rfl t T hT U hUopen htU hUT hn hBoundaryLim
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    (fun _ => Cpair) (fun _ => 0) (fun _ => hCpair) (fun _ => le_refl 0) hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmod hsup hUsub
    hgCD hgiCD hgpos h0Kmem hgdet0 ha hab rS hrS hKball hSact
    wA2 hwA2 CA2c hCA2c hεU hAdom2cap hmeasJ hInter hPd2conv
    hSecCont hBcont Cpair hCpair hGpow hDa hLap hLapZ hEZ hLapS hES

end QIQTH.HDuhamelSliverDischarged

section AxiomChecks
open QIQTH.HDuhamelSliverDischarged
#print axioms hDuhamelSlot_sliver_discharged
end AxiomChecks
