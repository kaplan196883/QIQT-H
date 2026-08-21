/-
  HDuhamelHQ1Discharged — eliminate the frozen first-order interchange EQUALITY carry `hQ1`
  from the LIVE order-1 `hDuhamel` slot, in favour of the SEVEN-leg frozen diff-under-∫ provider
  `hFrozenData` (the raw measurability / interval-integrability / dominator / `HasDerivAt` inputs)
  ALREADY sufficient to PROVE that equality via the banked `W2Finish.w2_hQ1`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure COMPOSITION / dependency-normalization brick — the missing wiring step between two ALREADY
  banked results on the `hDuhamel` surface, exactly analogous to J4-979 (which eliminated the
  approximate-identity limit `hmassone`), J4-980 (the four bundled interchange census binders), and
  J4-981 (the √ε matched-sliver amplitude carry).  This time it eliminates the frozen first-order
  interchange EQUALITY `hQ1` in favour of its raw diff-under-∫ INPUTS `hFrozenData`.

    • `HDuhamelSliverDischarged.hDuhamelSlot_sliver_discharged` (J4-981): the LIVE order-1 `hDuhamel`
      slot identity at the concrete van-Vleck gated witness, with `hmassone` / the four bundled
      interchange census binders / the √ε matched-sliver amplitude carry already discharged, but STILL
      carrying the frozen first-order interchange EQUALITY as a RAW hypothesis
          `hQ1 : ∀ m i, ∀ u ∈ U, ∀ y ∈ V,
             pd (fun x => heatConvFrozen W F u (u−ε_m) x 0) i y
               = ∫ s in (0)..(u−ε_m), ∫ z, witnessFieldDeriv … i (u−s) y z · F s z 0`
      on the SHARED field neighborhood `V ∋ 0` (a SINGLE, m-INDEPENDENT nbhd — the exact shape the
      slot binds; NO per-`(u,i,m)` existential, NO m-collapse trap).

    • `W2Finish.w2_hQ1` (J4-378, F3): DERIVES EXACTLY that shared-`V` equality — threading
      `SecondOrderInterchange.pd_heatConvFrozen_interchange` per `(m,i,u,y)` — FROM the seven-leg
      frozen first-order diff-under-∫ provider `hFrozenData` on the SAME shared `V`: a real-line nbhd
      `snb ∈ 𝓝 (y i)`, the witness / field-derivative pairing measurabilities and interval-
      integrabilities, an interval-integrable `s`-dominator, and the outer `s`-level `HasDerivAt`
      family.

  This file COMPOSES them: it derives the shared-`V` interchange equality `hQ1` from `hFrozenData`
  via `W2Finish.w2_hQ1`, and feeds it into the J4-981 slot, whose remaining surface is reproduced
  verbatim.  Net effect: the frozen first-order interchange EQUALITY `hQ1` is GONE from the live
  `hDuhamel` surface, traded for its raw diff-under-∫ INPUTS `hFrozenData` — a genuine
  dependency-frontier reduction (a cooked interchange identity replaced by the elementary
  satisfiable measurability / integrability / dominator / `HasDerivAt` side conditions that PROVE
  it), NOT a new analytic result and NOT a logical weakening.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## NOTE ON THE "UNIFORMITY GAP".
  The slot binds `hQ1` in the SHARED-`V` shape (a single fixed `V`, `∀ m i, ∀ u∈U, ∀ y∈V`).  This is
  EXACTLY the conclusion shape of `W2Finish.w2_hQ1`, whose input `hFrozenData` is ALSO on that same
  single shared `V`.  There is therefore NO m-uniformity gap to bridge here: the shared-`V` form is
  the natural output of the underlying pointwise `pd_heatConvFrozen_interchange` engine (the
  `V`-quantifier is on the OUTSIDE, shared; only the per-`(m,i,u,y)` `snb`/`bound` vary).  The
  per-`(u,i,m)` EXISTENTIAL `∃ V ∈ 𝓝 0` shape produced by `InnerDiffFamily.
  innerDiff_census_hQ1_of_frozenData` is a DELIBERATE WEAKENING of `w2_hQ1` aimed at the SEPARATE
  per-`u` census consumer (`PerUCensusInstantiation`), NOT at this slot — the slot wants the
  stronger shared-`V` form, which `w2_hQ1` supplies directly.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE LANDS.
    • `hDuhamelSlot_hQ1_discharged` — the EXACT `hDuhamel` slot identity of the LIVE order-1 capstone
      at the concrete van-Vleck gate, now a THEOREM whose antecedent surface NO LONGER carries the
      frozen first-order interchange EQUALITY `hQ1` (nor `hmassone` / the four census binders / the √ε
      sliver carry, gone in J4-979/980/981).  The `hQ1` equality is DERIVED internally from
      `W2Finish.w2_hQ1` (J4-378) fed the seven-leg frozen diff-under-∫ provider `hFrozenData`.

  ⚠  STILL NOT `a₁ = R/6`.  The remaining census members (the `RadialNormalCoordinateGauge`
  centre-identity leg + its geodesic-pullback bridge `hpull` — the opaque-chart wall — the Gaussian
  dominations, the τ⁻¹ᐟ² pairing carry `hGpow`, and the single W1-free `hBoundaryLim` slot) are NOT
  discharged here.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`; this brick only
  NORMALIZES the `hDuhamel` dependency further by eliminating the frozen first-order interchange
  equality in favour of its raw diff-under-∫ inputs — the `hDuhamel`-slot analogue of the
  `InnerDiffFamily` opener, now actually WIRED into the live slot identity in the slot's own
  shared-`V` shape.
-/
import QIQTH.HDuhamelSliverDischarged
import QIQTH.W2Finish

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.ETailRateBound QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Interval Topology BigOperators

namespace QIQTH.HDuhamelHQ1Discharged

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `hDuhamelSlot_hQ1_discharged`.**  The EXACT `hDuhamel` slot identity of the LIVE order-1
    capstone at the concrete van-Vleck gated witness — the parametrix Duhamel identity
    `heatOp g gi (H*L) t 0 0 = L t 0 0 + heatConv (heatOp g gi H) L t 0 0`
    (`L := leviSeries (heatOp g gi H)`) — with the frozen first-order interchange EQUALITY carry
    `hQ1` ELIMINATED from the antecedent surface (alongside `hmassone`, gone in J4-979; the four
    bundled interchange census binders, gone in J4-980; and the √ε matched-sliver amplitude carry,
    gone in J4-981).  The `hQ1` equality (shared-`V` shape, single `V ∈ 𝓝 0`) is DERIVED internally
    from `W2Finish.w2_hQ1` (J4-378), fed the seven-leg frozen first-order diff-under-∫ provider
    `hFrozenData` on the SAME shared `V`.  Every remaining binder is verbatim from
    `HDuhamelSliverDischarged.hDuhamelSlot_sliver_discharged` (J4-981).  Pure composition; NONE of
    the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hDuhamelSlot_hQ1_discharged (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hFrozenData : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ w : ℝ, AEStronglyMeasurable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) ∧
          IntervalIntegrable
            (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) y z * F s z 0)
            volume 0 (u - epsSeq m) ∧
          AEStronglyMeasurable
            (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
            (volume.restrict (Set.uIoc 0 (u - epsSeq m))) ∧
          IntervalIntegrable bound volume 0 (u - epsSeq m) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z * F s z 0‖ ≤ bound s) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
                (Function.update y i w) z * F s z 0)
              (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
                (Function.update y i w) z * F s z 0) w))
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
  -- Derive the shared-`V` frozen first-order interchange EQUALITY `hQ1` from its raw diff-under-∫
  -- inputs `hFrozenData`, via the banked `W2Finish.w2_hQ1` (J4-378).  The shared `V` is passed
  -- through unchanged — no per-`(u,i,m)` existential, no m-uniformity gap.
  have hQ1 := QIQTH.W2Finish.w2_hQ1 g gi hChr hK S a b U V hFrozenData
  -- Feed the derived interchange equality into the J4-981 slot; every other binder is verbatim.
  exact QIQTH.HDuhamelSliverDischarged.hDuhamelSlot_sliver_discharged
    g gi hChr hK S a b _ rfl t T hT U hUopen htU hUT hn hBoundaryLim
    hgi hΓ V hVopen hV0 snb hsnb hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hEdom hFdom hFzero hIlo hIhi
    A₀ A₁ hA₀ hA₁ hAdom hAzero hMeasFII hUfloor hInnerCont
    nb hnb hFmeas_d hFint_d hF'meas_d boundD hbdd_d hbound_d hpardiff L hLnn hCross
    ρ lam CW Cf τ₀ ta tb hρ hlam hCW hτ₀ hWmeas hffro_meas hfmov_meas hffro_bdd hfmov_bdd
    hWDom hmass hmod hsup hUsub
    hgCD hgiCD hgpos h0Kmem hgdet0 ha hab rS hrS hKball hSact
    wA2 hwA2 CA2c hCA2c hεU hAdom2cap hmeasJ hInter hPd2conv
    hSecCont hBcont Cpair hCpair hGpow hDa hLap hLapZ hEZ hLapS hES

end QIQTH.HDuhamelHQ1Discharged

section AxiomChecks
open QIQTH.HDuhamelHQ1Discharged
#print axioms hDuhamelSlot_hQ1_discharged
end AxiomChecks
