/-
  F2FamilyDischarge — J4-145: DISCHARGING the F2-REGULARITY GROUP (`hFII` / `hpar` / `htime` / `hR`)
  of the conditional Duhamel output `hDuhamel_final` (`DuhamelLimitWiring`) via the ALREADY-LANDED
  differentiation engines.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT `a₁ = R/6`, and proves NOTHING about
  `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET (the four "F2-regularity" carries of `DuhamelLimitWiring.hDuhamel_final`).

    `hFII`  : `∀ u ∈ U, IntervalIntegrable (fun s => ∫ z, H (u−s) 0 z · F s z 0) volume 0 u`;
    `hpar`  : `∀ᶠ m in atTop, ∀ u ∈ U,
                 HasDerivAt (fun a => heatConvFrozen H F a (u−ε_m) 0 0) (DaTrunc H F m u) u`;
    `htime` : `∀ᶠ m in atTop, ∀ u ∈ U,
                 HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
                   (∫ z, H (u−(u−ε_m)) 0 z · F (u−ε_m) z 0) (u−ε_m)`;
    `hR`    : `∀ᶠ m in atTop, ∀ u ∈ U,
                 HasFDerivAt (fun p : ℝ×ℝ => K p.1 p.2 − K p.1 (u−ε_m) − K u p.2) 0 (u, u−ε_m)`
                 with `K x y := heatConvFrozen H F x y 0 0`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (this file, ns `QIQTH.HeatResidualBound`).

    (R4) `heatConvInner_intervalIntegrable_H` — `hFII` OUTRIGHT, over `U`.  A thin lift of the landed
         F1 domination `heatConvInner_intervalIntegrable_gaussianDom` (the Chapman–Kolmogorov collapse
         `(3/2)(u−s)+2s ≥ (3/2)u`) at each `u ∈ U`.  CONDITIONAL only on the base `s`-measurability
         carry `hMeasFII` (deferred measurability family) + the D1/width-2 dominations; the DOMINATION
         is discharged.

    (R1) `htime_pointwise` / `htime_discharge` — `htime`.  The FTC upper-limit derivative at the gap
         `tt = u − ε_m` (inner time `ε_m > 0`, REGULAR) via `intervalIntegral.integral_hasDerivAt_right`:
         `IntervalIntegrable` on `[0, u−ε_m]` (from `hFII` restricted, `IntervalIntegrable.mono_set`)
         + local continuity at the interior gap point (from the carried `ContinuousOn (0,u)` family,
         `hInnerCont`).  Threaded eventually-in-`m` from a uniform floor on `U` (`epsSeq → 0`).

    (R2) `hpar_pointwise` / `hpar_discharge` — `hpar`.  The frozen-upper-limit parameter derivative via
         the C3ε under-integral engine `heatConv_hasDerivAt_underIntegral`: the frozen convolution is
         `DifferentiableAt u`, so `DifferentiableAt.hasDerivAt` gives `HasDerivAt _ (deriv _) u`, and
         `DaTrunc H F m u := deriv (…) u` DEFINITIONALLY, so the derivative slot is `DaTrunc` for free.
         Carries the genuine C3ε differentiation-under-∫ inputs on `∂_r H` (measurability / base &
         derivative integrability / uniform integrable derivative bound / pointwise `HasDerivAt`
         family) — regular because at the gap `a − s ≥ ε_m > 0`.

    (R3) `hR_of_crossBound` / `hR_discharge` — `hR`.  The moving-corner remainder is first-order
         negligible.  With `K x y := heatConvFrozen H F x y 0 0`, the mixed second difference
         `D(h,k) := K(a+h,b+k) − K(a+h,b) − K(a,b+k) + K(a,b)` satisfies `|D(h,k)| ≤ L·|h|·|k|`
         (the carried cross-Lipschitz `hCross`, satisfiable from the `∂_τ H` bound + segment MVT), and
         `L|h||k| ≤ L‖(h,k)‖² = o(‖(h,k)‖)`, so `HasFDerivAt (fun p => K p.1 p.2 − K p.1 b − K a p.2)
         0 (a,b)` by `hasFDerivAt_iff_isLittleO_nhds_zero`.  The little-o from the quadratic bound is
         done here; only the mixed-difference bound is carried.

    (R5) `hDuhamel_final_of_f2carries` — the F2 GROUP CLOSED into the consumer: threads R4/R2/R1/R3
         into the `hFII`/`hpar`/`htime`/`hR` slots of `DuhamelLimitWiring.hDuhamel_final`, leaving the
         Duhamel output conditional only on the NON-F2 carries (the `boundary_tendstoLocallyUniformlyOn`
         interface + the hard loc-unif `Da`-limit `hDaLimLU`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — the carries (each a genuine analytic fact, NONE the conclusion, none vacuous).

    R4  : `hMeasFII` (base `s`-measurability) + D1/width-2 dominations `hAdom`/`hAzero`/`hBdom`.
    R1  : `hInnerCont` (continuity of the inner `s`-pairing on the OPEN `(0,u)`, where every inner time
          is positive — the deferred continuity family), a uniform floor `hUfloor` on `U`, and `hFII`.
    R2  : the C3ε engine interface on `∂_r H` (`hFmeas`/`hFint`/`hF'meas`/`hbdd`/`hbound`/`hdiff`,
          neighborhood `nb`, dominator `bound`) — the away-from-singularity under-integral Leibniz.
    R3  : `hCross` (the mixed second-difference `≤ L|h||k|`) + `L ≥ 0` — the cross-Lipschitz bound.

    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.DuhamelLimitWiring
import QIQTH.HeatConvRegularity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.LaplaceBeltrami
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### R4 — `hFII`: interval-integrability of the `H*F` pairing over `U`.
    ############################################################################### -/

/-- **★ J4-145 (R4) — `hFII` OUTRIGHT.**  For Gaussian-dominated kernels `H` (D1, vanishing at
    nonpositive time) and `F` (width-2 on `(0,T]`), the inner `s`-pairing
        `s ↦ ∫ z, H (u−s) 0 z · F s z 0`
    is `IntervalIntegrable` on `[0,u]` for every `u ∈ U`.  A thin lift over `U` of the landed F1
    domination `heatConvInner_intervalIntegrable_gaussianDom` (the Chapman–Kolmogorov collapse
    `(3/2)(u−s)+2s ≥ (3/2)u`).  ⚠ CONDITIONAL only on the base `s`-measurability carry `hMeasFII`
    (deferred measurability family); the DOMINATION is discharged.  NOT `a₁ = R/6`. -/
theorem heatConvInner_intervalIntegrable_H
    (H F : ℝ → Point n → Point n → ℝ) (T : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, H (u - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 u))) :
    ∀ u ∈ U, IntervalIntegrable (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 u := by
  intro u hu
  exact heatConvInner_intervalIntegrable_gaussianDom H F u T (hUpos u hu) (hUT u hu)
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom (hMeasFII u hu)

/-! ###############################################################################
    ### R1 — `htime`: the FTC upper-limit derivative at the gap.
    ############################################################################### -/

/-- **★ J4-145 (R1, pointwise) — `htime` AT A FIXED `(m,u)`.**  With the outer time FROZEN at `u`,
    the frozen convolution `tt ↦ heatConvFrozen H F u tt 0 0 = ∫ s in 0..tt, ∫ z, H (u−s) 0 z · F s z 0`
    has, at the interior gap point `tt = u − ε_m` (`0 < ε_m < u`), the FTC upper-limit derivative
        `∫ z, H (u−(u−ε_m)) 0 z · F (u−ε_m) z 0`.
    Via `intervalIntegral.integral_hasDerivAt_right`: interval-integrability on `[0, u−ε_m]` (from the
    `[0,u]` carry `hII`, restricted by `IntervalIntegrable.mono_set`) + local continuity of the inner
    `s`-pairing at the interior gap point (from the carried `ContinuousOn (0,u)` family `hInnerCont`,
    a genuine deferred-continuity carry, NOT the conclusion). -/
theorem htime_pointwise
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ) (m : ℕ)
    (hgap : epsSeq m < u)
    (hII : IntervalIntegrable (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 u)
    (hInnerCont : ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u)) :
    HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
      (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0) (u - epsSeq m) := by
  have hpos := epsSeq_pos m
  have hu0 : (0 : ℝ) < u := lt_trans hpos hgap
  have hb0 : (0 : ℝ) < u - epsSeq m := by linarith
  have hmem : (u - epsSeq m) ∈ Set.Ioo (0 : ℝ) u := ⟨hb0, by linarith⟩
  have hnbhd : Set.Ioo (0 : ℝ) u ∈ 𝓝 (u - epsSeq m) := isOpen_Ioo.mem_nhds hmem
  -- interval-integrability on the sub-interval `[0, u − ε_m] ⊆ [0, u]`.
  have hsub : Set.uIcc (0 : ℝ) (u - epsSeq m) ⊆ Set.uIcc 0 u := by
    rw [Set.uIcc_of_le hb0.le, Set.uIcc_of_le hu0.le]
    exact Set.Icc_subset_Icc_right (by linarith)
  have hII' : IntervalIntegrable (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m) :=
    hII.mono_set hsub
  -- FTC upper-limit derivative at the interior gap point.
  have hd := intervalIntegral.integral_hasDerivAt_right hII'
    (hInnerCont.stronglyMeasurableAtFilter isOpen_Ioo (u - epsSeq m) hmem)
    (hInnerCont.continuousAt hnbhd)
  exact hd

/-- **★★ J4-145 (R1) — `htime` DISCHARGED (eventual-in-`m`, ∀ `u ∈ U`).**  Threads `htime_pointwise`
    over `U`, eventually in `m`: with a uniform floor `c > 0` below `U` and `epsSeq → 0`, eventually
    `ε_m < c ≤ u` for every `u ∈ U`, so the gap is positive and interior.  Produces the verbatim
    `htime` carry of `DuhamelLimitWiring.hDuhamel_final`.  ⚠ CONDITIONAL on `hFII` (R4), the carried
    inner-continuity family `hInnerCont`, and the floor; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem htime_discharge
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hFII : ∀ u ∈ U, IntervalIntegrable (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u)) :
    ∀ᶠ m in atTop, ∀ u ∈ U,
      HasDerivAt (fun tt => heatConvFrozen H F u tt 0 0)
        (∫ z, H (u - (u - epsSeq m)) 0 z * F (u - epsSeq m) z 0) (u - epsSeq m) := by
  obtain ⟨c, hc, hcU⟩ := hUfloor
  have hev : ∀ᶠ m in atTop, epsSeq m < c := epsSeq_tendsto.eventually (eventually_lt_nhds hc)
  filter_upwards [hev] with m hm
  intro u hu
  have hgap : epsSeq m < u := lt_of_lt_of_le hm (hcU u hu)
  exact htime_pointwise H F u m hgap (hFII u hu) (hInnerCont u hu)

/-! ###############################################################################
    ### R2 — `hpar`: the frozen-upper-limit parameter derivative.
    ############################################################################### -/

/-- **★ J4-145 (R2, pointwise) — `hpar` AT A FIXED `(m,u)`.**  With the outer upper limit FROZEN at
    `u − ε_m`, the frozen convolution `a ↦ heatConvFrozen H F a (u−ε_m) 0 0` is `DifferentiableAt u`
    (the C3ε under-integral engine `heatConv_hasDerivAt_underIntegral` fires, since at the gap
    `a − s ≥ ε_m > 0` the `∂_r H`-domination is regular); hence `DifferentiableAt.hasDerivAt` gives
    `HasDerivAt _ (deriv _) u`, and `DaTrunc H F m u := deriv (…) u` DEFINITIONALLY, so the derivative
    slot is exactly `DaTrunc`.  Carries the genuine C3ε differentiation-under-∫ inputs on `∂_r H`;
    none is the conclusion. -/
theorem hpar_pointwise
    (H F : ℝ → Point n → Point n → ℝ) (u : ℝ) (m : ℕ)
    (nb : Set ℝ) (hnb : nb ∈ 𝓝 u)
    (hFmeas : ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 (u - epsSeq m))
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a) :
    HasDerivAt (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) (DaTrunc H F m u) u := by
  have hHD := heatConv_hasDerivAt_underIntegral H
    (fun τ p q => deriv (fun r => H r p q) τ) F u (u - epsSeq m) 0 0 nb hnb
    hFmeas hFint hF'meas bound hbdd hbound hdiff
  have hdiffAt : DifferentiableAt ℝ (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) u :=
    hHD.differentiableAt
  exact hdiffAt.hasDerivAt

/-- **★★ J4-145 (R2) — `hpar` DISCHARGED (eventual-in-`m`, ∀ `u ∈ U`).**  Threads `hpar_pointwise`
    over `U` (∀ `m`; no floor needed — the C3ε engine fires at any frozen upper limit).  Produces the
    verbatim `hpar` carry of `DuhamelLimitWiring.hDuhamel_final`.  ⚠ CONDITIONAL on the per-`(m,u)`
    C3ε engine families (`nb`/`bound`/`hFmeas`/`hFint`/`hF'meas`/`hbdd`/`hbound`/`hdiff`); none is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem hpar_discharge
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bound : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (bound m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ bound m u s)
    (hdiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a) :
    ∀ᶠ m in atTop, ∀ u ∈ U,
      HasDerivAt (fun a => heatConvFrozen H F a (u - epsSeq m) 0 0) (DaTrunc H F m u) u := by
  refine Filter.Eventually.of_forall (fun m => ?_)
  intro u hu
  exact hpar_pointwise H F u m (nb m u) (hnb m u hu) (hFmeas m u hu) (hFint m u hu)
    (hF'meas m u hu) (bound m u) (hbdd m u hu) (hbound m u hu) (hdiff m u hu)

/-! ###############################################################################
    ### R3 — `hR`: the moving-corner remainder little-o.
    ############################################################################### -/

/-- **★ J4-145 (R3, abstract) — MIXED-DIFFERENCE ⟹ `HasFDerivAt 0`.**  For a scalar two-variable
    kernel `K : ℝ → ℝ → ℝ`, a base corner `(a,b)`, and a constant `L ≥ 0`, if the mixed second
    difference is cross-controlled,
        `|K(a+h,b+k) − K(a+h,b) − K(a,b+k) + K(a,b)| ≤ L·(|h|·|k|)`   (`hCross`),
    then the moving-corner remainder `p ↦ K p.1 p.2 − K p.1 b − K a p.2` has Fréchet derivative `0` at
    `(a,b)`.  ROUTE: `hasFDerivAt_iff_isLittleO_nhds_zero`; the increment is exactly the mixed
    difference `D(v.1,v.2)`, bounded by `L·|v.1|·|v.2| ≤ L·‖v‖² = o(‖v‖)` (`Asymptotics.isLittleO_iff`
    + the quadratic-vs-linear collapse `L‖v‖·‖v‖ ≤ c‖v‖` for `‖v‖ < c/(L+1)`).  `hCross` is the only
    carry (the cross-Lipschitz mixed-difference bound); it is NOT the conclusion. -/
theorem hR_of_crossBound (K : ℝ → ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hCross : ∀ h k : ℝ,
      |K (a + h) (b + k) - K (a + h) b - K a (b + k) + K a b| ≤ L * (|h| * |k|)) :
    HasFDerivAt (fun p : ℝ × ℝ => K p.1 p.2 - K p.1 b - K a p.2)
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) (a, b) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hLp : (0 : ℝ) < L + 1 := by positivity
  have hball : ∀ᶠ v in 𝓝 (0 : ℝ × ℝ), ‖v‖ < c / (L + 1) := by
    have hmem := Metric.ball_mem_nhds (0 : ℝ × ℝ) (by positivity : (0 : ℝ) < c / (L + 1))
    filter_upwards [hmem] with v hv
    simpa only [mem_ball_zero_iff] using hv
  filter_upwards [hball] with v hv
  -- reduce the increment to the mixed difference `D(v.1, v.2)`.
  have hv1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs, Prod.norm_def]; exact le_max_left _ _
  have hv2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs, Prod.norm_def]; exact le_max_right _ _
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hprod : ‖v‖ * (L + 1) < c := (lt_div_iff₀ hLp).mp hv
  have hLv : L * ‖v‖ ≤ c := by nlinarith [hnv, hL]
  have hEq : ((fun p : ℝ × ℝ => K p.1 p.2 - K p.1 b - K a p.2) ((a, b) + v)
        - (fun p : ℝ × ℝ => K p.1 p.2 - K p.1 b - K a p.2) (a, b)
        - (0 : (ℝ × ℝ) →L[ℝ] ℝ) v)
      = K (a + v.1) (b + v.2) - K (a + v.1) b - K a (b + v.2) + K a b := by
    simp only [Prod.fst_add, Prod.snd_add, ContinuousLinearMap.zero_apply, sub_zero]
    ring
  rw [hEq, Real.norm_eq_abs]
  calc |K (a + v.1) (b + v.2) - K (a + v.1) b - K a (b + v.2) + K a b|
      ≤ L * (|v.1| * |v.2|) := hCross v.1 v.2
    _ ≤ L * (‖v‖ * ‖v‖) := by gcongr
    _ ≤ c * ‖v‖ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hLv hnv

/-- **★★ J4-145 (R3) — `hR` DISCHARGED (eventual-in-`m`, ∀ `u ∈ U`).**  Threads `hR_of_crossBound`
    with `K x y := heatConvFrozen H F x y 0 0`, base corner `(u, u−ε_m)`, over `U` (∀ `m`).  The
    resulting `HasFDerivAt` function `p ↦ K p.1 p.2 − K p.1 (u−ε_m) − K u p.2` matches the `hR` carry
    of `DuhamelLimitWiring.hDuhamel_final` VERBATIM.  ⚠ CONDITIONAL on the carried cross-Lipschitz
    mixed-difference family `hCross` (satisfiable from the `∂_τ H`-domination + segment MVT at the
    gap); none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hR_discharge
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (L : ℕ → ℝ → ℝ) (hL : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen H F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen H F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen H F u (u - epsSeq m + k) 0 0
          + heatConvFrozen H F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|)) :
    ∀ᶠ m in atTop, ∀ u ∈ U,
      HasFDerivAt (fun p : ℝ × ℝ =>
          heatConvFrozen H F p.1 p.2 0 0 - heatConvFrozen H F p.1 (u - epsSeq m) 0 0
            - heatConvFrozen H F u p.2 0 0) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m) := by
  refine Filter.Eventually.of_forall (fun m => ?_)
  intro u hu
  exact hR_of_crossBound (fun x y => heatConvFrozen H F x y 0 0) u (u - epsSeq m)
    (L m u) (hL m u hu) (hCross m u hu)

/-! ###############################################################################
    ### R5 — the F2 group closed into the Duhamel consumer.
    ############################################################################### -/

/-- **★★★ J4-145 (R5) — THE F2 GROUP CLOSED INTO `hDuhamel_final`.**  The Duhamel-principle output
        `heatOp g gi (fun u p q => heatConv H F u p q) t 0 0 = F t 0 0 + heatConv (heatOp g gi H) F t 0 0`,
    with the four F2-regularity carries of `DuhamelLimitWiring.hDuhamel_final` DISCHARGED in place
    (R4 → `hFII`, R2 → `hpar`, R1 → `htime`, R3 → `hR`).  The remaining hypotheses are the NON-F2
    inputs: the `boundary_tendstoLocallyUniformlyOn` interface (near-diagonal parametrix + dominations
    + measurability/continuity) and the hard locally-uniform `Da`-limit `hDaLimLU`.  ⚠ STILL
    CONDITIONAL on those + the F2-discharge carries (floor / inner-continuity / C3ε engine families /
    cross-Lipschitz); NOT `a₁ = R/6`. -/
theorem hDuhamel_final_of_f2carries (g gi : Point n → Fin n → Fin n → ℝ)
    (H F : ℝ → Point n → Point n → ℝ) (t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        H τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn (fun x : ℝ × Point n => F x.1 x.2 0) (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => H τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    -- F2-discharge carries (R4):
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, H (u - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 u)))
    -- F2-discharge carries (R1):
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u))
    -- F2-discharge carries (R2):
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a, AEStronglyMeasurable
      (fun s => ∫ z, H (a - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      ‖∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a ∈ nb m u,
      HasDerivAt (fun a => ∫ z, H (a - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (a - s) * F s z 0) a)
    -- F2-discharge carries (R3):
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen H F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen H F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen H F u (u - epsSeq m + k) 0 0
          + heatConvFrozen H F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the remaining hard limit (NOT F2):
    (hDaLimLU : TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
        (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0
              + heatConv (heatOp g gi H) F u 0 0) atTop U) :
    heatOp g gi (fun u p q => heatConv H F u p q) t 0 0
      = F t 0 0 + heatConv (heatOp g gi H) F t 0 0 := by
  have hFII := heatConvInner_intervalIntegrable_H H F T U hUpos hUT A₀ A₁ C_L hA₀ hA₁ hC_L
    hAdom hAzero hBdom hMeasFII
  have hpar := hpar_discharge H F U nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
  have htime := htime_discharge H F U hUfloor hFII hInnerCont
  have hR := hR_discharge H F U L hLnn hCross
  exact hDuhamel_final g gi H F t T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀
    u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd A₀ A₁ hA₀ hA₁ hAdom C_L hC_L hBdom hBcont
    hAmeas hBmeas hu₀meas hu₁meas hFII hpar htime hR hDaLimLU

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.heatConvInner_intervalIntegrable_H
#print axioms QIQTH.HeatResidualBound.htime_pointwise
#print axioms QIQTH.HeatResidualBound.htime_discharge
#print axioms QIQTH.HeatResidualBound.hpar_pointwise
#print axioms QIQTH.HeatResidualBound.hpar_discharge
#print axioms QIQTH.HeatResidualBound.hR_of_crossBound
#print axioms QIQTH.HeatResidualBound.hR_discharge
#print axioms QIQTH.HeatResidualBound.hDuhamel_final_of_f2carries
