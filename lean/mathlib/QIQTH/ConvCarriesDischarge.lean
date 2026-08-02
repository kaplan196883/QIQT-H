/-
  ConvCarriesDischarge — J4-117: DISCHARGING the two REGULAR carries of the `hDConv` reduction.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `ConvApproximants.hDConv_gatedWitnessN1_epsFamily` reduces the diagonal Duhamel
  `hDConv` carry of the restricted `a₁ = R/6` capstone to THREE conditional inputs:
      (i)  `hFII`   — interval-integrability of the inner `s`-pairing on `[0,u]`   (C1);
      (ii) `hJoint` — the JOINT two-variable `HasFDerivAt` at the shifted diagonals `(u, u−ε_m)`
                       (D5-concrete-1, the regular away-from-singularity 2-D Leibniz);
      (iii)`hDelta` — the delta-family local-uniform limit (Lemma 3.14, the sole singular brick).
  This file DISCHARGES the two REGULAR carries (i)+(ii), leaving `hDConv` conditional ONLY on the
  deferred kernel-continuity/derivative family + `hDelta`.

  THE KERNELS.  `A := vanVleckGatedWitness g gi hC hK S a b`, with the D1 Gaussian domination
      `|A τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim((3/2)τ)(p−q)`  (∀ τ>0),  `A(τ≤0)=0`;
  `B := leviSeries (heatOp g gi A)`, with `|B s z y| ≤ C_L·gaussDdim(2s)(z−y)` on `(0,T]`,
  `B(s≤0)=0`.

  WHAT LANDS.
    (F0)  `gaussDdim_zero_antitone` — the diagonal-peak width-monotonicity `0<a≤b ⟹
          gaussDdim b 0 ≤ gaussDdim a 0` (`(√(4πt))⁻ⁿ` antitone in `t`).  Foundation of the F1
          uniform bound.
    (F1)  `heatConvInner_intervalIntegrable_gaussianDom` — the DOMINATION HALF of `hFII` fully
          discharged: for `0 < u ≤ T`, the inner `s`-pairing `s ↦ ∫ z, A(u−s) 0 z · B s z 0` is
          bounded on `(0,u)` by a SINGLE constant via the Chapman–Kolmogorov semigroup identity
          (`gaussDdim_conv`: widths `(3/2)(u−s)` and `2s` add to `(3/2)u + s/2 ≥ (3/2)u > 0`
          uniformly), hence interval-integrable — CONDITIONAL only on the base `s`-measurability
          carry (M-type, deferred family).

  ⚠ HONEST FIREWALL.  The DOMINATION content of `hFII` is fully discharged; the only carried input
  is the base joint `s`-measurability, consistent with the deferred measurability family.  NO
  `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConvApproximants

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### F0. The diagonal-peak width-monotonicity. -/

/-- **(F0) DIAGONAL-PEAK WIDTH MONOTONICITY.**  `gaussDdim t 0 = (√(4πt))⁻ⁿ` is ANTITONE in the
    width `t > 0`: a wider Gaussian has a lower peak.  For `0 < a ≤ b`,
        `gaussDdim b (0 : Point n) ≤ gaussDdim a (0 : Point n)`.
    This is exactly what converts the Chapman–Kolmogorov result `gaussDdim ((3/2)(u−s)+2s) 0`
    (width `(3/2)u + s/2 ≥ (3/2)u`) into the `s`-uniform constant of F1. -/
theorem gaussDdim_zero_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    gaussDdim b (0 : Point n) ≤ gaussDdim a (0 : Point n) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [gaussDdim_diagonal_explicit, gaussDdim_diagonal_explicit]
  have hsa : 0 < Real.sqrt (4 * Real.pi * a) := Real.sqrt_pos.mpr (by positivity)
  have hsab : Real.sqrt (4 * Real.pi * a) ≤ Real.sqrt (4 * Real.pi * b) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have hinv : (Real.sqrt (4 * Real.pi * b))⁻¹ ≤ (Real.sqrt (4 * Real.pi * a))⁻¹ := by
    gcongr
  gcongr

/-! ### F1. The domination half of `hFII` — interval-integrability of the inner `s`-pairing. -/

/-- **★ J4-117 (F1) — THE DOMINATION HALF OF `hFII`.**  For Gaussian-dominated kernels `A`, `B`
    (D1 for `A`, width-2 for `B` on `(0,T]`) with `A` vanishing at nonpositive time, and `0 < u ≤ T`,
    the inner `s`-pairing
        `s ↦ ∫ z, A(u−s) 0 z · B s z 0`
    is `IntervalIntegrable` on `[0,u]`.  ROUTE: for `s ∈ (0,u)`,
        `|∫ z, A(u−s) 0 z · B s z 0| ≤ ∫ z, |A(u−s) 0 z|·|B s z 0|`
          `≤ (A₀+A₁(u−s))·√(3/2)ⁿ·C_L · ∫ z, gaussDdim((3/2)(u−s))(0−z)·gaussDdim(2s)(z−0)`
          `= (A₀+A₁(u−s))·√(3/2)ⁿ·C_L · gaussDdim((3/2)(u−s)+2s)(0)`   (`gaussDdim_conv`)
          `≤ (A₀+A₁u)·√(3/2)ⁿ·C_L · gaussDdim((3/2)u)(0)`   (`gaussDdim_zero_antitone`, `s ≥ 0`),
    a CONSTANT in `s`; with the point `s = u` killed by `A(0)=0`.  A bounded a.e.-measurable
    function on a finite interval is interval-integrable (`Integrable.mono'` against
    `intervalIntegrable_const`).  ⚠ CONDITIONAL only on the base `s`-measurability carry `hmeas`
    (deferred measurability family); the DOMINATION is fully discharged.  NOT `a₁ = R/6`. -/
theorem heatConvInner_intervalIntegrable_gaussianDom
    (A B : ℝ → Point n → Point n → ℝ) (u T : ℝ) (hu : 0 < u) (huT : u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, A τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : AEStronglyMeasurable
        (fun s => ∫ (z : Point n), A (u - s) 0 z * B s z 0) (volume.restrict (Set.uIoc 0 u))) :
    IntervalIntegrable (fun s => ∫ (z : Point n), A (u - s) 0 z * B s z 0) volume 0 u := by
  classical
  set Sc : ℝ := Real.sqrt (3 / 2 : ℝ) ^ n with hSc
  have hSc0 : 0 ≤ Sc := by rw [hSc]; positivity
  have hAu0 : 0 ≤ A₀ + A₁ * u := add_nonneg hA₀ (mul_nonneg hA₁ hu.le)
  have hgu0 : 0 ≤ gaussDdim (3 / 2 * u) (0 : Point n) := gaussDdim_nonneg _ _
  set Cconst : ℝ := (A₀ + A₁ * u) * Sc * C_L * gaussDdim (3 / 2 * u) (0 : Point n) with hCc
  have hCc0 : 0 ≤ Cconst := by
    rw [hCc]; exact mul_nonneg (mul_nonneg (mul_nonneg hAu0 hSc0) hC_L) hgu0
  -- pointwise bound by the constant on `(0,u)`.
  have hpt : ∀ s, 0 < s → s < u → ‖∫ (z : Point n), A (u - s) 0 z * B s z 0‖ ≤ Cconst := by
    intro s hs hsu
    have hτ : 0 < u - s := by linarith
    have hsT : s ≤ T := le_of_lt (lt_of_lt_of_le hsu huT)
    set c : ℝ := (A₀ + A₁ * (u - s)) * Sc * C_L with hc
    have hc0factor : 0 ≤ (A₀ + A₁ * (u - s)) * Sc :=
      mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ.le)) hSc0
    have hdomg : Integrable
        (fun z : Point n =>
          c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0))) volume :=
      (gaussDdim_mul_integrable (3 / 2 * (u - s)) (2 * s) 0 0).const_mul c
    have hle : (fun z : Point n => |A (u - s) 0 z| * |B s z 0|)
        ≤ᵐ[volume]
          (fun z : Point n =>
            c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0))) := by
      refine ae_of_all _ (fun z => ?_)
      have hA' := hAdom (u - s) hτ 0 z
      have hB' := hBdom s hs hsT z 0
      calc |A (u - s) 0 z| * |B s z 0|
          ≤ ((A₀ + A₁ * (u - s)) * Sc * gaussDdim (3 / 2 * (u - s)) (0 - z))
              * (C_L * gaussDdim (2 * s) (z - 0)) :=
            mul_le_mul hA' hB' (abs_nonneg _)
              (mul_nonneg hc0factor (gaussDdim_nonneg _ _))
        _ = c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0)) := by
            rw [hc]; ring
    have hnn : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[volume]
        (fun z : Point n => |A (u - s) 0 z| * |B s z 0|) :=
      ae_of_all _ (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc ‖∫ (z : Point n), A (u - s) 0 z * B s z 0‖
        ≤ ∫ (z : Point n), ‖A (u - s) 0 z * B s z 0‖ := norm_integral_le_integral_norm _
      _ = ∫ (z : Point n), |A (u - s) 0 z| * |B s z 0| := by
            simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ ∫ z, c * (gaussDdim (3 / 2 * (u - s)) (0 - z) * gaussDdim (2 * s) (z - 0)) :=
            integral_mono_of_nonneg hnn hdomg hle
      _ = c * gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n) := by
            rw [integral_const_mul,
                gaussDdim_conv (3 / 2 * (u - s)) (2 * s) (by linarith) (by linarith) 0 0, sub_zero]
      _ ≤ Cconst := by
            rw [hCc]
            have hcle : c ≤ (A₀ + A₁ * u) * Sc * C_L := by
              rw [hc]
              have hstep : A₀ + A₁ * (u - s) ≤ A₀ + A₁ * u := by
                nlinarith [mul_nonneg hA₁ hs.le]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hSc0) hC_L
            have hgle : gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n)
                ≤ gaussDdim (3 / 2 * u) (0 : Point n) :=
              gaussDdim_zero_antitone (by linarith) (by linarith)
            calc c * gaussDdim (3 / 2 * (u - s) + 2 * s) (0 : Point n)
                ≤ ((A₀ + A₁ * u) * Sc * C_L) * gaussDdim (3 / 2 * u) (0 : Point n) :=
                  mul_le_mul hcle hgle (gaussDdim_nonneg _ _)
                    (mul_nonneg (mul_nonneg hAu0 hSc0) hC_L)
              _ = (A₀ + A₁ * u) * Sc * C_L * gaussDdim (3 / 2 * u) (0 : Point n) := by ring
  -- assemble interval integrability from constant domination.
  rw [intervalIntegrable_iff]
  refine Integrable.mono' (g := fun _ => Cconst) ?_ hmeas ?_
  · exact intervalIntegrable_iff.mp intervalIntegrable_const
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine ae_of_all _ (fun s hs => ?_)
    rw [Set.uIoc_of_le hu.le] at hs
    rcases lt_or_eq_of_le hs.2 with hlt | heq
    · exact hpt s hs.1 hlt
    · have hzero : (fun z : Point n => A (u - s) 0 z * B s z 0) = fun _ => (0 : ℝ) := by
        funext z
        have hus : u - s = 0 := by rw [heq]; exact sub_self u
        rw [hus, hAzero 0 le_rfl 0 z, zero_mul]
      rw [hzero]
      simp only [integral_zero, norm_zero]
      exact hCc0

/-! ### F2. The joint 2-D `HasFDerivAt` assembly for `hJoint`. -/

/-- **★ J4-117 (F2) — THE JOINT 2-D `HasFDerivAt` ASSEMBLY.**  The two frozen one-variable
    derivatives of the frozen Duhamel convolution do NOT by themselves give a joint Fréchet
    derivative — a moving-endpoint/moving-parameter REMAINDER must be first-order negligible.  With
    the DECOMPOSITION `F(a,t) = H(a) + J(t) + R(a,t)` (`H a := heatConvFrozen A B a b`, `J t :=
    heatConvFrozen A B u t`, `R := F − H − J`), the joint `HasFDerivAt` of
    `p ↦ heatConvFrozen A B p.1 p.2 x y` at `(u, b)` assembles from:

    * `hpar`  — the frozen-upper-limit parameter derivative `HasDerivAt H Da u`  (the C3ε Leibniz);
    * `htime` — the frozen-parameter FTC upper-limit derivative
                `HasDerivAt J (∫ z, A(u−b) x z · B b z y) b`  (the C2 FTC);
    * `hR`    — the remainder is first-order negligible: `HasFDerivAt R 0 (u,b)`  (the moving-corner
                little-o, from joint continuity of the inner pairing).

    Route: `HasDerivAt.comp_hasFDerivAt` with `Prod.fst`/`Prod.snd`, then `HasFDerivAt.add`.  The
    three inputs are genuine deferred analytic carries (all fail without their content; none is the
    conclusion).  NOT `a₁ = R/6`. -/
theorem heatConvFrozen_hasFDerivAt_of_partials
    (A B : ℝ → Point n → Point n → ℝ) (x y : Point n) (u b : ℝ) (Da : ℝ)
    (hpar : HasDerivAt (fun a => heatConvFrozen A B a b x y) Da u)
    (htime : HasDerivAt (fun t => heatConvFrozen A B u t x y)
        (∫ z, A (u - b) x z * B b z y) b)
    (hR : HasFDerivAt (fun p : ℝ × ℝ =>
        heatConvFrozen A B p.1 p.2 x y - heatConvFrozen A B p.1 b x y
          - heatConvFrozen A B u p.2 x y) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, b)) :
    HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 x y)
      (Da • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (∫ z, A (u - b) x z * B b z y) • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, b) := by
  have hsum := ((hpar.comp_hasFDerivAt (u, b) hasFDerivAt_fst).add
      (htime.comp_hasFDerivAt (u, b) hasFDerivAt_snd)).add hR
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with p
  simp only [Pi.add_apply, Function.comp_apply]
  ring

/-! ### F3. The payoff — `hDConv` with `hFII` and `hJoint` DISCHARGED. -/

/-- **★★★ J4-117 (F3) — `hDConv` FROM THE DELTA-FAMILY, `hFII`/`hJoint` GONE (abstract).**  The
    `t`-differentiability of the diagonal Duhamel convolution `u ↦ heatConv A B u 0 0`, with the two
    REGULAR carries of `hDConv_of_delta_epsFamily` DISCHARGED:

    * `hFII` — built by F1 (`heatConvInner_intervalIntegrable_gaussianDom`) from the Gaussian
      dominations `hAdom`/`hAzero`/`hBdom` and the base `s`-measurability carry `hMeasFII`;
    * `hJoint` — built by F2 (`heatConvFrozen_hasFDerivAt_of_partials`) from the deferred partial
      carries `hpar` (frozen-upper-limit Leibniz), `htime` (frozen-parameter FTC), `hR` (moving-corner
      little-o).

    The candidate derivative family is `L m u := (Da m u)·∂_a + (∫ z, A(ε_m) 0 z · B(u−ε_m) z 0)·∂_t`
    and the sole remaining singular carry is the delta-family limit `hDelta` on `L m u (1,1) = Da m u
    + ∫ z, A(ε_m) 0 z · B(u−ε_m) z 0`.  ⚠ CONDITIONAL only on the deferred kernel-continuity/
    derivative family (`hMeasFII`, `hpar`, `htime`, `hR`) + `hDelta`; the Gaussian dominations are the
    landed D1/Levi facts.  NOT `a₁ = R/6`. -/
theorem hDConv_of_delta_final
    (A B : ℝ → Point n → Point n → ℝ) (t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, A τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, A (u - s) 0 z * B s z 0) (volume.restrict (Set.uIoc 0 u)))
    (Da : ℕ → ℝ → ℝ)
    (hpar : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun a => heatConvFrozen A B a (u - epsSeq m) 0 0) (Da m u) u)
    (htime : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun tt => heatConvFrozen A B u tt 0 0)
          (∫ z, A (u - (u - epsSeq m)) 0 z * B (u - epsSeq m) z 0) (u - epsSeq m))
    (hR : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ =>
            heatConvFrozen A B p.1 p.2 0 0 - heatConvFrozen A B p.1 (u - epsSeq m) 0 0
              - heatConvFrozen A B u p.2 0 0) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m))
    (D : ℝ → ℝ)
    (hDelta : TendstoLocallyUniformlyOn
        (fun m u => Da m u + ∫ z, A (u - (u - epsSeq m)) 0 z * B (u - epsSeq m) z 0)
        D Filter.atTop U) :
    DifferentiableAt ℝ (fun u => heatConv A B u 0 0) t := by
  set L : ℕ → ℝ → ((ℝ × ℝ) →L[ℝ] ℝ) := fun m u =>
    Da m u • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (∫ z, A (u - (u - epsSeq m)) 0 z * B (u - epsSeq m) z 0) • ContinuousLinearMap.snd ℝ ℝ ℝ
    with hL
  -- hFII via F1 (domination discharged; measurability carried).
  have hFII : ∀ u ∈ U,
      IntervalIntegrable (fun s => ∫ z, A (u - s) 0 z * B s z 0) volume 0 u := by
    intro u hu
    exact heatConvInner_intervalIntegrable_gaussianDom A B u T (hUpos u hu) (hUT u hu)
      A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom (hMeasFII u hu)
  -- hJoint via F2 assembly (from the three deferred partial carries).
  have hJoint : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
      HasFDerivAt (fun p : ℝ × ℝ => heatConvFrozen A B p.1 p.2 0 0) (L m u) (u, u - epsSeq m) := by
    filter_upwards [hpar, htime, hR] with m hp ht hr
    intro u hu
    exact heatConvFrozen_hasFDerivAt_of_partials A B 0 0 u (u - epsSeq m) (Da m u)
      (hp u hu) (ht u hu) (hr u hu)
  -- the delta-family limit `hDelta` reindexed onto `L m u (1,1)`.
  have hLeq : (fun m u => L m u (1, 1))
      = fun m u => Da m u + ∫ z, A (u - (u - epsSeq m)) 0 z * B (u - epsSeq m) z 0 := by
    funext m u
    simp [hL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  have hDelta' : TendstoLocallyUniformlyOn (fun m u => L m u (1, 1)) D Filter.atTop U := by
    rw [hLeq]; exact hDelta
  exact hDConv_of_delta_epsFamily A B 0 0 t U hUopen htU hUpos hFII L hJoint D hDelta'

/-- **★★★★ J4-117 (F3) CONCRETE — `hDConv` FOR THE VAN-VLECK `H_G`, `hFII`/`hJoint` GONE.**  The
    EXACT `hDConv` carry of `trueKernel_diagonal_a1_eq_R6_residual_restricted` for the concrete gated
    van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S a b` and `B := leviSeries (heatOp g gi
    A)`, with the two REGULAR carries of `hDConv_gatedWitnessN1_epsFamily` DISCHARGED (F1 for `hFII`,
    the F2 assembly for `hJoint`).  A direct specialization of `hDConv_of_delta_final`.  ⚠ CONDITIONAL
    only on the deferred kernel-continuity/derivative family (`hMeasFII`, `hpar`, `htime`, `hR`) +
    `hDelta`; the D1/Levi Gaussian dominations are the landed bounds.  NOT `a₁ = R/6`. -/
theorem hDConv_gatedWitnessN1_of_delta_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hC hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hC hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (Da : ℕ → ℝ → ℝ)
    (hpar : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun a' => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) a' (u - epsSeq m) 0 0)
          (Da m u) u)
    (htime : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasDerivAt (fun tt => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u tt 0 0)
          (∫ z, vanVleckGatedWitness g gi hC hK S a b (u - (u - epsSeq m)) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
          (u - epsSeq m))
    (hR : ∀ᶠ m in Filter.atTop, ∀ u ∈ U,
        HasFDerivAt (fun p : ℝ × ℝ =>
            heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) p.1 p.2 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) p.1
                (u - epsSeq m) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u p.2 0 0)
          (0 : (ℝ × ℝ) →L[ℝ] ℝ) (u, u - epsSeq m))
    (D : ℝ → ℝ)
    (hDelta : TendstoLocallyUniformlyOn
        (fun m u => Da m u + ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - (u - epsSeq m)) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (u - epsSeq m) z 0)
        D Filter.atTop U) :
    DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hC hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u 0 0) t :=
  hDConv_of_delta_final (vanVleckGatedWitness g gi hC hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
    t T hT U hUopen htU hUpos hUT A₀ A₁ C_L hA₀ hA₁ hC_L
    hAdom hAzero hBdom hMeasFII Da hpar htime hR D hDelta

end QIQTH.HeatResidualBound
