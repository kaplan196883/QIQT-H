/-
  RDomEnvelope — J4-289: the (R-dom) INTEGRAL-ENVELOPE construction for the convolution-step
  Gaussian dominator, feeding the OUTER parametric-continuity engine of `QIQTH.IterEContinuity`
  (J4-282) and, downstream, the Levi M-test of `QIQTH.MovingCorrAssembly` (J4-281).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  Gaussian integral-envelope (regularity / domination) brick.  No `sorry` (this header prose aside),
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or
  trivially yielding) the conclusion, no existing file edited.

  ── WHERE THIS SITS.  `HeatOpWitnessContinuity.convStepIntegrand_pointwise_bound` (J4-283) gives the
  POINTWISE `w`-integrand domination
        `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)`.
  The OUTER engine `IterEContinuity.heatConv_jointContinuousOn_of_dominated` then needs, over the
  fixed-domain `u`-integral (`s₁ = s − s·u`, `s₂ = s·u` after the `σ = s·u` rescale), an INTEGRABLE
  `u`-envelope `bnd : ℝ → ℝ` dominating `‖∫ w, E s₁ z w · iterE E k s₂ w 0‖`, uniformly in
  `z ∈ closedBall 0 R` and `s ∈ Icc t₁ t₂` (`0 < t₁`).  Building that envelope from the pointwise
  bound is the (R-dom) INTEGRAL-ENVELOPE remainder named in `HeatOpWitnessContinuity`'s residual —
  this file constructs it.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (E1) `iterKernelW_zero_apply` — the `α = 0` closed form of the iterated model kernel:
        `iterKernelW κ 0 k s w 0 = (1/Γ(k))·s^(k−1)·gaussDdim (κ·s) (w−0)`  (κ>0, k≥1, s>0).
      Instantiates the banked `GaussianWidthTolerant.iterKernelW_eq` at `α = 0` (Γ(1)=1, k·1=k).

    * (E1) `convStepBound_integral_eq` — ★ THE CHAPMAN–KOLMOGOROV INTEGRAL IDENTITY (the mission's
      MINIMUM BANKABLE).  For κ>0, k≥1, s₁,s₂>0,
        `∫ w, (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)
           = C^(k+1)·(1/Γ(k))·s₂^(k−1)·gaussDdim (κ·(s₁+s₂)) z`.
      Route: `baseKernelW_zero_apply` + `iterKernelW_zero_apply` reduce the integrand to a scalar times
      a two-Gaussian product; pull the scalar out (`integral_const_mul`); close the `w`-convolution with
      the width-`κ` semigroup `gaussDdim_conv_scaled` (variances add: `κs₁ + κs₂ = κ(s₁+s₂)`).

    * (E2) `convStepBound_integral_le_diagonal` — the `z`-uniform (peak) reduction: the same integral is
      `≤ C^(k+1)·(1/Γ(k))·s₂^(k−1)·gaussDdim (κ·(s₁+s₂)) 0`, via the Gaussian peak
      `gaussDdim t v ≤ gaussDdim t 0` (`gaussDdim_le_diagonal`).  This kills the `z`-dependence.

    * (E2/E3) `convStepBound_uEnvelope_bound` — ★★ THE `u`-ONLY ENVELOPE BOUND (hbound-ready).  On the
      compact `s ∈ Icc t₁ t₂` (`0 < t₁`), `u ∈ (0,1)`, `z ∈ closedBall 0 R`, with `s₁ = s − s·u`,
      `s₂ = s·u`,
        `∫ w, (C·baseKernelW κ 0 (s−s·u) z w)·(C^k·iterKernelW κ 0 k (s·u) w 0)
           ≤ (C^(k+1)·(1/Γ(k))·t₂^(k−1)·gaussDdim (κ·t₁) 0) · u^(k−1)`.
      Route: E2 with `s₁+s₂ = s`, then the width-antitone diagonal `gaussDdim (κs) 0 ≤ gaussDdim (κt₁) 0`
      (`gaussDdim_zero_antitone`, `t₁ ≤ s`) and `(s·u)^(k−1) ≤ (t₂·u)^(k−1) = t₂^(k−1)·u^(k−1)`
      (`Real.rpow_le_rpow`, `Real.mul_rpow`).  The RHS is `M · u^(k−1)` with `M` a `(s,z)`-free constant.

    * (E3) `uEnvelope_integrableOn` — ★ THE `u`-ENVELOPE INTEGRABILITY.  `u ↦ M·u^(k−1)` is
      `IntegrableOn (Ioc 0 1)` (bounded — `u^(k−1) ≤ 1` on `(0,1]` since `k−1 ≥ 0` — and
      continuous, on the finite-measure `Ioc 0 1`).  This is the OUTER engine's `hbnd_int` slot.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     (E4) the MEASURABILITY slots (`AEStronglyMeasurable` of the actual `w`- and `u`-integrands) are
       NOT built here — they need the banked witness/`iterE` measurability machinery (the S1 /
       tripleHEmeas slice lemmas), threaded at the wiring site.  Carried, not discharged.
     (E5) the FINAL ENGINE INSTANTIATION at `E := heatOp(witness)` — feeding
       `iterE_succ_jointContinuousOn_of_dominated` — additionally needs, for the ACTUAL integrand, the
       banked per-`E` bounds (`ParametrixHEboundWiring.iterConvW_bound`: `|E s₁ z w| ≤ C·baseKernelW …`,
       `|iterE E k s₂ w 0| ≤ C^k·iterKernelW …`) plus the integral-monotonicity bridge
       `‖∫ w, actual‖ ≤ ∫ w, dominator` (needs `w`-integrability of the actual integrand).  Those are
       genuine per-`E` carries, not built here.  E1–E3 supply the DOMINATOR side of that bridge
       (its value, its `z`/`s`-uniform envelope, and that envelope's `u`-integrability).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatOpWitnessContinuity
import QIQTH.GaussianWidthTolerant
import QIQTH.BoundaryAssembly
import QIQTH.ConvCarriesDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open scoped Topology

namespace QIQTH.RDomEnvelope

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (E1) The `α = 0` closed form of the iterated model kernel and the
    ##      Chapman–Kolmogorov integral identity of the dominator product.
    ############################################################################### -/

/-- **(E1) `iterKernelW_zero_apply`.**  The `α = 0` instance of `GaussianWidthTolerant.iterKernelW_eq`:
    for `κ > 0`, `k ≥ 1`, `s > 0`,
        `iterKernelW κ 0 k s w 0 = (1/Γ(k))·s^(k−1)·gaussDdim (κ·s) (w − 0)`.
    (`Γ(0+1)=Γ(1)=1`, `1^k=1`, `k·(0+1)=k`.)  Kept in the `(w − 0)` shape so the width-`κ`
    convolution semigroup `gaussDdim_conv_scaled` applies verbatim.  NOT `a₁ = R/6`. -/
theorem iterKernelW_zero_apply (κ : ℝ) (hκ : 0 < κ) {k : ℕ} (hk : 1 ≤ k)
    {s : ℝ} (hs : 0 < s) (w : Point n) :
    iterKernelW κ 0 k s w 0
      = (1 / Real.Gamma (k : ℝ)) * s ^ ((k : ℝ) - 1) * gaussDdim (κ * s) (w - 0) := by
  rw [iterKernelW_eq κ 0 hκ (by norm_num) s hs w 0 hk]
  simp only [zero_add, Real.Gamma_one, one_pow, mul_one]

/-- **(E1) ★ `convStepBound_integral_eq` — THE CHAPMAN–KOLMOGOROV INTEGRAL IDENTITY** (the mission's
    MINIMUM BANKABLE).  For `κ > 0`, `k ≥ 1`, `s₁, s₂ > 0`, the `w`-integral of the convolution-step
    Gaussian dominator product has the explicit closed form
        `∫ w, (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)
           = C^(k+1)·(1/Γ(k))·s₂^(k−1)·gaussDdim (κ·(s₁+s₂)) z`.
    Route: `baseKernelW_zero_apply` (base = Gaussian) + `iterKernelW_zero_apply` (iterated = scalar ·
    Gaussian) reduce the integrand to `[C^(k+1)·(1/Γ(k))·s₂^(k−1)] · (G_{κs₁}(z−w)·G_{κs₂}(w−0))`; pull
    the scalar out (`integral_const_mul`); close the `w`-convolution with the width-`κ` semigroup
    `gaussDdim_conv_scaled` (`κs₁ + κs₂ = κ(s₁+s₂)`).  Carried hypotheses are the genuine
    positivity/width inputs of the semigroup identity — none is the conclusion.  NOT `a₁ = R/6`. -/
theorem convStepBound_integral_eq
    (κ C : ℝ) (hκ : 0 < κ) {k : ℕ} (hk : 1 ≤ k) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (z : Point n) :
    (∫ w, (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0))
      = C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * s₂ ^ ((k : ℝ) - 1)
          * gaussDdim (κ * (s₁ + s₂)) z := by
  have hcong : ∀ w : Point n,
      (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0)
        = (C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * s₂ ^ ((k : ℝ) - 1))
            * (gaussDdim (κ * s₁) (z - w) * gaussDdim (κ * s₂) (w - 0)) := by
    intro w
    rw [baseKernelW_zero_apply, iterKernelW_zero_apply κ hκ hk hs₂ w]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hcong), integral_const_mul,
      gaussDdim_conv_scaled κ s₁ s₂ hκ hs₁ hs₂ z 0, sub_zero]

/-! ###############################################################################
    ## (E2) The `z`-uniform (peak) reduction.
    ############################################################################### -/

/-- **(E2) `convStepBound_integral_le_diagonal` — the `z`-uniform peak reduction.**  From E1 and the
    Gaussian peak `gaussDdim t v ≤ gaussDdim t 0` (`gaussDdim_le_diagonal`), the same integral is
    dominated, uniformly in `z`, by its diagonal value
        `∫ w, … ≤ C^(k+1)·(1/Γ(k))·s₂^(k−1)·gaussDdim (κ·(s₁+s₂)) 0`.
    Requires `0 ≤ C` (coefficient nonnegativity for the monotone multiply).  NOT `a₁ = R/6`. -/
theorem convStepBound_integral_le_diagonal
    (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (z : Point n) :
    (∫ w, (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0))
      ≤ C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * s₂ ^ ((k : ℝ) - 1)
          * gaussDdim (κ * (s₁ + s₂)) (0 : Point n) := by
  have hΓ : 0 < Real.Gamma (k : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (by omega : 0 < k))
  have hcoef : 0 ≤ C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * s₂ ^ ((k : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hC _) (one_div_nonneg.mpr hΓ.le))
      (Real.rpow_nonneg hs₂.le _)
  rw [convStepBound_integral_eq κ C hκ hk hs₁ hs₂ z]
  exact mul_le_mul_of_nonneg_left
    (gaussDdim_le_diagonal (mul_pos hκ (add_pos hs₁ hs₂)) z) hcoef

/-! ###############################################################################
    ## (E2/E3) The `u`-only envelope bound and its integrability.
    ############################################################################### -/

/-- **(E2/E3) ★★ `convStepBound_uEnvelope_bound` — THE `u`-ONLY ENVELOPE BOUND (hbound-ready).**  On
    the positive-time compact `s ∈ Icc t₁ t₂` (`0 < t₁`), `u ∈ (0,1)`, `z ∈ closedBall 0 R`, with the
    rescaled times `s₁ = s − s·u`, `s₂ = s·u`, the convolution-step dominator integral is bounded by an
    explicit `(s,z)`-FREE constant times `u^(k−1)`:
        `∫ w, (C·baseKernelW κ 0 (s−s·u) z w)·(C^k·iterKernelW κ 0 k (s·u) w 0)
           ≤ (C^(k+1)·(1/Γ(k))·t₂^(k−1)·gaussDdim (κ·t₁) 0) · u^(k−1)`.
    Route: E2 (peak, with `s₁+s₂ = s`), the width-antitone diagonal `gaussDdim (κs) 0 ≤ gaussDdim (κt₁) 0`
    (`gaussDdim_zero_antitone`, `κt₁ ≤ κs`) and `(s·u)^(k−1) ≤ (t₂·u)^(k−1) = t₂^(k−1)·u^(k−1)`
    (`Real.rpow_le_rpow` + `Real.mul_rpow`, `k−1 ≥ 0`).  This is EXACTLY the OUTER engine's `hbound`
    dominator (a `u`-only function).  Carried hypotheses are positivity/compactness inputs; none is the
    conclusion.  NOT `a₁ = R/6`. -/
theorem convStepBound_uEnvelope_bound
    (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    {t₁ t₂ R : ℝ} (ht₁ : 0 < t₁)
    {s u : ℝ} (hs : s ∈ Set.Icc t₁ t₂) (hu0 : 0 < u) (hu1 : u < 1)
    (z : Point n) (_hz : z ∈ Metric.closedBall (0 : Point n) R) :
    (∫ w, (C * baseKernelW κ 0 (s - s * u) z w) * (C ^ k * iterKernelW κ 0 k (s * u) w 0))
      ≤ (C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * t₂ ^ ((k : ℝ) - 1)
          * gaussDdim (κ * t₁) (0 : Point n)) * u ^ ((k : ℝ) - 1) := by
  have hspos : 0 < s := lt_of_lt_of_le ht₁ hs.1
  have ht₂ : 0 < t₂ := lt_of_lt_of_le hspos hs.2
  have hs1 : 0 < s - s * u := by
    nlinarith [mul_pos hspos (by linarith : (0 : ℝ) < 1 - u)]
  have hs2 : 0 < s * u := mul_pos hspos hu0
  have hΓ : 0 < Real.Gamma (k : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (by omega : 0 < k))
  have he : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hAnn : 0 ≤ C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) :=
    mul_nonneg (pow_nonneg hC _) (one_div_nonneg.mpr hΓ.le)
  -- the rescaled-time peak envelope
  have hstep1 :
      (∫ w, (C * baseKernelW κ 0 (s - s * u) z w) * (C ^ k * iterKernelW κ 0 k (s * u) w 0))
        ≤ C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * (s * u) ^ ((k : ℝ) - 1)
            * gaussDdim (κ * ((s - s * u) + s * u)) (0 : Point n) :=
    convStepBound_integral_le_diagonal κ C hκ hC hk hs1 hs2 z
  -- collapse `s₁ + s₂ = s` and majorize the two `s`/`z`-dependent factors
  have hsum : (s - s * u) + s * u = s := by ring
  rw [hsum] at hstep1
  refine hstep1.trans ?_
  -- `(s·u)^(k−1) ≤ (t₂·u)^(k−1)` and `gaussDdim (κs) 0 ≤ gaussDdim (κt₁) 0`
  have hbase_le : s * u ≤ t₂ * u := mul_le_mul_of_nonneg_right hs.2 hu0.le
  have hrpow_le : (s * u) ^ ((k : ℝ) - 1) ≤ (t₂ * u) ^ ((k : ℝ) - 1) :=
    Real.rpow_le_rpow hs2.le hbase_le he
  have hgauss_le : gaussDdim (κ * s) (0 : Point n) ≤ gaussDdim (κ * t₁) (0 : Point n) :=
    gaussDdim_zero_antitone (mul_pos hκ ht₁) (mul_le_mul_of_nonneg_left hs.1 hκ.le)
  have hmid :
      C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * (s * u) ^ ((k : ℝ) - 1)
          * gaussDdim (κ * s) (0 : Point n)
        ≤ C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * (t₂ * u) ^ ((k : ℝ) - 1)
            * gaussDdim (κ * t₁) (0 : Point n) := by
    refine mul_le_mul ?_ hgauss_le (gaussDdim_nonneg _ _) ?_
    · exact mul_le_mul_of_nonneg_left hrpow_le hAnn
    · exact mul_nonneg hAnn (Real.rpow_nonneg (by positivity) _)
  refine hmid.trans_eq ?_
  rw [Real.mul_rpow ht₂.le hu0.le]
  ring

/-- **(E3) ★ `uEnvelope_integrableOn` — the `u`-envelope integrability (hbnd_int slot).**  For any
    constant `M` and `k ≥ 1`, the envelope `u ↦ M·u^(k−1)` is `IntegrableOn (Ioc 0 1)`: on `(0,1]` it
    is continuous (`κ`-free base `> 0`) and bounded by `|M|` (since `0 ≤ u^(k−1) ≤ 1` for `k−1 ≥ 0`),
    on the finite-measure `Ioc 0 1`.  This is the OUTER engine's `hbnd_int` slot for the
    `convStepBound_uEnvelope_bound` dominator.  NOT `a₁ = R/6`. -/
theorem uEnvelope_integrableOn (M : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    IntegrableOn (fun u => M * u ^ ((k : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1) volume := by
  have he : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have hconst : IntegrableOn (fun _ : ℝ => |M|) (Set.Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine hconst.mono' ?_ ?_
  · -- AEStronglyMeasurable via continuity on `Ioc 0 1`
    have hcont : ContinuousOn (fun u : ℝ => u ^ ((k : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1) := by
      intro u hu
      exact (Real.continuousAt_rpow_const u ((k : ℝ) - 1)
        (Or.inl (ne_of_gt hu.1))).continuousWithinAt
    exact (continuousOn_const.mul hcont).aestronglyMeasurable measurableSet_Ioc
  · -- pointwise bound `‖M·u^(k−1)‖ ≤ |M|` on `Ioc 0 1`
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine ae_of_all _ (fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hue : |u ^ ((k : ℝ) - 1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hu.1.le _)]
      calc u ^ ((k : ℝ) - 1) ≤ (1 : ℝ) ^ ((k : ℝ) - 1) := Real.rpow_le_rpow hu.1.le hu.2 he
        _ = 1 := Real.one_rpow _
    calc |M| * |u ^ ((k : ℝ) - 1)| ≤ |M| * 1 := mul_le_mul_of_nonneg_left hue (abs_nonneg _)
      _ = |M| := mul_one _

#check @iterKernelW_zero_apply
#check @convStepBound_integral_eq
#check @convStepBound_integral_le_diagonal
#check @convStepBound_uEnvelope_bound
#check @uEnvelope_integrableOn

end QIQTH.RDomEnvelope

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.RDomEnvelope
#print axioms iterKernelW_zero_apply
#print axioms convStepBound_integral_eq
#print axioms convStepBound_integral_le_diagonal
#print axioms convStepBound_uEnvelope_bound
#print axioms uEnvelope_integrableOn
end AxiomChecks
