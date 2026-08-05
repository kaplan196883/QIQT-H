/-
  IterEEngineWiring — J4-290: the `iterE` engine WIRING (E4 + E5).  Threads the banked per-`E`
  Gaussian bounds, the model-side integrability, and the S1/`iterE` measurability into the
  `QIQTH.IterEContinuity` parametric-continuity engines, discharging the DERIVABLE half of the
  OUTER-engine slots (`hbound`, `hbnd_int`) at the actual convolution-step integrand and reducing
  the ALL-`k` termwise joint continuity of the iterated residual `iterE E` to two precisely-named
  honest carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity / wiring brick.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ── WHERE THIS SITS.  Everything the OUTER engine
     `IterEContinuity.iterE_succ_jointContinuousOn_of_dominated` consumes at rung `k` is one of four
     slots — `hmeas` (`u`-measurability), `hbound` (the `u`-envelope bound on `‖∫ w …‖`), `hbnd_int`
     (that envelope's `u`-integrability), `hcont` (a.e.-`u` inner joint continuity).  Two of them are
     DERIVABLE from the banked material and are BUILT here; the other two are genuine analytic carries.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * (W1) `convStepIntegrand_bound_wired` — the concrete pointwise `w`-integrand bound
        `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)`
      threaded at the actual `E` from the carried one-step width-`κ` bound `hEbound` and the banked
      iterated bound (`HeatResidualBound.iterConvW_bound`, fed `hEbound`+`hInt`), via
      `HeatOpWitnessContinuity.convStepIntegrand_pointwise_bound`.

    * (W3) `convStepIntegrand_aestronglyMeasurable` — the actual `w`-integrand
        `w ↦ E s₁ z w · iterE E k s₂ w 0`
      is `AEStronglyMeasurable`, from the single base joint measurability `hEmeas` of `E`
      (`HeatResidualBound.iterE_zmeas` for the `iterE` slice + `hEmeas`-composition for the `E` slice).

    * (W2) `convStepIntegrand_integrable` — the actual `w`-integrand is `Integrable`, by
      `Integrable.mono'` against the model dominator (integrable by
      `HeatResidualBound.modelZ_integrableW`) with the W1 pointwise bound and the W3 measurability.

    * (E5/hbound) `convStepIntegral_uEnvelope_bound` — ★★ the OUTER engine's `hbound` slot at the
      ACTUAL integrand: on the positive-time compact `s ∈ Icc t₁ t₂`, `z ∈ closedBall 0 R`, and
      `u ∈ (0,1)` (`s₁ = s − s·u`, `s₂ = s·u`),
        `‖∫ w, E (s−s·u) z w · iterE E k (s·u) w 0‖ ≤ M · u^(k−1)`,
        `M = C^(k+1)·(1/Γ(k))·t₂^(k−1)·gaussDdim (κ·t₁) 0`.
      Route: `norm_integral_le_of_norm_le` (against the model dominator, W1 pointwise) then
      `RDomEnvelope.convStepBound_uEnvelope_bound` (the dominator integral ≤ the `u`-only envelope).
      This is the genuine derivation that turns the pointwise bound into the parametric `hbound`.

    * (E5/step) `iterE_succ_jointContinuousOn_wired` — the OUTER-engine STEP at rung `k` with the two
      DERIVABLE slots FILLED: `hbnd_int` from `RDomEnvelope.uEnvelope_integrableOn`, `hbound` from
      `convStepIntegral_uEnvelope_bound`.  Consumes only the two honest carries `hmeas`/`hcont`.

    * (E4/E5/ALL) `iterE_jointContinuousOn_wired` — the ALL-`k` termwise joint continuity of
      `p ↦ iterE E (k+1) p.1 p.2 0`, feeding the BASE `hbase` (= the `E`-continuity, J4-288's chart-free
      capstone at the concrete gated van-Vleck witness) into `IterEContinuity.iterE_jointContinuousOn`
      with each rung's STEP discharged by `iterE_succ_jointContinuousOn_wired`.  Two per-level carries
      (`hmeas`, `hcont`) remain; neither is the conclusion.

    * `iterE_jointContinuousOn_concrete` — the same ALL-`k` output specialized to the concrete residual
      shape `E := heatOp g gi Wit` (the Levi residual, one heat operator past the witness kernel), for
      the direct `MovingCorrAssembly` M-test feed.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     The two OUTER-engine slots NOT built here (genuine analytic carries, threaded, both satisfiable
     and non-vacuous):
       (C-meas) `hmeas` — for each `p` on the compact, the `AEStronglyMeasurable`ity of the `u`-integral
                `u ↦ ∫ w, E (p.1−p.1·u) p.2 w · iterE E k (p.1·u) w 0` on `Ioc 0 1` (a Fubini
                `u`-measurability; dischargeable from the S1/`iterE_joint_stronglyMeasurable` machinery
                by a parametric-Fubini slice, not wired here);
       (C-cont) `hcont` — for a.e. `u`, the joint `(s,z)`-continuity of the inner spatial integral
                `p ↦ ∫ w, E (p.1−p.1·u) p.2 w · iterE E k (p.1·u) w 0` (the INNER-engine output, a
                genuinely RECURSIVE parametric-continuity brick).
     The DERIVABLE half — `hbound` (with the actual integrand) and `hbnd_int` — is fully PROVEN here.

     Also carried (all satisfiable at the concrete `E`, none the conclusion): `hEbound` (the width-`κ`
     one-step residual bound — the C4c far-field/off-diagonal wall), `hInt` (`IterConvIntegrableW`,
     dischargeable by `iterConvIntegrableW_of_bound_baseMeas`), `hEmeas` (base joint measurability,
     from `tripleHEmeas`/`Continuous.stronglyMeasurable`), and `hbase` (J4-288).

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RDomEnvelope
import QIQTH.ModelIntegrableW
import QIQTH.IterEMeasurable

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.TrueHeatKernel QIQTH.RDomEnvelope QIQTH.HeatOpWitnessContinuity QIQTH.IterEContinuity
open scoped Topology

namespace QIQTH.IterEEngineWiring

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (W1) The concrete pointwise `w`-integrand bound (banked bounds threaded at `E`).
    ############################################################################### -/

/-- **(W1) `convStepIntegrand_bound_wired`.**  The convolution-step pointwise `w`-integrand bound
        `|E s₁ z w · iterE E k s₂ w 0| ≤ (C·baseKernelW κ 0 s₁ z w)·(C^k·iterKernelW κ 0 k s₂ w 0)`
    threaded at the ACTUAL residual `E`: the one-step factor is the carried width-`κ` bound `hEbound`
    at `s₁`, the iterated factor is the banked `HeatResidualBound.iterConvW_bound` (fed `hEbound`+`hInt`)
    at `s₂`, combined by `HeatOpWitnessContinuity.convStepIntegrand_pointwise_bound` (the majorant
    one-step factor is `≥ 0` since `0 ≤ C` and `baseKernelW κ 0 = gaussDdim ≥ 0`).  Carried hypotheses
    are the banked residual bounds; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem convStepIntegrand_bound_wired
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C) (z w : Point n) :
    |E s₁ z w * iterE E k s₂ w 0|
      ≤ (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0) := by
  refine convStepIntegrand_pointwise_bound E κ C k s₁ s₂ z w (hEbound s₁ z w hs₁)
    (iterConvW_bound E κ 0 C hEbound hInt k hk s₂ hs₂ w 0) ?_
  exact mul_nonneg hC (by rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _)

/-! ###############################################################################
    ## (W3) The `w`-integrand joint measurability (from the single base measurability).
    ############################################################################### -/

/-- **(W3) `convStepIntegrand_aestronglyMeasurable`.**  The actual convolution-step `w`-integrand
        `w ↦ E s₁ z w · iterE E k s₂ w 0`
    is `AEStronglyMeasurable` for `volume`, from the single base joint measurability `hEmeas` of `E`:
    the `E`-slice `w ↦ E s₁ z w` is `hEmeas` composed with the measurable section `w ↦ (s₁, z, w)`; the
    `iterE`-slice `w ↦ iterE E k s₂ w 0` is `HeatResidualBound.iterE_zmeas`.  NOT `a₁ = R/6`. -/
theorem convStepIntegrand_aestronglyMeasurable
    (E : ℝ → Point n → Point n → ℝ) {k : ℕ} (hk : 1 ≤ k) (s₁ s₂ : ℝ)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (z : Point n) :
    AEStronglyMeasurable (fun w => E s₁ z w * iterE E k s₂ w 0) volume := by
  have hEsl : AEStronglyMeasurable (fun w : Point n => E s₁ z w) volume :=
    (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  exact hEsl.mul (iterE_zmeas E hEmeas k hk s₂ 0)

/-! ###############################################################################
    ## (W2) The `w`-integrability of the actual integrand (dominated by the model).
    ############################################################################### -/

/-- **(W2) `convStepIntegrand_integrable`.**  The actual convolution-step `w`-integrand
        `w ↦ E s₁ z w · iterE E k s₂ w 0`
    is `Integrable` for `volume`, by `Integrable.mono'` against the model Gaussian dominator
        `w ↦ C·baseKernelW κ 0 s₁ z w · (C^k·iterKernelW κ 0 k s₂ w 0)`,
    which is `Integrable` (`HeatResidualBound.modelZ_integrableW` at outer time `t = s₁ + s₂`, inner
    time `s₂`), with the W1 pointwise bound and the W3 measurability.  NOT `a₁ = R/6`. -/
theorem convStepIntegrand_integrable
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (z : Point n) :
    Integrable (fun w => E s₁ z w * iterE E k s₂ w 0) volume := by
  have hDint : Integrable
      (fun w => C * baseKernelW κ 0 s₁ z w * (C ^ k * iterKernelW κ 0 k s₂ w 0)) volume := by
    have h := modelZ_integrableW κ C hκ k hk (s₁ + s₂) (add_pos hs₁ hs₂) z 0 s₂
    have he : s₁ + s₂ - s₂ = s₁ := by ring
    rw [he] at h; exact h
  refine Integrable.mono' hDint
    (convStepIntegrand_aestronglyMeasurable E hk s₁ s₂ hEmeas z) ?_
  refine ae_of_all _ (fun w => ?_)
  rw [Real.norm_eq_abs]
  calc |E s₁ z w * iterE E k s₂ w 0|
      ≤ (C * baseKernelW κ 0 s₁ z w) * (C ^ k * iterKernelW κ 0 k s₂ w 0) :=
        convStepIntegrand_bound_wired E κ C hC hk hs₁ hs₂ hEbound hInt z w
    _ = C * baseKernelW κ 0 s₁ z w * (C ^ k * iterKernelW κ 0 k s₂ w 0) := by ring

/-! ###############################################################################
    ## (E5 / hbound) The OUTER engine's `u`-envelope bound at the actual integrand.
    ############################################################################### -/

/-- **★★ (E5/hbound) `convStepIntegral_uEnvelope_bound` — the actual `hbound` slot.**  On the
    positive-time compact `s ∈ Icc t₁ t₂` (`0 < t₁`), `z ∈ closedBall 0 R`, `u ∈ (0,1)` (rescaled times
    `s₁ = s − s·u`, `s₂ = s·u`, both `> 0`), the actual convolution-step `w`-integral is bounded by the
    `u`-only envelope:
        `‖∫ w, E (s−s·u) z w · iterE E k (s·u) w 0‖
           ≤ (C^(k+1)·(1/Γ(k))·t₂^(k−1)·gaussDdim (κ·t₁) 0) · u^(k−1)`.
    Route: `norm_integral_le_of_norm_le` (`‖∫ f‖ ≤ ∫ dominator` via the W1 pointwise bound), then
    `RDomEnvelope.convStepBound_uEnvelope_bound` (`∫ dominator ≤ the `u`-only envelope`).  This is EXACTLY
    the OUTER engine's `hbound` slot at the ACTUAL integrand — the genuine derivation from the pointwise
    bound.  Carried hypotheses are the banked residual bounds and positivity; none is the conclusion.
    NOT `a₁ = R/6`. -/
theorem convStepIntegral_uEnvelope_bound
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    {t₁ t₂ R : ℝ} (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    {s u : ℝ} (hs : s ∈ Set.Icc t₁ t₂) (hu0 : 0 < u) (hu1 : u < 1)
    (z : Point n) (hz : z ∈ Metric.closedBall (0 : Point n) R) :
    ‖∫ w, E (s - s * u) z w * iterE E k (s * u) w 0‖
      ≤ (C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * t₂ ^ ((k : ℝ) - 1)
          * gaussDdim (κ * t₁) (0 : Point n)) * u ^ ((k : ℝ) - 1) := by
  have hspos : 0 < s := lt_of_lt_of_le ht₁ hs.1
  have hs1 : 0 < s - s * u := by nlinarith [mul_pos hspos (by linarith : (0 : ℝ) < 1 - u)]
  have hs2 : 0 < s * u := mul_pos hspos hu0
  -- ‖∫ f‖ ≤ ∫ (model dominator)
  have hnorm : ‖∫ w, E (s - s * u) z w * iterE E k (s * u) w 0‖
      ≤ ∫ w, (C * baseKernelW κ 0 (s - s * u) z w) * (C ^ k * iterKernelW κ 0 k (s * u) w 0) := by
    have hDint : Integrable
        (fun w => (C * baseKernelW κ 0 (s - s * u) z w)
          * (C ^ k * iterKernelW κ 0 k (s * u) w 0)) volume := by
      have h := modelZ_integrableW κ C hκ k hk s hspos z 0 (s * u)
      have he : s - s * u = s - s * u := rfl
      -- rewrite the model's `t - s'` shape into our `s - s*u`
      have hcong : (fun w : Point n =>
            C * baseKernelW κ 0 (s - s * u) z w * (C ^ k * iterKernelW κ 0 k (s * u) w 0))
          = fun w : Point n =>
            (C * baseKernelW κ 0 (s - s * u) z w) * (C ^ k * iterKernelW κ 0 k (s * u) w 0) := by
        funext w; ring
      rw [hcong] at h; exact h
    refine norm_integral_le_of_norm_le hDint (ae_of_all _ (fun w => ?_))
    rw [Real.norm_eq_abs]
    exact convStepIntegrand_bound_wired E κ C hC hk hs1 hs2 hEbound hInt z w
  refine hnorm.trans ?_
  exact convStepBound_uEnvelope_bound κ C hκ hC hk ht₁ hs hu0 hu1 z hz

/-! ###############################################################################
    ## (E5 / step) The OUTER-engine STEP with the two derivable slots filled.
    ############################################################################### -/

/-- **(E5/step) `iterE_succ_jointContinuousOn_wired`.**  The OUTER-engine STEP
    (`IterEContinuity.iterE_succ_jointContinuousOn_of_dominated`) at rung `k`, with the two DERIVABLE
    slots FILLED at the concrete envelope `bnd u = M · u^(k−1)`:
      • `hbnd_int` ← `RDomEnvelope.uEnvelope_integrableOn`;
      • `hbound`   ← `convStepIntegral_uEnvelope_bound` (excluding the null endpoint `u = 1`).
    Consumes only the two honest carries: `hmeas` (the `u`-measurability) and `hcont` (the a.e.-`u`
    inner joint continuity).  Output: `ContinuousOn (fun p => iterE E (k+1) p.1 p.2 0)` on the compact.
    Neither carry is the conclusion.  NOT `a₁ = R/6`. -/
theorem iterE_succ_jointContinuousOn_wired
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) {k : ℕ} (hk : 1 ≤ k)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hmeas : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable
        (fun u => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0)
        (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcont : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E k (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine iterE_succ_jointContinuousOn_of_dominated E hk t₁ t₂ R
    (fun u => (C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * t₂ ^ ((k : ℝ) - 1)
        * gaussDdim (κ * t₁) (0 : Point n)) * u ^ ((k : ℝ) - 1))
    hmeas ?_
    (uEnvelope_integrableOn
      (C ^ (k + 1) * (1 / Real.Gamma (k : ℝ)) * t₂ ^ ((k : ℝ) - 1)
        * gaussDdim (κ * t₁) (0 : Point n)) hk)
    hcont
  -- the `hbound` slot: exclude the null endpoint `u = 1`, then apply the actual-integrand envelope.
  intro p hp
  have hne1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) := by
    refine ae_restrict_of_ae ?_
    have hmem : ({(1:ℝ)} : Set ℝ)ᶜ ∈ (ae volume) := by
      rw [mem_ae_iff, compl_compl, Real.volume_singleton]
    filter_upwards [hmem] with u hu
    simpa using hu
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with u hu hune
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
  exact convStepIntegral_uEnvelope_bound E κ C hκ hC hk ht₁ hEbound hInt hp.1 hu.1 hu1 p.2 hp.2

/-! ###############################################################################
    ## (E4 / E5 / ALL) The ALL-`k` termwise joint continuity (the M-test feed).
    ############################################################################### -/

/-- **(E4/E5/ALL) `iterE_jointContinuousOn_wired` — the M-test feed.**  `∀ k`, the joint `ContinuousOn`
    of `p ↦ iterE E (k+1) p.1 p.2 0` on `Icc t₁ t₂ ×ˢ closedBall 0 R`, feeding the BASE `hbase`
    (= the `E`-continuity; at the concrete residual this is J4-288's chart-free capstone) into
    `IterEContinuity.iterE_jointContinuousOn`, each rung's STEP discharged by
    `iterE_succ_jointContinuousOn_wired`.  The per-level honest carries `hmeas`/`hcont` (the
    `u`-measurability and the a.e.-`u` inner joint continuity) are the only remaining inputs; neither is
    the `∀ k` conclusion.  NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_wired
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW E κ 0 C)
    (hbase : ContinuousOn (fun p : ℝ × Point n => E p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hmeas : ∀ k : ℕ, ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable
        (fun u => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
        (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, E (p.1 - p.1 * u) p.2 w * iterE E (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × Point n => iterE E (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine iterE_jointContinuousOn E t₁ t₂ R hbase (fun k _ih => ?_)
  exact iterE_succ_jointContinuousOn_wired E κ C hκ hC (Nat.succ_le_succ (Nat.zero_le k))
    t₁ t₂ R ht₁ hEbound hInt (hmeas k) (hcont k)

/-- **`iterE_jointContinuousOn_concrete`.**  The ALL-`k` termwise joint continuity specialized to the
    concrete residual shape `E := heatOp g gi Wit` (the Levi residual — one heat operator past the
    witness kernel).  A direct specialization of `iterE_jointContinuousOn_wired`; the carried
    `hbase` is exactly J4-288's `heatOpGatedWitness_jointContinuousOn_chartFree` output at the concrete
    gated van-Vleck witness, `hEbound`/`hInt`/`hEmeas` its banked bounds/measurability.  This `∀ k`
    output is EXACTLY the `hterm` feed (modulo the harmless `(−1)^(k+1)` scalar) of
    `MovingCorrAssembly.leviSlice_jointContinuousOn_of_termwise`.  NOT `a₁ = R/6`. -/
theorem iterE_jointContinuousOn_concrete
    (g gi : Point n → Fin n → Fin n → ℝ) (Wit : ℝ → Point n → Point n → ℝ) (κ C : ℝ)
    (hκ : 0 < κ) (hC : 0 ≤ C) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hEbound : ∀ τ p q, 0 < τ → |heatOp g gi Wit τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi Wit) κ 0 C)
    (hbase : ContinuousOn (fun p : ℝ × Point n => heatOp g gi Wit p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hmeas : ∀ k : ℕ, ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      AEStronglyMeasurable
        (fun u => ∫ w, heatOp g gi Wit (p.1 - p.1 * u) p.2 w
          * iterE (heatOp g gi Wit) (k + 1) (p.1 * u) w 0)
        (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hcont : ∀ k : ℕ, ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
      ContinuousOn
        (fun p : ℝ × Point n => ∫ w, heatOp g gi Wit (p.1 - p.1 * u) p.2 w
          * iterE (heatOp g gi Wit) (k + 1) (p.1 * u) w 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ k : ℕ, ContinuousOn
      (fun p : ℝ × Point n => iterE (heatOp g gi Wit) (k + 1) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  iterE_jointContinuousOn_wired (heatOp g gi Wit) κ C hκ hC t₁ t₂ R ht₁ hEbound hInt hbase hmeas hcont

#check @convStepIntegrand_bound_wired
#check @convStepIntegrand_aestronglyMeasurable
#check @convStepIntegrand_integrable
#check @convStepIntegral_uEnvelope_bound
#check @iterE_succ_jointContinuousOn_wired
#check @iterE_jointContinuousOn_wired
#check @iterE_jointContinuousOn_concrete

end QIQTH.IterEEngineWiring

/-! ## Axiom checks — every theorem should be `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.IterEEngineWiring
#print axioms convStepIntegrand_bound_wired
#print axioms convStepIntegrand_aestronglyMeasurable
#print axioms convStepIntegrand_integrable
#print axioms convStepIntegral_uEnvelope_bound
#print axioms iterE_succ_jointContinuousOn_wired
#print axioms iterE_jointContinuousOn_wired
#print axioms iterE_jointContinuousOn_concrete
end AxiomChecks
