/-
  CConvV2GaussianPairing — J4-323 (facade-v2 brick 2 of 14): the GAUSSIAN-PAIRING integrability that
  DISCHARGES the V2 source contract's `hFpair` from a source Gaussian bound.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It proves the
  scalar Gaussian-pairing analysis behind `CConvV2Contracts.CConvSourceDataV2.hFpair`.  NO `sorry`
  (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis in this
  file's own theorems, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ANALYTIC CORE.  Given a source Gaussian bound
      `|F s z| ≤ CF · s^γ · gaussDdim (cF·s) z`   (γ > −1, cF > 0),
  the paired integrand of `hFpair`,
      `g(s) := (t−s)^{−1/2} · ∫ z, gaussDdim (2(t−s)) z · |F s z| dz`,
  is `IntegrableOn (Ioc 0 t)`.  The `s`-UNIFORM control comes from the Gaussian PRODUCT integral:
      `∫ z, gaussDdim a z · gaussDdim b z dz = gaussDdim (a+b) 0`
  (obtained from the banked CONVOLUTION semigroup `GaussianConvolution.gaussDdim_conv` at `x=y=0` via
  origin-evenness `gaussDdim_zero_sub`), and `gaussDdim (a+b) 0 = (√(4π(a+b)))⁻ⁿ` is ANTITONE in
  `a+b`.  With `a = 2(t−s)`, `b = cF·s`, one has `a+b ≥ (min 2 cF)·t` on `(0,t)`, so the pairing
  integral is bounded by the `s`-INDEPENDENT constant `K := gaussDdim ((min 2 cF)·t) 0`.  Hence
      `g(s) ≤ CF·K · s^γ · (t−s)^{−1/2}`,
  the Beta-type integrand `s^γ·(t−s)^{−1/2}` (integrable on `(0,t)` for γ > −1 by the split at `t/2`).

  ## WHICH SUB-PIECES LANDED (per the SOL brick-2 plan P1–P5).
    • (P1/P2) `gaussDdim_pairing_integral` — the pairing integral `= gaussDdim (a+b) 0` (NO separate
      product-identity + mass-one needed: the banked convolution `gaussDdim_conv` supplies it directly).
    • (P2-value) `gaussDdim_zero` / `gaussDdim_zero_antitone` — `gaussDdim τ 0 = (√(4πτ))⁻ⁿ`, antitone
      in `τ > 0` (the `s`-uniform Gaussian bound).
    • (P3) `abLower` — `(min 2 cF)·t ≤ 2(t−s) + cF·s` on `0 ≤ s ≤ t`.
    • (P4) `betaPow_integrableOn` — `IntegrableOn (s ↦ s^γ·(t−s)^{−1/2}) (Ioc 0 t)` for γ > −1
      (elementary split at `t/2` via `intervalIntegrable_rpow'` + `mul_continuousOn`/`continuousOn_mul`).
    • (P5) `sourcePair_of_gaussian_bound` — the assembly.  The parametric-integral MEASURABILITY of
      `g` (`hgMeas`) is CARRIED as an honest satisfiable side hypothesis (true for `F ≡ 0` — the
      integrand collapses to `0`; in general it follows from the joint measurability of `F`).  This is
      the sole carried input; the analytic content (domination + `s`-uniform Gaussian bound + Beta
      integrability) is fully proven.

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvV2Contracts
import QIQTH.GaussianConvolution
import QIQTH.ModelIntegrableW
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatResidualBound QIQTH.GaussianConvolution QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.CConvV2GaussianPairing

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — P2 (value): the Gaussian peak `gaussDdim τ 0 = (√(4πτ))⁻ⁿ` and its antitonicity.
    ############################################################################### -/

/-- **`gaussDdim_zero`.**  The `d`-dim Gaussian peak: `gaussDdim τ 0 = (√(4πτ))⁻ⁿ` (each of the `n`
    coordinate factors is `heatKernel1D τ 0 = (√(4πτ))⁻¹`).  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_zero (τ : ℝ) :
    gaussDdim τ (0 : Point n) = ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n := by
  have h1 : ∀ k : Fin n, heatKernel1D τ ((0 : Point n) k) = (Real.sqrt (4 * Real.pi * τ))⁻¹ := by
    intro k
    simp [heatKernel1D]
  calc gaussDdim τ (0 : Point n)
      = ∏ _k : Fin n, (Real.sqrt (4 * Real.pi * τ))⁻¹ := by
        simp only [gaussDdim]; exact Finset.prod_congr rfl (fun k _ => h1 k)
    _ = ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`gaussDdim_zero_antitone`.**  `gaussDdim · 0` is ANTITONE on `(0,∞)`: `0 < τ₀ ≤ τ ⟹
    gaussDdim τ 0 ≤ gaussDdim τ₀ 0`.  The larger width has the smaller peak `(√(4πτ))⁻ⁿ`.  This is
    the `s`-uniform Gaussian bound of the pairing integral.  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_zero_antitone (τ₀ τ : ℝ) (h0 : 0 < τ₀) (hle : τ₀ ≤ τ) :
    gaussDdim τ (0 : Point n) ≤ gaussDdim τ₀ (0 : Point n) := by
  rw [gaussDdim_zero, gaussDdim_zero]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hs0 : (0 : ℝ) < Real.sqrt (4 * Real.pi * τ₀) := Real.sqrt_pos.mpr (by positivity)
  have hsle : Real.sqrt (4 * Real.pi * τ₀) ≤ Real.sqrt (4 * Real.pi * τ) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hinv : (Real.sqrt (4 * Real.pi * τ))⁻¹ ≤ (Real.sqrt (4 * Real.pi * τ₀))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hs0 hsle
  exact pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hinv n

/-! ###############################################################################
    ### §2 — P1/P2: the Gaussian PRODUCT integral `∫ G_a · G_b = G_{a+b}(0)` + product integrability.
    ############################################################################### -/

/-- **`gaussDdim_pair_integrable`.**  The two-Gaussian PRODUCT `z ↦ gaussDdim a z · gaussDdim b z` is
    integrable (from the banked `gaussDdim_mul_integrable` at `x=y=0`, via origin-evenness).
    ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_pair_integrable (a b : ℝ) :
    Integrable (fun z : Point n => gaussDdim a z * gaussDdim b z) volume := by
  have h := gaussDdim_mul_integrable a b (0 : Point n) (0 : Point n)
  refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [gaussDdim_zero_sub, sub_zero]

/-- **★ `gaussDdim_pairing_integral` (P1/P2).**  The Gaussian PRODUCT integral equals the peak of the
    combined width:
        `∫ z, gaussDdim a z · gaussDdim b z dz = gaussDdim (a+b) 0`   (`a, b > 0`).
    Derived from the banked CONVOLUTION semigroup `gaussDdim_conv` at `x = y = 0` (`∫ G_a(0−z)·G_b(z−0)
    = G_{a+b}(0)`) using origin-evenness `gaussDdim_zero_sub` (`G_a(0−z) = G_a z`).  ⚠ NOT `a₁ = R/6`. -/
theorem gaussDdim_pairing_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ z : Point n, gaussDdim a z * gaussDdim b z) = gaussDdim (a + b) (0 : Point n) := by
  have hconv := gaussDdim_conv a b ha hb (0 : Point n) (0 : Point n)
  rw [sub_self] at hconv
  rw [← hconv]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [gaussDdim_zero_sub, sub_zero]

/-! ###############################################################################
    ### §3 — P3: the combined-width lower bound `(min 2 cF)·t ≤ 2(t−s) + cF·s`.
    ############################################################################### -/

/-- **`abLower` (P3).**  On `0 ≤ s ≤ t`, the combined Gaussian width is bounded below `s`-uniformly:
        `(min 2 cF)·t ≤ 2·(t − s) + cF·s`.
    (`2(t−s) ≥ (min 2 cF)(t−s)` and `cF·s ≥ (min 2 cF)·s`, summed.)  ⚠ NOT `a₁ = R/6`. -/
theorem abLower (t cF s : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t) :
    min 2 cF * t ≤ 2 * (t - s) + cF * s := by
  have h2 : min 2 cF ≤ 2 := min_le_left _ _
  have hc : min 2 cF ≤ cF := min_le_right _ _
  have hts : 0 ≤ t - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hts, mul_le_mul_of_nonneg_right hc hs0]

/-! ###############################################################################
    ### §4 — P4: the Beta-type integrability `IntegrableOn (s ↦ s^γ·(t−s)^{−1/2}) (Ioc 0 t)`.
    ############################################################################### -/

/-- **★ `betaPow_integrableOn` (P4).**  For `t > 0`, `γ > −1`:
        `IntegrableOn (fun s ↦ s^γ · (t−s)^{−1/2}) (Ioc 0 t)`.
    Elementary split at `t/2`: on `[0, t/2]` the singular factor is `s^γ` (`intervalIntegrable_rpow'`)
    times the CONTINUOUS `(t−s)^{−1/2}` (`mul_continuousOn`); on `[t/2, t]` the singular factor is
    `(t−s)^{−1/2}` (`intervalIntegrable_rpow'` reflected by `comp_sub_left`) times the CONTINUOUS
    `s^γ` (`continuousOn_mul`).  ⚠ NOT `a₁ = R/6`. -/
theorem betaPow_integrableOn (t γ : ℝ) (ht : 0 < t) (hγ : -1 < γ) :
    IntegrableOn (fun s : ℝ => s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) (Set.Ioc 0 t) volume := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hr : (-1 : ℝ) < -(1 : ℝ) / 2 := by norm_num
  have ht2 : (0 : ℝ) ≤ t / 2 := by linarith
  -- segment 1: [0, t/2].  singular s^γ · continuous (t−s)^{−1/2}.
  have hseg1 : IntervalIntegrable (fun s : ℝ => s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) volume 0 (t / 2) := by
    refine IntervalIntegrable.mul_continuousOn (intervalIntegral.intervalIntegrable_rpow' hγ) ?_
    refine ContinuousOn.rpow_const ((continuous_const.sub continuous_id).continuousOn) ?_
    intro s hs
    rw [Set.uIcc_of_le ht2] at hs
    left
    have : s < t := lt_of_le_of_lt hs.2 (by linarith)
    exact sub_ne_zero.mpr (by linarith)
  -- segment 2: [t/2, t].  continuous s^γ · singular (t−s)^{−1/2}.
  have hseg2 : IntervalIntegrable (fun s : ℝ => s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) volume (t / 2) t := by
    have hf : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)) volume (t / 2) t := by
      have hbase : IntervalIntegrable (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) volume (t / 2) 0 :=
        intervalIntegral.intervalIntegrable_rpow' hr
      have h2 := hbase.comp_sub_left t
      rw [sub_zero, show t - t / 2 = t / 2 from by ring] at h2
      exact h2
    refine IntervalIntegrable.continuousOn_mul hf ?_
    refine ContinuousOn.rpow_const (continuous_id.continuousOn) ?_
    intro s hs
    rw [Set.uIcc_of_le (by linarith : t / 2 ≤ t)] at hs
    left
    exact ne_of_gt (by linarith [hs.1])
  exact hseg1.trans hseg2

/-! ###############################################################################
    ### §5 — P5: the assembly.  `hFpair` from the source Gaussian bound.
    ############################################################################### -/

/-- **★★★ `sourcePair_of_gaussian_bound` (P5) — the `hFpair` discharge.**  From a source Gaussian
    bound `|F s z| ≤ CF·s^γ·gaussDdim (cF·s) z` (γ > −1, cF > 0) and the (honest, satisfiable)
    parametric-integral measurability `hgMeas` of the paired integrand, the `hFpair` object is
    `IntegrableOn (Ioc 0 t)`:
        `fun s ↦ (t−s)^{−1/2} · ∫ z, gaussDdim (2(t−s)) z · |F s z| dz`.
    Route: dominate by `CF·K · s^γ · (t−s)^{−1/2}` where `K := gaussDdim ((min 2 cF)·t) 0` bounds the
    pairing integral `s`-uniformly (`gaussDdim_pairing_integral` + `gaussDdim_zero_antitone` + `abLower`),
    then invoke Beta integrability (`betaPow_integrableOn`).  `hgMeas` is the ONLY carried input (true
    for `F ≡ 0`); the analytic content is fully proven.  This is EXACTLY the `hFpair` field of
    `CConvV2Contracts.CConvSourceDataV2`.  ⚠ NOT `a₁ = R/6`. -/
theorem sourcePair_of_gaussian_bound
    (F : ℝ → Point n → ℝ) (t CF cF γ : ℝ)
    (ht : 0 < t) (hCF : 0 ≤ CF) (hcF : 0 < cF) (hγ : -1 < γ)
    (hgMeas : AEStronglyMeasurable
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 t)))
    (hF : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z, |F s z| ≤ CF * s ^ γ * gaussDdim (cF * s) z) :
    IntegrableOn
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      (Set.Ioc 0 t) (volume : Measure ℝ) := by
  set c₀ := min 2 cF with hc0def
  have hc0pos : 0 < c₀ := lt_min (by norm_num) hcF
  set K := gaussDdim (c₀ * t) (0 : Point n) with hKdef
  -- the dominating (Beta-type) function, integrable on `Ioc 0 t`.
  have hdom_int : IntegrableOn
      (fun s : ℝ => CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2))) (Set.Ioc 0 t) volume :=
    (betaPow_integrableOn t γ ht hγ).const_mul (CF * K)
  -- the pointwise domination on the interior `Ioo 0 t`.
  have hIoo : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖(t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n))‖
        ≤ CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    have hts : 0 < t - s := by linarith
    have ha : 0 < 2 * (t - s) := by linarith
    have hb : 0 < cF * s := mul_pos hcF hs0
    have hgauss_nonneg : ∀ z : Point n, 0 ≤ gaussDdim (2 * (t - s)) z :=
      fun z => gaussDdim_nonneg _ _
    have htsrpow : 0 ≤ (t - s) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hts.le _
    have hinner_nonneg :
        0 ≤ ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)) :=
      integral_nonneg (fun z => mul_nonneg (hgauss_nonneg z) (abs_nonneg _))
    -- dominating INTEGRAND (over `z`) and its `z`-integral.
    have hdomz_int : Integrable
        (fun z => (CF * s ^ γ) * (gaussDdim (2 * (t - s)) z * gaussDdim (cF * s) z))
        (volume : Measure (Point n)) :=
      (gaussDdim_pair_integrable (2 * (t - s)) (cF * s)).const_mul (CF * s ^ γ)
    have hle_z : ∀ z : Point n, gaussDdim (2 * (t - s)) z * |F s z|
        ≤ (CF * s ^ γ) * (gaussDdim (2 * (t - s)) z * gaussDdim (cF * s) z) := by
      intro z
      calc gaussDdim (2 * (t - s)) z * |F s z|
          ≤ gaussDdim (2 * (t - s)) z * (CF * s ^ γ * gaussDdim (cF * s) z) :=
            mul_le_mul_of_nonneg_left (hF s ⟨hs0, hst.le⟩ z) (hgauss_nonneg z)
        _ = (CF * s ^ γ) * (gaussDdim (2 * (t - s)) z * gaussDdim (cF * s) z) := by ring
    have hCFsγ_nonneg : 0 ≤ CF * s ^ γ := mul_nonneg hCF (Real.rpow_nonneg hs0.le _)
    have hinner_le :
        (∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
          ≤ CF * s ^ γ * K := by
      calc (∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
          ≤ ∫ z, (CF * s ^ γ) * (gaussDdim (2 * (t - s)) z * gaussDdim (cF * s) z)
              ∂(volume : Measure (Point n)) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun z => mul_nonneg (hgauss_nonneg z) (abs_nonneg _)))
              hdomz_int (Filter.Eventually.of_forall hle_z)
        _ = (CF * s ^ γ)
              * ∫ z, gaussDdim (2 * (t - s)) z * gaussDdim (cF * s) z
                  ∂(volume : Measure (Point n)) := by
            rw [integral_const_mul]
        _ = (CF * s ^ γ) * gaussDdim (2 * (t - s) + cF * s) (0 : Point n) := by
            rw [gaussDdim_pairing_integral (2 * (t - s)) (cF * s) ha hb]
        _ ≤ (CF * s ^ γ) * K := by
            refine mul_le_mul_of_nonneg_left ?_ hCFsγ_nonneg
            exact gaussDdim_zero_antitone (c₀ * t) (2 * (t - s) + cF * s)
              (mul_pos hc0pos ht) (by rw [hc0def]; exact abLower t cF s hs0.le hst.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htsrpow hinner_nonneg)]
    calc (t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n))
        ≤ (t - s) ^ (-(1 : ℝ) / 2) * (CF * s ^ γ * K) :=
          mul_le_mul_of_nonneg_left hinner_le htsrpow
      _ = CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by ring
  -- lift the pointwise bound to `a.e.` on `Ioc 0 t` (endpoint `{t}` is `volume`-null).
  have hvol_t : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton t
  have hdom_ae : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ioc 0 t)),
      ‖(t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (2 * (t - s)) z * |F s z| ∂(volume : Measure (Point n))‖
        ≤ CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hvol_t]
      with s hsIoc hsne
    exact hIoo s ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hsne⟩
  exact Integrable.mono' hdom_int hgMeas hdom_ae

end QIQTH.CConvV2GaussianPairing

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2GaussianPairing
#print axioms gaussDdim_zero
#print axioms gaussDdim_zero_antitone
#print axioms gaussDdim_pair_integrable
#print axioms gaussDdim_pairing_integral
#print axioms abLower
#print axioms betaPow_integrableOn
#print axioms sourcePair_of_gaussian_bound
end AxiomChecks
