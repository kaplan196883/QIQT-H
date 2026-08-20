/-
  GaussTauTraceChartTransported — the ABSTRACT composition of residues (a) + (b) of the chart-CoV
  cancellation route: the UNIFORM (bounded-horizon) FLAT TWO-TERM Gaussian census bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the follow-on to J4-923's
  `gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz`.  It COMPOSES the two obligations that
  J4-923's honest report flagged before the chart-CoV route can discharge `hGpow`/`hCross`:
    (a) the FULL PAIRED WEIGHT `q₁` (post-CoV: `A(Vw)·F(s,·)(Vw)/|det DW₀(w)|`) is bounded + center-
        Lipschitz on an inner ball — here reduced to the ALGEBRAIC fact that a PRODUCT of bounded +
        center-Lipschitz-at-0 factors is bounded + center-Lipschitz-at-0 (`product_center_lipschitz`,
        `product3_center_lipschitz`), with a constant that is τ-UNIFORM iff the factor constants are;
    (b) the ZEROTH-ORDER term `q₂` (post-CoV: `Cfield(Vw)·F/|det|`) is `O(1)` in τ (bounded Gaussian
        mass), hence `≤ √T·τ^{−1/2}` on a bounded horizon `0 < τ ≤ T`.
  The capstone `two_term_census_bound_uniform` glues J4-923 (term 1) + the Gaussian-mass bound (term 2)
  + the super-polynomial tail absorption (`e^{−r²/8τ}/τ ≤ 8/r²`, via `Real.add_one_le_exp`) into a
  single `O(τ^{−1/2})` bound on `0 < τ ≤ T`, with a τ-INDEPENDENT constant.

  ## WHAT THIS DOES — AND DOES NOT — UNBLOCK (gpt-5.6-sol audit, verbatim honest).
  This isolates residues (a)+(b) as REUSABLE analytic lemmas and REDUCES `hGpow` to exactly the
  GEOMETRIC per-factor facts it does NOT prove: `A∘V` center-Lipschitz, `F∘V` center-Lipschitz,
  `1/|det f'|∘V` center-Lipschitz + bounded, `W₀∘V = id` on `Ω` (recoverable from the banked left
  inverse), `MeasurableSet Ω`, and the uniform per-factor constants.  It does NOT close `hGpow`/`hCross`.
  The likely remaining geometric bottleneck (Sol) is proving `1/|det f'|∘V` center-Lipschitz.

  ## WHAT LANDS.
    • `product_center_lipschitz` — ★ (a) two-factor: for `f,h` globally bounded (`|f|≤M_f`,`|h|≤M_h`) and
        center-Lipschitz at `0` on `ball 0 r` (`|f w − f 0|≤L_f‖w‖`, likewise `h`), the product `f·h` is
        globally bounded by `M_f·M_h` and center-Lipschitz at `0` with constant `M_f·L_h + M_h·L_f`.
    • `product3_center_lipschitz` — ★ (a) three-factor (the exact `A·F·(1/|det|)` shape), by chaining.
    • `two_term_census_bound_uniform` — ★★ (a)+(b) COMPOSED.  For `0<τ≤T`, `q₁` measurable+bounded(`M₁`)+
        center-Lipschitz(`L`) on `ball 0 r`, `q₂` measurable+bounded(`M₂`), and measurable `Ω⊇ball 0 r`:
          `|∫_{z∈Ω} (∑ᵢ((zᵢ)²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{z∈Ω} gaussDdim τ z·q₂ z|`
            `≤ L·(n²(16√2+1))/√τ  +  (3n·M₁·√2ⁿ·(4(2n+1)/r²) + M₂)·(√T/√τ)` .
    • `two_term_census_bound_uniform_combined` — the same, folded to the single `Cpair/√τ` shape
        (`Cpair` τ-independent) that `hGpow`'s `∃Cpair, |·|≤Cpair·(u−s)^{−1/2}` consumes.
    • `..._hyp_satisfiable` witnesses (non-vacuity, TEETH inherited from J4-923's center-Lipschitz-but-
        NOT-globally-Lipschitz weight `sin(‖z‖²)`).

  ⚠  STILL NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none equal
  to the conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.GaussTauTraceCancellationInnerBall
import QIQTH.DeltaFamilyBoundary
import QIQTH.ResidueBound

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — (a): the ALGEBRAIC product-of-center-Lipschitz-bounded core.
    ############################################################################### -/

/-- **★ `product_center_lipschitz` — (a), two-factor.**  For `f,h : Point n → ℝ` globally bounded
    (`|f z|≤M_f`, `|h z|≤M_h`, constants `≥0`) and CENTER-Lipschitz at `0` on `ball 0 r`
    (`|f w − f 0| ≤ L_f·‖w‖`, likewise `h`), the product `f·h` is globally bounded by `M_f·M_h` and
    CENTER-Lipschitz at `0` with constant `M_f·L_h + M_h·L_f`.  τ-uniform iff the inputs are (they carry
    no `τ`).  Pure real analysis (`add-and-subtract` + `abs_mul`).  NOT `a₁ = R/6`. -/
theorem product_center_lipschitz (r : ℝ) (f h : Point n → ℝ)
    (M_f M_h L_f L_h : ℝ) (hMf : 0 ≤ M_f) (hMh : 0 ≤ M_h)
    (hfbnd : ∀ z, |f z| ≤ M_f) (hhbnd : ∀ z, |h z| ≤ M_h)
    (hfcl : ∀ z ∈ Metric.ball (0 : Point n) r, |f z - f 0| ≤ L_f * ‖z‖)
    (hhcl : ∀ z ∈ Metric.ball (0 : Point n) r, |h z - h 0| ≤ L_h * ‖z‖) :
    (∀ z, |f z * h z| ≤ M_f * M_h) ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        |f z * h z - f 0 * h 0| ≤ (M_f * L_h + M_h * L_f) * ‖z‖) := by
  refine ⟨fun z => ?_, fun z hz => ?_⟩
  · -- product bound
    rw [abs_mul]
    exact mul_le_mul (hfbnd z) (hhbnd z) (abs_nonneg _) hMf
  · -- product center-Lipschitz
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have key : f z * h z - f 0 * h 0 = f z * (h z - h 0) + h 0 * (f z - f 0) := by ring
    rw [key]
    calc |f z * (h z - h 0) + h 0 * (f z - f 0)|
        ≤ |f z * (h z - h 0)| + |h 0 * (f z - f 0)| := abs_add_le _ _
      _ = |f z| * |h z - h 0| + |h 0| * |f z - f 0| := by rw [abs_mul, abs_mul]
      _ ≤ M_f * (L_h * ‖z‖) + M_h * (L_f * ‖z‖) := by
          apply add_le_add
          · exact mul_le_mul (hfbnd z) (hhcl z hz) (abs_nonneg _) hMf
          · exact mul_le_mul (hhbnd 0) (hfcl z hz) (abs_nonneg _) hMh
      _ = (M_f * L_h + M_h * L_f) * ‖z‖ := by ring

/-- **★ `product3_center_lipschitz` — (a), three-factor (the `A·F·(1/|det|)` shape).**  Chains
    `product_center_lipschitz` twice.  For `f,h,k` globally bounded + center-Lipschitz at `0` on
    `ball 0 r`, the triple product `f·h·k` is bounded by `M_f·M_h·M_k` and center-Lipschitz at `0` with
    constant `(M_f·M_h)·L_k + M_k·(M_f·L_h + M_h·L_f)`.  NOT `a₁ = R/6`. -/
theorem product3_center_lipschitz (r : ℝ) (f h k : Point n → ℝ)
    (M_f M_h M_k L_f L_h L_k : ℝ) (hMf : 0 ≤ M_f) (hMh : 0 ≤ M_h) (hMk : 0 ≤ M_k)
    (hfbnd : ∀ z, |f z| ≤ M_f) (hhbnd : ∀ z, |h z| ≤ M_h) (hkbnd : ∀ z, |k z| ≤ M_k)
    (hfcl : ∀ z ∈ Metric.ball (0 : Point n) r, |f z - f 0| ≤ L_f * ‖z‖)
    (hhcl : ∀ z ∈ Metric.ball (0 : Point n) r, |h z - h 0| ≤ L_h * ‖z‖)
    (hkcl : ∀ z ∈ Metric.ball (0 : Point n) r, |k z - k 0| ≤ L_k * ‖z‖) :
    (∀ z, |f z * h z * k z| ≤ M_f * M_h * M_k) ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        |f z * h z * k z - f 0 * h 0 * k 0|
          ≤ ((M_f * M_h) * L_k + M_k * (M_f * L_h + M_h * L_f)) * ‖z‖) := by
  obtain ⟨hfh_bnd, hfh_cl⟩ :=
    product_center_lipschitz r f h M_f M_h L_f L_h hMf hMh hfbnd hhbnd hfcl hhcl
  exact product_center_lipschitz r (fun z => f z * h z) k (M_f * M_h) M_k (M_f * L_h + M_h * L_f) L_k
    (mul_nonneg hMf hMh) hMk hfh_bnd hkbnd hfh_cl hkcl

/-! ###############################################################################
    ### §B — (a)+(b) COMPOSED: the uniform flat two-term Gaussian census bound.
    ############################################################################### -/

/-- **★★ `two_term_census_bound_uniform` — (a)+(b) COMPOSED (bounded-horizon, τ-UNIFORM constant).**
    For `0 < τ ≤ T`, `r > 0`, `q₁` measurable + globally bounded (`|q₁|≤M₁`) + CENTER-Lipschitz (`L`)
    on `ball 0 r`, `q₂` measurable + globally bounded (`|q₂|≤M₂`), and ANY measurable `Ω ⊇ ball 0 r`:
      `|∫_{z∈Ω}(∑ᵢ((zᵢ)²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{z∈Ω} gaussDdim τ z·q₂ z|`
        `≤ L·(n²(16√2+1))/√τ  +  (3n·M₁·√2ⁿ·(4(2n+1)/r²) + M₂)·(√T/√τ)` .
    Term 1 = J4-923's `gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz` with the tail
    `3n·M₁·√2ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)` absorbed into `3n·M₁·√2ⁿ·(4(2n+1)/r²)` via `e^{−a/τ}/τ ≤ 1/a`
    (`Real.add_one_le_exp`).  Term 2 = the `O(1)` Gaussian-mass bound `|∫_Ω G·q₂| ≤ M₂`, promoted to
    `M₂·√T/√τ` by `1 ≤ √T/√τ` (`τ ≤ T`).  Both terms `O(τ^{−1/2})`, constant τ-independent.
    NOT `a₁ = R/6`. -/
theorem two_term_census_bound_uniform
    (τ r T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T) (hr : 0 < r)
    (q₁ q₂ : Point n → ℝ)
    (L M₁ M₂ : ℝ) (hL : 0 ≤ L) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hq₁meas : AEStronglyMeasurable q₁ volume) (hq₂meas : AEStronglyMeasurable q₂ volume)
    (hq₁bnd : ∀ z, |q₁ z| ≤ M₁) (hq₂bnd : ∀ z, |q₂ z| ≤ M₂)
    (hcl : ∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖)
    (Ω : Set (Point n)) (hΩ : MeasurableSet Ω) (hball : Metric.ball (0 : Point n) r ⊆ Ω) :
    |(∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
        + (∫ z in Ω, gaussDdim τ z * q₂ z)|
      ≤ L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ
        + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂)
            * (Real.sqrt T / Real.sqrt τ) := by
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hr0 : r ≠ 0 := hr.ne'
  -- ═══ TERM 1 (J4-923). ═══
  have hA := gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz
    τ r hτ hr q₁ L hL hq₁meas M₁ hq₁bnd hcl Ω hΩ hball
  -- ═══ TERM 2: the `O(1)` Gaussian-mass bound `|∫_Ω G·q₂| ≤ M₂`. ═══
  have hGq2 : Integrable (fun z : Point n => gaussDdim τ z * q₂ z) volume := by
    refine Integrable.mono' ((gaussDdim_integrable τ hτ).mul_const M₂)
      ((gaussDdim_integrable τ hτ).aestronglyMeasurable.mul hq₂meas)
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ z)]
    exact mul_le_mul_of_nonneg_left (hq₂bnd z) (gaussDdim_nonneg τ z)
  have hB : |∫ z in Ω, gaussDdim τ z * q₂ z| ≤ M₂ := by
    have h1 : |∫ z in Ω, gaussDdim τ z * q₂ z| ≤ ∫ z in Ω, |gaussDdim τ z * q₂ z| := by
      have := norm_integral_le_integral_norm (μ := volume.restrict Ω)
        (f := fun z => gaussDdim τ z * q₂ z)
      simpa only [Real.norm_eq_abs] using this
    have h2 : (∫ z in Ω, |gaussDdim τ z * q₂ z|) ≤ ∫ z in Ω, gaussDdim τ z * M₂ := by
      refine setIntegral_mono_on hGq2.abs.integrableOn
        ((gaussDdim_integrable τ hτ).mul_const M₂).integrableOn hΩ (fun z _ => ?_)
      rw [abs_mul, abs_of_nonneg (gaussDdim_nonneg τ z)]
      exact mul_le_mul_of_nonneg_left (hq₂bnd z) (gaussDdim_nonneg τ z)
    have h4 : (∫ z in Ω, gaussDdim τ z) ≤ ∫ z, gaussDdim τ z :=
      setIntegral_le_integral (gaussDdim_integrable τ hτ)
        (Filter.Eventually.of_forall (fun z => gaussDdim_nonneg τ z))
    calc |∫ z in Ω, gaussDdim τ z * q₂ z|
        ≤ ∫ z in Ω, |gaussDdim τ z * q₂ z| := h1
      _ ≤ ∫ z in Ω, gaussDdim τ z * M₂ := h2
      _ = (∫ z in Ω, gaussDdim τ z) * M₂ := by rw [integral_mul_const]
      _ ≤ 1 * M₂ :=
          mul_le_mul_of_nonneg_right (h4.trans (le_of_eq (gaussDdim_integral_eq_one τ hτ))) hM₂
      _ = M₂ := one_mul M₂
  -- ═══ TAIL ABSORPTION: `e^{−a/τ}·(1/(2τ)) ≤ 4/r²` uniformly on `τ > 0`. ═══
  have hexp : Real.exp (-(r ^ 2) / (8 * τ)) ≤ 8 * τ / r ^ 2 := by
    have ha : (0 : ℝ) < r ^ 2 / (8 * τ) := by positivity
    have hax : r ^ 2 / (8 * τ) ≤ Real.exp (r ^ 2 / (8 * τ)) := by
      have := Real.add_one_le_exp (r ^ 2 / (8 * τ)); linarith
    have hneg : -(r ^ 2) / (8 * τ) = -(r ^ 2 / (8 * τ)) := by ring
    rw [hneg, Real.exp_neg]
    have h1 : (Real.exp (r ^ 2 / (8 * τ)))⁻¹ ≤ (r ^ 2 / (8 * τ))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le ha hax
    rw [inv_div] at h1
    exact h1
  have hE : Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))
      ≤ 4 * (2 * (n : ℝ) + 1) / r ^ 2 := by
    have hfrac_nn : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) / (2 * τ) := by positivity
    calc Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))
        ≤ (8 * τ / r ^ 2) * ((2 * (n : ℝ) + 1) / (2 * τ)) :=
          mul_le_mul_of_nonneg_right hexp hfrac_nn
      _ = 4 * (2 * (n : ℝ) + 1) / r ^ 2 := by field_simp; ring
  have htail :
      3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
          * ((2 * (n : ℝ) + 1) / (2 * τ)))
        ≤ 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) := by
    have h0 : (0 : ℝ) ≤ 3 * (n : ℝ) * M₁ := mul_nonneg (by positivity) hM₁
    have hs2 : (0 : ℝ) ≤ Real.sqrt 2 ^ n := by positivity
    apply mul_le_mul_of_nonneg_left _ h0
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hE hs2
  -- ═══ HORIZON PROMOTION: `1 ≤ √T/√τ`. ═══
  have hge1 : 1 ≤ Real.sqrt T / Real.sqrt τ := by
    have h := Real.sqrt_le_sqrt hτT
    calc (1 : ℝ) = Real.sqrt τ / Real.sqrt τ := (div_self hsτ.ne').symm
      _ ≤ Real.sqrt T / Real.sqrt τ := by gcongr
  have hCt : (0 : ℝ) ≤ 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) :=
    mul_nonneg (mul_nonneg (by positivity) hM₁) (by positivity)
  have hCtM : (0 : ℝ) ≤ 3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂ :=
    add_nonneg hCt hM₂
  have hmul :
      3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂
        ≤ (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂)
            * (Real.sqrt T / Real.sqrt τ) :=
    le_mul_of_one_le_right hCtM hge1
  -- ═══ COMBINE. ═══
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add hA hB) ?_
  linarith [htail, hmul]

/-- **★★ `two_term_census_bound_uniform_combined` — the single `Cpair/√τ` shape for `hGpow`.**  Folds
    the two `O(τ^{−1/2})` terms of `two_term_census_bound_uniform` into `Cpair/√τ` with the τ-INDEPENDENT
      `Cpair := L·(n²(16√2+1)) + (3n·M₁·√2ⁿ·(4(2n+1)/r²) + M₂)·√T ≥ 0` .
    This is the exact shape `hGpow`'s `∃ Cpair ≥ 0, |·| ≤ Cpair·(u−s)^{−1/2}` consumes (`(u−s)^{−1/2} =
    (√(u−s))⁻¹`).  NOT `a₁ = R/6`. -/
theorem two_term_census_bound_uniform_combined
    (τ r T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T) (hr : 0 < r)
    (q₁ q₂ : Point n → ℝ)
    (L M₁ M₂ : ℝ) (hL : 0 ≤ L) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hq₁meas : AEStronglyMeasurable q₁ volume) (hq₂meas : AEStronglyMeasurable q₂ volume)
    (hq₁bnd : ∀ z, |q₁ z| ≤ M₁) (hq₂bnd : ∀ z, |q₂ z| ≤ M₂)
    (hcl : ∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖)
    (Ω : Set (Point n)) (hΩ : MeasurableSet Ω) (hball : Metric.ball (0 : Point n) r ⊆ Ω) :
    |(∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
        + (∫ z in Ω, gaussDdim τ z * q₂ z)|
      ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1))
          + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂)
              * Real.sqrt T) / Real.sqrt τ := by
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h := two_term_census_bound_uniform τ r T hτ hτT hr q₁ q₂ L M₁ M₂ hL hM₁ hM₂
    hq₁meas hq₂meas hq₁bnd hq₂bnd hcl Ω hΩ hball
  refine h.trans (le_of_eq ?_)
  field_simp

/-! ###############################################################################
    ### §C — non-vacuity (the hypothesis bundles are jointly satisfiable, with TEETH).
    ############################################################################### -/

/-- **Non-vacuity of `product_center_lipschitz`.**  Exhibited at the genuine bounded, center-Lipschitz-
    but-NOT-globally-Lipschitz factors `f z = h z := sin(‖z‖²)` on `ball 0 1`.  NOT `a₁ = R/6`. -/
theorem product_center_lipschitz_hyp_satisfiable :
    ∃ (r : ℝ) (f h : Point n → ℝ) (M_f M_h L_f L_h : ℝ),
      0 ≤ M_f ∧ 0 ≤ M_h ∧ (∀ z, |f z| ≤ M_f) ∧ (∀ z, |h z| ≤ M_h) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |f z - f 0| ≤ L_f * ‖z‖) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |h z - h 0| ≤ L_h * ‖z‖) := by
  refine ⟨1, fun z => Real.sin (‖z‖ ^ 2), fun z => Real.sin (‖z‖ ^ 2), 1, 1, 1, 1,
    zero_le_one, zero_le_one, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (intro z; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
    | (intro z hz
       have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
       have h0 : (Real.sin (‖(0 : Point n)‖ ^ 2)) = 0 := by simp
       have hsinabs : |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := by
         rcases eq_or_ne (‖z‖ ^ 2) 0 with h | h
         · rw [h]; simp
         · exact (Real.abs_sin_lt_abs h).le
       show |Real.sin (‖z‖ ^ 2) - Real.sin (‖(0 : Point n)‖ ^ 2)| ≤ 1 * ‖z‖
       rw [h0, sub_zero, one_mul]
       calc |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := hsinabs
         _ = ‖z‖ ^ 2 := abs_of_nonneg (by positivity)
         _ ≤ ‖z‖ := by nlinarith [hz1, norm_nonneg z])

/-- **Non-vacuity of `two_term_census_bound_uniform`.**  Exhibited with `q₁ z := sin(‖z‖²)` (bounded,
    center-Lipschitz `L=1` on `ball 0 1` but NOT globally Lipschitz — TEETH inherited from J4-923),
    `q₂ z := cos ‖z‖` (bounded, `M₂=1`), on the PROPER superset `Ω = ball 0 5 ⊋ ball 0 1`, with
    `0 < τ = 1 ≤ T = 1`.  NOT `a₁ = R/6`. -/
theorem two_term_census_bound_uniform_hyp_satisfiable :
    ∃ (τ r T : ℝ) (q₁ q₂ : Point n → ℝ) (L M₁ M₂ : ℝ) (Ω : Set (Point n)),
      0 < τ ∧ τ ≤ T ∧ 0 < r ∧ 0 ≤ L ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
        AEStronglyMeasurable q₁ (volume : Measure (Point n)) ∧
        AEStronglyMeasurable q₂ (volume : Measure (Point n)) ∧
        (∀ z, |q₁ z| ≤ M₁) ∧ (∀ z, |q₂ z| ≤ M₂) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖) ∧
        MeasurableSet Ω ∧ Metric.ball (0 : Point n) r ⊆ Ω := by
  refine ⟨1, 1, 1, fun z => Real.sin (‖z‖ ^ 2), fun z => Real.cos ‖z‖, 1, 1, 1,
    Metric.ball (0 : Point n) 5, one_pos, le_refl 1, one_pos, zero_le_one, zero_le_one, zero_le_one,
    ?_, ?_, ?_, ?_, ?_, measurableSet_ball, Metric.ball_subset_ball (by norm_num)⟩
  · exact (Real.continuous_sin.comp ((continuous_norm.pow 2))).aestronglyMeasurable
  · exact (Real.continuous_cos.comp continuous_norm).aestronglyMeasurable
  · intro z; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  · intro z; exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · intro z hz
    have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    have h0 : (Real.sin (‖(0 : Point n)‖ ^ 2)) = 0 := by simp
    have hsinabs : |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := by
      rcases eq_or_ne (‖z‖ ^ 2) 0 with h | h
      · rw [h]; simp
      · exact (Real.abs_sin_lt_abs h).le
    show |Real.sin (‖z‖ ^ 2) - Real.sin (‖(0 : Point n)‖ ^ 2)| ≤ 1 * ‖z‖
    rw [h0, sub_zero, one_mul]
    calc |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := hsinabs
      _ = ‖z‖ ^ 2 := abs_of_nonneg (by positivity)
      _ ≤ ‖z‖ := by nlinarith [hz1, norm_nonneg z]

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms product_center_lipschitz
#print axioms product3_center_lipschitz
#print axioms two_term_census_bound_uniform
#print axioms two_term_census_bound_uniform_combined
#print axioms product_center_lipschitz_hyp_satisfiable
#print axioms two_term_census_bound_uniform_hyp_satisfiable
end AxiomChecks
