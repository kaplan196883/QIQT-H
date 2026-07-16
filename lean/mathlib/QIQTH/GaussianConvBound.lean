/-
  GaussianConvBound — the SELF-SIMILAR Gaussian × time-power convolution identity (Phase C2 of the
  convergence-infrastructure campaign, docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md).

  This is the one-step estimate coupling C1's spatial Gaussian semigroup (`gaussDdim_conv`) with the
  Beta time integral.  It is the heart of why the Levi/Duhamel Neumann series converges: iterating
  this identity over the time simplex (C3) produces the factorial (Beta-function) decay.

  WHAT LANDS HERE.

    • `gaussTimePow_conv` — THE self-similar identity (the C2 capstone).  For the two kernels
        `A τ p q = τ^a · G_τ(p−q)`, `B σ p q = σ^b · G_σ(p−q)` (`G = gaussDdim`), the space-time
        Duhamel convolution factorizes as
            `heatConv A B t x y = (∫₀ᵗ (t−s)^a s^b ds) · G_t(x−y)`.
      This rides directly on C1 (`gaussDdim_conv`, "variances add") pulled through the `z`-integral,
      plus the scalar pull-outs (`integral_const_mul`, `intervalIntegral.integral_mul_const`).  The
      time powers `τ^a`, `σ^b` are `Real.rpow` (the parametrix offsets are non-integer `−d/2`).

    • `betaTimeIntegral_eq` — the scaled Beta time integral (`a>−1, b>−1, t>0`):
            `∫₀ᵗ (t−s)^a s^b ds = t^(a+b+1) · (Γ(a+1) Γ(b+1) / Γ(a+b+2))`.
      Route: the substitution `s = t·u` reduces it to `t^(a+b+1) ∫₀¹ u^b (1−u)^a du`, which is
      `Complex.betaIntegral (b+1) (a+1)` cast to ℝ, evaluated by `Complex.betaIntegral_eq_Gamma_mul_div`
      (Mathlib has NO real `betaIntegral`; only the complex one — so a small ℝ↔ℂ cast bridges it).

    • `gaussTimePow_conv_beta` — combine the two: the same LHS `= t^(a+b+1)·Β(a+1,b+1)·G_t(x−y)`.

  ⚠ HONEST SCOPE.  This is the FLAT self-similar one-step convolution.  It is NOT the true curved
  heat kernel, the Seeley–DeWitt recursion, or `a₁ = R/6` (phases C5/C6).  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.GaussianConvolution
import QIQTH.HeatDuhamel

open Real MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianConvolution QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.GaussianConvBound

set_option maxHeartbeats 1600000

/-! ### The self-similar convolution identity (the C2 capstone / deliverable floor). -/

/-- **★ THE SELF-SIMILAR GAUSSIAN × TIME-POWER CONVOLUTION IDENTITY (Phase C2).**
    With the two kernels `A τ p q = τ^a · G_τ(p−q)` and `B σ p q = σ^b · G_σ(p−q)` (`G = gaussDdim`,
    `τ^a`, `σ^b` the `Real.rpow` time powers), the space-time Duhamel convolution factorizes into a
    pure time integral times the Gaussian:
        `heatConv A B t x y = (∫₀ᵗ (t−s)^a s^b ds) · G_t(x−y)`.

    PROOF.  Unfold `heatConv`.  For a.e. `s` on `[0,t]` (i.e. `s ∈ Ioo 0 t`, dropping the endpoints
    where `t−s` or `s` vanishes) the inner `z`-integrand is
    `((t−s)^a G_{t−s}(x−z))·(s^b G_s(z−y))`; the `z`-independent scalar `(t−s)^a s^b` pulls out
    (`integral_const_mul`), and C1 (`gaussDdim_conv (t−s) s`, "variances add", `(t−s)+s = t`) closes
    the `z`-integral to `G_t(x−y)`.  The now-constant-in-`s` Gaussian `G_t(x−y)` then pulls out of the
    `s`-interval-integral (`intervalIntegral.integral_mul_const`).  Carries `a>−1, b>−1, t>0` (genuine;
    the time integral converges only then). -/
theorem gaussTimePow_conv {n : ℕ} (a b : ℝ) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    heatConv (fun τ p q => τ ^ a * gaussDdim τ (p - q))
             (fun σ p q => σ ^ b * gaussDdim σ (p - q)) t x y
      = (∫ s in (0)..t, (t - s) ^ a * s ^ b) * gaussDdim t (x - y) := by
  simp only [heatConv]
  -- Rewrite the inner `z`-integral a.e. in `s` (endpoints have measure zero).
  have hkey : ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.uIoc 0 t →
      (∫ z : Point n,
          ((t - s) ^ a * gaussDdim (t - s) (x - z)) * (s ^ b * gaussDdim s (z - y)))
        = ((t - s) ^ a * s ^ b) * gaussDdim t (x - y) := by
    have hne : ({t} : Set ℝ)ᶜ ∈ MeasureTheory.ae volume := by
      rw [MeasureTheory.mem_ae_iff, compl_compl]
      exact MeasureTheory.measure_singleton t
    filter_upwards [hne] with s hs
    intro hmem
    rw [Set.uIoc_of_le ht.le] at hmem
    obtain ⟨hs0, hst⟩ := hmem
    have hsne : s ≠ t := by simpa using hs
    have hts : 0 < t - s := by
      have : s < t := lt_of_le_of_ne hst hsne
      linarith
    calc (∫ z : Point n,
            ((t - s) ^ a * gaussDdim (t - s) (x - z)) * (s ^ b * gaussDdim s (z - y)))
        = ∫ z : Point n,
            ((t - s) ^ a * s ^ b) *
              (gaussDdim (t - s) (x - z) * gaussDdim s (z - y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          ring
      _ = ((t - s) ^ a * s ^ b) *
            ∫ z : Point n, gaussDdim (t - s) (x - z) * gaussDdim s (z - y) :=
          integral_const_mul _ _
      _ = ((t - s) ^ a * s ^ b) * gaussDdim ((t - s) + s) (x - y) := by
          rw [gaussDdim_conv (t - s) s hts hs0 x y]
      _ = ((t - s) ^ a * s ^ b) * gaussDdim t (x - y) := by
          rw [show (t - s) + s = t from by ring]
  rw [intervalIntegral.integral_congr_ae hkey]
  exact intervalIntegral.integral_mul_const _ _

/-! ### The Beta time integral (the Γ closed form). -/

/-- **The unit-interval Beta integral in Γ form.**  `∫₀¹ u^b (1−u)^a du = Γ(b+1)Γ(a+1)/Γ(a+b+2)`
    for `a>−1, b>−1`.  Mathlib has NO real `betaIntegral` — only `Complex.betaIntegral` — so we bridge
    via the ℝ→ℂ cast: for `x ∈ [0,1]` the real integrand `x^b(1−x)^a` casts to the complex
    `(↑x)^b(1−↑x)^a` (`Complex.ofReal_cpow`, valid since `x≥0`, `1−x≥0`), identifying the (`ofReal` of
    the) real integral with `Complex.betaIntegral (b+1) (a+1)`; `Complex.betaIntegral_eq_Gamma_mul_div`
    + `Complex.Gamma_ofReal` then give the Γ form, pulled back through `Complex.ofReal_inj`. -/
theorem unitInterval_beta (a b : ℝ) (ha : -1 < a) (hb : -1 < b) :
    (∫ u in (0:ℝ)..1, u ^ b * (1 - u) ^ a)
      = Real.Gamma (b + 1) * Real.Gamma (a + 1) / Real.Gamma (a + b + 2) := by
  have hbc : (0:ℝ) < ((b : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have hac : (0:ℝ) < ((a : ℂ) + 1).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re]; linarith
  have key : ((∫ u in (0:ℝ)..1, u ^ b * (1 - u) ^ a : ℝ) : ℂ)
      = Complex.Gamma ((b : ℂ) + 1) * Complex.Gamma ((a : ℂ) + 1)
          / Complex.Gamma (((b : ℂ) + 1) + ((a : ℂ) + 1)) := by
    rw [← Complex.betaIntegral_eq_Gamma_mul_div ((b : ℂ) + 1) ((a : ℂ) + 1) hbc hac,
        Complex.betaIntegral]
    simp only [add_sub_cancel_right]
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0,
        Complex.ofReal_cpow (by linarith : (0:ℝ) ≤ 1 - x),
        Complex.ofReal_sub, Complex.ofReal_one]
  have hcast : Complex.Gamma ((b : ℂ) + 1) * Complex.Gamma ((a : ℂ) + 1)
        / Complex.Gamma (((b : ℂ) + 1) + ((a : ℂ) + 1))
      = ((Real.Gamma (b + 1) * Real.Gamma (a + 1) / Real.Gamma (a + b + 2) : ℝ) : ℂ) := by
    rw [show ((b : ℂ) + 1) + ((a : ℂ) + 1) = ((a + b + 2 : ℝ) : ℂ) from by push_cast; ring,
        show ((b : ℂ) + 1) = ((b + 1 : ℝ) : ℂ) from by push_cast; ring,
        show ((a : ℂ) + 1) = ((a + 1 : ℝ) : ℂ) from by push_cast; ring,
        Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast; ring
  rw [hcast] at key
  exact_mod_cast key

/-- **★ THE SCALED BETA TIME INTEGRAL (Phase C2, #1).**  For `a>−1, b>−1, t>0`,
        `∫₀ᵗ (t−s)^a s^b ds = t^(a+b+1) · (Γ(a+1) Γ(b+1) / Γ(a+b+2))`,
    the RHS constant being `Β(a+1, b+1)`.  PROOF: the substitution `s = t·u`
    (`intervalIntegral.smul_integral_comp_mul_left`, `c = t`) maps `(0,t)→(0,1)` and, via
    `Real.mul_rpow` (`t≥0`, `1−u≥0`, `u≥0`) + `Real.rpow_add` (`t>0`), factors the integrand as
    `t^(a+b) · u^b (1−u)^a`; pulling the `t^(a+b)` scalar out (`intervalIntegral.integral_const_mul`)
    leaves `t·t^(a+b)·∫₀¹ u^b(1−u)^a = t^(a+b+1)·Β(a+1,b+1)` (`unitInterval_beta`).  Carries
    `a>−1, b>−1` (genuine: the Beta integral converges only then) and `t>0`. -/
theorem betaTimeIntegral_eq (a b : ℝ) (ha : -1 < a) (hb : -1 < b) (t : ℝ) (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, (t - s) ^ a * s ^ b)
      = t ^ (a + b + 1) * (Real.Gamma (a + 1) * Real.Gamma (b + 1) / Real.Gamma (a + b + 2)) := by
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (f := fun s => (t - s) ^ a * s ^ b) (a := (0:ℝ)) (b := (1:ℝ)) t
  simp only [mul_zero, mul_one] at hsub
  rw [← hsub]
  have hInt : (∫ x in (0:ℝ)..1, (t - t * x) ^ a * (t * x) ^ b)
      = t ^ (a + b) * ∫ x in (0:ℝ)..1, x ^ b * (1 - x) ^ a := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    rw [show t - t * x = t * (1 - x) from by ring,
        Real.mul_rpow ht.le (by linarith : (0:ℝ) ≤ 1 - x),
        Real.mul_rpow ht.le hx0,
        show t ^ a * (1 - x) ^ a * (t ^ b * x ^ b)
          = (t ^ a * t ^ b) * (x ^ b * (1 - x) ^ a) from by ring,
        ← Real.rpow_add ht]
  rw [hInt, unitInterval_beta a b ha hb, smul_eq_mul]
  have ht1 : t ^ (a + b + 1) = t ^ (a + b) * t := by
    rw [show a + b + 1 = (a + b) + 1 from by ring, Real.rpow_add ht, Real.rpow_one]
  rw [ht1]; ring

/-! ### The self-similar identity in closed Β/Γ form (combine #1 + #2). -/

/-- **★ THE SELF-SIMILAR CONVOLUTION IN CLOSED Β/Γ FORM (Phase C2, #3).**  Combining the
    self-similar identity (`gaussTimePow_conv`, #2) with the Beta time integral (`betaTimeIntegral_eq`,
    #1): for `a>−1, b>−1, t>0`,
        `heatConv (τ^a G_τ) (σ^b G_σ) t x y
           = t^(a+b+1) · (Γ(a+1) Γ(b+1) / Γ(a+b+2)) · G_t(x−y)`.
    The `t^(a+b+1)` scaling + Beta constant `Β(a+1,b+1)` is EXACTLY the factor whose iteration over the
    time simplex (C3) yields the factorial decay driving Neumann-series convergence. -/
theorem gaussTimePow_conv_beta {n : ℕ} (a b : ℝ) (ha : -1 < a) (hb : -1 < b)
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    heatConv (fun τ p q => τ ^ a * gaussDdim τ (p - q))
             (fun σ p q => σ ^ b * gaussDdim σ (p - q)) t x y
      = t ^ (a + b + 1) * (Real.Gamma (a + 1) * Real.Gamma (b + 1) / Real.Gamma (a + b + 2))
          * gaussDdim t (x - y) := by
  rw [gaussTimePow_conv a b t ht x y, betaTimeIntegral_eq a b ha hb t ht]

end QIQTH.GaussianConvBound
