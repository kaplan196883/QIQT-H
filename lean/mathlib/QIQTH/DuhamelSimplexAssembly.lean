/-
  DuhamelSimplexAssembly — the honest E(τ) → O(τ²) ASSEMBLY STEP for the Levi/Duhamel correction.

  CONTEXT (J4-499).  The traced diagonal Duhamel correction is, by unfolding `heatConv`,
      E_tr(τ)  =  ∫₀^τ  R(τ − s, s)  ds ,          R(a, s) := ∫_z (residual z-slice)(a, s, z) dz,
  where — CRITICALLY — the age of the parametrix (Gaussian) factor is the REMAINING time `a = τ − s`
  (from `heatConv A B t = ∫₀ᵗ ∫_z A (t − s) x z · B s z y`), NOT the outer time `τ`.  On the Duhamel
  integration path the age-plus-source-time sum is CONSTANT,
      a + s = (τ − s) + s = τ ,
  so ANY post-cancellation slice bound of the shape `‖R(a,s)‖ ≤ K·(a + s)` collapses to the uniform
  constant `K·τ` along the path, and the `∫₀^τ ds` then produces the desired `O(τ²)`:
      ‖E_tr(τ)‖ ≤ K·τ².

  This file lands EXACTLY that assembly step (`duhamel_simplex_quadratic_bound`) — the shape needed to
  discharge the CARRIED hypothesis `hCorrHigher : heatConv H F (τ,0,0) = pref·(τ²·cRem)` of
  `QIQTH.TrueKernelA1.trueKernel_diagonal_a1_eq_R6`, ONCE a post-cancellation `O(a+s)` slice bound is
  available.

  ⚠ HONEST SCOPE — what this does NOT do.  It does NOT provide the `O(a+s)` slice bound: the currently
  PROVEN fixed-time residual bound is only `‖R(a,s)‖ ≤ C/a` (`ConcreteRemainderOrder.concreteRemainder_order`,
  the `M₀·(n+1)/(2τ)` + `Mqc·(n+1)/(2τ)` dominant `1/a` terms).  Instantiated at the Duhamel age
  `a = τ − s` that ABSOLUTE bound gives `∫₀^τ C/(τ−s) ds = C·∫₀^τ dσ/σ = +∞` — the genuine
  LOG-DIVERGENCE confirming the q≈1 verdict: the sup-norm `1/a` bound is coefficient-insufficient
  (indeed nonintegrable) to reach `O(τ²)`.  Closing the gap requires REPLACING the `1/a` absolute bound
  by an exact Gaussian moment extraction (`GaussianMomentExtraction.poly2_gauss_extraction`: the signed
  Hessian-Gaussian pairing is `O(1)`, not `O(1/a)`, because the constant/linear jets are annihilated) —
  which upgrades `O(1/a) → O(1)` — AND then a transport-cancellation identity that annihilates the
  surviving `O(1)` transport coefficient (this is exactly the van-Vleck 2-jet `D²u₀(0) = (1/6)Ric`
  wall) to land the `O(a+s)` slice this lemma consumes.  This file is the LAST link (the ds-assembly),
  NOT the missing estimate; it is `sorry`-free and does NOT claim `a₁ = R/6`.

  No axioms beyond Mathlib's; no `sorry`.
-/
import Mathlib

open MeasureTheory intervalIntegral
open scoped Interval

namespace QIQTH.DuhamelAssembly

/-- **★ The Duhamel-simplex `O(τ²)` assembly step.**  If the traced residual slice `r (τ − s) s`
    (age `= τ − s` = remaining Duhamel time, source-time `= s`) satisfies the post-cancellation
    `O(a + s)` bound `‖r (τ − s) s‖ ≤ K·((τ − s) + s)` on the integration interval, then — because
    `(τ − s) + s = τ` is CONSTANT on the Duhamel path — the assembled traced correction
        `E_tr(τ) = ∫₀^τ r (τ − s) s  ds`
    is `O(τ²)`:
        `‖∫₀^τ r (τ − s) s ds‖ ≤ K·τ²`.

    This is the exact shape that discharges the carried `hCorrHigher` (`heatConv H F (τ,0,0) = pref·τ²·cRem`)
    of `trueKernel_diagonal_a1_eq_R6`, MODULO the still-open `O(a+s)` slice bound (moment extraction +
    transport cancellation).  ⚠ NOT `a₁ = R/6`. -/
theorem duhamel_simplex_quadratic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ → ℝ → E) (K τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s ∈ Ι (0 : ℝ) τ, ‖r (τ - s) s‖ ≤ K * ((τ - s) + s)) :
    ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖ ≤ K * τ ^ 2 := by
  -- On the Duhamel path the age `τ − s` plus source-time `s` is the CONSTANT `τ`.
  have hr' : ∀ s ∈ Ι (0 : ℝ) τ, ‖r (τ - s) s‖ ≤ K * τ := fun s hs =>
    (hr s hs).trans_eq (by ring)
  -- Constant-bound interval-integral estimate: `‖∫₀^τ …‖ ≤ (K·τ)·|τ − 0| = K·τ²`.
  calc ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖
      ≤ K * τ * |τ - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hr'
    _ = K * τ ^ 2 := by rw [sub_zero, abs_of_nonneg hτ]; ring

/-- **Prefactor form** — the `pref·(τ²·cRem)` shape of `hCorrHigher`.  With a scalar heat prefactor
    `pref` multiplying the assembled correction, the same `O(a+s)` slice bound gives
        `‖pref · ∫₀^τ r (τ − s) s ds‖ ≤ |pref|·K·τ²`.
    (Immediate from `duhamel_simplex_quadratic_bound` + `norm_smul`.)  ⚠ NOT `a₁ = R/6`. -/
theorem duhamel_simplex_quadratic_bound_pref {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ → ℝ → E) (pref K τ : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ s ∈ Ι (0 : ℝ) τ, ‖r (τ - s) s‖ ≤ K * ((τ - s) + s)) :
    ‖pref • ∫ s in (0 : ℝ)..τ, r (τ - s) s‖ ≤ |pref| * K * τ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs]
  have hbase := duhamel_simplex_quadratic_bound r K τ hτ hr
  calc |pref| * ‖∫ s in (0 : ℝ)..τ, r (τ - s) s‖
      ≤ |pref| * (K * τ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hbase (abs_nonneg _)
    _ = |pref| * K * τ ^ 2 := by ring

/-- **Satisfiability witness** — the `O(a+s)` hypothesis of `duhamel_simplex_quadratic_bound` is
    INHABITED and the conclusion is SHARP (non-vacuous).  Take `r a s := (a + s : ℝ)` and `K := 1`:
    the hypothesis `‖r (τ−s) s‖ = |(τ−s)+s| ≤ 1·((τ−s)+s)` holds on `[0,τ]`, and the assembled integral
    is `∫₀^τ τ ds = τ²`, matching the bound `K·τ² = τ²` with equality.  This certifies the assembly
    lemma is not vacuously true. -/
theorem duhamel_simplex_quadratic_bound_sharp (τ : ℝ) :
    (∫ s in (0 : ℝ)..τ, ((τ - s) + s)) = τ ^ 2 := by
  have hconst : (fun s : ℝ => (τ - s) + s) = fun _ : ℝ => τ := by
    funext s; ring
  rw [hconst, intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring

#print axioms QIQTH.DuhamelAssembly.duhamel_simplex_quadratic_bound
#print axioms QIQTH.DuhamelAssembly.duhamel_simplex_quadratic_bound_pref
#print axioms QIQTH.DuhamelAssembly.duhamel_simplex_quadratic_bound_sharp

end QIQTH.DuhamelAssembly
