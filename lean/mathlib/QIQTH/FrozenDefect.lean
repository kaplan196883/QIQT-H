/-
  FrozenDefect — J4-610: the τ^{−1/2} Levi defect bound for the per-q frozen Gaussian
  (inhabits `FrozenDefectBound`, the J4-609 next-brick target; Sol milestone "FrozenDefectNegHalf").

  THE MATHEMATICS.  J4-609 banked the frozen-SPD Gaussian `Γ_q = frozenGauss (g^K(q))` with EXACT
  cancellation against the frozen operator (`frozenGauss_frozen_heat` / `frozenGauss_heatOp_zero`).
  The residual of the TRUE (moving-coefficient) operator applied to `Γ_q` is therefore purely the
  coefficient modulus: the Levi defect
      E(τ,q,v) = ∑ᵢⱼ (gⁱʲ(q+v) − gⁱʲ(q)) · ∂ᵢ∂ⱼΓ_q(τ,v).
  This file proves the classical `O(τ^{−1/2})` bound `|E| ≤ (C/√τ)·G_{2τ}(v)` on the space-form
  ball (`K ≤ 0`, `rncRadialSq q ≤ r²`, `0 < τ ≤ 1`), i.e. inhabits `FrozenDefectBound n K r C 2`.

  THE THREE INGREDIENTS (each with honest EXPLICIT constants in `K, r, n`):
    (i)  `curvedRNCInv_diff_bound` — the coefficient-modulus bound from the closed rational form
         `gi^K(x) = (δ − (K/3)xxᵀ)/(1 − (K/3)‖x‖²)` (denominator ≥ 1 for K ≤ 0):
             `|gⁱʲ(q+v) − gⁱʲ(q)| ≤ (−K/3)·(4r‖v‖ + 2‖v‖²)`.
         ⚠ HONEST SHAPE: this is NOT a pure Lipschitz `L·‖v‖` bound — `v` is UNRESTRICTED in
         `FrozenDefectBound` (no ball on `v`), and the honest global bound is affine in
         `(‖v‖, ‖v‖²)`.  The quadratic term folds at order `τ⁰ ≤ τ^{−1/2}` (τ ≤ 1), so the
         `τ^{−1/2}` rate is unharmed.
    (ii) `frozenGauss_pd_pd_abs_le` + `frozenGauss_le_detBound_mul_gauss` — the second-partial
         bound from the exact `frozenGauss_pd_pd` calculus and the banked space-form comparison:
             `|∂ᵢ∂ⱼΓ_q| ≤ (M/(2τ) + n²M²‖v‖²/(4τ²)) · √(n!·Mⁿ) · G_τ(v)`,  `M = 1 + (−K/3)r²`
         (entry bound `|g^K(q)ᵢⱼ| ≤ M`, row bound `|(g^K(q)v)ᵢ| ≤ nM‖v‖`, `det ≤ n!·Mⁿ` via
         `Matrix.det_le` — the `n!` is the crude-but-honest Leibniz bound, not claimed sharp).
    (iii) `defect_scalar_fold` + the banked `gaussDdim_absorb_zero/one/two`
         (η = 0, lam = 2, gate trivial at w = z = v) — the width-fold: with `x = ‖v‖²/τ`,
             `‖v‖/τ ≤ (1+x)/√τ`,  `‖v‖³/τ² ≤ (1+x)x/√τ`,  `x, x² ≤ x/√τ, x²/√τ`  (τ ≤ 1),
         so the whole coefficient is `≤ (K₀+K₁x+K₂x²)/√τ`, and the polynomial absorbs into the
         width-2 Gaussian: `xᵏ·G_τ ≤ Cₖ·G_{2τ}`.  ⚠ HONEST WIDTH: `lam = 2` exactly (the
         absorption widens `τ → 2τ`); the exponent is exactly `τ^{−1/2}` — no `τ^{−1}` remnant.

  WHAT LANDS (all proved, no sorry):
    • ★ `frozenDefectBound_spaceForm` — `∃ C > 0, FrozenDefectBound n K r C 2` for every `K ≤ 0`,
      `r ≥ 0` (C explicit in the proof: `n²·√(n!Mⁿ)·(K₀C₀+K₁C₁+K₂C₂) + 1` with the `Kᵢ` from the
      scalar fold and `Cₖ` the banked absorption constants `(√2)ⁿ·k!·4ᵏ/(1/2)ᵏ…`).
    • `curvedRNCInv_sub_eq` / `curvedRNCInv_diff_bound` — the exact rational-difference identity
      and the honest coefficient-modulus bound (i).
    • `curvedRNCMetric_entry_abs_le` / `curvedRNCMetric_row_abs_le` /
      `frozenGauss_pd_pd_abs_le` / `frozenGauss_le_detBound_mul_gauss` — ingredient (ii).
    • `defect_scalar_fold` — ingredient (iii), the τ^{−1/2} bookkeeping isolated as a scalar lemma.
    • NON-VACUITY: `frozenDefect_witness_ne_zero` — for `K < 0`, `n ≥ 2`, any `r`, any `τ > 0`
      there are `q, v` IN the antecedent range (q = 0, v = unit vector) at which the bounded
      defect sum is GENUINELY NONZERO (evaluates to `(n−1)·(1−1/(1−K/3))·Γ/(2τ) > 0`): the bound
      is exercised, not vacuously about `0`.
    • GO/NO-GO RECON CERTIFICATES (Sol's checks, small certifying lemmas):
      `width2_closed_fold` — the D2 engine's width-2 Gaussian model folds CLOSED at fixed width 2
      (`G_{2t} * G_{2s} = G_{2(t+s)}`, re-export of the banked rescaled semigroup) — GO/NO-GO 1.
      `betaTime_negHalf_integral` — the α = −1/2 time-convolution `∫₀ᵗ (t−s)^{−1/2}s^{−1/2} ds = π`
      converges with exact value (the `−1 < α` Beta machinery admits α = −1/2) — the per-step half
      of GO/NO-GO 2.  ⚠ The SERIES-summability half (`modelCoeff_summable` etc.) is currently
      `0 ≤ α` only — the α-generalization of `gamma_ratio_tendsto_zero` is a REPORTED gap, not
      certified here.

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: the flat tower is non-vacuous and closed, but
  the curved re-base still owes the α-fork (α = −1/2 D2 summability + consumer α-generalization,
  or per-q first-jet cancellation), the per-q re-based producer re-assembly, the fat-K
  hEmeas/hAdom/hcont piles, the capstone co-instantiation, and the prior piles.  This brick is the
  defect bound + go/no-go reconnaissance only.  No axioms, no sorry.
-/
import Mathlib
import QIQTH.FrozenGauss
import QIQTH.GaussianWidthTolerant
import QIQTH.GaussianConvBound

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss

namespace QIQTH.FrozenDefect

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 0. Elementary radial helpers. -/

/-- A coordinate is bounded by the radius: `|wₐ| ≤ √(‖w‖²)`. -/
theorem abs_apply_le_sqrt_radialSq (w : Point n) (a : Fin n) :
    |w a| ≤ Real.sqrt (rncRadialSq w) := by
  have h1 : (w a) ^ 2 ≤ rncRadialSq w := by
    have h := Finset.single_le_sum (f := fun i => (w i) ^ 2)
      (fun i _ => sq_nonneg (w i)) (Finset.mem_univ a)
    simpa [rncRadialSq] using h
  calc |w a| = Real.sqrt ((w a) ^ 2) := (Real.sqrt_sq_eq_abs (w a)).symm
    _ ≤ Real.sqrt (rncRadialSq w) := Real.sqrt_le_sqrt h1

/-- On the ball `‖q‖² ≤ r²` every coordinate obeys `|qₐ| ≤ r`. -/
theorem abs_apply_le_of_radialSq_le {r : ℝ} (hr : 0 ≤ r) {q : Point n}
    (hq : rncRadialSq q ≤ r ^ 2) (a : Fin n) : |q a| ≤ r := by
  calc |q a| ≤ Real.sqrt (rncRadialSq q) := abs_apply_le_sqrt_radialSq q a
    _ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hq
    _ = r := Real.sqrt_sq hr

/-- Cauchy–Schwarz in radial form: `|⟨q,v⟩| ≤ √(‖q‖²)·√(‖v‖²)`. -/
theorem abs_inner_le_sqrt (q v : Point n) :
    |∑ a, q a * v a| ≤ Real.sqrt (rncRadialSq q) * Real.sqrt (rncRadialSq v) := by
  have hcs : (∑ a, q a * v a) ^ 2 ≤ rncRadialSq q * rncRadialSq v := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => q i) (fun i => v i)
    simpa [rncRadialSq] using h
  calc |∑ a, q a * v a| = Real.sqrt ((∑ a, q a * v a) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (rncRadialSq q * rncRadialSq v) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (rncRadialSq q) * Real.sqrt (rncRadialSq v) :=
        Real.sqrt_mul (rncRadialSq_nonneg q) _

/-- The radial-square expansion `‖q+v‖² = ‖q‖² + 2⟨q,v⟩ + ‖v‖²`. -/
theorem rncRadialSq_add (q v : Point n) :
    rncRadialSq (fun a => q a + v a)
      = rncRadialSq q + 2 * (∑ a, q a * v a) + rncRadialSq v := by
  simp only [rncRadialSq]
  have h1 : ∀ a : Fin n, (q a + v a) ^ 2 = q a ^ 2 + 2 * (q a * v a) + v a ^ 2 :=
    fun a => by ring
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The denominator of `gi^K` is `≥ 1` on the `K ≤ 0` branch. -/
theorem one_sub_K3_radial_ge_one (K : ℝ) (hK : K ≤ 0) (w : Point n) :
    1 ≤ 1 - K / 3 * rncRadialSq w := by
  have h1 : K / 3 * rncRadialSq w ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (rncRadialSq_nonneg w)
  linarith

/-! ### 1. Ingredient (i): the coefficient-modulus (Lipschitz-type) bound for `gi^K`. -/

/-- **The exact rational-difference identity** for the moving inverse metric:
    `gi^K(q+v) − gi^K(q)` splits into the product-modulus term over `α(q+v)` and the
    radial-modulus term over `α(q+v)·α(q)` (`α(x) = 1 − (K/3)‖x‖²`). -/
theorem curvedRNCInv_sub_eq (K : ℝ) (hK : K ≤ 0) (q v : Point n) (i j : Fin n) :
    curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j
      = (-(K / 3)) * ((q i + v i) * (q j + v j) - q i * q j)
            / (1 - K / 3 * rncRadialSq (fun a => q a + v a))
        + ((if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j))
            * (K / 3 * (rncRadialSq (fun a => q a + v a) - rncRadialSq q))
            / ((1 - K / 3 * rncRadialSq (fun a => q a + v a))
                * (1 - K / 3 * rncRadialSq q)) := by
  have hax : (1 - K / 3 * rncRadialSq (fun a => q a + v a)) ≠ 0 := by
    have h := one_sub_K3_radial_ge_one K hK (fun a => q a + v a); linarith
  have haq : (1 - K / 3 * rncRadialSq q) ≠ 0 := by
    have h := one_sub_K3_radial_ge_one K hK q; linarith
  have hax3 : (3 - K * rncRadialSq (fun a => q a + v a)) ≠ 0 := by
    have h := one_sub_K3_radial_ge_one K hK (fun a => q a + v a); intro hc; linarith
  have haq3 : (3 - K * rncRadialSq q) ≠ 0 := by
    have h := one_sub_K3_radial_ge_one K hK q; intro hc; linarith
  simp only [curvedRNCInv]
  field_simp
  ring

/-- **★ Ingredient (i): the honest coefficient-modulus bound.**  On the ball `‖q‖² ≤ r²`
    (`K ≤ 0`, `r ≥ 0`), for EVERY `v` (no ball on `v` — matching `FrozenDefectBound`):
        `|gⁱʲ(q+v) − gⁱʲ(q)| ≤ (−K/3)·(4r‖v‖ + 2‖v‖²)`.
    Derived from the closed rational form; the denominators `α ≥ 1` are simply dropped
    (that is the honest direction — no smallness of `v` is needed). -/
theorem curvedRNCInv_diff_bound (K : ℝ) (hK : K ≤ 0) (r : ℝ) (hr : 0 ≤ r)
    (q v : Point n) (hq : rncRadialSq q ≤ r ^ 2) (i j : Fin n) :
    |curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j|
      ≤ -K / 3 * (4 * r * Real.sqrt (rncRadialSq v) + 2 * rncRadialSq v) := by
  set s := Real.sqrt (rncRadialSq v) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = rncRadialSq v := Real.sq_sqrt (rncRadialSq_nonneg v)
  have hk0 : (0 : ℝ) ≤ -K / 3 := by linarith
  have hax1 : 1 ≤ 1 - K / 3 * rncRadialSq (fun a => q a + v a) :=
    one_sub_K3_radial_ge_one K hK _
  have haq1 : 1 ≤ 1 - K / 3 * rncRadialSq q := one_sub_K3_radial_ge_one K hK q
  have hax0 : 0 < 1 - K / 3 * rncRadialSq (fun a => q a + v a) := lt_of_lt_of_le one_pos hax1
  have haq0 : 0 < 1 - K / 3 * rncRadialSq q := lt_of_lt_of_le one_pos haq1
  have hqa : ∀ a, |q a| ≤ r := abs_apply_le_of_radialSq_le hr hq
  have hva : ∀ a, |v a| ≤ s := fun a => abs_apply_le_sqrt_radialSq v a
  -- product-modulus bound B2
  have hB2 : |(q i + v i) * (q j + v j) - q i * q j| ≤ 2 * r * s + s ^ 2 := by
    have hexp : (q i + v i) * (q j + v j) - q i * q j
        = q i * v j + v i * q j + v i * v j := by ring
    rw [hexp]
    have h1 : |q i * v j| ≤ r * s := by
      rw [abs_mul]; exact mul_le_mul (hqa i) (hva j) (abs_nonneg _) hr
    have h2 : |v i * q j| ≤ s * r := by
      rw [abs_mul]; exact mul_le_mul (hva i) (hqa j) (abs_nonneg _) hs0
    have h3 : |v i * v j| ≤ s * s := by
      rw [abs_mul]; exact mul_le_mul (hva i) (hva j) (abs_nonneg _) hs0
    calc |q i * v j + v i * q j + v i * v j|
        ≤ |q i * v j + v i * q j| + |v i * v j| := abs_add_le _ _
      _ ≤ (|q i * v j| + |v i * q j|) + |v i * v j| := by
          have h := abs_add_le (q i * v j) (v i * q j); linarith
      _ ≤ (r * s + s * r) + s * s := by
          have := h1; have := h2; have := h3; linarith
      _ = 2 * r * s + s ^ 2 := by ring
  -- radial-modulus bound B1
  have hdot : |∑ a, q a * v a| ≤ r * s := by
    calc |∑ a, q a * v a|
        ≤ Real.sqrt (rncRadialSq q) * Real.sqrt (rncRadialSq v) := abs_inner_le_sqrt q v
      _ ≤ r * s := by
          apply mul_le_mul_of_nonneg_right _ hs0
          calc Real.sqrt (rncRadialSq q) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt hq
            _ = r := Real.sqrt_sq hr
  have hB1 : |rncRadialSq (fun a => q a + v a) - rncRadialSq q| ≤ 2 * r * s + s ^ 2 := by
    rw [rncRadialSq_add]
    have hshape : rncRadialSq q + 2 * (∑ a, q a * v a) + rncRadialSq v - rncRadialSq q
        = 2 * (∑ a, q a * v a) + rncRadialSq v := by ring
    rw [hshape]
    calc |2 * (∑ a, q a * v a) + rncRadialSq v|
        ≤ |2 * (∑ a, q a * v a)| + |rncRadialSq v| := abs_add_le _ _
      _ = 2 * |∑ a, q a * v a| + rncRadialSq v := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
              abs_of_nonneg (rncRadialSq_nonneg v)]
      _ ≤ 2 * r * s + s ^ 2 := by
          have := hdot; linarith [hs2]
  -- the E-factor is dominated by the q-denominator
  have hqq : |q i * q j| ≤ rncRadialSq q := by
    calc |q i * q j| = |q i| * |q j| := abs_mul _ _
      _ ≤ Real.sqrt (rncRadialSq q) * Real.sqrt (rncRadialSq q) :=
          mul_le_mul (abs_apply_le_sqrt_radialSq q i) (abs_apply_le_sqrt_radialSq q j)
            (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq q := Real.mul_self_sqrt (rncRadialSq_nonneg q)
  have hE : |(if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j)|
      ≤ 1 - K / 3 * rncRadialSq q := by
    have hd1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases h : i = j <;> simp [h]
    have htri : |(if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j)|
        ≤ |(if i = j then (1 : ℝ) else 0)| + |K / 3 * (q i * q j)| := by
      have h := abs_add_le (if i = j then (1 : ℝ) else 0) (-(K / 3 * (q i * q j)))
      simpa [sub_eq_add_neg] using h
    have habs : |K / 3 * (q i * q j)| = -(K / 3) * |q i * q j| := by
      rw [abs_mul, abs_of_nonpos (by linarith : K / 3 ≤ 0)]
    have hmul : -(K / 3) * |q i * q j| ≤ -(K / 3) * rncRadialSq q :=
      mul_le_mul_of_nonneg_left hqq (by linarith)
    calc |(if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j)|
        ≤ |(if i = j then (1 : ℝ) else 0)| + |K / 3 * (q i * q j)| := htri
      _ ≤ 1 + -(K / 3) * rncRadialSq q := by rw [habs]; linarith
      _ = 1 - K / 3 * rncRadialSq q := by ring
  -- assemble
  rw [curvedRNCInv_sub_eq K hK q v i j]
  have ht1 : |(-(K / 3)) * ((q i + v i) * (q j + v j) - q i * q j)
        / (1 - K / 3 * rncRadialSq (fun a => q a + v a))|
      ≤ -K / 3 * (2 * r * s + s ^ 2) := by
    rw [abs_div, abs_of_pos hax0, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ -(K / 3))]
    calc -(K / 3) * |(q i + v i) * (q j + v j) - q i * q j|
          / (1 - K / 3 * rncRadialSq (fun a => q a + v a))
        ≤ -(K / 3) * |(q i + v i) * (q j + v j) - q i * q j| :=
          div_le_self (mul_nonneg (by linarith) (abs_nonneg _)) hax1
      _ ≤ -(K / 3) * (2 * r * s + s ^ 2) := mul_le_mul_of_nonneg_left hB2 (by linarith)
      _ = -K / 3 * (2 * r * s + s ^ 2) := by ring
  have ht2 : |((if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j))
        * (K / 3 * (rncRadialSq (fun a => q a + v a) - rncRadialSq q))
        / ((1 - K / 3 * rncRadialSq (fun a => q a + v a)) * (1 - K / 3 * rncRadialSq q))|
      ≤ -K / 3 * (2 * r * s + s ^ 2) := by
    rw [abs_div, abs_of_pos (mul_pos hax0 haq0), abs_mul]
    have habsK : |K / 3 * (rncRadialSq (fun a => q a + v a) - rncRadialSq q)|
        = -(K / 3) * |rncRadialSq (fun a => q a + v a) - rncRadialSq q| := by
      rw [abs_mul, abs_of_nonpos (by linarith : K / 3 ≤ 0)]
    rw [habsK]
    have hnum : |(if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j)|
          * (-(K / 3) * |rncRadialSq (fun a => q a + v a) - rncRadialSq q|)
        ≤ (1 - K / 3 * rncRadialSq q) * (-(K / 3) * (2 * r * s + s ^ 2)) := by
      apply mul_le_mul hE (mul_le_mul_of_nonneg_left hB1 (by linarith))
        (mul_nonneg (by linarith) (abs_nonneg _)) (by linarith)
    have hden0 : (0 : ℝ)
        < (1 - K / 3 * rncRadialSq (fun a => q a + v a)) * (1 - K / 3 * rncRadialSq q) :=
      mul_pos hax0 haq0
    calc |(if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j)|
          * (-(K / 3) * |rncRadialSq (fun a => q a + v a) - rncRadialSq q|)
          / ((1 - K / 3 * rncRadialSq (fun a => q a + v a)) * (1 - K / 3 * rncRadialSq q))
        ≤ (1 - K / 3 * rncRadialSq q) * (-(K / 3) * (2 * r * s + s ^ 2))
          / ((1 - K / 3 * rncRadialSq (fun a => q a + v a)) * (1 - K / 3 * rncRadialSq q)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden0.le)
      _ = -(K / 3) * (2 * r * s + s ^ 2)
          / (1 - K / 3 * rncRadialSq (fun a => q a + v a)) := by
          rw [show (1 - K / 3 * rncRadialSq (fun a => q a + v a))
                * (1 - K / 3 * rncRadialSq q)
              = (1 - K / 3 * rncRadialSq q)
                * (1 - K / 3 * rncRadialSq (fun a => q a + v a)) from mul_comm _ _,
            mul_div_mul_left _ _ haq0.ne']
      _ ≤ -(K / 3) * (2 * r * s + s ^ 2) :=
          div_le_self (mul_nonneg (by linarith)
            (by nlinarith [hs0, hr, sq_nonneg s])) hax1
      _ = -K / 3 * (2 * r * s + s ^ 2) := by ring
  calc |(-(K / 3)) * ((q i + v i) * (q j + v j) - q i * q j)
        / (1 - K / 3 * rncRadialSq (fun a => q a + v a))
      + ((if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j))
        * (K / 3 * (rncRadialSq (fun a => q a + v a) - rncRadialSq q))
        / ((1 - K / 3 * rncRadialSq (fun a => q a + v a)) * (1 - K / 3 * rncRadialSq q))|
      ≤ |(-(K / 3)) * ((q i + v i) * (q j + v j) - q i * q j)
          / (1 - K / 3 * rncRadialSq (fun a => q a + v a))|
        + |((if i = j then (1 : ℝ) else 0) - K / 3 * (q i * q j))
          * (K / 3 * (rncRadialSq (fun a => q a + v a) - rncRadialSq q))
          / ((1 - K / 3 * rncRadialSq (fun a => q a + v a))
              * (1 - K / 3 * rncRadialSq q))| := abs_add_le _ _
    _ ≤ -K / 3 * (2 * r * s + s ^ 2) + -K / 3 * (2 * r * s + s ^ 2) := add_le_add ht1 ht2
    _ = -K / 3 * (4 * r * s + 2 * s ^ 2) := by ring
    _ = -K / 3 * (4 * r * s + 2 * rncRadialSq v) := by rw [hs2]

/-! ### 2. Ingredient (ii): entry/row/det bounds and the second-partial bound. -/

/-- Entry bound on the ball: `|g^K(q)ᵢⱼ| ≤ M = 1 + (−K/3)r²`. -/
theorem curvedRNCMetric_entry_abs_le (K : ℝ) (hK : K ≤ 0) (r : ℝ)
    (q : Point n) (hq : rncRadialSq q ≤ r ^ 2) (i j : Fin n) :
    |curvedRNCMetric K q i j| ≤ 1 + -K / 3 * r ^ 2 := by
  have hk0 : (0 : ℝ) ≤ -K / 3 := by linarith
  have hqq : |q i * q j| ≤ r ^ 2 := by
    calc |q i * q j| = |q i| * |q j| := abs_mul _ _
      _ ≤ Real.sqrt (rncRadialSq q) * Real.sqrt (rncRadialSq q) :=
          mul_le_mul (abs_apply_le_sqrt_radialSq q i) (abs_apply_le_sqrt_radialSq q j)
            (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq q := Real.mul_self_sqrt (rncRadialSq_nonneg q)
      _ ≤ r ^ 2 := hq
  by_cases hij : i = j
  · subst hij
    have hqi2 : q i * q i ≤ rncRadialSq q := by
      have h := Finset.single_le_sum (f := fun a => (q a) ^ 2)
        (fun a _ => sq_nonneg (q a)) (Finset.mem_univ i)
      simpa [rncRadialSq, pow_two] using h
    have hval : curvedRNCMetric K q i i = 1 - K / 3 * (rncRadialSq q - q i * q i) := by
      simp [curvedRNCMetric]
    rw [hval, abs_le]
    have hge : 0 ≤ rncRadialSq q - q i * q i := by linarith
    have hle : rncRadialSq q - q i * q i ≤ r ^ 2 := by
      have := mul_self_nonneg (q i); linarith
    have hub : -(K / 3) * (rncRadialSq q - q i * q i) ≤ -(K / 3) * r ^ 2 :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    have hlb : 0 ≤ -(K / 3) * (rncRadialSq q - q i * q i) :=
      mul_nonneg (by linarith) hge
    constructor <;> nlinarith [hub, hlb]
  · have hval : curvedRNCMetric K q i j = K / 3 * (q i * q j) := by
      simp only [curvedRNCMetric, if_neg hij]
      ring
    rw [hval]
    calc |K / 3 * (q i * q j)| = -(K / 3) * |q i * q j| := by
          rw [abs_mul, abs_of_nonpos (by linarith : K / 3 ≤ 0)]
      _ ≤ -(K / 3) * r ^ 2 := mul_le_mul_of_nonneg_left hqq (by linarith)
      _ ≤ 1 + -K / 3 * r ^ 2 := by nlinarith [sq_nonneg r]

/-- Row bound on the ball: `|(g^K(q)v)ᵢ| ≤ n·M·√(‖v‖²)`. -/
theorem curvedRNCMetric_row_abs_le (K : ℝ) (hK : K ≤ 0) (r : ℝ)
    (q : Point n) (hq : rncRadialSq q ≤ r ^ 2) (v : Point n) (i : Fin n) :
    |∑ k, curvedRNCMetric K q i k * v k|
      ≤ (n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v) := by
  have hM0 : (0 : ℝ) ≤ 1 + -K / 3 * r ^ 2 := by nlinarith [sq_nonneg r]
  calc |∑ k, curvedRNCMetric K q i k * v k|
      ≤ ∑ k, |curvedRNCMetric K q i k * v k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (curvedRNCMetric_entry_abs_le K hK r q hq i k)
          (abs_apply_le_sqrt_radialSq v k) (abs_nonneg _) hM0
    _ = (n : ℝ) * ((1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v) := by ring

/-- The frozen Gaussian is (unconditionally) nonnegative. -/
theorem frozenGauss_nonneg (A : Fin n → Fin n → ℝ) (τ : ℝ) (v : Point n) :
    0 ≤ frozenGauss A τ v := by
  simp only [frozenGauss]
  positivity

/-- **Ingredient (ii), coefficient part**: the exact `frozenGauss_pd_pd` calculus gives
    `|∂ᵢ∂ⱼΓ_q| ≤ (M/(2τ) + n²M²‖v‖²/(4τ²))·Γ_q` on the ball (`M = 1 + (−K/3)r²`). -/
theorem frozenGauss_pd_pd_abs_le (K : ℝ) (hK : K ≤ 0) (r : ℝ)
    (q : Point n) (hq : rncRadialSq q ≤ r ^ 2) (τ : ℝ) (hτ : 0 < τ)
    (v : Point n) (i j : Fin n) :
    |pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
      ≤ ((1 + -K / 3 * r ^ 2) / (2 * τ)
          + (n : ℝ) ^ 2 * (1 + -K / 3 * r ^ 2) ^ 2 * rncRadialSq v / (4 * τ ^ 2))
        * frozenGauss (curvedRNCMetric K q) τ v := by
  rw [frozenGauss_pd_pd (curvedRNCMetric K q) (fun a b => curvedRNCMetric_symm K q a b)
      τ hτ v i j, abs_mul, abs_of_nonneg (frozenGauss_nonneg _ _ _)]
  apply mul_le_mul_of_nonneg_right _ (frozenGauss_nonneg _ _ _)
  have hM0 : (0 : ℝ) ≤ 1 + -K / 3 * r ^ 2 := by nlinarith [sq_nonneg r]
  have hs2 : Real.sqrt (rncRadialSq v) * Real.sqrt (rncRadialSq v) = rncRadialSq v :=
    Real.mul_self_sqrt (rncRadialSq_nonneg v)
  have hrow_i := curvedRNCMetric_row_abs_le K hK r q hq v i
  have hrow_j := curvedRNCMetric_row_abs_le K hK r q hq v j
  have h1 : |-(curvedRNCMetric K q i j) / (2 * τ)|
      = |curvedRNCMetric K q i j| / (2 * τ) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * τ)]
  have h2 : |(∑ k, curvedRNCMetric K q i k * v k) * (∑ k, curvedRNCMetric K q j k * v k)
        / (4 * τ ^ 2)|
      = |∑ k, curvedRNCMetric K q i k * v k| * |∑ k, curvedRNCMetric K q j k * v k|
        / (4 * τ ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * τ ^ 2)]
  have hrn0 : (0 : ℝ) ≤ (n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v) := by
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hM0) (Real.sqrt_nonneg _)
  calc |-(curvedRNCMetric K q i j) / (2 * τ)
        + (∑ k, curvedRNCMetric K q i k * v k) * (∑ k, curvedRNCMetric K q j k * v k)
          / (4 * τ ^ 2)|
      ≤ |curvedRNCMetric K q i j| / (2 * τ)
        + |∑ k, curvedRNCMetric K q i k * v k| * |∑ k, curvedRNCMetric K q j k * v k|
          / (4 * τ ^ 2) := by
        calc _ ≤ |-(curvedRNCMetric K q i j) / (2 * τ)|
              + |(∑ k, curvedRNCMetric K q i k * v k)
                  * (∑ k, curvedRNCMetric K q j k * v k) / (4 * τ ^ 2)| := abs_add_le _ _
          _ = _ := by rw [h1, h2]
    _ ≤ (1 + -K / 3 * r ^ 2) / (2 * τ)
        + ((n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v))
          * ((n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v))
          / (4 * τ ^ 2) := by
        apply add_le_add
        · rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (curvedRNCMetric_entry_abs_le K hK r q hq i j)
            (inv_nonneg.mpr (by positivity))
        · rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hrow_i hrow_j (abs_nonneg _) hrn0)
            (inv_nonneg.mpr (by positivity))
    _ = (1 + -K / 3 * r ^ 2) / (2 * τ)
        + (n : ℝ) ^ 2 * (1 + -K / 3 * r ^ 2) ^ 2 * rncRadialSq v / (4 * τ ^ 2) := by
        rw [show ((n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v))
              * ((n : ℝ) * (1 + -K / 3 * r ^ 2) * Real.sqrt (rncRadialSq v))
            = (n : ℝ) ^ 2 * (1 + -K / 3 * r ^ 2) ^ 2
              * (Real.sqrt (rncRadialSq v) * Real.sqrt (rncRadialSq v)) from by ring, hs2]

/-- **Ingredient (ii), det part**: `Γ_q ≤ √(n!·Mⁿ)·G_τ` on the ball — the banked space-form
    comparison (`m = 1`, exact prefactor) with the Leibniz determinant bound `det ≤ n!·Mⁿ`
    (`Matrix.det_le`; crude but honest, and uniform in `q` over the ball). -/
theorem frozenGauss_le_detBound_mul_gauss (K : ℝ) (hK : K ≤ 0) (r : ℝ)
    (q : Point n) (hq : rncRadialSq q ≤ r ^ 2) (τ : ℝ) (hτ : 0 < τ) (v : Point n) :
    frozenGauss (curvedRNCMetric K q) τ v
      ≤ Real.sqrt ((Nat.factorial n : ℝ) * (1 + -K / 3 * r ^ 2) ^ n) * gaussDdim τ v := by
  refine le_trans (frozenGauss_comparison_spaceForm K hK r q hq τ hτ v).2 ?_
  have hG0 : 0 ≤ gaussDdim τ v := by rw [gaussDdim_closed]; positivity
  apply mul_le_mul_of_nonneg_right _ hG0
  apply Real.sqrt_le_sqrt
  have hentry : ∀ i j, |curvedRNCMetric K q i j| ≤ 1 + -K / 3 * r ^ 2 :=
    fun i j => curvedRNCMetric_entry_abs_le K hK r q hq i j
  have hdet := Matrix.det_le (A := (curvedRNCMetric K q : Matrix (Fin n) (Fin n) ℝ))
    (abv := AbsoluteValue.abs) (x := 1 + -K / 3 * r ^ 2) (fun i j => hentry i j)
  have hdet' : |Matrix.det (curvedRNCMetric K q)|
      ≤ (Nat.factorial n : ℝ) * (1 + -K / 3 * r ^ 2) ^ n := by
    simpa [Fintype.card_fin, nsmul_eq_mul] using hdet
  exact le_trans (le_abs_self _) hdet'

/-! ### 3. Ingredient (iii): the τ^{−1/2} scalar fold. -/

/-- **The τ^{−1/2} bookkeeping, isolated.**  For `0 < τ ≤ 1` and `s ≥ 0` (`s = ‖v‖`), the full
    coefficient product folds to `(K₀ + K₁·x + K₂·x²)/√τ` with `x = s²/τ`:
    the half-power moves use only `s·√τ ≤ τ + s²` (AM–GM) and `√τ ≤ 1`.
    The `τ^{−1/2}` exponent is EXACT — every term carries at most one factor `1/√τ`. -/
theorem defect_scalar_fold (c M r nR : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hn : 0 ≤ nR) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (s : ℝ) (hs : 0 ≤ s) :
    c * (4 * r * s + 2 * s ^ 2) * (M / (2 * τ) + nR ^ 2 * M ^ 2 * s ^ 2 / (4 * τ ^ 2))
      ≤ 1 / Real.sqrt τ
        * (2 * c * M * r
            + (2 * c * M * r + c * nR ^ 2 * M ^ 2 * r + c * M) * (s ^ 2 / τ)
            + (c * nR ^ 2 * M ^ 2 * r + c * nR ^ 2 * M ^ 2 / 2) * (s ^ 2 / τ) ^ 2) := by
  have hst0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  set st := Real.sqrt τ with hstdef
  have hst2 : st ^ 2 = τ := Real.sq_sqrt hτ.le
  have hst1 : st ≤ 1 := by
    rw [hstdef]
    calc Real.sqrt τ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hτ1
      _ = 1 := Real.sqrt_one
  have hkey : s * st ≤ τ + s ^ 2 := by nlinarith [sq_nonneg (s - st), hst2]
  have h1 : 2 * c * M * r * τ * (s * st) ≤ 2 * c * M * r * τ * (τ + s ^ 2) :=
    mul_le_mul_of_nonneg_left hkey
      (by have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc) hM) hr) hτ.le
          linarith)
  have h2 : c * nR ^ 2 * M ^ 2 * r * s ^ 2 * (s * st)
      ≤ c * nR ^ 2 * M ^ 2 * r * s ^ 2 * (τ + s ^ 2) :=
    mul_le_mul_of_nonneg_left hkey
      (by have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg hc (sq_nonneg nR)) (sq_nonneg M)) hr) (sq_nonneg s)) (le_refl (0:ℝ))
          positivity)
  have h3 : c * M * (s ^ 2 * τ) * st ≤ c * M * (s ^ 2 * τ) * 1 :=
    mul_le_mul_of_nonneg_left hst1 (by positivity)
  have h4 : c * nR ^ 2 * M ^ 2 / 2 * s ^ 4 * st ≤ c * nR ^ 2 * M ^ 2 / 2 * s ^ 4 * 1 :=
    mul_le_mul_of_nonneg_left hst1 (by positivity)
  have hpoly : c * st * (4 * r * s + 2 * s ^ 2) * (M * τ / 2 + nR ^ 2 * M ^ 2 * s ^ 2 / 4)
      ≤ 2 * c * M * r * τ ^ 2
        + (2 * c * M * r + c * nR ^ 2 * M ^ 2 * r + c * M) * (s ^ 2 * τ)
        + (c * nR ^ 2 * M ^ 2 * r + c * nR ^ 2 * M ^ 2 / 2) * s ^ 4 := by
    nlinarith [h1, h2, h3, h4]
  have hτne : τ ≠ 0 := hτ.ne'
  have hstne : st ≠ 0 := hst0.ne'
  have hdenpos : (0 : ℝ) < st * τ ^ 2 := by positivity
  calc c * (4 * r * s + 2 * s ^ 2) * (M / (2 * τ) + nR ^ 2 * M ^ 2 * s ^ 2 / (4 * τ ^ 2))
      = c * st * (4 * r * s + 2 * s ^ 2) * (M * τ / 2 + nR ^ 2 * M ^ 2 * s ^ 2 / 4)
        / (st * τ ^ 2) := by
        field_simp
    _ ≤ (2 * c * M * r * τ ^ 2
          + (2 * c * M * r + c * nR ^ 2 * M ^ 2 * r + c * M) * (s ^ 2 * τ)
          + (c * nR ^ 2 * M ^ 2 * r + c * nR ^ 2 * M ^ 2 / 2) * s ^ 4) / (st * τ ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hpoly (inv_nonneg.mpr hdenpos.le)
    _ = 1 / st
        * (2 * c * M * r
            + (2 * c * M * r + c * nR ^ 2 * M ^ 2 * r + c * M) * (s ^ 2 / τ)
            + (c * nR ^ 2 * M ^ 2 * r + c * nR ^ 2 * M ^ 2 / 2) * (s ^ 2 / τ) ^ 2) := by
        field_simp

/-! ### 4. ★ The J4-610 target: `FrozenDefectBound` inhabited at width `lam = 2`. -/

/-- **★ THE τ^{−1/2} LEVI DEFECT BOUND (J4-610).**  For every `K ≤ 0` and `r ≥ 0` there is an
    explicit `C > 0` with `FrozenDefectBound n K r C 2`: uniformly over `0 < τ ≤ 1`, `q` in the
    ball and ALL `v`,
        `|∑ᵢⱼ (gⁱʲ(q+v) − gⁱʲ(q))·∂ᵢ∂ⱼΓ_q(τ,v)| ≤ (C/√τ)·G_{2τ}(v)`.
    `C = n²·√(n!·Mⁿ)·(K₀C₀ + K₁C₁ + K₂C₂) + 1` with `M = 1 + (−K/3)r²`, the `Kᵢ` the scalar-fold
    coefficients (explicit in `K, r, n`) and `Cₖ` the banked width-2 absorption constants.
    HONEST: exponent exactly `τ^{−1/2}`; width exactly `2τ`; no smallness condition on `r` or `v`
    (`K ≤ 0` branch: `g^K ≥ δ` globally). -/
theorem frozenDefectBound_spaceForm (K : ℝ) (hK : K ≤ 0) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ FrozenDefectBound n K r C 2 := by
  obtain ⟨C₀, hC₀, hb₀⟩ := gaussDdim_absorb_zero (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₁, hC₁, hb₁⟩ := gaussDdim_absorb_one (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hb₂⟩ := gaussDdim_absorb_two (n := n) (η := 0) (lam := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hk0 : (0 : ℝ) ≤ -K / 3 := by linarith
  set M : ℝ := 1 + -K / 3 * r ^ 2 with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; nlinarith [sq_nonneg r]
  set D : ℝ := Real.sqrt ((Nat.factorial n : ℝ) * M ^ n) with hDdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  set K₀ : ℝ := 2 * (-K / 3) * M * r with hK₀def
  set K₁ : ℝ := 2 * (-K / 3) * M * r + -K / 3 * (n : ℝ) ^ 2 * M ^ 2 * r + -K / 3 * M
    with hK₁def
  set K₂ : ℝ := -K / 3 * (n : ℝ) ^ 2 * M ^ 2 * r + -K / 3 * (n : ℝ) ^ 2 * M ^ 2 / 2
    with hK₂def
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk0) hM0) hr
  have hK₁0 : 0 ≤ K₁ := by
    rw [hK₁def]
    have ha : 0 ≤ 2 * (-K / 3) * M * r :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk0) hM0) hr
    have hb : 0 ≤ -K / 3 * (n : ℝ) ^ 2 * M ^ 2 * r :=
      mul_nonneg (mul_nonneg (mul_nonneg hk0 (sq_nonneg _)) (sq_nonneg _)) hr
    have hcM : 0 ≤ -K / 3 * M := mul_nonneg hk0 hM0
    linarith
  have hK₂0 : 0 ≤ K₂ := by
    rw [hK₂def]
    have ha : 0 ≤ -K / 3 * (n : ℝ) ^ 2 * M ^ 2 * r :=
      mul_nonneg (mul_nonneg (mul_nonneg hk0 (sq_nonneg _)) (sq_nonneg _)) hr
    have hb : 0 ≤ -K / 3 * (n : ℝ) ^ 2 * M ^ 2 / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hk0 (sq_nonneg _)) (sq_nonneg _)) (by norm_num)
    linarith
  have hSum0 : 0 ≤ K₀ * C₀ + K₁ * C₁ + K₂ * C₂ :=
    add_nonneg (add_nonneg (mul_nonneg hK₀0 hC₀.le) (mul_nonneg hK₁0 hC₁.le))
      (mul_nonneg hK₂0 hC₂.le)
  have hA0 : 0 ≤ (n : ℝ) ^ 2 * D * (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hD0) hSum0
  refine ⟨(n : ℝ) ^ 2 * D * (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) + 1, by linarith, ?_⟩
  intro τ hτ hτ1 q v hq
  set s := Real.sqrt (rncRadialSq v) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = rncRadialSq v := Real.sq_sqrt (rncRadialSq_nonneg v)
  have hG0 : 0 ≤ gaussDdim τ v := by rw [gaussDdim_closed]; positivity
  have hG20 : 0 ≤ gaussDdim (2 * τ) v := by rw [gaussDdim_closed]; positivity
  have hgate : (1 - 0) * rncRadialSq v ≤ rncRadialSq v := by norm_num
  have hcoef0 : 0 ≤ M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2) := by
    apply add_nonneg (div_nonneg hM0 (by positivity))
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (rncRadialSq_nonneg v)) (by positivity)
  have hDG0 : 0 ≤ D * gaussDdim τ v := mul_nonneg hD0 hG0
  have hB0 : 0 ≤ -K / 3 * (4 * r * s + 2 * rncRadialSq v) := by
    apply mul_nonneg hk0
    have h4 : 0 ≤ 4 * r * s := mul_nonneg (mul_nonneg (by norm_num) hr) hs0
    have hv0 := rncRadialSq_nonneg v
    linarith
  -- per-term bound
  have hterm : ∀ i j : Fin n,
      |(curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
        * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
      ≤ (-K / 3 * (4 * r * s + 2 * rncRadialSq v))
        * ((M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
            * (D * gaussDdim τ v)) := by
    intro i j
    rw [abs_mul]
    apply mul_le_mul (curvedRNCInv_diff_bound K hK r hr q v hq i j) ?_ (abs_nonneg _) hB0
    calc |pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
        ≤ (M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
          * frozenGauss (curvedRNCMetric K q) τ v :=
          frozenGauss_pd_pd_abs_le K hK r q hq τ hτ v i j
      _ ≤ (M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
          * (D * gaussDdim τ v) :=
          mul_le_mul_of_nonneg_left
            (frozenGauss_le_detBound_mul_gauss K hK r q hq τ hτ v) hcoef0
  -- sum bound
  have hsum : |∑ i, ∑ j,
        (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
          * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
      ≤ (n : ℝ) ^ 2 * ((-K / 3 * (4 * r * s + 2 * rncRadialSq v))
          * ((M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
              * (D * gaussDdim τ v))) := by
    calc |∑ i, ∑ j,
          (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
            * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
        ≤ ∑ i, |∑ j,
            (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
              * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, |(curvedRNCInv K (fun a => q a + v a) i j
              - curvedRNCInv K q i j)
              * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (-K / 3 * (4 * r * s + 2 * rncRadialSq v))
            * ((M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                * (D * gaussDdim τ v)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = (n : ℝ) ^ 2 * ((-K / 3 * (4 * r * s + 2 * rncRadialSq v))
            * ((M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
                * (D * gaussDdim τ v))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  -- fold the scalar coefficient to (K₀ + K₁ x + K₂ x²)/√τ
  have hfold : (-K / 3 * (4 * r * s + 2 * rncRadialSq v))
        * (M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
      ≤ 1 / Real.sqrt τ
        * (K₀ + K₁ * (rncRadialSq v / τ) + K₂ * (rncRadialSq v / τ) ^ 2) := by
    have h := defect_scalar_fold (-K / 3) M r ((n : ℝ)) hk0 hM0 hr (Nat.cast_nonneg n)
      τ hτ hτ1 s hs0
    rw [hs2] at h
    exact h
  -- absorption at width 2
  have habs : K₀ * gaussDdim τ v + K₁ * ((rncRadialSq v / τ) * gaussDdim τ v)
        + K₂ * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v)
      ≤ (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) * gaussDdim (2 * τ) v := by
    have h0 := hb₀ τ hτ v v hgate
    have h1 := hb₁ τ hτ v v hgate
    have h2 := hb₂ τ hτ v v hgate
    calc K₀ * gaussDdim τ v + K₁ * ((rncRadialSq v / τ) * gaussDdim τ v)
          + K₂ * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v)
        ≤ K₀ * (C₀ * gaussDdim (2 * τ) v) + K₁ * (C₁ * gaussDdim (2 * τ) v)
          + K₂ * (C₂ * gaussDdim (2 * τ) v) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hK₀0)
            (mul_le_mul_of_nonneg_left h1 hK₁0)) (mul_le_mul_of_nonneg_left h2 hK₂0)
      _ = (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) * gaussDdim (2 * τ) v := by ring
  -- final assembly
  have hstpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  calc |∑ i, ∑ j,
        (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
          * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v|
      ≤ (n : ℝ) ^ 2 * ((-K / 3 * (4 * r * s + 2 * rncRadialSq v))
          * ((M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2))
              * (D * gaussDdim τ v))) := hsum
    _ = (n : ℝ) ^ 2 * D * (((-K / 3 * (4 * r * s + 2 * rncRadialSq v))
          * (M / (2 * τ) + (n : ℝ) ^ 2 * M ^ 2 * rncRadialSq v / (4 * τ ^ 2)))
            * gaussDdim τ v) := by ring
    _ ≤ (n : ℝ) ^ 2 * D * ((1 / Real.sqrt τ
          * (K₀ + K₁ * (rncRadialSq v / τ) + K₂ * (rncRadialSq v / τ) ^ 2))
            * gaussDdim τ v) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) hD0)
        exact mul_le_mul_of_nonneg_right hfold hG0
    _ = 1 / Real.sqrt τ * ((n : ℝ) ^ 2 * D
          * (K₀ * gaussDdim τ v + K₁ * ((rncRadialSq v / τ) * gaussDdim τ v)
              + K₂ * ((rncRadialSq v / τ) ^ 2 * gaussDdim τ v))) := by ring
    _ ≤ 1 / Real.sqrt τ * ((n : ℝ) ^ 2 * D
          * ((K₀ * C₀ + K₁ * C₁ + K₂ * C₂) * gaussDdim (2 * τ) v)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left habs (mul_nonneg (sq_nonneg _) hD0)
    _ = (n : ℝ) ^ 2 * D * (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) * gaussDdim (2 * τ) v
          / Real.sqrt τ := by ring
    _ ≤ ((n : ℝ) ^ 2 * D * (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) + 1) * gaussDdim (2 * τ) v
          / Real.sqrt τ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hstpos.le)
        exact mul_le_mul_of_nonneg_right (by linarith) hG20
    _ = ((n : ℝ) ^ 2 * D * (K₀ * C₀ + K₁ * C₁ + K₂ * C₂) + 1) / Real.sqrt τ
          * gaussDdim (2 * τ) v := by ring

/-! ### 5. Non-vacuity: the bounded defect is genuinely nonzero in the antecedent range. -/

/-- The probe vector: the `i0`-th unit coordinate vector. -/
noncomputable def frozenDefectProbe (i0 : Fin n) : Point n :=
  fun k => if k = i0 then (1 : ℝ) else 0

theorem frozenDefectProbe_apply_self (i0 : Fin n) : frozenDefectProbe i0 i0 = 1 :=
  if_pos rfl

theorem frozenDefectProbe_apply_ne {i0 k : Fin n} (h : k ≠ i0) :
    frozenDefectProbe i0 k = 0 := if_neg h

theorem frozenDefectProbe_radialSq (i0 : Fin n) :
    rncRadialSq (frozenDefectProbe i0) = 1 := by
  simp only [rncRadialSq, frozenDefectProbe]
  have h1 : ∀ k : Fin n, (if k = i0 then (1 : ℝ) else 0) ^ 2
      = if k = i0 then (1 : ℝ) else 0 := by
    intro k; by_cases h : k = i0 <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_ite_eq']
  simp

theorem frozenDefectProbe_mul_ne (i0 : Fin n) {i j : Fin n} (hij : i ≠ j) :
    frozenDefectProbe i0 i * frozenDefectProbe i0 j = 0 := by
  by_cases hi : i = i0
  · have hj : j ≠ i0 := fun h => hij (hi.trans h.symm)
    rw [frozenDefectProbe_apply_ne hj, mul_zero]
  · rw [frozenDefectProbe_apply_ne hi, zero_mul]

theorem frozenDefectProbe_row (i0 i : Fin n) :
    (∑ k, (if i = k then (1 : ℝ) else 0) * frozenDefectProbe i0 k)
      = frozenDefectProbe i0 i := by
  have h1 : ∀ k : Fin n, (if i = k then (1 : ℝ) else 0) * frozenDefectProbe i0 k
      = if i = k then frozenDefectProbe i0 k else 0 := by
    intro k; by_cases h : i = k <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_ite_eq]
  simp

/-- **NON-VACUITY GATE (adversarial).**  For `K < 0`, `n ≥ 2`, ANY ball radius `r` and ANY
    `τ > 0`, there are `q, v` IN the `FrozenDefectBound` antecedent range (`q = 0` is in every
    ball; `v` = unit vector) at which the bounded defect sum is NONZERO — it evaluates to
    `∑_{i≠i0}(1/(1−K/3) − 1)·(−Γ/(2τ)) = (n−1)·(1−1/(1−K/3))·Γ/(2τ) > 0`.  The τ^{−1/2} bound
    is therefore exercised at a genuinely nonzero, genuinely curved defect — not vacuously
    about `0`. -/
theorem frozenDefect_witness_ne_zero (K : ℝ) (hKlt : K < 0) (hn : 2 ≤ n)
    (r τ : ℝ) (hτ : 0 < τ) :
    ∃ q v : Point n, rncRadialSq q ≤ r ^ 2 ∧
      (∑ i, ∑ j, (curvedRNCInv K (fun a => q a + v a) i j - curvedRNCInv K q i j)
          * pd (fun y => pd (fun z => frozenGauss (curvedRNCMetric K q) τ z) j y) i v)
        ≠ 0 := by
  have h0n : 0 < n := by omega
  have h1n : 1 < n := by omega
  have hβ : (1 : ℝ) < 1 - K / 3 := by linarith
  have hβ0 : (0 : ℝ) < 1 - K / 3 := by linarith
  refine ⟨0, frozenDefectProbe ⟨0, h0n⟩, ?_, ?_⟩
  · have h : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
    rw [h]; positivity
  · set i0 : Fin n := ⟨0, h0n⟩
    set i1 : Fin n := ⟨1, h1n⟩
    have hzeroadd : (fun a => (0 : Point n) a + frozenDefectProbe i0 a)
        = frozenDefectProbe i0 := by
      funext a; simp
    have hA0 : curvedRNCMetric K (0 : Point n)
        = (fun a b => if a = b then (1 : ℝ) else 0) :=
      funext fun a => funext fun b => curvedRNCMetric_zero K a b
    have hgi0 : curvedRNCInv K (0 : Point n)
        = (fun a b => if a = b then (1 : ℝ) else 0) :=
      funext fun a => funext fun b => curvedRNCInv_zero K a b
    rw [hzeroadd, hA0, hgi0]
    -- the flat matrix data
    have hδsym : ∀ a b : Fin n,
        (fun a b => if a = b then (1 : ℝ) else 0) a b
          = (fun a b => if a = b then (1 : ℝ) else 0) b a := by
      intro a b
      by_cases h : a = b
      · subst h; rfl
      · simp only [if_neg h, if_neg (Ne.symm h)]
    have hΓpos : 0 < frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ
        (frozenDefectProbe i0) :=
      frozenGauss_pos _ τ hτ (by rw [det_delta]; norm_num) _
    -- the exact diagonal pd·pd value
    have hPdiag : ∀ i : Fin n,
        pd (fun y => pd (fun z =>
            frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ z) i y) i
          (frozenDefectProbe i0)
        = (-(1 : ℝ) / (2 * τ)
            + frozenDefectProbe i0 i * frozenDefectProbe i0 i / (4 * τ ^ 2))
          * frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ
            (frozenDefectProbe i0) := by
      intro i
      rw [frozenGauss_pd_pd (fun a b => if a = b then (1 : ℝ) else 0) hδsym τ hτ
        (frozenDefectProbe i0) i i]
      have hrow : (∑ k, (if i = k then (1 : ℝ) else 0) * frozenDefectProbe i0 k)
          = frozenDefectProbe i0 i := frozenDefectProbe_row i0 i
      simp only []
      rw [hrow]
      simp
    -- Δ vanishes off-diagonal
    have hoffΔ : ∀ i j : Fin n, i ≠ j →
        curvedRNCInv K (frozenDefectProbe i0) i j - (if i = j then (1 : ℝ) else 0) = 0 := by
      intro i j hij
      have hmul : frozenDefectProbe i0 i * frozenDefectProbe i0 j = 0 :=
        frozenDefectProbe_mul_ne i0 hij
      simp only [curvedRNCInv, if_neg hij, frozenDefectProbe_radialSq]
      rw [mul_assoc, hmul, mul_zero]
      simp
    -- Δ vanishes at the i0-diagonal
    have hΔi0 : curvedRNCInv K (frozenDefectProbe i0) i0 i0
        - (if i0 = i0 then (1 : ℝ) else 0) = 0 := by
      have hbne : (1 : ℝ) - K / 3 ≠ 0 := hβ0.ne'
      have h3K : (3 : ℝ) - K ≠ 0 := by intro hc; linarith
      simp only [curvedRNCInv, frozenDefectProbe_radialSq, frozenDefectProbe_apply_self,
        eq_self_iff_true, if_true, mul_one]
      field_simp
      norm_num
    -- Δ at an off-center diagonal
    have hΔdiag : ∀ i : Fin n, i ≠ i0 →
        curvedRNCInv K (frozenDefectProbe i0) i i - (if i = i then (1 : ℝ) else 0)
          = 1 / (1 - K / 3) - 1 := by
      intro i hi
      simp only [curvedRNCInv, if_pos rfl, frozenDefectProbe_radialSq,
        frozenDefectProbe_apply_ne hi]
      norm_num
    -- the diagonal term is positive off-center
    have hpos : ∀ i : Fin n, i ≠ i0 →
        0 < (curvedRNCInv K (frozenDefectProbe i0) i i - (if i = i then (1 : ℝ) else 0))
          * pd (fun y => pd (fun z =>
              frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ z) i y) i
            (frozenDefectProbe i0) := by
      intro i hi
      rw [hΔdiag i hi, hPdiag i, frozenDefectProbe_apply_ne hi]
      have hΔneg : 1 / (1 - K / 3) - 1 < 0 := by
        have h1 : 1 / (1 - K / 3) < 1 := by
          rw [div_lt_one hβ0]; linarith
        linarith
      have hcoef : (-(1 : ℝ) / (2 * τ) + 0 * 0 / (4 * τ ^ 2)) = -(1 / (2 * τ)) := by
        ring
      rw [hcoef]
      have hPneg : -(1 / (2 * τ))
          * frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ
            (frozenDefectProbe i0) < 0 := by
        apply mul_neg_of_neg_of_pos _ hΓpos
        have : (0 : ℝ) < 1 / (2 * τ) := by positivity
        linarith
      exact mul_pos_of_neg_of_neg hΔneg hPneg
    -- collapse the inner sums to the diagonal
    have hinner : ∀ i : Fin n,
        (∑ j, (curvedRNCInv K (frozenDefectProbe i0) i j - (if i = j then (1 : ℝ) else 0))
            * pd (fun y => pd (fun z =>
                frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ z) j y) i
              (frozenDefectProbe i0))
        = (curvedRNCInv K (frozenDefectProbe i0) i i - (if i = i then (1 : ℝ) else 0))
            * pd (fun y => pd (fun z =>
                frozenGauss (fun a b => if a = b then (1 : ℝ) else 0) τ z) i y) i
              (frozenDefectProbe i0) := by
      intro i
      apply Finset.sum_eq_single
      · intro j _ hji
        rw [hoffΔ i j fun h => hji h.symm, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    apply ne_of_gt
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : i = i0
      · subst hi
        rw [hΔi0, zero_mul]
      · exact (hpos i hi).le
    · refine ⟨i1, Finset.mem_univ i1, hpos i1 ?_⟩
      exact Fin.ne_of_val_ne (by norm_num)

/-! ### 6. GO/NO-GO recon certificates (Sol's checks). -/

/-- **GO/NO-GO 1 CERTIFICATE — the width-2 CLOSED fold.**  The D2 engine's width-2 Gaussian
    model folds at FIXED width under convolution: `G_{2t} * G_{2s} = G_{2(t+s)}` — the width
    factor 2 is invariant (times add, width does not double).  Re-export of the banked
    rescaled-width semigroup identity; this is the mechanism by which `iterKernelW 2 α k`
    carries `gaussDdim (2t)` at EVERY iterate `k`. -/
theorem width2_closed_fold (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (x y : Point n) :
    ∫ z : Point n, gaussDdim (2 * t) (x - z) * gaussDdim (2 * s) (z - y)
      = gaussDdim (2 * (t + s)) (x - y) :=
  QIQTH.GaussianWidthTolerant.gaussDdim_conv_scaled 2 t s (by norm_num) ht hs x y

/-- **GO/NO-GO 2 CERTIFICATE (per-step half) — the α = −1/2 time convolution converges.**
    `∫₀ᵗ (t−s)^{−1/2}·s^{−1/2} ds = π` exactly (Beta/Γ machinery at `a = b = −1/2 > −1`;
    `Γ(1/2)² / Γ(1) = π`, `t⁰ = 1`).  The `−1 < α` per-step engine admits `α = −1/2`.
    ⚠ The SERIES half (`modelCoeff_summable` / `gamma_ratio_tendsto_zero`) is `0 ≤ α` only as
    the code stands — a reported α-generalization gap, NOT certified here. -/
theorem betaTime_negHalf_integral (t : ℝ) (ht : 0 < t) :
    (∫ s in (0:ℝ)..t, (t - s) ^ (-(1/2) : ℝ) * s ^ (-(1/2) : ℝ)) = Real.pi := by
  have h := QIQTH.GaussianConvBound.betaTimeIntegral_eq (-(1/2)) (-(1/2))
    (by norm_num) (by norm_num) t ht
  rw [show (-(1/2) : ℝ) + -(1/2) + 1 = 0 by norm_num,
      show (-(1/2) : ℝ) + 1 = 1/2 by norm_num,
      show (-(1/2) : ℝ) + -(1/2) + 2 = 1 by norm_num,
      Real.rpow_zero, Real.Gamma_one, Real.Gamma_one_half_eq] at h
  rw [h, one_mul, div_one, Real.mul_self_sqrt Real.pi_pos.le]

end QIQTH.FrozenDefect
