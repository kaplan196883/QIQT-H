import Mathlib
import QIQTH.SphereHeatTrace
import QIQTH.FlatTorusHeatKernel

/-!
# The heat trace on the product `S² × S¹` (curved, `d = 3`, `R = 2`)

**What this file proves.** The heat trace of `e^{tΔ}` on the Riemannian product `S² × S¹`
(unit 2-sphere times unit circle). On a product manifold the Laplace–Beltrami spectrum is the
*sum* of the factor spectra, so `e^{-t(λ+μ)} = e^{-tλ} e^{-tμ}` and the heat trace **factorizes**:
`Θ_{S²×S¹}(t) = Θ_{S²}(t) · Θ_{S¹}(t)` (`productHeatTrace`, defined as this product of the two
factor traces already formalized in `QIQTH.SphereHeatTrace` and `QIQTH.FlatTorusHeatKernel`).

The Seeley–DeWitt short-time expansion is `t^{3/2} Θ_prod(t) = a₀ + a₁ t + o(t)` with
* `a₀ = vol(S²×S¹)/(4π)^{3/2} = 4π/(4π)^{3/2} = 1/(2√π)` (the Weyl term, `d = 3`, `vol = 4π`);
* `a₁ = a₀ · (R/6)` with `R = R_{S²} + R_{S¹} = 2 + 0 = 2`, i.e. `a₁ = (1/(2√π))·(2/6) = 1/(6√π)`.

This gives a **NEW `(R, a₁)` data point** distinct from `S³`: same dimension `d = 3`, but scalar
curvature `R = 2` (not `S³`'s `R = 6`). Together with the sphere and flat-torus files it confirms
that `a₁` tracks the **scalar curvature `R`, not the dimension `d`**, and that (like `R`) `a₁` is
**additive under Riemannian products** — here `a₁(S²×S¹) = a₁(S²) + a₁(S¹) = 1/3 + 0`, rescaled by
the product Weyl density.

**Main results (all axiom-free, `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`):**
* `productHeatTrace_a0` — the Weyl (`a₀`) limit `t^{3/2} Θ_prod(t) → 1/(2√π)`.
* `productHeatTrace_a1` — the Seeley–DeWitt (`a₁`) limit
  `(t^{3/2} Θ_prod(t) − 1/(2√π))/t → 1/(6√π)`, i.e. `a₁ = R/6` on `S²×S¹`.
* `circle_a0` / `circle_rate` — the two circle-factor inputs: `√t · Θ_{S¹}(t) → 1/(2√π)` and the
  **exp-small remainder rate** `(√(4πt) · Θ_{S¹}(t) − 1)/t → 0` (the one nontrivial analytic step,
  from the Jacobi-theta `S`-transformation + `norm_jacobiTheta_sub_one_le`).
* `product_a1_coeff_eq` — the coefficient tie `1/(6√π) = (1/(2√π))·(2/6)`, exhibiting `a₁ = a₀·R/6`.

**Firewall (binding, honest).** This validates `a₁ = R/6` on ONE MORE explicit geometry — the
CURVED product `S² × S¹` — via the **explicit product spectrum** (the carried classical input: the
factor spectra `{l(l+1), mult 2l+1}` of `−Δ` on `S²` and `{(2πk)²}` on `S¹`, whose sum is the
product spectrum). It reuses NONE of the missing infrastructure (no Rellich compactness, no elliptic
regularity, no trace-class API, no manifold-`L²`/`Δ` machinery, no curved heat-kernel EXISTENCE).
It does **NOT** discharge the GENERAL curved `a₁ = R/6` (the manifold heat-kernel-parametrix /
Seeley–DeWitt wall), which stays open precisely because a general curved spectrum is not explicit.
This is NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity. No `axiom`,
no `sorry`.
-/

namespace QIQTH.ProductHeatTrace

open scoped Real
open Filter Topology
open QIQTH.SphereHeatTrace QIQTH.FlatTorusHeatKernel

/-- The `S² × S¹` heat trace `Θ_{S²×S¹}(t) = Θ_{S²}(t) · Θ_{S¹}(t)`. On a Riemannian product the
Laplacian spectrum is the (multiset) sum of the factor spectra, so `e^{-t(λ+μ)} = e^{-tλ}e^{-tμ}`
and the heat trace of the product is the product of the factor heat traces; we take that product of
the two already-formalized factor traces as the definition. -/
noncomputable def productHeatTrace (t : ℝ) : ℝ :=
  QIQTH.SphereHeatTrace.sphereHeatTrace t * QIQTH.FlatTorusHeatKernel.heatTraceCircle t

/-- `√(4πt) = 2√π · √t` (a nonnegativity-only square-root identity). -/
private lemma sqrt_four_pi_mul (t : ℝ) (_ht : 0 ≤ t) :
    Real.sqrt (4 * π * t) = 2 * Real.sqrt π * Real.sqrt t := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [show (4 : ℝ) * π * t = (4 * π) * t by ring, Real.sqrt_mul (by positivity) t,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) π, h4]

/-- **The theta `S`-transformation on the imaginary axis** (reproduced locally; the version in
`FlatTorusHeatKernel` is `private`). For `a > 0`,
`√a · jacobiTheta (I·a) = jacobiTheta (I/a)` — Mathlib's `jacobiTheta_S_smul` at `τ = I·a`. -/
private lemma theta_funeq {a : ℝ} (ha : 0 < a) :
    (Real.sqrt a : ℂ) * jacobiTheta (Complex.I * (a : ℂ)) = jacobiTheta (Complex.I / (a : ℂ)) := by
  have hane : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hzim : 0 < (Complex.I * (a : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      one_mul, mul_zero, zero_add]
    exact ha
  set τ : UpperHalfPlane := UpperHalfPlane.mk (Complex.I * (a : ℂ)) hzim with hτdef
  have hcτ : (τ : ℂ) = Complex.I * (a : ℂ) := UpperHalfPlane.coe_mk _ hzim
  have key := jacobiTheta_S_smul τ
  rw [hcτ] at key
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = Complex.I / (a : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hcτ]
    have hone : (Complex.I / (a : ℂ)) * (-(Complex.I * (a : ℂ))) = 1 := by
      have hrw : (Complex.I / (a : ℂ)) * (-(Complex.I * (a : ℂ)))
          = (-(Complex.I * Complex.I)) * ((a : ℂ) / (a : ℂ)) := by ring
      rw [hrw, Complex.I_mul_I, div_self hane]; ring
    exact inv_eq_of_mul_eq_one_left hone
  have hfac : (-Complex.I * (Complex.I * (a : ℂ))) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    have hbase : -Complex.I * (Complex.I * (a : ℂ)) = (a : ℂ) := by
      have h2 : -Complex.I * (Complex.I * (a : ℂ)) = (-(Complex.I * Complex.I)) * (a : ℂ) := by
        ring
      rw [h2, Complex.I_mul_I]; ring
    rw [hbase, Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  rw [hS, hfac] at key
  exact key.symm

/-- **Circle `a₀`.** `√t · Θ_{S¹}(t) → 1/(2√π)` as `t → 0⁺` — the leading Weyl term of the unit
circle rescaled by `√t` (from `heatTraceCircle_asymptotic`, `√(4πt)·Θ_{S¹} → 1`, using
`√(4πt) = 2√π√t`). -/
theorem circle_a0 :
    Tendsto (fun t : ℝ => Real.sqrt t * heatTraceCircle t)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 * Real.sqrt π))) := by
  have h := heatTraceCircle_asymptotic.div_const (2 * Real.sqrt π)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [sqrt_four_pi_mul t ht0.le]
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']

/-- **Circle exp-small remainder rate** (the one nontrivial analytic step). As `t → 0⁺`,
`(√(4πt) · Θ_{S¹}(t) − 1)/t → 0`. Because `√(4πt)·Θ_{S¹}(t) = (jacobiTheta (I/(4πt))).re` (theta
`S`-transformation), the remainder is controlled by `norm_jacobiTheta_sub_one_le`:
`‖jacobiTheta σ − 1‖ ≤ 2/(1−e^{−π σ.im})·e^{−π σ.im}` with `σ.im = (4πt)⁻¹`, i.e. an `O(e^{−1/(4t)})`
exponentially small bound, which stays `o(t)` (in fact `o(tⁿ)` for every `n`) since
`x·e^{−x} → 0` as `x = π(4πt)⁻¹ → +∞`. -/
theorem circle_rate :
    Tendsto (fun t : ℝ => (Real.sqrt (4 * π * t) * heatTraceCircle t - 1) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- `(4πt)⁻¹ → +∞` and `π(4πt)⁻¹ → +∞`.
  have hinv : Tendsto (fun t : ℝ => (4 * π * t)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
    have h1 : Tendsto (fun t : ℝ => (4 * π)⁻¹ * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
    refine h1.congr (fun t => ?_)
    rw [← mul_inv]
  have hwtop : Tendsto (fun t : ℝ => π * (4 * π * t)⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Tendsto.const_mul_atTop Real.pi_pos hinv
  -- `e^{−π(4πt)⁻¹} → 0`.
  have hg : Tendsto (fun t : ℝ => -π * (4 * π * t)⁻¹) (𝓝[>] (0 : ℝ)) atBot :=
    hinv.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-π * (4 * π * t)⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hg
  -- `e^{−π(4πt)⁻¹}/t → 0` (super-polynomial decay beats `1/t`).
  have hpe : Tendsto (fun t : ℝ => (π * (4 * π * t)⁻¹) ^ 1 * Real.exp (-(π * (4 * π * t)⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hwtop
  have hexpdivt : Tendsto (fun t : ℝ => Real.exp (-π * (4 * π * t)⁻¹) / t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h4 := hpe.const_mul (4 : ℝ)
    rw [mul_zero] at h4
    refine h4.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [pow_one, show (-π * (4 * π * t)⁻¹) = -(π * (4 * π * t)⁻¹) by ring]
    field_simp [ht0.ne', Real.pi_pos.ne']
  -- The bounding function `D(t) = 2/(1−e^{−π(4πt)⁻¹})·(e^{−π(4πt)⁻¹}/t) → 2·0 = 0`.
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-π * (4 * π * t)⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp0
  have hDfac : Tendsto (fun t : ℝ => 2 / (1 - Real.exp (-π * (4 * π * t)⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hD : Tendsto (fun t : ℝ => 2 / (1 - Real.exp (-π * (4 * π * t)⁻¹))
      * (Real.exp (-π * (4 * π * t)⁻¹) / t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hDfac.mul hexpdivt
    rwa [mul_zero] at h
  -- Squeeze the remainder by `D(t)`.
  refine squeeze_zero_norm' ?_ hD
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hapos : (0 : ℝ) < 4 * π * t := by positivity
  set σ : ℂ := Complex.I / ((4 * π * t : ℝ) : ℂ) with hσ
  -- `(√(4πt)·Θ_{S¹}(t) : ℂ) = jacobiTheta σ`.
  have hCeq : ((Real.sqrt (4 * π * t) : ℝ) : ℂ) * ((heatTraceCircle t : ℝ) : ℂ) = jacobiTheta σ := by
    rw [heatTraceCircle_eq_jacobiTheta ht0,
      show jacobiTheta (Complex.I * (4 * π * t)) = jacobiTheta (Complex.I * ((4 * π * t : ℝ) : ℂ))
        from by congr 1; push_cast; ring]
    rw [hσ]; exact theta_funeq hapos
  have hcast : ((Real.sqrt (4 * π * t) * heatTraceCircle t : ℝ) : ℂ) = jacobiTheta σ := by
    rw [Complex.ofReal_mul]; exact hCeq
  have hre : Real.sqrt (4 * π * t) * heatTraceCircle t = (jacobiTheta σ).re := by
    rw [← hcast, Complex.ofReal_re]
  -- `σ.im = (4πt)⁻¹ > 0`, and the theta bound.
  have hσim : σ.im = (4 * π * t)⁻¹ := by
    rw [hσ, div_eq_mul_inv, ← Complex.ofReal_inv]; simp [Complex.mul_im]
  have hσpos : 0 < σ.im := by rw [hσim]; positivity
  have hbound := norm_jacobiTheta_sub_one_le hσpos
  rw [hσim] at hbound
  -- `|(jacobiTheta σ).re − 1| ≤ ‖jacobiTheta σ − 1‖ ≤ 2/(1−e)·e`.
  have hstep1 : |(jacobiTheta σ).re - 1| ≤ ‖jacobiTheta σ - 1‖ := by
    have he : (jacobiTheta σ).re - 1 = (jacobiTheta σ - 1).re := by simp [Complex.sub_re]
    rw [he]; exact Complex.abs_re_le_norm _
  have hnum : |(jacobiTheta σ).re - 1|
      ≤ 2 / (1 - Real.exp (-π * (4 * π * t)⁻¹)) * Real.exp (-π * (4 * π * t)⁻¹) :=
    hstep1.trans hbound
  rw [Real.norm_eq_abs, hre, abs_div, abs_of_pos ht0, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum ht0.le

/-- **Product Weyl (`a₀`) term.** `t^{3/2} Θ_{S²×S¹}(t) → 1/(2√π) = vol(S²×S¹)/(4π)^{3/2}`
as `t → 0⁺`, since `t^{3/2}Θ_prod = (t·Θ_{S²})·(√t·Θ_{S¹}) → 1 · 1/(2√π)`. -/
theorem productHeatTrace_a0 :
    Tendsto (fun t : ℝ => t ^ ((3 : ℝ) / 2) * productHeatTrace t)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 * Real.sqrt π))) := by
  have hcomb := sphereHeatTrace_asymptotic.mul circle_a0
  rw [one_mul] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have ht32 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht0,
      Real.rpow_one]
  simp only [productHeatTrace]
  rw [ht32]; ring

/-- **★ `a₁ = R/6` on `S² × S¹`.** As `t → 0⁺`,
`(t^{3/2} Θ_{S²×S¹}(t) − 1/(2√π))/t → 1/(6√π)`, i.e. `t^{3/2}Θ_prod = 1/(2√π) + (1/(6√π))·t + o(t)`.
The subleading coefficient `1/(6√π) = a₀·(R/6) = (1/(2√π))·(2/6)` with `R = R_{S²}+R_{S¹} = 2`,
so `a₁ = R/6` on this `d = 3`, `R = 2` geometry — a data point distinct from `S³` (`d = 3`, `R = 6`).
Assembled from `A(t) = t·Θ_{S²} = 1 + (1/3)t + o(t)` (`sphereHeatTrace_a1`), `B(t) = √t·Θ_{S¹} →
1/(2√π)` (`circle_a0`) and the circle rate `(B − 1/(2√π))/t → 0` (`circle_rate`), via
`(A·B − 1/(2√π))/t = ((A−1)/t)·B + (B − 1/(2√π))/t → (1/3)·(1/(2√π)) + 0`. -/
theorem productHeatTrace_a1 :
    Filter.Tendsto (fun t : ℝ => (t ^ ((3 : ℝ) / 2) * productHeatTrace t - 1 / (2 * Real.sqrt π)) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / (6 * Real.sqrt π))) := by
  have hsπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  -- `A`-fact: `(t·Θ_{S²} − 1)/t → 1/3`.
  have hA1 : Tendsto (fun t : ℝ => (t * sphereHeatTrace t - 1) / t) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 3)) := by
    refine sphereHeatTrace_a1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    field_simp
  -- `B`-rate from the circle rate.
  have hBrate : Tendsto (fun t : ℝ => (Real.sqrt t * heatTraceCircle t - 1 / (2 * Real.sqrt π)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := circle_rate.div_const (2 * Real.sqrt π)
    rw [zero_div] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [sqrt_four_pi_mul t ht0.le]
    field_simp
  -- Assemble.
  have hcomb := (hA1.mul circle_a0).add hBrate
  have hlim : (1 : ℝ) / 3 * (1 / (2 * Real.sqrt π)) + 0 = 1 / (6 * Real.sqrt π) := by
    field_simp
    ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have ht32 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht0,
      Real.rpow_one]
  simp only [productHeatTrace]
  rw [ht32]
  field_simp
  ring

/-- **Coefficient tie: `a₁ = a₀ · R/6`.** The subleading coefficient factors as the Weyl density
`a₀ = 1/(2√π)` times `R/6 = 2/6`, exhibiting `a₁ = R/6` on `S²×S¹` (`R = 2`). -/
theorem product_a1_coeff_eq :
    1 / (6 * Real.sqrt π) = (1 / (2 * Real.sqrt π)) * (2 / 6) := by
  have hsπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

end QIQTH.ProductHeatTrace
