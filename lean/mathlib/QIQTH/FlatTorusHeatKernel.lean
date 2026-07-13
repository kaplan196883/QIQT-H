import Mathlib

/-!
# The heat trace on the flat circle `ℝ/ℤ` (unit 1-torus)

**What this file proves.** The heat trace of `e^{tΔ}` on the FLAT circle `ℝ/ℤ` (unit torus,
circumference/volume `1`): the explicit spectral sum
`Tr e^{tΔ} = Σ_{k∈ℤ} e^{-t (2πk)²} = Σ_{k∈ℤ} e^{-4π²t k²}`, shown here to equal
`jacobiTheta (I · 4πt)` (`heatTraceCircle_eq_jacobiTheta`) with the short-time (Weyl /
Seeley–DeWitt) asymptotic `heatTraceCircle t ~ (4πt)^{-1/2}` as `t → 0⁺`
(`heatTraceCircle_asymptotic`) — i.e. the leading `a₀ · vol · (4πt)^{-d/2}` term for `d = 1`,
`vol = 1`, `a₀ = 1`.

**Firewall (binding, honest).**

* This BREAKS THE HEAT-KERNEL WALL ONLY FOR THIS SPECIFIC FLAT GEOMETRY. On `ℝ/ℤ` the operator
  `-Δ` has the *explicit* Fourier eigenbasis `eₖ(x) = e^{2πikx}` with eigenvalues `λₖ = (2πk)²`
  (elementary: `∂ₓ² eₖ = -(2πk)² eₖ`; the algebra is `laplacian_eigenvalue_circle`). Because the
  spectrum `{(2πk)²}` and eigenfunctions are explicit, the heat trace is a *concrete Fourier
  series* and needs NONE of the missing infrastructure — no Rellich compactness, no elliptic
  regularity, no general trace-class API, no manifold-`L²`/`Δ` machinery. The GENERAL (curved)
  manifold heat kernel remains the WALL.

* FLAT ⟹ `R = 0`: this validates the leading Weyl coefficient `a₀ = 1` but NOT `a₁ = R/6`
  (which needs curvature — the flat torus has `a₁ = 0`). The `a₁ = R/6` analytic discharge stays
  open.

* The "trace" here is the spectral sum in the (canonical) Fourier eigenbasis — honest for this
  diagonal operator; it is NOT a general basis-independent trace (that would need the absent
  trace-class API).

* This is NOT the conjecture, NOT the strong holographic principle, NOT quantum gravity. It uses
  Mathlib's `jacobiTheta` and its `S`-transformation functional equation `jacobiTheta_S_smul`
  (`θ(-1/τ) = √(-iτ)·θ(τ)`) plus the `i∞`-bound `norm_jacobiTheta_sub_one_le`. No `axiom`, no
  `sorry`.
-/

namespace QIQTH.FlatTorusHeatKernel

open scoped Real
open Filter Topology

/-- The flat-circle spectral heat trace `Tr e^{tΔ} = Σ_{k∈ℤ} e^{-t (2πk)²}` on `ℝ/ℤ`. -/
noncomputable def heatTraceCircle (t : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-(4 * π ^ 2 * t) * (k : ℝ) ^ 2)

/-- The heat-trace summand has Gaussian decay, so the spectral sum converges (for `t > 0`).
The eigenvalues `(2πk)²` grow quadratically; this is the elementary Fourier fact that on a flat
torus no compactness/regularity input is needed. -/
theorem heatTraceCircle_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℤ => Real.exp (-(4 * π ^ 2 * t) * (k : ℝ) ^ 2)) := by
  have hτim : (Complex.I * ((4 * π * t : ℝ) : ℂ)).im = 4 * π * t := by
    simp [Complex.mul_im]
  have hτpos : 0 < (Complex.I * ((4 * π * t : ℝ) : ℂ)).im := by rw [hτim]; positivity
  have hc : Summable (fun n : ℤ => jacobiTheta₂_term n 0 (Complex.I * ((4 * π * t : ℝ) : ℂ))) :=
    (summable_jacobiTheta₂_term_iff 0 _).mpr hτpos
  have hn : Summable (fun n : ℤ => ‖jacobiTheta₂_term n 0 (Complex.I * ((4 * π * t : ℝ) : ℂ))‖) :=
    summable_norm_iff.mpr hc
  refine hn.congr (fun n => ?_)
  rw [norm_jacobiTheta₂_term, hτim]
  simp only [Complex.zero_im, mul_zero, sub_zero]
  congr 1
  push_cast
  ring

/-- **Heat trace = Jacobi theta.** The flat-circle heat trace is exactly Mathlib's Jacobi theta
function evaluated at `τ = I · 4πt`, since `jacobiTheta τ = Σ_k exp(π I k² τ)` and
`π I k² (I · 4πt) = -4π²t k²`. -/
theorem heatTraceCircle_eq_jacobiTheta {t : ℝ} (ht : 0 < t) :
    (heatTraceCircle t : ℂ) = jacobiTheta (Complex.I * (4 * π * t)) := by
  unfold heatTraceCircle
  rw [Complex.ofReal_tsum]
  unfold jacobiTheta
  refine tsum_congr (fun k => ?_)
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination (-(4 * (π : ℂ) ^ 2 * (t : ℂ)) * (k : ℂ) ^ 2) * Complex.I_sq

/-- **The theta `S`-transformation, specialised to the imaginary axis.** For `a > 0`,
`√a · jacobiTheta (I·a) = jacobiTheta (I/a)`. This is Mathlib's `jacobiTheta_S_smul`
(`θ(-1/τ) = √(-iτ)·θ(τ)`) at the purely-imaginary point `τ = I·a`, where `-1/τ = I/a` and
`√(-iτ) = √a`. -/
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
  -- Compute the image point `↑(S • τ) = I / a`.
  have hS : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = Complex.I / (a : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, hcτ]
    have hone : (Complex.I / (a : ℂ)) * (-(Complex.I * (a : ℂ))) = 1 := by
      have hrw : (Complex.I / (a : ℂ)) * (-(Complex.I * (a : ℂ)))
          = (-(Complex.I * Complex.I)) * ((a : ℂ) / (a : ℂ)) := by ring
      rw [hrw, Complex.I_mul_I, div_self hane]; ring
    exact inv_eq_of_mul_eq_one_left hone
  -- Compute the prefactor `(-I · τ)^{1/2} = √a`.
  have hfac : (-Complex.I * (Complex.I * (a : ℂ))) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    have hbase : -Complex.I * (Complex.I * (a : ℂ)) = (a : ℂ) := by
      have h2 : -Complex.I * (Complex.I * (a : ℂ)) = (-(Complex.I * Complex.I)) * (a : ℂ) := by
        ring
      rw [h2, Complex.I_mul_I]; ring
    rw [hbase, Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
    norm_num
  rw [hS, hfac] at key
  exact key.symm

/-- **Short-time (Weyl) asymptotic.** `√(4πt) · heatTraceCircle t → 1` as `t → 0⁺`, i.e.
`heatTraceCircle t ~ (4πt)^{-1/2}`. This is the leading `a₀ · vol · (4πt)^{-d/2}` Seeley–DeWitt
term for `d = 1`, `vol = 1`, `a₀ = 1`. The proof feeds the `S`-transformation `theta_funeq`
(so `√(4πt)·jacobiTheta(I·4πt) = jacobiTheta(I/4πt)`) and the fact that `jacobiTheta(I/4πt) → 1`
as `t → 0⁺` (its argument has imaginary part `1/(4πt) → +∞`, so `norm_jacobiTheta_sub_one_le`
squeezes it to `1`). -/
theorem heatTraceCircle_asymptotic :
    Filter.Tendsto (fun t : ℝ => Real.sqrt (4 * π * t) * heatTraceCircle t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  -- Imaginary part of the transformed argument.
  have hσim : ∀ t : ℝ, (Complex.I / ((4 * π * t : ℝ) : ℂ)).im = (4 * π * t)⁻¹ := by
    intro t
    rw [div_eq_mul_inv, ← Complex.ofReal_inv]
    simp [Complex.mul_im]
  -- `jacobiTheta (I / 4πt) → 1` as `t → 0⁺`.
  have htheta : Tendsto (fun t : ℝ => jacobiTheta (Complex.I / ((4 * π * t : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hinv : Tendsto (fun t : ℝ => (4 * π * t)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
      have h1 : Tendsto (fun t : ℝ => (4 * π)⁻¹ * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
        Tendsto.const_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
      refine h1.congr (fun t => ?_)
      rw [← mul_inv]
    have hg : Tendsto (fun t : ℝ => -π * (4 * π * t)⁻¹) (𝓝[>] (0 : ℝ)) atBot :=
      hinv.const_mul_atTop_of_neg (neg_lt_zero.mpr Real.pi_pos)
    have hE : Tendsto (fun t : ℝ => Real.exp (-π * (4 * π * t)⁻¹)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hg
    have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-π * (4 * π * t)⁻¹))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hE
    have hBd : Tendsto (fun t : ℝ =>
        2 / (1 - Real.exp (-π * (4 * π * t)⁻¹)) * Real.exp (-π * (4 * π * t)⁻¹))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => 2 / (1 - Real.exp (-π * (4 * π * t)⁻¹)))
          (𝓝[>] (0 : ℝ)) (𝓝 2) := by
        simpa using tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0)
      simpa using h2.mul hE
    have hsub : Tendsto (fun t : ℝ => jacobiTheta (Complex.I / ((4 * π * t : ℝ) : ℂ)) - 1)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hBd
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have hσpos : 0 < (Complex.I / ((4 * π * t : ℝ) : ℂ)).im := by rw [hσim t]; positivity
      have hb := norm_jacobiTheta_sub_one_le hσpos
      rw [hσim t] at hb
      exact hb
    have hfin := hsub.add (tendsto_const_nhds (x := (1 : ℂ)))
    simpa using hfin
  -- Rewrite the (complexified) target as `jacobiTheta (I / 4πt)` on `t > 0`.
  have heq : (fun t : ℝ => ((Real.sqrt (4 * π * t) : ℝ) : ℂ) * ((heatTraceCircle t : ℝ) : ℂ))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun t : ℝ => jacobiTheta (Complex.I / ((4 * π * t : ℝ) : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    have hapos : (0 : ℝ) < 4 * π * t := by positivity
    rw [heatTraceCircle_eq_jacobiTheta ht']
    rw [show jacobiTheta (Complex.I * (4 * π * t))
        = jacobiTheta (Complex.I * ((4 * π * t : ℝ) : ℂ)) from by congr 1; push_cast; ring]
    exact theta_funeq hapos
  have hcomplex : Tendsto (fun t : ℝ =>
      ((Real.sqrt (4 * π * t) : ℝ) : ℂ) * ((heatTraceCircle t : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := htheta.congr' heq.symm
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simp only [Complex.one_re] at hre
  refine hre.congr (fun t => ?_)
  rw [Function.comp_apply, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The eigenvalue algebra grounding `λₖ = (2πk)²`.** The Fourier mode `eₖ(x) = e^{2πikx}`
satisfies `∂ₓ² eₖ = (2πik)² eₖ = -(2πk)² eₖ`, so `-Δ eₖ = (2πk)² eₖ`. Here we record the scalar
identity `(2πik)² = -(2πk)²` that pins the eigenvalue to `(2πk)²`. -/
theorem laplacian_eigenvalue_circle (k : ℤ) :
    (2 * (π : ℂ) * Complex.I * (k : ℂ)) ^ 2 = -(2 * (π : ℂ) * (k : ℂ)) ^ 2 := by
  have h : (2 * (π : ℂ) * Complex.I * (k : ℂ)) ^ 2
      = Complex.I ^ 2 * (2 * (π : ℂ) * (k : ℂ)) ^ 2 := by ring
  rw [h, Complex.I_sq, neg_one_mul]

end QIQTH.FlatTorusHeatKernel
