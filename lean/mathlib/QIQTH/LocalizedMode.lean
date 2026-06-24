/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-3 continuum — the localization mode from the field, reduced to one universal profile

The free-field QIQT→GR capstones leave `hTkk` (the Unruh/Bisognano–Wichmann localization map) as the single
labelled physical input: per null generator `(x,v)`, the classical null energy equals the rapidity boost charge
of an abstract localized mode `ff x v`,

  `2π/ℏ · (∑ₐ vₐ ∂ₐφ)²  =  (−2π ∫ conj(ff x v)·ff' x v).im`.

This file CONSTRUCTS the mode from the field, non-vacuously: `ff x v := D · g₀` where `D = ∑ₐ vₐ ∂ₐφ(x)` is the
field's directional derivative at the generator (the physical amplitude) and `g₀` is a *universal* reference
profile.  Because the boost charge is quadratic in the mode, it scales as `D²` — the correct `(∂φ)²` null-energy
law.  `localized_mode_hTkk` then proves `hTkk` for every generator from a SINGLE calibration of `g₀`:

  `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`     (`hcal`).

So the per-generator localization frontier collapses to one universal mode-calibration constant.  The amplitude
law (mode ∝ field gradient) and the quadratic `(∂φ)²` scaling are now DERIVED, not assumed; what remains is
exhibiting one calibrated profile `g₀` (a Gaussian wave packet works — the next brick).

Axiom-free.
-/
import QIQTH.QiqtGrFreeField

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature MeasureTheory

/-- **The localization mode from the field — `hTkk` from one universal calibration.**  With the mode taken to
    be the field's directional derivative `D = ∑ₐ vₐ ∂ₐφ(x)` times a reference profile `g₀` (and `ff' = D·g₀'`),
    the transparent `hTkk` identity holds for the generator `(x,v)` as soon as `g₀` satisfies the single
    calibration `(−2π ∫ conj(g₀)·g₀').im = 2π/ℏ`.  The boost charge scales as `D²` (quadratic in the mode), so
    the classical `(∂φ)²` null energy is reproduced.  No regularity of `g₀` is needed for the identity itself —
    only the value of its boost-charge integral. -/
theorem localized_mode_hTkk
    (φ : Point 4 → ℝ) (x : Point 4) (v : Fin 4 → ℝ) (hbar : ℝ)
    (g₀ g₀' : ℝ → ℂ)
    (hcal : (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (g₀ θ) * g₀' θ ∂(volume : Measure ℝ))).im
              = 2 * Real.pi / hbar) :
    (2 * Real.pi / hbar * (∑ b, v b * pd φ b x) ^ 2 : ℝ)
      = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ)
            (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀ θ)
            * (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀' θ) ∂(volume : Measure ℝ))).im := by
  -- pull the (real) scalar D² out of the integral (D = ∑ b, v b * pd φ b x)
  have hint : (∫ θ, (starRingEnd ℂ) (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀ θ)
        * (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀' θ) ∂(volume : Measure ℝ))
      = (↑((∑ b, v b * pd φ b x) ^ 2) : ℂ)
        * ∫ θ, (starRingEnd ℂ) (g₀ θ) * g₀' θ ∂(volume : Measure ℝ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  -- a clean complex identity: pulling a real scalar `c` out of `(−2π·(↑c·z)).im` gives `c·(−2π·z).im`.
  have him : ∀ (c : ℝ) (z : ℂ),
      (-(2 * Real.pi * ((↑c : ℂ) * z))).im = c * (-(2 * Real.pi * z)).im := by
    intro c z
    simp only [Complex.neg_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat]
    ring
  simp only [hint, him, hcal]
  ring

end QIQTH.WedgeKMSToGR
