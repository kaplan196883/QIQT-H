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
    only the value of its boost-charge integral.

    ⚠ **HONEST SCOPE (HT0).** This is a **CALIBRATED RANK-ONE ANSATZ, not the physical localization map.** It
    proves the `(∂φ)²` amplitude scaling and collapses the per-generator localization family to ONE scalar
    calibration (`hcal`); it does **NOT** establish that `ff = D·g₀` is the field's actual positive-frequency
    wedge one-particle mode, and the coefficient `2π/ℏ` is **CALIBRATED** (via `g₀`'s normalization + the unit
    phase `−iθ`), **NOT derived** from the KG two-point function / KMS temperature `β=2π`.  The mode shape/width
    is free (`GaussianModeFamily` — every width calibrates).  So `hTkk` here is **REDUCED, not DERIVED**.  The
    physical localization map — the positive-frequency wedge smearing of `∂_v φ` built from φ, with the `2π/ℏ`
    coefficient forced by Bisognano–Wichmann + the KG stress-tensor Noether charge — is the cited frontier
    (`IsPhysicalWedgeMode` below; see `THE_HTKK_PHYSICAL_PLAN.md`, HT1–HT4). -/
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

/-- **Honest re-export of `localized_mode_hTkk` under its truthful name.**  The Gaussian `hTkk` discharge is a
    *calibrated rank-one ansatz*: the mode is `ff = D·g₀` (field-gradient amplitude × a universal profile whose
    normalization is *tuned* to hit `2π/ℏ`).  This alias makes the status explicit at the call site — it is the
    same statement as `localized_mode_hTkk`, kept under both names so dependents (`QiqtGrGaussian`,
    `QiqtGrComplete`) do not break.  See the `localized_mode_hTkk` docstring and `IsPhysicalWedgeMode` for what
    this does NOT establish (the physical wedge-smearing localization map is the cited frontier). -/
theorem calibrated_rank_one_hTkk
    (φ : Point 4 → ℝ) (x : Point 4) (v : Fin 4 → ℝ) (hbar : ℝ)
    (g₀ g₀' : ℝ → ℂ)
    (hcal : (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (g₀ θ) * g₀' θ ∂(volume : Measure ℝ))).im
              = 2 * Real.pi / hbar) :
    (2 * Real.pi / hbar * (∑ b, v b * pd φ b x) ^ 2 : ℝ)
      = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ)
            (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀ θ)
            * (((∑ b, v b * pd φ b x : ℝ) : ℂ) * g₀' θ) ∂(volume : Measure ℝ))).im :=
  localized_mode_hTkk φ x v hbar g₀ g₀' hcal

/-- **The FRONTIER INTERFACE — what the physical discharge of `hTkk` must establish (HT3/HT4).**

    `IsPhysicalWedgeMode physWedge m φ x v ff` asserts that `ff : ℝ → ℂ` is the field `φ`'s **actual
    positive-frequency wedge one-particle mode** localized at the null generator `(x,v)` for the KG field of mass
    `m` — i.e. the positive-frequency wedge smearing of `∂_v φ` near `(x,v)`.

    Because the smearing / one-particle-projection map is **not yet formalizable** in Mathlib (the continuum
    mode-expansion the corpus flags as "beyond current Mathlib reach"), we do NOT fabricate its content here.
    Instead the honest requirement is carried as an **open predicate field** `physWedge` passed in: the future
    physical construction (HT3) will supply the genuine `physWedge` (built from φ, the KG two-point function and
    the Bisognano–Wichmann boost charge) and prove this Prop for the mode it constructs.  This is deliberately
    **NOT** a vacuous `True` placeholder — it names exactly the open obligation without pretending it is
    discharged. -/
def IsPhysicalWedgeMode
    (physWedge : ℝ → (Point 4 → ℝ) → Point 4 → (Fin 4 → ℝ) → (ℝ → ℂ) → Prop)
    (m : ℝ) (φ : Point 4 → ℝ) (x : Point 4) (v : Fin 4 → ℝ) (ff : ℝ → ℂ) : Prop :=
  physWedge m φ x v ff

end QIQTH.WedgeKMSToGR
