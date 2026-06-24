/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-3-C3 — the free-field QIQT→GR capstone with the localization mode CONSTRUCTED from the field

`qiqt_gr_freefield_nullEnergy` leaves `hTkk` (the localization map) as a labelled input over an abstract mode
`ff`.  This file discharges it: the mode is BUILT from the field as `ff x v θ := (∑ₐ vₐ ∂ₐφ(x))·g₀(θ)` with `g₀`
the calibrated Gaussian wave packet (`GaussianMode`).  Its regularity (`MemLp`/`Integrable`/`HasDerivAt`/
measurability/bounded derivative) follows from the `gaussMode` lemmas scaled by the field gradient, and `hTkk`
itself is `localized_mode_hTkk` fed by `gaussMode_calibration`.

Result: Einstein's equations `a·kgStress = G + Λg` with the per-generator Gap-2 localization map **constructed
from φ**, not assumed — only the Clausius/area physics + the Raychaudhuri congruence setup remain labelled.
Axiom-free.
-/
import QIQTH.QiqtGrFreeField
import QIQTH.GaussianMode

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.EinsteinEOS Complex MeasureTheory Real Filter Topology

/-- **★★★ The free-field QIQT→GR capstone with the localization mode constructed from the field.**  Identical to
    `qiqt_gr_freefield_nullEnergy`, but the wedge mode `ff` and its derivative `ff'`, all their regularity, and
    the localization identity `hTkk` are no longer inputs — they are BUILT from `φ`:
    `ff x v θ := ↑(∑ₐ vₐ ∂ₐφ(x))·gaussMode ℏ θ`.  `hTkk` is discharged by `localized_mode_hTkk` +
    `gaussMode_calibration`.  Only the Clausius/area physics (`hbound`/`hsat`/`hDnn`/`hD0`/`hK`) and the
    Raychaudhuri congruence setup (`hWx`/`hWC`/`hWgeo`/`hWequil`/`hWarea`) remain labelled.  Axiom-free. -/
theorem qiqt_gr_freefield_gaussian
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (φ : Point 4 → ℝ) (m η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (hbar_pos : 0 < hbar) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hφ : ContDiff ℝ ⊤ φ) (hKG : ∀ x, boxField φ g gi x = m ^ 2 * φ x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    (Sf KE A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd ad : Point 4 → (Fin 4 → ℝ) → ℝ)
    (hS : ∀ x v, BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 →
        HasDerivAt (KE x v) (2 * Real.pi / hbar * BL (kgStress m φ g gi x) v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0)
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, Sf x v t ≤ η * A x v t)
    (hsat : ∀ x v, BL (g x) v = 0 → Sf x v 0 = η * A x v 0)
    (hDnn : ∀ x v, BL (g x) v = 0 → ∀ t, 0 ≤ KE x v t - Sf x v t)
    (hD0 : ∀ x v, BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    (W : Point 4 → (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hWx : ∀ x v, BL (g x) v = 0 → W x v x = v)
    (hWC : ∀ x v μ, ContDiff ℝ ⊤ (fun y => W x v y μ))
    (hWgeo : ∀ x v, ∀ y μ, (∑ ν, W x v y ν * covDerivVec g gi (W x v) ν μ y) = 0)
    (hWequil : ∀ x v, BL (g x) v = 0 →
        (∑ μ, ∑ ν, covDerivVec g gi (W x v) μ ν x * covDerivVec g gi (W x v) ν μ x) = 0)
    (hWarea : ∀ x v, BL (g x) v = 0 →
        ad x v = - ∑ ν, W x v x ν * pd (fun y => expansion g gi (W x v) y) ν x)
    : ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  refine qiqt_gr_freefield_nullEnergy g gi hsymm hsymm_gi hinv hCg hCgi φ m η hbar a hbar0 heta ha hφ hKG
    P Pinv hPP hPP' hcong Sf KE A sd ad hS hK hA hbound hsat hDnn hD0 mw hmw
    (fun x v θ => ((∑ b, v b * pd φ b x : ℝ) : ℂ) * gaussMode hbar θ)
    (fun x v θ => ((∑ b, v b * pd φ b x : ℝ) : ℂ) * gaussMode' hbar θ)
    (fun x v => (gaussMode_memLp hbar).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v => (gaussMode_integrable_fn hbar hbar_pos).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v θ => (gaussMode_hasDerivAt hbar θ).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v => (continuous_const.mul (gaussMode'_continuous hbar)).aestronglyMeasurable)
    (fun x v => |∑ b, v b * pd φ b x| * gaussC hbar)
    (fun x v θ => ?_)
    (fun x v _ => localized_mode_hTkk φ x v hbar (gaussMode hbar) (gaussMode' hbar)
      (gaussMode_calibration hbar hbar_pos))
    W hWx hWC hWgeo hWequil hWarea
  -- the derivative bound `‖ff' x v θ‖ ≤ Bd x v`:
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (gaussMode'_norm_le hbar hbar_pos θ) (abs_nonneg _)

end QIQTH.WedgeKMSToGR
