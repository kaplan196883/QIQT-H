/-
  FrameDecompLogDet — the frame-decomposition log-det relation for the van-Vleck discharge.

  For the frame Jacobi matrix `Y = E⁻¹ · B` (frame components of the coordinate Jacobi
  matrix `B`, with `E` a `g`-orthonormal frame satisfying `Eᵀ · G · E = 1`),

      `log det B = log det Y − ½ log det G`.

  This holds pointwise wherever `E` is orthonormal and all four determinants are positive,
  and hence eventually on a neighborhood.  It is derived from
  `det E = 1/√det G` (`QIQTH.Curvature.gorthonormal_det_sq`: `(det E)² · det G = 1`)
  together with `det Y = det B / det E`.

  This is exactly the `hrel` hypothesis of `vanVleck_ray_secondDeriv_ricci`: the frame
  Jacobi matrix `Y` records the frame components of the coordinate Jacobi matrix `B`.

  WHAT IS **NOT** HERE (honest scope):
    • a general matrix-calculus / determinant identity only.
    • NOT the frame Raychaudhuri equation `h4`, NOT the van-Vleck discharge itself,
      NOT `B'' = −R̃ B`, NOT `tr R̃ = Ric`, NOT the heat-kernel `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OrthonormalFrameDet

set_option maxHeartbeats 800000

namespace QIQTH.Curvature

open Matrix

variable {n : ℕ}

/-- **Frame-decomposition log-det relation.**

    For `Y = E⁻¹ · B` with `E` a `g`-orthonormal frame (`Eᵀ · G · E = 1`) and all four
    determinants (`E`, `G`, `B`, and hence `Y`) positive on a neighborhood of `t`,

      `log det B = log det (E⁻¹ B) − ½ log det G`

    eventually near `t`.  Uses `det E = 1/√det G` via `gorthonormal_det_sq`
    (`(det E)² · det G = 1`), so `log det E = −½ log det G`, and `det (E⁻¹ B) = det B / det E`.
    This is the `hrel` hypothesis of `vanVleck_ray_secondDeriv_ricci`. -/
theorem logdet_frame_decomp_eventuallyEq (G E B : ℝ → Matrix (Fin n) (Fin n) ℝ) {t : ℝ}
    (hortho : ∀ᶠ s in nhds t, (E s)ᵀ * G s * E s = 1)
    (hEdet : ∀ᶠ s in nhds t, 0 < (E s).det)
    (hGdet : ∀ᶠ s in nhds t, 0 < (G s).det)
    (hBdet : ∀ᶠ s in nhds t, 0 < (B s).det) :
    (fun s => Real.log ((B s).det))
      =ᶠ[nhds t]
    (fun s => Real.log (((E s)⁻¹ * B s).det) - (1/2 : ℝ) * Real.log ((G s).det)) := by
  filter_upwards [hortho, hEdet, hGdet, hBdet] with s h1 h2 h3 h4
  -- abbreviations
  set dE := (E s).det with hdE
  set dG := (G s).det with hdG
  set dB := (B s).det with hdB
  have hEne : dE ≠ 0 := h2.ne'
  have hGne : dG ≠ 0 := h3.ne'
  have hBne : dB ≠ 0 := h4.ne'
  -- det of the inverse
  have hEunit : IsUnit dE := isUnit_iff_ne_zero.mpr hEne
  have hEmatunit : IsUnit (E s) := (Matrix.isUnit_iff_isUnit_det (E s)).mpr hEunit
  have hinvdet : ((E s)⁻¹).det = dE⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  -- det Y = dB / dE
  have hY : ((E s)⁻¹ * B s).det = dE⁻¹ * dB := by
    rw [Matrix.det_mul, hinvdet]
  -- log det E = -(1/2) log det G, from (det E)^2 * det G = 1
  have hsq : dE ^ 2 * dG = 1 := gorthonormal_det_sq (G s) (E s) h1
  have hloge : Real.log dE = -(1/2 : ℝ) * Real.log dG := by
    have hlogsq : Real.log (dE ^ 2) = - Real.log dG := gorthonormal_logdet (G s) (E s) h1 h3
    rw [Real.log_pow] at hlogsq
    push_cast at hlogsq
    linarith
  -- log det Y = log dB - log dE
  have hlogY : Real.log (((E s)⁻¹ * B s).det) = Real.log dB - Real.log dE := by
    rw [hY, Real.log_mul (inv_ne_zero hEne) hBne, Real.log_inv]
    ring
  rw [hlogY, hloge]
  ring

end QIQTH.Curvature
