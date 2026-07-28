/-
  OrthonormalFrameDet — the METRIC-FACTOR lemma for the van-Vleck coordinate connection.

  A `g`-orthonormal frame `E` (a real matrix with `Eᵀ · g · E = 1`) has determinant
  `±1/√det g`.  Concretely, this brick proves the sign-safe determinant identity

      `(det E)² · det g = 1`

  and its logarithmic form (for `det g > 0`)

      `log((det E)²) = − log(det g)`.

  This is exactly the source of the `f = −½ log det g` metric factor: writing
  `f := −½ log det g = ½ log((det E)²) = log |det E|`, the coordinate exp-differential
  trace `θ_B` and the frame trace `θ_Y` are related by `θ_B = θ_Y + f'`
  (`QIQTH.ExpMap.trace_raychaudhuri_det_factor` consumes `f` with `log det N =ᶠ log det M + f`).

  WHAT IS **NOT** HERE (honest scope):
    • this is a general determinant identity — it does NOT prove the `θ_B ↔ θ_Y`
      connection, `B'' = −R̃ B`, `tr R̃ = Ric`, or the heat-kernel `a₁ = R/6`.
    • no frame ODE, no parallel transport; only the algebraic determinant fact lands here.
-/
import Mathlib

set_option maxHeartbeats 400000

namespace QIQTH.Curvature

open Matrix

variable {n : ℕ}

/-- **Metric-factor determinant identity.**

    For a real `g`-orthonormal frame matrix `E` (`Eᵀ · G · E = 1`), the determinant satisfies
    `(det E)² · det G = 1`.  Hence `det E = ±1/√det G`, the source of the `−½ log det g`
    metric factor in the van-Vleck coordinate connection. -/
theorem gorthonormal_det_sq (G E : Matrix (Fin n) (Fin n) ℝ) (hE : Eᵀ * G * E = 1) :
    (E.det) ^ 2 * G.det = 1 := by
  have hdet : (Eᵀ * G * E).det = (1 : Matrix (Fin n) (Fin n) ℝ).det := by rw [hE]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  -- `hdet : E.det * G.det * E.det = 1`
  rw [← hdet]; ring

/-- **Logarithmic metric factor.**

    For a real `g`-orthonormal frame matrix `E` (`Eᵀ · G · E = 1`) with `det G > 0`,
    `log((det E)²) = − log(det G)`.  This is the sign-safe form of `f = −½ log det g`
    (equivalently `f = log |det E| = ½ log((det E)²)`). -/
theorem gorthonormal_logdet (G E : Matrix (Fin n) (Fin n) ℝ) (hE : Eᵀ * G * E = 1)
    (hGpos : 0 < G.det) :
    Real.log (E.det ^ 2) = - Real.log G.det := by
  have hsq : (E.det) ^ 2 * G.det = 1 := gorthonormal_det_sq G E hE
  have hGne : G.det ≠ 0 := hGpos.ne'
  have hinv : (E.det) ^ 2 = (G.det)⁻¹ := by
    field_simp at hsq ⊢
    linarith [hsq]
  rw [hinv, Real.log_inv]

end QIQTH.Curvature
