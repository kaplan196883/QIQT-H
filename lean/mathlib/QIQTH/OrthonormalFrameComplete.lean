/-
  OrthonormalFrameComplete — the COMPLETENESS relation for a g-orthonormal frame.

  A `g`-orthonormal frame is COMPLETE: its outer products reconstruct the INVERSE metric,

      `∑_i e_i^μ e_i^ν = gi^{μν}`.

  This is a general linear-algebra identity.  Package the frame vectors as the columns of a
  real matrix `E := Matrix.of (fun a i => e i a)`.  Then:
    • `hortho` (`∑_a ∑_b G a b · e i a · e k b = δ_{ik}`) says `Eᵀ · G · E = 1`;
    • `hinv`  (`∑_b G a b · Gi μ b = δ_{aμ}`) says `G · Giᵀ = 1`, so `Giᵀ = G⁻¹`;
    • from `Eᵀ G E = 1` the square matrix `E` is invertible with `E⁻¹ = Eᵀ G`
      (`Matrix.mul_eq_one_comm`), hence `E Eᵀ G = 1`;
    • right-multiplying by `Giᵀ = G⁻¹` gives `E Eᵀ = Giᵀ`.
  Reading entry `(μ,ν)` and using symmetry of the (symmetric) inverse metric `Gi` yields
  `∑_i e_i^μ e_i^ν = Gi μ ν`.

  This is exactly the `hcomplete` hypothesis consumed by `frame_ricci_trace` /
  `expFlow_frame_raychaudhuri`, DERIVED from orthonormality `hortho` plus the metric-inverse
  identity `hinv` (and symmetry of `Gi`, which the metric enjoys at every call site).

  WHAT IS **NOT** HERE (honest scope):
    • this is a general matrix identity — NOT the frame CONSTRUCTION (`exists_gorthonormal_frame`),
      not parallel transport, not `Ỹ'' = −R̃ Ỹ`, `tr R̃ = Ric`, nor the heat-kernel `a₁ = R/6`.
-/
import Mathlib

set_option maxHeartbeats 800000

namespace QIQTH.Curvature

open Matrix

variable {n : ℕ}

/-- **Completeness of a g-orthonormal frame.**

    Given a real symmetric-invertible metric with `hortho` (frame orthonormality,
    `∑_a ∑_b G a b · e i a · e k b = δ_{ik}`), `hinv` (metric-inverse identity,
    `∑_b G a b · Gi μ b = δ_{aμ}`) and symmetry of the inverse metric `Gi`, the frame is
    COMPLETE: `∑_i e_i^μ e_i^ν = Gi μ ν`.  This is the `hcomplete` hypothesis of
    `frame_ricci_trace` / `expFlow_frame_raychaudhuri`. -/
theorem gorthonormal_frame_complete (G Gi : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → (Fin n → ℝ))
    (hortho : ∀ i k, (∑ a, ∑ b, G a b * e i a * e k b) = if i = k then (1 : ℝ) else 0)
    (hinv : ∀ a μ, (∑ b, G a b * Gi μ b) = if a = μ then (1 : ℝ) else 0)
    (hGisymm : ∀ μ ν, Gi μ ν = Gi ν μ) :
    ∀ μ ν, (∑ i, e i μ * e i ν) = Gi μ ν := by
  classical
  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun a i => e i a) with hE
  -- `Eᵀ · G · E = 1` from orthonormality.
  have hEGE : Eᵀ * G * E = 1 := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hE, Matrix.of_apply, Matrix.one_apply]
    rw [← hortho i k]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  -- `G · Giᵀ = 1` from the metric-inverse identity.
  have hGGi : G * Giᵀ = 1 := by
    ext a μ
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [← hinv a μ]
  -- `E` is invertible: left inverse `Eᵀ G`, hence also right inverse (square).
  have hleft : (Eᵀ * G) * E = 1 := hEGE
  have hright : E * (Eᵀ * G) = 1 := mul_eq_one_comm.mp hleft
  have hEEtG : (E * Eᵀ) * G = 1 := by rw [Matrix.mul_assoc]; exact hright
  -- `E Eᵀ = Giᵀ` by right-multiplying with `Giᵀ = G⁻¹`.
  have hEEt : E * Eᵀ = Giᵀ := by
    calc E * Eᵀ = (E * Eᵀ) * 1 := by rw [Matrix.mul_one]
      _ = (E * Eᵀ) * (G * Giᵀ) := by rw [hGGi]
      _ = ((E * Eᵀ) * G) * Giᵀ := by rw [← Matrix.mul_assoc]
      _ = 1 * Giᵀ := by rw [hEEtG]
      _ = Giᵀ := by rw [Matrix.one_mul]
  -- Read entry `(μ,ν)` and use symmetry of the inverse metric.
  intro μ ν
  have hval := congrFun (congrFun hEEt μ) ν
  rw [Matrix.mul_apply] at hval
  simp only [Matrix.transpose_apply, hE, Matrix.of_apply] at hval
  rw [hGisymm ν μ] at hval
  exact hval

end QIQTH.Curvature
