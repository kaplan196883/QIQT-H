/-
  OrthonormalFrameExists — the INITIAL-CONDITION FLOOR of the parallel-orthonormal-frame
  construction (Phase M2b-2).

  At a single point where the metric matrix `G := g(p)` is real symmetric POSITIVE-DEFINITE
  (`G.PosDef`), a `G`-orthonormal frame EXISTS:

      `∃ e : Fin n → (Fin n → ℝ),
          ∀ i j, (∑ a, ∑ b, G a b · e i a · e j b) = if i = j then 1 else 0.`

  This is exactly the `h0` (base-point orthonormality) hypothesis consumed by
  `QIQTH.ParallelTransport.parallel_orthonormal_preserved`.  The frame is built by the
  spectral theorem: `G = U · diag(λ) · Uᵀ` with `U` orthogonal (`eigenvectorUnitary`) and
  `λ` the (positive) eigenvalues; then `E := U · diag(λ^{-1/2})` satisfies `Eᵀ · G · E = 1`,
  and its columns `e i := (a ↦ E a i)` are the `G`-orthonormal frame.

  WHAT IS **NOT** HERE (honest scope):
    • no PARALLEL TRANSPORT of the frame along a curve — the linear frame ODE
      `e_i' = −Γ(γ)(γ',e_i)` (M2b-2) is not solved; this brick only provides the base-point IC.
    • it does NOT discharge the frame data of `expFlow_frame_raychaudhuri`.
    • no `Ỹ'' = −R̃ Ỹ`, no `tr R̃ = Ric`, no heat-kernel `a₁ = R/6`.
  Only the EXISTENCE of a `g(p)`-orthonormal frame at the base point lands here.
-/
import Mathlib

set_option maxHeartbeats 800000

namespace QIQTH.Curvature

open Matrix Finset

variable {n : ℕ}

/-- **A `G`-orthonormal frame exists** at a point where the metric is positive-definite.

    For a real symmetric positive-definite matrix `G` (the metric `g(p)` in coordinates), there is
    a family `e : Fin n → (Fin n → ℝ)` of frame vectors that is `G`-orthonormal:
    `∑_{a,b} G a b · e_i a · e_j b = δ_{ij}`.  Constructed via the spectral theorem
    `G = U · diag(λ) · Uᵀ` (orthogonal `U`, positive eigenvalues `λ`) with `E := U · diag(λ^{-1/2})`,
    whose columns are the frame; then `Eᵀ · G · E = 1` entrywise.

    This is the base-point initial condition `h0` for `parallel_orthonormal_preserved`; it does NOT
    build the parallel transport of the frame along a curve (that ODE stays open). -/
theorem exists_gorthonormal_frame (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ e : Fin n → (Fin n → ℝ),
      ∀ i j, (∑ a, ∑ b, G a b * e i a * e j b) = if i = j then (1 : ℝ) else 0 := by
  classical
  -- Spectral data of the Hermitian (here symmetric) matrix `G`.
  set hA := hG.1 with hAdef
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set d : Fin n → ℝ := fun i => (Real.sqrt (hA.eigenvalues i))⁻¹ with hd
  set E : Matrix (Fin n) (Fin n) ℝ := U * Matrix.diagonal d with hE
  -- Orthogonality of the eigenvector matrix: `Uᵀ · U = 1`.
  have hUU : star U * U = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    simpa [hU, Unitary.coe_star] using this
  -- Spectral theorem for `G` (real ⇒ `ofReal` is the identity, `star` is transpose).
  have hspec : G = U * Matrix.diagonal (fun i => hA.eigenvalues i) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have hdiag : (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.diagonal (fun i => hA.eigenvalues i) := by
      simp [RCLike.ofReal_real_eq_id]
    rw [hdiag] at h
    simpa [hU, Unitary.coe_star] using h
  -- `star E = diag(d) · Uᵀ`  (diagonal of reals is star-invariant).
  have hstarD : star (Matrix.diagonal d) = Matrix.diagonal d := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  have hsE : star E = Matrix.diagonal d * star U := by
    rw [hE, star_mul, hstarD]
  -- Core identity `Eᵀ · G · E = 1`.
  have hkey : star E * G * E = 1 := by
    have hstep : star E * G * E
        = (Matrix.diagonal d * star U)
            * (U * Matrix.diagonal (fun i => hA.eigenvalues i) * star U)
            * (U * Matrix.diagonal d) := by
      rw [hsE, hE]
      conv_lhs => rw [hspec]
    rw [hstep]
    simp only [mul_assoc]
    rw [← mul_assoc (star U) U, hUU, one_mul, ← mul_assoc (star U) U, hUU, one_mul]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hpos : 0 < hA.eigenvalues i := hG.eigenvalues_pos i
    have hs : Real.sqrt (hA.eigenvalues i) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    have hss : Real.sqrt (hA.eigenvalues i) * Real.sqrt (hA.eigenvalues i) = hA.eigenvalues i :=
      Real.mul_self_sqrt hpos.le
    simp only [hd]
    field_simp
    linarith [hss]
  -- Read off the `G`-orthonormality of the columns of `E` from the matrix identity.
  refine ⟨fun i => fun a => E a i, ?_⟩
  intro i j
  have hmat : (star E * G * E) i j = if i = j then (1 : ℝ) else 0 := by
    rw [hkey, Matrix.one_apply]
  have hexp : (star E * G * E) i j = ∑ a, ∑ b, G a b * E a i * E b j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  show (∑ a, ∑ b, G a b * E a i * E b j) = if i = j then (1 : ℝ) else 0
  rw [← hexp]; exact hmat

end QIQTH.Curvature
