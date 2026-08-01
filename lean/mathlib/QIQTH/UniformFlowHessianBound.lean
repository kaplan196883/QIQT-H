/-
  # J4-69 (R3 layer) — the UNIFORM operator-norm bound on the uniform-flow exp Hessian.

  Brick-A(β) regularity climb for `uniformFlowExp` (uniform radius `ρ_K`, NO `expRho`).

  R2 (`uniformFlowExp_fderiv_hasFDerivAt`, `UniformFlowHessian`) established that the velocity jet map
  `w ↦ fderiv ℝ (uniformFlowExp g gi hC hK q) w` is Fréchet-differentiable at `v` (‖v‖ < ρ_K), so the
  Hessian
      `B₂(q,v) := fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v`
        `: Point n →L[ℝ] Point n →L[ℝ] Point n`
  EXISTS.  This file lands the two GENUINE reusable pieces of the R3 route (U2 + the symmetry input),
  and the honest conditional assembly, firewalling the one heavy residue precisely.

  ## What is PROVEN here (unconditional, DERIVED)

  * `bilinear_opNorm_le_of_symm_diag_bound` — **U2, the polarization operator-norm bound**, generic in
    any real normed space (no inner product / parallelogram law assumed).  For a SYMMETRIC bounded
    bilinear `B` with a diagonal bound `‖B a a‖ ≤ M‖a‖²` (`M ≥ 0`), one gets `‖B‖ ≤ 2M`.  Proof:
    the polarization identity `4 • B a b = B (a+b) (a+b) − B (a−b) (a−b)` (needs symmetry) gives the
    degree-2 bound `4‖B a b‖ ≤ M(‖a+b‖² + ‖a−b‖²)`; homogenising via unit-vector rescaling turns it into
    the product bound `‖B a b‖ ≤ 2M‖a‖‖b‖`, then `ContinuousLinearMap.opNorm_le_bound₂`.  (Over a
    general normed space the sharp constant is `2M`, not `M` — the `M`-sharp version needs parallelogram,
    which `Point n = Fin n → ℝ` with the sup norm does NOT satisfy.  A uniform `∃ M` bound is all R3
    needs, so `2M` is fine.)

  * `uniformFlowExp_hessian_symm` — **the symmetry input**: the Hessian is a symmetric bilinear form,
    `B₂(q,v) a b = B₂(q,v) b a`.  DERIVED from `second_derivative_symmetric_of_eventually_of_real`
    (Mathlib) fed with (i) the eventual first-derivative `HasFDerivAt (uniformFlowExp q) (fderiv…) y`
    for `‖y‖ < ρ_K` (`uniformFlowExp_hasFDerivAt`, K2), and (ii) R2's second-derivative `HasFDerivAt`.
    No `expRho`.

  * `uniformFlowExp_hessian_opNorm_le_of_diag_bound` — **R3 assembled, CONDITIONAL on the diagonal
    bound.**  Given a uniform diagonal Hessian bound `‖B₂(q,v) a a‖ ≤ M‖a‖²` (`q ∈ K`, `‖v‖ < r₀ ≤ ρ_K`),
    the two pieces above yield the uniform operator-norm bound
        `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖B₂(q,v)‖ ≤ M'`   (with `M' = 2M`).

  ## FIREWALLED (the one heavy residue — NOT claimed here)

  The uniform diagonal bound `‖B₂(q,v) a a‖ ≤ M‖a‖²` requires the diagonal VALUE identification
  `B₂(q,v) a a = (Zf 1).1` (`Zf` R1's intrinsic second-variation field, `UniformFlowSecondJet`,
  `‖Zf 1‖ ≤ M₂j‖a‖²`).  Producing that value id via `hid_of_doubled_data` (`JacobiOperatorFDeriv`) needs
  the TWO-SIDED doubled second-variation supply for `uniformFlowExp` (`hid.hZf` demands a genuine
  `HasDerivAt`, whereas R1's `Zf` only solves the second-variation ODE with WITHIN derivatives because
  the padded uniform tube is continuous only on the OPEN `(-2,2)`).  That two-sided second-jet supply is
  one order above the R2-a first-jet supply (`uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt`) and
  is the genuine next brick.  It is CARRIED as the hypothesis `hdiag`, NOT assumed as the conclusion.
-/
import QIQTH.UniformFlowHessian
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowSecondJet
import QIQTH.JacobiOperatorFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000

/-! ### U2 — the polarization operator-norm bound (generic real normed space) -/

section Polarization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Polarization identity for a symmetric continuous bilinear map.**
    `4 • B a b = B (a+b) (a+b) − B (a−b) (a−b)`. -/
theorem symm_bilinear_polarization (B : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ x y, B x y = B y x) (a b : E) :
    B (a + b) (a + b) - B (a - b) (a - b) = (4 : ℝ) • B a b := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [hsymm b a]
  module

/-- **The degree-2 polarization bound.**  From the diagonal bound `‖B a a‖ ≤ M‖a‖²`,
    `4‖B a b‖ ≤ M(‖a+b‖² + ‖a−b‖²)`. -/
theorem symm_bilinear_deg2_bound (B : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ x y, B x y = B y x) {M : ℝ}
    (hdiag : ∀ a : E, ‖B a a‖ ≤ M * ‖a‖ ^ 2) (a b : E) :
    (4 : ℝ) * ‖B a b‖ ≤ M * (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2) := by
  have h4 : ‖(4 : ℝ) • B a b‖ = 4 * ‖B a b‖ := by
    rw [norm_smul]; norm_num
  calc (4 : ℝ) * ‖B a b‖
      = ‖(4 : ℝ) • B a b‖ := h4.symm
    _ = ‖B (a + b) (a + b) - B (a - b) (a - b)‖ := by rw [symm_bilinear_polarization B hsymm a b]
    _ ≤ ‖B (a + b) (a + b)‖ + ‖B (a - b) (a - b)‖ := norm_sub_le _ _
    _ ≤ M * ‖a + b‖ ^ 2 + M * ‖a - b‖ ^ 2 := add_le_add (hdiag _) (hdiag _)
    _ = M * (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2) := by ring

/-- **U2 — polarization operator-norm bound.**  A SYMMETRIC bounded bilinear map with a diagonal bound
    `‖B a a‖ ≤ M‖a‖²` (`M ≥ 0`) has operator norm `≤ 2M`.  No inner-product / parallelogram assumed;
    the constant is `2M` (sharp `M` would need the parallelogram law). -/
theorem bilinear_opNorm_le_of_symm_diag_bound (B : E →L[ℝ] E →L[ℝ] F)
    (hsymm : ∀ x y, B x y = B y x) {M : ℝ} (hM : 0 ≤ M)
    (hdiag : ∀ a : E, ‖B a a‖ ≤ M * ‖a‖ ^ 2) :
    ‖B‖ ≤ 2 * M := by
  -- product bound `‖B a b‖ ≤ 2M‖a‖‖b‖`, obtained by unit-vector rescaling.
  have hprod : ∀ a b : E, ‖B a b‖ ≤ 2 * M * ‖a‖ * ‖b‖ := by
    intro a b
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; simp
    rcases eq_or_ne b 0 with hb | hb
    · subst hb; simp
    have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
    set a' : E := (‖a‖⁻¹) • a with ha'
    set b' : E := (‖b‖⁻¹) • b with hb'
    have hna' : ‖a'‖ = 1 := by
      rw [ha', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hna,
        inv_mul_cancel₀ (ne_of_gt hna)]
    have hnb' : ‖b'‖ = 1 := by
      rw [hb', norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hnb,
        inv_mul_cancel₀ (ne_of_gt hnb)]
    -- unit diagonal bound: `‖B a' b'‖ ≤ 2M`.
    have hsum : ‖a' + b'‖ ^ 2 ≤ 4 := by
      have h := norm_add_le a' b'
      rw [hna', hnb'] at h
      nlinarith [norm_nonneg (a' + b'), h]
    have hdif : ‖a' - b'‖ ^ 2 ≤ 4 := by
      have h := norm_sub_le a' b'
      rw [hna', hnb'] at h
      nlinarith [norm_nonneg (a' - b'), h]
    have hunit : ‖B a' b'‖ ≤ 2 * M := by
      have hd := symm_bilinear_deg2_bound B hsymm hdiag a' b'
      nlinarith [hd, hsum, hdif, hM, norm_nonneg (B a' b'),
        mul_nonneg hM (by linarith [hsum] : (0:ℝ) ≤ 4 - ‖a' + b'‖ ^ 2),
        mul_nonneg hM (by linarith [hdif] : (0:ℝ) ≤ 4 - ‖a' - b'‖ ^ 2)]
    -- rescale back: `B a b = (‖a‖·‖b‖) • B a' b'`.
    have haa : a = ‖a‖ • a' := by
      rw [ha', smul_smul, mul_inv_cancel₀ (ne_of_gt hna), one_smul]
    have hbb : b = ‖b‖ • b' := by
      rw [hb', smul_smul, mul_inv_cancel₀ (ne_of_gt hnb), one_smul]
    have hab : B a b = (‖a‖ * ‖b‖) • B a' b' := by
      conv_lhs => rw [haa, hbb]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
      rw [mul_comm ‖b‖ ‖a‖]
    rw [hab, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖a‖ * ‖b‖ * ‖B a' b'‖
        ≤ ‖a‖ * ‖b‖ * (2 * M) :=
          mul_le_mul_of_nonneg_left hunit (by positivity)
      _ = 2 * M * ‖a‖ * ‖b‖ := by ring
  exact B.opNorm_le_bound₂ (by positivity) hprod

end Polarization

/-! ### The Hessian symmetry input for `uniformFlowExp` -/

variable {n : ℕ}

/-- **Symmetry of the uniform-flow exp Hessian.**  For `q ∈ K` and `‖v‖ < ρ_K`, the second Fréchet
    derivative `B₂(q,v) = fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp q) w) v` is a SYMMETRIC bilinear
    form.  DERIVED from `second_derivative_symmetric_of_eventually_of_real` fed with the eventual
    first-derivative (K2, `uniformFlowExp_hasFDerivAt`) and R2's second-derivative `HasFDerivAt`
    (`uniformFlowExp_fderiv_hasFDerivAt`).  No `expRho`. -/
theorem uniformFlowExp_hessian_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b : Point n) :
    (fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a b
      = (fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) b a := by
  -- eventual first-derivative on the open uniform-flow ball (a nbhd of `v`).
  have hev : ∀ᶠ y in 𝓝 v,
      HasFDerivAt (uniformFlowExp g gi hC hK q)
        (fderiv ℝ (uniformFlowExp g gi hC hK q) y) y := by
    have hball : Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) ∈ 𝓝 v := by
      refine Metric.isOpen_ball.mem_nhds ?_
      rw [Metric.mem_ball, dist_zero_right]; exact hv
    refine Filter.eventually_of_mem hball (fun y hy => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hy
    obtain ⟨L, hL⟩ := uniformFlowExp_hasFDerivAt g gi hC hK q hq y hy
    exact hL.differentiableAt.hasFDerivAt
  -- R2: the second-derivative `HasFDerivAt`.
  obtain ⟨B₂, hB₂⟩ := uniformFlowExp_fderiv_hasFDerivAt g gi hC hK q hq v hv
  have hfd : fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v = B₂ := hB₂.fderiv
  rw [hfd]
  exact second_derivative_symmetric_of_eventually_of_real hev hB₂ a b

/-! ### R3 assembled — CONDITIONAL on the uniform diagonal Hessian bound -/

/-- **R3 (assembled, conditional).**  Given a uniform DIAGONAL Hessian bound over `K`
    (`‖B₂(q,v) a a‖ ≤ M‖a‖²` for `q ∈ K`, `‖v‖ < r₀ ≤ ρ_K`), the symmetry input
    (`uniformFlowExp_hessian_symm`) plus the polarization bound
    (`bilinear_opNorm_le_of_symm_diag_bound`) give the UNIFORM operator-norm bound on the Hessian
        `∃ M', ∀ q ∈ K, ∀ ‖v‖ < r₀, ‖fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp q) w) v‖ ≤ M'`
    with `M' = 2M`, uniform over `q ∈ K`.  The diagonal bound `hdiag` is a GENUINE carried input (the
    firewalled two-sided second-variation value id + R1 bound), NOT the conclusion.  No `expRho`. -/
theorem uniformFlowExp_hessian_opNorm_le_of_diag_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {r₀ M : ℝ} (hM : 0 ≤ M)
    (hrρ : r₀ ≤ uniformFlowRadius g gi hC hK)
    (hdiag : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ a : Point n,
      ‖(fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v) a a‖ ≤ M * ‖a‖ ^ 2) :
    ∃ M' : ℝ, ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ →
      ‖fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v‖ ≤ M' := by
  refine ⟨2 * M, ?_⟩
  intro q hq v hv
  have hvρ : ‖v‖ < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hv hrρ
  exact bilinear_opNorm_le_of_symm_diag_bound
    (fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) v)
    (fun a b => uniformFlowExp_hessian_symm g gi hC hK q hq v hvρ a b)
    hM (fun a => hdiag q hq v hv a)

end QIQTH.ExpMap
