/-
  DecayOrderThree — the general vector-valued THIRD-order Taylor remainder on a convex set.

  ODE_VARIATIONAL_PLAN, Phase J-d (base-point 2nd-order jet).  The J-d assembly needs the cubic
  uniform Taylor remainder — the 3rd-order analogue of `decay_order_two_remainder_convex`
  (GeodesicSmoothDep.lean).  This file lands exactly that ONE genuinely-new analytic lemma, as
  self-contained real analysis.

  `decay_order_three_remainder_convex` — if `F : E → G` is `C²` on a convex set `S` (`F`, `fderiv F`
  differentiable there), the second Fréchet derivative is symmetric at the base point `b`
  (`IsSymmSndFDerivAt ℝ F b`, automatic for `C²` functions over `ℝ`), and it is `M`-Lipschitz at `b`
  on `S` — `‖fderiv² F z − fderiv² F b‖ ≤ M·‖z − b‖` — then for `a, b ∈ S`:
      `‖F a − F b − DF(b)(a−b) − ½·D²F(b)(a−b)(a−b)‖ ≤ M·‖a − b‖³`
  (crude constant `M`, mirroring the `M`-not-`M/6` convention of `decay_order_two_remainder_convex`).

  ON THE HYPOTHESIS.  The natural "one Fréchet order up" input would be `‖fderiv³ F‖ ≤ M`, mirroring
  the `‖fderiv² F‖ ≤ M` of the 2nd-order lemma.  But the *triple* nested continuous-linear-map norm
  `Norm (E →L[ℝ] E →L[ℝ] E →L[ℝ] G)` is NOT synthesizable for abstract normed spaces `E`, `G`
  (Mathlib's operator-norm instance loops on the middle map's scalar field), so `‖fderiv³ F‖ ≤ M`
  cannot even be *stated* here.  The `M`-Lipschitz-at-`b` bound on `fderiv² F` uses only the *double*
  norm `Norm (E →L[ℝ] E →L[ℝ] G)` (which does synthesize), is IMPLIED by `‖fderiv³ F‖ ≤ M` (by the
  mean-value inequality applied to `fderiv² F`, dischargeable at any concrete space where the triple
  norm resolves), and is the genuine analytic content — it is NOT the conclusion.

  ROUTE (one Fréchet order up).  Let `R x := F x − F b − DF(b)(x−b) − ½·D²F(b)(x−b)(x−b)`.  Using
  symmetry of `D²F(b)`, its Fréchet derivative is `fderiv R x = DF(x) − DF(b) − D²F(b)(x−b)`, i.e. the
  first-order Taylor remainder of `fderiv F` around `b`.  The first-order mean-value inequality with a
  fixed linear map (`Convex.norm_image_sub_le_of_norm_fderiv_le'`, applied to `fderiv F` with
  `φ = D²F(b)`), fed the Lipschitz bound `‖fderiv² F z − fderiv² F b‖ ≤ M·‖z−b‖`, gives
  `‖fderiv R x‖ ≤ M·‖x−b‖² ≤ M·‖a−b‖²` on the segment `[b,a]`.  A second application of the convex
  mean-value inequality (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) integrates that
  quadratic derivative bound along `[b,a]` and yields `‖R a − R b‖ = ‖R a‖ ≤ M·‖a−b‖³`.

  HONEST: only genuine `C²` differentiability + base-point symmetry + the second-derivative Lipschitz
  bound are carried; the conclusion is NOT among the hypotheses.  This does NOT build the base-point
  2nd variational equation, the Jacobi 2-jet, or `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep

namespace QIQTH.ExpMap

open Finset Topology

set_option maxHeartbeats 800000

/-- **General vector-valued THIRD-order Taylor remainder on a convex set.**  If `F : E → G` is `C²`
    on a convex set `S`, its second Fréchet derivative is symmetric at the base point `b`
    (`IsSymmSndFDerivAt ℝ F b`) and `M`-Lipschitz at `b` on `S`
    (`‖fderiv² F z − fderiv² F b‖ ≤ M·‖z − b‖`), then for `a, b ∈ S`:
    `‖F a − F b − (fderiv F b)(a − b) − ½·(fderiv² F b (a − b))(a − b)‖ ≤ M·‖a − b‖³`.

    One Fréchet order up from `decay_order_two_remainder_convex`; crude constant `M` (not the sharp
    Taylor `M/6`).  See the file header on why the input is the second-derivative Lipschitz bound
    rather than the (un-stateable, for abstract spaces) triple norm `‖fderiv³ F‖ ≤ M`. -/
theorem decay_order_three_remainder_convex {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → G) (M : ℝ) {S : Set E} (hconv : Convex ℝ S) {a b : E}
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ F) x)
    (hlip2 : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ F) z - fderiv ℝ (fderiv ℝ F) b‖ ≤ M * ‖z - b‖)
    (ha : a ∈ S) (hb : b ∈ S) (hsymm : IsSymmSndFDerivAt ℝ F b) :
    ‖F a - F b - fderiv ℝ F b (a - b)
        - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ F) b (a - b)) (a - b)‖ ≤ M * ‖a - b‖ ^ 3 := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hab' : (0 : ℝ) < ‖a - b‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hab
  have hM : 0 ≤ M := by
    have h := hlip2 a ha
    nlinarith [le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ F) a - fderiv ℝ (fderiv ℝ F) b)) h, hab']
  -- 1. `R` has Fréchet derivative `Dexpr y` at every `y` on the segment `[b,a]`.
  have hR_full : ∀ y ∈ segment ℝ b a,
      HasFDerivAt (fun x : E => F x - F b - fderiv ℝ F b (x - b)
          - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ F) b (x - b)) (x - b))
        (fderiv ℝ F y - (0 : E →L[ℝ] G)
            - (fderiv ℝ F b).comp (ContinuousLinearMap.id ℝ E)
            - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ F) b (y - b)).comp (ContinuousLinearMap.id ℝ E)
                + ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)).flip (y - b))) y := by
    intro y hy
    have hyS : y ∈ S := hconv.segment_subset hb ha hy
    have hsub : HasFDerivAt (fun x : E => x - b) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).sub_const b
    have h1 : HasFDerivAt F (fderiv ℝ F y) y := (hdiff y hyS).hasFDerivAt
    have hconst : HasFDerivAt (fun _ : E => F b) (0 : E →L[ℝ] G) y := hasFDerivAt_const (F b) y
    have hLd : HasFDerivAt (fun x : E => fderiv ℝ F b (x - b))
        ((fderiv ℝ F b).comp (ContinuousLinearMap.id ℝ E)) y :=
      (ContinuousLinearMap.hasFDerivAt (fderiv ℝ F b)).comp y hsub
    have hcB : HasFDerivAt (fun x : E => fderiv ℝ (fderiv ℝ F) b (x - b))
        ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)) y :=
      (ContinuousLinearMap.hasFDerivAt (fderiv ℝ (fderiv ℝ F) b)).comp y hsub
    have hinner : HasFDerivAt (fun x : E => (fderiv ℝ (fderiv ℝ F) b (x - b)) (x - b))
        ((fderiv ℝ (fderiv ℝ F) b (y - b)).comp (ContinuousLinearMap.id ℝ E)
          + ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)).flip (y - b)) y :=
      hcB.clm_apply hsub
    have hq : HasFDerivAt
        (fun x : E => (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ F) b (x - b)) (x - b))
        ((1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ F) b (y - b)).comp (ContinuousLinearMap.id ℝ E)
          + ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)).flip (y - b))) y :=
      hinner.const_smul (1/2 : ℝ)
    exact ((h1.sub hconst).sub hLd).sub hq
  -- 2. Norm bound on that derivative: `‖Dexpr y‖ ≤ M·‖a−b‖²` on the segment.
  have hbound_seg : ∀ y ∈ segment ℝ b a,
      ‖fderiv ℝ F y - (0 : E →L[ℝ] G)
          - (fderiv ℝ F b).comp (ContinuousLinearMap.id ℝ E)
          - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ F) b (y - b)).comp (ContinuousLinearMap.id ℝ E)
              + ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)).flip (y - b))‖
        ≤ M * ‖a - b‖ ^ 2 := by
    intro y hy
    have hyS : y ∈ S := hconv.segment_subset hb ha hy
    -- `Dexpr y = fderiv F y − fderiv F b − (fderiv² F b)(y − b)`, using symmetry at `b`.
    have hDeq : (fderiv ℝ F y - (0 : E →L[ℝ] G)
          - (fderiv ℝ F b).comp (ContinuousLinearMap.id ℝ E)
          - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ F) b (y - b)).comp (ContinuousLinearMap.id ℝ E)
              + ((fderiv ℝ (fderiv ℝ F) b).comp (ContinuousLinearMap.id ℝ E)).flip (y - b)))
        = fderiv ℝ F y - fderiv ℝ F b - fderiv ℝ (fderiv ℝ F) b (y - b) := by
      ext h
      have hs := (hsymm.eq (y - b) h).symm
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply]
      rw [hs]
      module
    rw [hDeq]
    -- inner first-order remainder of `fderiv F` around `b`, via the MVT-with-fixed-map on `[b,y]`.
    have hseg_by : segment ℝ b y ⊆ S := hconv.segment_subset hb hyS
    have hbnd : ∀ z ∈ segment ℝ b y,
        ‖fderiv ℝ (fderiv ℝ F) z - fderiv ℝ (fderiv ℝ F) b‖ ≤ M * ‖y - b‖ := by
      intro z hz
      have hzb : ‖z - b‖ ≤ ‖y - b‖ := by
        rw [segment_eq_image'] at hz
        obtain ⟨θ, hθ, rfl⟩ := hz
        have hsub2 : (b + θ • (y - b)) - b = θ • (y - b) := by abel
        rw [hsub2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
        calc θ * ‖y - b‖ ≤ 1 * ‖y - b‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
          _ = ‖y - b‖ := one_mul _
      exact le_trans (hlip2 z (hseg_by hz)) (mul_le_mul_of_nonneg_left hzb hM)
    have hquad := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := fderiv ℝ F)
      (φ := fderiv ℝ (fderiv ℝ F) b) (fun z hz => hdiff2 z (hseg_by hz)) hbnd
      (convex_segment b y) (left_mem_segment ℝ b y) (right_mem_segment ℝ b y)
    -- `‖y − b‖ ≤ ‖a − b‖` on the outer segment.
    have hyb : ‖y - b‖ ≤ ‖a - b‖ := by
      rw [segment_eq_image'] at hy
      obtain ⟨θ, hθ, rfl⟩ := hy
      have hsub2 : (b + θ • (a - b)) - b = θ • (a - b) := by abel
      rw [hsub2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖a - b‖ ≤ 1 * ‖a - b‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ = ‖a - b‖ := one_mul _
    calc ‖fderiv ℝ F y - fderiv ℝ F b - fderiv ℝ (fderiv ℝ F) b (y - b)‖
        ≤ M * ‖y - b‖ * ‖y - b‖ := hquad
      _ = M * ‖y - b‖ ^ 2 := by ring
      _ ≤ M * ‖a - b‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hM
          exact pow_le_pow_left₀ (norm_nonneg _) hyb 2
  -- 3. Integrate the quadratic derivative bound along `[b,a]` (convex mean-value inequality).
  have hMVT := (convex_segment b a).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hR_full y hy).hasFDerivWithinAt) hbound_seg
    (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)
  -- `R b = 0`; conclude with the constant `M·‖a−b‖²·‖a−b‖ = M·‖a−b‖³`.
  have key : ‖(fun x : E => F x - F b - fderiv ℝ F b (x - b)
        - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ F) b (x - b)) (x - b)) a
      - (fun x : E => F x - F b - fderiv ℝ F b (x - b)
        - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ F) b (x - b)) (x - b)) b‖
      ≤ M * ‖a - b‖ ^ 3 := by
    refine le_trans hMVT (le_of_eq ?_); ring
  simpa using key

end QIQTH.ExpMap
