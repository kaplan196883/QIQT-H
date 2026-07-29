/-
  RNCTaylorPeano — the general-`v` second-order Peano (little-`o`) Taylor expansion for a `C²`
  scalar field on `Point n = Fin n → ℝ`, expressed in the repo's `pd` partial-derivative language.

  This is the FOUNDATIONAL primitive of the general-`v` RNC Taylor-`o(r²)` framework: the tool that
  will close the FULL off-diagonal `O(1/t)` cancellation in the van-Vleck / heat-kernel program
  (currently discharged only to Hessian order AT THE CENTRE).  Mathlib has the multivariable
  Fréchet/`iteratedFDeriv` calculus but NO ready-made multivariable second-order Peano remainder;
  the analytic core here is an honest mean-value-inequality argument built on
  `Convex.isLittleO_pow_succ`, and the coordinate work is the conversion `fderiv → ∑ pd` and
  `fderiv² (bilinear) → ∑∑ pd`, using the existing bridges `Curvature.pd_eq_fderiv` and
  `RNCExpansion.pd_pd_eq_of_contDiffAt2`.

  FLOOR reached: **F1 (full).**  `pd_taylor_two_peano` states, for `hf : ContDiffAt ℝ 2 f 0`,
    `(fun v => f v - f 0 - ∑ᵢ (∂ᵢf)(0)·vⁱ - ½ ∑ᵢⱼ (∂ᵢ∂ⱼf)(0)·vⁱ·vʲ) =o[𝓝 0] (fun v => ‖v‖²)`.
  Both conversions closed (F2 subsumed), and the first-order gradient Peano `pd_taylor_one_peano`
  (F3) lands as a standalone corollary.  Axiom-clean (`propext`/`Classical.choice`/`Quot.sound`),
  no `sorry`, no new axioms, `hf` a genuine `C²` hypothesis.

  Exact Mathlib Taylor-Peano tool used: `Convex.isLittleO_pow_succ`
    `(hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hff' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)`
    `(hf' : f' =o[𝓝[s] x₀] fun x ↦ ‖x - x₀‖ ^ n) : (fun x ↦ f x - f x₀) =o[𝓝[s] x₀] ‖x - x₀‖ ^ (n+1)`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RNCExpansion

namespace QIQTH.RNCExpansion

open QIQTH.Curvature Finset Asymptotics

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- A vector of `Point n = Fin n → ℝ` is the coordinate combination of the standard basis vectors. -/
theorem pi_eq_sum_smul_single (v : Point n) : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
  have h : ∀ i : Fin n, v i • Pi.single i (1 : ℝ) = Pi.single i (v i) := by
    intro i
    ext j
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [h]
  exact (Finset.univ_sum_single v).symm

/-- **Diagonal of a continuous bilinear form as a coordinate double sum.**  Pure algebra: for a
    continuous bilinear form `B` on `Point n`, `B v v = ∑ᵢ ∑ⱼ vⁱ vʲ · B eᵢ eⱼ`. -/
theorem clm_bilinear_diag_eq_sum (B : Point n →L[ℝ] Point n →L[ℝ] ℝ) (v : Point n) :
    B v v = ∑ i, ∑ j, v i * v j * B (Pi.single i 1) (Pi.single j 1) := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := pi_eq_sum_smul_single v
  have e1 : B v = ∑ i, v i • B (Pi.single i 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]; simp_rw [map_smul]
  have e2 : ∀ w : Point n, B w v = ∑ j, v j • (B w) (Pi.single j 1) := by
    intro w
    conv_lhs => rw [hv]
    rw [map_sum]; simp_rw [map_smul]
  calc B v v = (∑ i, v i • B (Pi.single i 1)) v := by rw [e1]
    _ = ∑ i, (v i • B (Pi.single i 1)) v := by rw [ContinuousLinearMap.sum_apply]
    _ = ∑ i, v i • ((B (Pi.single i 1)) v) := by simp_rw [ContinuousLinearMap.smul_apply]
    _ = ∑ i, v i • (∑ j, v j • (B (Pi.single i 1)) (Pi.single j 1)) := by simp_rw [e2]
    _ = ∑ i, ∑ j, v i * v j * B (Pi.single i 1) (Pi.single j 1) := by
        simp_rw [Finset.smul_sum, smul_smul, smul_eq_mul]

/-- **Gradient-as-partials.**  `Df(0)[v] = ∑ᵢ (∂ᵢf)(0)·vⁱ`. -/
theorem fderiv_apply_eq_sum_pd (f : Point n → ℝ) (v : Point n) (hf : DifferentiableAt ℝ f 0) :
    fderiv ℝ f 0 v = ∑ i, pd f i 0 * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := pi_eq_sum_smul_single v
  conv_lhs => rw [hv, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul, pd_eq_fderiv f i 0 hf]; ring

/-- **Hessian-as-second-partials (diagonal).**  `D²f(0)[v,v] = ∑ᵢ ∑ⱼ (∂ᵢ∂ⱼf)(0)·vⁱ·vʲ`, from the
    `pd ↔ fderiv²` bridge `pd_pd_eq_of_contDiffAt2` and the bilinear diagonal expansion. -/
theorem sndFDeriv_apply_eq_sum_pd (f : Point n → ℝ) (v : Point n) (hf : ContDiffAt ℝ 2 f 0) :
    fderiv ℝ (fderiv ℝ f) 0 v v
      = ∑ i, ∑ j, pd (fun y => pd f j y) i 0 * v i * v j := by
  rw [clm_bilinear_diag_eq_sum (fderiv ℝ (fderiv ℝ f) 0) v]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← pd_pd_eq_of_contDiffAt2 f i j hf]; ring

/-- **Second-order Peano expansion in Fréchet form.**  For `f` twice continuously differentiable at
    `0`, the second-order Taylor polynomial approximates `f` to `o(‖v‖²)`.  Proof: an honest
    mean-value inequality (`Convex.isLittleO_pow_succ`) — the derivative of the remainder is
    `o(‖v‖)` because `fderiv f` is differentiable at `0` with derivative the (symmetric) Hessian. -/
theorem contDiffAt2_taylor_snd_isLittleO (f : Point n → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    (fun v => f v - f 0 - fderiv ℝ f 0 v - (1 / 2) * (fderiv ℝ (fderiv ℝ f) 0 v v))
      =o[nhds (0 : Point n)] (fun v => ‖v‖ ^ 2) := by
  set L := fderiv ℝ f 0 with hLdef
  set B := fderiv ℝ (fderiv ℝ f) 0 with hBdef
  -- Symmetry of the second Fréchet derivative (Clairaut).
  have hsymm : ∀ v w : Point n, B v w = B w v := hf.isSymmSndFDerivAt (by simp)
  have hflip : B.flip = B := by
    ext v w; exact (hsymm v w).symm
  -- `fderiv f` is differentiable at `0` with derivative `B`.
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hf2 : HasFDerivAt (fun y => fderiv ℝ f y) B 0 := by
    rw [hBdef]; exact hfd2.hasFDerivAt
  -- A convex open neighbourhood `s` of `0` on which `f` is differentiable.
  have hdiff_ev : ∀ᶠ x in nhds (0 : Point n), DifferentiableAt ℝ f x := by
    have hev : ∀ᶠ x in nhds (0 : Point n), ContDiffAt ℝ 2 f x := hf.eventually (by norm_num)
    filter_upwards [hev] with x hx using hx.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.1 hdiff_ev
  set s : Set (Point n) := Metric.ball 0 δ with hs_def
  have hs_conv : Convex ℝ s := convex_ball 0 δ
  have hs_mem : s ∈ nhds (0 : Point n) := Metric.ball_mem_nhds 0 hδ
  have hx0s : (0 : Point n) ∈ s := Metric.mem_ball_self hδ
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x := fun x hx => hδp (Metric.mem_ball.1 hx)
  -- The remainder is `C¹` on `s`, with derivative `x ↦ Df(x) - L - B x`.
  have hRhas : ∀ x ∈ s, HasFDerivWithinAt
      (fun v => f v - f 0 - L v - (1 / 2 : ℝ) * (B v v)) (fderiv ℝ f x - L - B x) s x := by
    intro x hx
    have h1 : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x hx).hasFDerivAt
    have h2 : HasFDerivAt (fun v => (B v) v) (B x + B.flip x) x := by
      simpa using (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    have h3 : HasFDerivAt (fun v => (1 / 2 : ℝ) * (B v v)) ((1 / 2 : ℝ) • (B x + B.flip x)) x :=
      h2.const_mul (1 / 2)
    have hL : HasFDerivAt (fun v => L v) L x := L.hasFDerivAt
    have hconst : HasFDerivAt (fun _ : Point n => f 0) (0 : Point n →L[ℝ] ℝ) x :=
      hasFDerivAt_const (f 0) x
    have hbig := ((h1.sub hconst).sub hL).sub h3
    have hderiv_eq :
        (fderiv ℝ f x - (0 : Point n →L[ℝ] ℝ) - L) - (1 / 2 : ℝ) • (B x + B.flip x)
          = fderiv ℝ f x - L - B x := by
      rw [hflip]; module
    exact (hderiv_eq ▸ hbig).hasFDerivWithinAt
  -- The remainder derivative is `o(‖x‖)`.
  have hR'lo : (fun x => fderiv ℝ f x - L - B x)
      =o[nhdsWithin (0 : Point n) s] fun x => ‖x - (0 : Point n)‖ ^ 1 := by
    have h0 := hasFDerivAt_iff_isLittleO.1 hf2
    have h1 := Asymptotics.isLittleO_norm_right.mpr h0
    refine (h1.congr' (Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)).mono nhdsWithin_le_nhds
    · simp only [sub_zero, ← hLdef]
    · simp only [pow_one]
  -- Assemble via the mean-value Peano step.
  have key := hs_conv.isLittleO_pow_succ hx0s hRhas hR'lo
  rw [nhdsWithin_eq_nhds.2 hs_mem] at key
  refine key.congr' (Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => ?_)
  · simp
  · simp

/-- **The general-`v` second-order Peano (little-`o`) Taylor expansion, in `pd` language.**
    For a `C²` scalar field `f` on `Point n`,
      `f v = f 0 + ∑ᵢ (∂ᵢf)(0)·vⁱ + ½ ∑ᵢⱼ (∂ᵢ∂ⱼf)(0)·vⁱ·vʲ + o(‖v‖²)`.
    This is the foundational primitive of the RNC Taylor-`o(r²)` framework that will close the full
    off-diagonal `O(1/t)` cancellation (beyond the Hessian-order-at-centre result). -/
theorem pd_taylor_two_peano (f : Point n → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    (fun v => f v - f 0 - (∑ i, pd f i 0 * v i)
        - (1 / 2) * ∑ i, ∑ j, pd (fun y => pd f j y) i 0 * v i * v j)
      =o[nhds (0 : Point n)] (fun v => ‖v‖ ^ 2) := by
  have hEq : (fun v : Point n => f v - f 0 - (∑ i, pd f i 0 * v i)
        - (1 / 2 : ℝ) * ∑ i, ∑ j, pd (fun y => pd f j y) i 0 * v i * v j)
      = (fun v => f v - f 0 - fderiv ℝ f 0 v - (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) 0 v v)) := by
    funext v
    rw [fderiv_apply_eq_sum_pd f v (hf.differentiableAt (by norm_num)),
        sndFDeriv_apply_eq_sum_pd f v hf]
  rw [hEq]
  exact contDiffAt2_taylor_snd_isLittleO f hf

/-- **First-order gradient Peano expansion, in `pd` language (F3).**
    `f v = f 0 + ∑ᵢ (∂ᵢf)(0)·vⁱ + o(‖v‖)` for `f` differentiable at `0`. -/
theorem pd_taylor_one_peano (f : Point n → ℝ) (hf : DifferentiableAt ℝ f 0) :
    (fun v => f v - f 0 - (∑ i, pd f i 0 * v i))
      =o[nhds (0 : Point n)] (fun v => ‖v‖) := by
  have hgrad : (fun v : Point n => f v - f 0 - (∑ i, pd f i 0 * v i))
      = (fun v => f v - f 0 - fderiv ℝ f 0 v) := by
    funext v; rw [fderiv_apply_eq_sum_pd f v hf]
  rw [hgrad]
  have h0 := hasFDerivAt_iff_isLittleO.1 hf.hasFDerivAt
  have h1 := Asymptotics.isLittleO_norm_right.mpr h0
  refine h1.congr' (Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
  · simp only [sub_zero]
  · simp only [sub_zero]

end QIQTH.RNCExpansion
