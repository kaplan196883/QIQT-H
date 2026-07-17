/-
  RadialTransport — the DeWitt heat-parametrix transport recursion solved ALONG RADIAL RAYS.

  Phase J3 of the Jacobi/van-Vleck campaign (docs/qg_roadmap/JACOBI_VANVLECK_PLAN.md): the heat-parametrix
  transport coefficients `u_k(v)` satisfy, off the diagonal, the radial transport ODE
    `(k + r∂_r) u_k = f_k`,    `f_k = transportOp(u_{k−1})`,   `r∂_r = ∑ vⁱ ∂ᵢ` (the Euler field),
  where `r∂_r` is the `radialDeriv` of `QIQTH.RadialDistance`.  The KEY tractable fact is that this ODE has
  an EXPLICIT ray-integral solution — no `r^{−k}` singularity, since the `r`'s cancel under the ray
  substitution:
    `u_k(v) = ∫₀¹ s^{k−1} f(s•v) ds`   (`radialTransportSolve`).
  This file builds that solution operator and PROVES it solves the transport equation
  (`radialTransportSolve_transport_eq`), via the clean route: differentiate under the integral (Leibniz),
  the ray chain rule `deriv (s ↦ f(s•v)) = ∑ vⁱ (∂ᵢf)(s•v)`, and integration by parts (Euler's identity in
  disguise: `∫₀¹ s^k g'(s) ds = g(1) − k∫₀¹ s^{k−1} g(s) ds`).

  ⚠ HONEST SCOPE.  This is the transport-equation SOLUTION OPERATOR (the engine for every `u_k`).  It is NOT
  the full parametrix assembly (J4), NOT the residual bound (J5), NOT `a₁ = R/6` (J6).  The carried input is
  exactly the genuine smoothness of `f` (`ContDiff ℝ ⊤ f`) demanded by the Leibniz/IBP steps — nothing
  vacuous, nothing that assumes the conclusion.  Axiom-free (std-3).
-/
import Mathlib
import QIQTH.Curvature
import QIQTH.RadialDistance

namespace QIQTH.RadialTransport

open QIQTH.Curvature QIQTH.RadialDistance MeasureTheory
open scoped BigOperators Interval

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ### Continuity of the coordinate partial derivative -/

/-- The one-parameter family `t ↦ update v i t` (varying only the `i`-th coordinate) is continuous. -/
theorem continuous_updatePt (v : Point n) (i : Fin n) :
    Continuous (fun t : ℝ => Function.update v i t) := by
  refine continuous_pi (fun j => ?_)
  simp only [Function.update_apply]
  by_cases h : j = i
  · simp only [if_pos h]; exact continuous_id
  · simp only [if_neg h]; exact continuous_const

/-- For a `C∞` field `f`, the partial derivative `∂ᵢ f` is continuous. -/
theorem continuous_pd (f : Point n → ℝ) (hf : ContDiff ℝ ⊤ f) (i : Fin n) :
    Continuous (fun x => pd f i x) := by
  have e : (fun x => pd f i x) = fun x => fderiv ℝ f x (Pi.single i 1) :=
    funext (fun x => pd_eq_fderiv f i x ((hf.differentiable (by simp)).differentiableAt))
  rw [e]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-! ### The directional derivative as a radial sum, and the ray chain rule -/

/-- **`fderiv` in the radial direction as a coordinate sum**: `Df(pt)[v] = ∑ᵢ vⁱ (∂ᵢf)(pt)`. -/
theorem fderiv_radialSum (f : Point n → ℝ) (pt v : Point n) (hf : DifferentiableAt ℝ f pt) :
    fderiv ℝ f pt v = ∑ i, v i * pd f i pt := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hs : Pi.single i (v i) = v i • (Pi.single i (1:ℝ) : Point n) := by
    funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [hs, map_smul, pd_eq_fderiv f i pt hf, smul_eq_mul]

/-- **The ray chain rule**: `deriv (s ↦ f(s•v)) = ∑ᵢ vⁱ (∂ᵢf)(s•v)`.  The tangent of the ray `s ↦ s•v`
    is the constant vector `v`, so the chain rule contracts `Df` against `v`. -/
theorem hasDerivAt_ray (f : Point n → ℝ) (v : Point n) (s : ℝ)
    (hf : DifferentiableAt ℝ f (s • v)) :
    HasDerivAt (fun s : ℝ => f (s • v)) (∑ i, v i * pd f i (s • v)) s := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v s := by
    simpa using (hasDerivAt_id' s).smul_const v
  have h2 : HasFDerivAt f (fderiv ℝ f (s • v)) (s • v) := hf.hasFDerivAt
  have h3 := h2.comp_hasDerivAt s h1
  rw [fderiv_radialSum f (s • v) v hf] at h3
  exact h3

/-! ### The radial transport solution operator -/

/-- **The radial transport solution operator** `u_k(v) = ∫₀¹ s^{k−1} f(s•v) ds` — the explicit ray-integral
    solution of the DeWitt transport ODE `(k + r∂_r) u = f` (for `k ≥ 1`).  `s • v` is the scalar-mul ray. -/
noncomputable def radialTransportSolve (k : ℕ) (f : Point n → ℝ) (v : Point n) : ℝ :=
  ∫ s in (0:ℝ)..1, s ^ (k - 1) * f (s • v)

/-- **The base transport coefficient** `u_0 ≡ 1`: `radialTransportSolve 1 (·↦1) = 1`.  (The `k=1`, `f≡1`
    case: `∫₀¹ s⁰·1 ds = 1`.) -/
theorem radialTransportSolve_one_const (v : Point n) :
    radialTransportSolve 1 (fun _ => (1:ℝ)) v = 1 := by
  simp [radialTransportSolve]

/-! ### The transport equation is solved -/

/-- **THE J3 deliverable — the transport ODE is solved.**  For `k ≥ 1` and `f` smooth (`ContDiff ℝ ⊤`),
    `radialTransportSolve k f` solves `(k + r∂_r) u_k = f`:
      `k · u_k(v) + radialDeriv(u_k)(v) = f(v)`.
    Proof: differentiate under the integral (Leibniz, with a compactness bound on `∂ᵢf` over the ray tube)
    gives `∂ᵢ u_k(v) = ∫₀¹ s^{k−1}·s·(∂ᵢf)(s•v) ds`; the ray chain rule turns `∑ᵢ vⁱ (∂ᵢf)(s•v)` into
    `(d/ds) f(s•v)`; integration by parts (`∫₀¹ s^k g'(s) ds = g(1) − k∫₀¹ s^{k−1} g(s) ds`) then yields
    `radialDeriv(u_k)(v) = f(v) − k·u_k(v)`. -/
theorem radialTransportSolve_transport_eq (k : ℕ) (hk : 1 ≤ k) (f : Point n → ℝ)
    (hf : ContDiff ℝ ⊤ f) (v : Point n) :
    (k : ℝ) * radialTransportSolve k f v + radialDeriv (radialTransportSolve k f) v = f v := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ f x :=
    fun x => (hf.differentiable (by simp)).differentiableAt
  -- `s^{k-1}·s = s^k` for `k ≥ 1`.
  have hpow : ∀ s : ℝ, s ^ (k - 1) * s = s ^ k := fun s => by
    rw [← pow_succ]; congr 1; omega
  -- === Leibniz: the `i`-th partial of `u_k` at `v`. ===
  have hpd : ∀ i : Fin n, pd (radialTransportSolve k f) i v
      = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := by
    intro i
    -- a uniform bound on `∂ᵢf` over the compact ray tube `[0,1] × closedBall (v i) 1`.
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (v i) 1)).exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ => pd f i (p.1 • Function.update v i p.2))
      ((continuous_pd f hf i).comp
        (continuous_fst.smul ((continuous_updatePt v i).comp continuous_snd))).continuousOn
    -- continuity of the integrand and its parameter-derivative.
    have hcF : ∀ t : ℝ, Continuous (fun s : ℝ => s ^ (k - 1) * f (s • Function.update v i t)) :=
      fun t => (continuous_pow (k - 1)).mul (hf.continuous.comp (continuous_id.smul continuous_const))
    have hcF' : ∀ t : ℝ,
        Continuous (fun s : ℝ => s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) :=
      fun t => (continuous_pow (k - 1)).mul (continuous_id.mul
        ((continuous_pd f hf i).comp (continuous_id.smul continuous_const)))
    -- the dominating bound.
    have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          ‖s ^ (k - 1) * (s * pd f i (s • Function.update v i t))‖ ≤ (fun _ => M) s := by
      refine Filter.Eventually.of_forall (fun s hs t ht => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      obtain ⟨hs0, hs1⟩ := hs
      have hmem : (s, t) ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v i) 1 :=
        ⟨⟨le_of_lt hs0, hs1⟩, Metric.ball_subset_closedBall ht⟩
      have hb := hM (s, t) hmem
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_mul, abs_mul]
      have h1 : |s ^ (k - 1)| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (le_of_lt hs0) hs1
      have h2 : |s| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hs0)]; exact hs1
      have hpdnn : (0:ℝ) ≤ |pd f i (s • Function.update v i t)| := abs_nonneg _
      have step : |s| * |pd f i (s • Function.update v i t)| ≤ M :=
        le_trans (mul_le_mul h2 hb hpdnn (by norm_num)) (le_of_eq (one_mul M))
      calc |s ^ (k - 1)| * (|s| * |pd f i (s • Function.update v i t)|)
          ≤ 1 * M := mul_le_mul h1 step (by positivity) (by norm_num)
        _ = M := one_mul M
    -- the pointwise `t`-derivative.
    have hderiv : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          HasDerivAt (fun t => s ^ (k - 1) * f (s • Function.update v i t))
            (s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) t := by
      refine Filter.Eventually.of_forall (fun s _ t _ => ?_)
      have hup : HasDerivAt (fun t => s • Function.update v i t) (s • Pi.single i 1) t :=
        (hasDerivAt_update v i t).const_smul s
      have hff : HasFDerivAt f (fderiv ℝ f (s • Function.update v i t))
          (s • Function.update v i t) := (hdiffbl _).hasFDerivAt
      have hcomp := hff.comp_hasDerivAt t hup
      have hval : (fderiv ℝ f (s • Function.update v i t)) (s • Pi.single i 1)
          = s * pd f i (s • Function.update v i t) := by
        rw [map_smul, smul_eq_mul, ← pd_eq_fderiv f i (s • Function.update v i t) (hdiffbl _)]
      rw [hval] at hcomp
      exact HasDerivAt.const_mul (s ^ (k - 1)) hcomp
    -- apply the parametric Leibniz rule.
    have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t s => s ^ (k - 1) * f (s • Function.update v i t))
      (F' := fun t s => s ^ (k - 1) * (s * pd f i (s • Function.update v i t)))
      (bound := fun _ => M) (x₀ := v i) (s := Metric.ball (v i) 1) (a := 0) (b := 1)
      (Metric.ball_mem_nhds (v i) one_pos)
      (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
      ((hcF (v i)).intervalIntegrable 0 1)
      ((hcF' (v i)).aestronglyMeasurable)
      hbound intervalIntegrable_const hderiv
    -- read off `pd u_k i v`, rewriting `update v i (v i) = v`.
    have h0 : HasDerivAt
        (fun t => ∫ s in (0:ℝ)..1, s ^ (k - 1) * f (s • Function.update v i t))
        (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v))) (v i) := by
      have := leibniz.2
      rw [show (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • Function.update v i (v i))))
            = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) from
          intervalIntegral.integral_congr (fun s _ => by rw [Function.update_eq_self])] at this
      exact this
    have hval2 : deriv (fun t => radialTransportSolve k f (Function.update v i t)) (v i)
        = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := h0.deriv
    rw [pd]; exact hval2
  -- === radialDeriv u_k as a single ray integral. ===
  have hRD : radialDeriv (radialTransportSolve k f) v
      = ∫ s in (0:ℝ)..1, s ^ k * (∑ i, v i * pd f i (s • v)) := by
    rw [radialDeriv]
    have hswap : ∀ i, v i * pd (radialTransportSolve k f) i v
        = ∫ s in (0:ℝ)..1, v i * (s ^ (k - 1) * (s * pd f i (s • v))) := by
      intro i; rw [hpd i, ← intervalIntegral.integral_const_mul]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        IntervalIntegrable (fun s => v i * (s ^ (k - 1) * (s * pd f i (s • v)))) volume 0 1 :=
      fun i _ => (continuous_const.mul ((continuous_pow (k - 1)).mul (continuous_id.mul
        ((continuous_pd f hf i).comp (continuous_id.smul continuous_const))))).intervalIntegrable 0 1
    rw [Finset.sum_congr rfl (fun i _ => hswap i), ← intervalIntegral.integral_finsetSum hInt]
    apply intervalIntegral.integral_congr
    intro s _
    show (∑ i, v i * (s ^ (k - 1) * (s * pd f i (s • v))))
        = s ^ k * ∑ i, v i * pd f i (s • v)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hpow s]; ring
  -- === integration by parts. ===
  have hv'int : IntervalIntegrable (fun s => ∑ i, v i * pd f i (s • v)) volume 0 1 :=
    (continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul
      ((continuous_pd f hf i).comp (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s ^ k) (v := fun s => f (s • v))
    (u' := fun s => (k : ℝ) * s ^ (k - 1)) (v' := fun s => ∑ i, v i * pd f i (s • v))
    (fun s _ => hasDerivAt_pow k s)
    (fun s _ => hasDerivAt_ray f v s (hdiffbl _))
    ((continuous_const.mul (continuous_pow (k - 1))).intervalIntegrable 0 1)
    hv'int
  have hInt2 : (∫ s in (0:ℝ)..1, ((k : ℝ) * s ^ (k - 1)) * f (s • v))
      = (k : ℝ) * radialTransportSolve k f v := by
    rw [radialTransportSolve, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _; ring
  rw [hRD, hIBP, hInt2]
  simp only [one_pow, one_smul, one_mul, zero_pow (show k ≠ 0 by omega), zero_mul, sub_zero]
  ring

end QIQTH.RadialTransport
