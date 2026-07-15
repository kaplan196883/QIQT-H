/-
  PullbackMetric — the pullback of the ambient metric through the geodesic exponential map,
  and its regularity ledger toward the `κ = 1/6` endgame (THE_PARAMETRIX_CRITICAL_PATH R3→κ).

  Setting.  `Point n = Fin n → ℝ`.  The ambient metric `g : Point n → Fin n → Fin n → ℝ` (component
  form: `g y a b` is the `(a,b)`-component of the metric at `y`).  The geodesic exponential map at `p`,
  `exp_p := expMap g gi hC p : Point n → Point n`, is `ContDiff³` on `ball 0 (expRho …)` (Rung 3,
  `expMap_contDiffOn_three`, unconditional).

  The pullback metric is `g̃(x)_{ij} = ∑_{a,b} g(exp_p x)_{ab} · (D exp_p x · e_i)_a · (D exp_p x · e_j)_b`,
  with `D exp_p x = fderiv ℝ exp_p x` and `e_i = Pi.single i 1`.  It is the metric that Riemann normal
  coordinates centred at `p` are built to satisfy the RNC gauge for.

  MAIN RESULT (this file).  From `exp_p ∈ C³` (Rung 3) and `g ∈ C^∞` (ambient smoothness), the pullback
  metric is `ContDiffOn ℝ 2` on the exp-ball.  This is SHARP for the composition budget:
  `g̃` involves `fderiv exp_p`, which drops one order from `exp_p`, so `C³ exp_p ⟹ C² (fderiv exp_p)`
  and hence `C² g̃`.  The regularity ledger for the `κ = 1/6` step is recorded at the end of the file.
-/
import Mathlib
import QIQTH.ExpMapContDiff3

namespace QIQTH.PullbackMetric

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic
open Finset

variable {n : ℕ}

/-- **The pullback metric** `g̃ = exp_p^* g`, in component form.

    `expPullbackMetric g gi hC p x i j = ∑_{a,b} g(exp_p x)_{ab} · (D exp_p x · e_i)_a · (D exp_p x · e_j)_b`

    where `exp_p := expMap g gi hC p`, `D exp_p x = fderiv ℝ exp_p x` is the Fréchet derivative
    (Jacobian) of the exponential map at `x`, and `e_i = Pi.single i 1` is the `i`-th coordinate basis
    vector.  This is the ordinary tensorial pullback of the ambient metric `g` by `exp_p`.

    Well-behaved only where `exp_p` is a differentiable diffeomorphism onto its image, i.e. on
    `ball 0 (expRho g gi hC p)` (where Rung 1–3 supply the regularity used below). -/
noncomputable def expPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (x : Point n) (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, g (expMap g gi hC p x) a b
    * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
    * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b

/-- **The Jacobian of `exp_p` is `ContDiffOn ℝ 2` on the exp-ball.**  `fderiv` drops one differentiability
    order from the `ContDiff³` `exp_p` (Rung 3, `expMap_contDiffOn_three`), on the open ball. -/
theorem contDiffOn_fderiv_expMap (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 2 (fun x => fderiv ℝ (expMap g gi hC p) x)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
  (expMap_contDiffOn_three g gi hC p).fderiv_of_isOpen Metric.isOpen_ball (by norm_num)

/-- Each scalar component of the Jacobian, `x ↦ (D exp_p x · e_i)_a`, is `ContDiffOn ℝ 2` on the
    exp-ball: apply the `ContDiffOn ℝ 2` CLM-field `x ↦ D exp_p x` to the constant vector `e_i`
    (`ContDiffOn.clm_apply`) and read off the `a`-th coordinate (compose with the projection CLM). -/
theorem contDiffOn_fderiv_expMap_component (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a : Fin n) :
    ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  have hJv : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1))
      (Metric.ball (0 : Point n) (expRho g gi hC p)) :=
    (contDiffOn_fderiv_expMap g gi hC p).clm_apply contDiffOn_const
  exact hJv.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a)

/-- **REGULARITY OF THE PULLBACK METRIC (the deliverable):** each component `x ↦ g̃(x)_{ij}` of the
    pullback metric is `ContDiffOn ℝ 2` on the exp-ball, given `exp_p ∈ C³` (Rung 3) and the ambient
    metric `g ∈ C^∞`.

    Composition budget (why `m = 2` is the best provable, and is sharp for this construction):
    * `x ↦ g(exp_p x)_{ab}` is `ContDiffOn ℝ 3` (`C^∞` `g` composed with `C³` `exp_p`);
    * `x ↦ (D exp_p x · e_i)_a` is `ContDiffOn ℝ 2` (`fderiv exp_p` is one order below `exp_p`);
    * the triple product and the finite `∑_{a,b}` preserve the minimum order `2`. -/
theorem contDiffOn_expPullbackMetric (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j : Fin n) :
    ContDiffOn ℝ 2 (fun x => expPullbackMetric g gi hC p x i j)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hs
  -- `exp_p ∈ C³` on `s`; downgrade to `C²` where needed.
  have hE : ContDiffOn ℝ 2 (expMap g gi hC p) s :=
    (expMap_contDiffOn_three g gi hC p).of_le (by norm_num)
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  -- `x ↦ g(exp_p x)_{ab}` : `C^∞` `g`-component composed with `C²` `exp_p`.
  have hgcomp : ContDiffOn ℝ 2 (fun x => g (expMap g gi hC p x) a b) s :=
    ((hg a b).of_le (le_top)).comp_contDiffOn hE
  -- the two Jacobian components.
  have hJa : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) s :=
    contDiffOn_fderiv_expMap_component g gi hC p i a
  have hJb : ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) s :=
    contDiffOn_fderiv_expMap_component g gi hC p j b
  exact (hgcomp.mul hJa).mul hJb

/-!
### RNC value/first-order jets of `g̃` at `0` (the load-bearing normal-coordinate facts)
-/

/-- **`exp_p 0 = p`.**  The exponential map fixes the basepoint.  Extracted from the value 2-jet
    little-o (`expMap_value_two_jet`): the jet remainder is `o(‖v‖²)`, hence its value AT `v = 0`
    (where `‖v‖² = 0`) must itself vanish; at `v = 0` the quadratic Christoffel term also vanishes,
    leaving `exp_p 0 − p = 0`. -/
theorem expMap_apply_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    expMap g gi hC p 0 = p := by
  have hb := ((expMap_value_two_jet g gi hC p).def one_pos).self_of_nhds
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    norm_le_zero_iff] at hb
  have hz : (fun i => ∑ j, ∑ k, christoffel g gi i j k p * (0 : Point n) j * (0 : Point n) k)
      = (0 : Point n) := by funext i; simp
  rw [hz, smul_zero, add_zero, sub_zero, sub_eq_zero] at hb
  exact hb

/-- **`D exp_p 0 = id`.**  The Fréchet derivative of the exponential map at the origin is the
    identity (the defining normal-coordinate gauge on the frame).  Immediate from
    `hasStrictFDerivAt_expMap`. -/
theorem fderiv_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    fderiv ℝ (expMap g gi hC p) 0 = ContinuousLinearMap.id ℝ (Point n) :=
  (hasStrictFDerivAt_expMap g gi hC p).hasFDerivAt.fderiv

/-- **`g̃(0)_{ij} = g(p)_{ij}` (the RNC value jet).**  At the centre of the exp-normal coordinates the
    pullback metric equals the ambient metric at `p`: `exp_p 0 = p` and `D exp_p 0 = id` collapse the
    Jacobian factors to Kronecker deltas.  In a `p`-orthonormal frame (`g p = δ`) this is the standard
    `g̃(0) = δ`; we record the frame-free form. -/
theorem expPullbackMetric_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i j : Fin n) :
    expPullbackMetric g gi hC p 0 i j = g p i j := by
  simp only [expPullbackMetric, expMap_apply_zero, fderiv_expMap_zero,
    ContinuousLinearMap.id_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Scalar form of the exp-map Jacobian one-jet model `expJetOneJetModel g gi p v`, evaluated on a
    vector `w` and read at coordinate `a`. -/
theorem expJetOneJetModel_apply (g gi : Point n → Fin n → Fin n → ℝ) (p v w : Point n) (a : Fin n) :
    (expJetOneJetModel g gi p v) w a
      = (1 / 2) * ∑ j, (-(∑ k, christoffel g gi a j k p * v k)
          - ∑ k, christoffel g gi a k j p * v k) * w j := by
  simp only [expJetOneJetModel, ContinuousLinearMap.smul_apply, matVecCLM_apply, Pi.smul_apply,
    smul_eq_mul]

/-- The map `v ↦ expJetOneJetModel g gi p v` packaged as a **continuous linear map** in `v` (it is
    linear in `v`, and `Point n` is finite-dimensional so it is automatically continuous).  Its value
    is the derivative of the exp-map Jacobian `v ↦ D exp_p v` at the origin. -/
noncomputable def expJetOneJetModelL (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) :
    Point n →L[ℝ] (Point n →L[ℝ] Point n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => expJetOneJetModel g gi p v
      map_add' := by
        intro v w
        refine ContinuousLinearMap.ext fun η => funext fun a => ?_
        simp only [ContinuousLinearMap.add_apply, Pi.add_apply, expJetOneJetModel_apply,
          Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hsplit : ∀ c : Fin n → ℝ, (∑ k, c k * (v k + w k))
            = (∑ k, c k * v k) + ∑ k, c k * w k :=
          fun c => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [hsplit (fun k => christoffel g gi a j k p), hsplit (fun k => christoffel g gi a k j p)]
        ring
      map_smul' := by
        intro c v
        refine ContinuousLinearMap.ext fun η => funext fun a => ?_
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
          expJetOneJetModel_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hsplit : ∀ d : Fin n → ℝ, (∑ k, d k * (c * v k)) = c * ∑ k, d k * v k :=
          fun d => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [hsplit (fun k => christoffel g gi a j k p), hsplit (fun k => christoffel g gi a k j p)]
        ring }

@[simp] theorem expJetOneJetModelL_apply (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) :
    expJetOneJetModelL g gi p v = expJetOneJetModel g gi p v := rfl

/-- **The exp-map Jacobian `v ↦ D exp_p v` is Fréchet-differentiable at `0`, with derivative the
    linear model `expJetOneJetModelL`.**  This upgrades the one-jet big-`O` bound
    `hasFDerivAt_expMap_jacobian_one_jet` (`D exp_p v − (id + model v) = O(‖v‖²)`) to a genuine
    `HasFDerivAt`, since `‖v‖² = o(‖v‖)` at `0` and `D exp_p 0 = id`. -/
theorem hasFDerivAt_fderiv_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    HasFDerivAt (fun v => fderiv ℝ (expMap g gi hC p) v) (expJetOneJetModelL g gi p) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have haux : (fun v : Point n => ‖v‖ ^ 2) =o[nhds (0 : Point n)] (fun v => v) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    filter_upwards [Metric.ball_mem_nhds (0 : Point n) hc] with v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul_of_nonneg_right hv.le (norm_nonneg _)
  have hbo := (hasFDerivAt_expMap_jacobian_one_jet g gi hC p).trans_isLittleO haux
  refine hbo.congr' (Filter.Eventually.of_forall fun h => ?_) (Filter.EventuallyEq.refl _ _)
  simp only [zero_add, expJetOneJetModelL_apply, fderiv_expMap_zero]
  abel

/-- **The scalar Jacobian component `x ↦ (D exp_p x)(e_i)_a` is Fréchet-differentiable at `0`.**
    It is `Λ ∘ (v ↦ D exp_p v)` for the evaluation-then-projection CLM `Λ T = T(e_i)_a`, and both
    factors are differentiable at `0` (`hasFDerivAt_fderiv_expMap_zero`). -/
theorem hasFDerivAt_jacobian_component_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a : Fin n) :
    HasFDerivAt (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
      (((ContinuousLinearMap.proj a).comp
          (ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1))).comp
        (expJetOneJetModelL g gi p)) 0 := by
  set Λ : (Point n →L[ℝ] Point n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1))
      with hΛ
  have hcomp0 := Λ.hasFDerivAt.comp 0 (hasFDerivAt_fderiv_expMap_zero g gi hC p)
  exact hcomp0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [hΛ, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply])

/-- **The first jet of the exp-map Jacobian at `0`.**  In the exp-normal coordinates,
    `∂_l (D exp_p · e_i)_a (0) = ½(−Γ^a_{il}(p) − Γ^a_{li}(p))`.  This is the load-bearing
    normal-coordinate fact behind `∂g̃(0) = 0`: the Jacobian's linear correction is exactly the
    (symmetrised) Christoffel symbol at `p`.  Proof: the scalar field
    `x ↦ (D exp_p x)(e_i)_a = Λ(D exp_p x)` (evaluation-then-projection `Λ`) has Fréchet derivative
    `Λ ∘ expJetOneJetModelL` at `0` (`hasFDerivAt_fderiv_expMap_zero`); evaluating on `e_l` and reading
    off `expJetOneJetModel`'s scalar form collapses the two `Pi.single` sums. -/
theorem pd_jacobian_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a l : Fin n) :
    pd (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) l 0
      = (1 / 2) * (-christoffel g gi a i l p - christoffel g gi a l i p) := by
  have hcomp := hasFDerivAt_jacobian_component_expMap_zero g gi hC p i a
  rw [pd_eq_fderiv _ l 0 hcomp.differentiableAt, hcomp.fderiv,
    ContinuousLinearMap.comp_apply, expJetOneJetModelL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply, expJetOneJetModel_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **The Jacobian component `x ↦ (D exp_p x)(e_i)_a` value at `0` is the Kronecker delta.** -/
theorem jacobian_component_expMap_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a : Fin n) :
    (fderiv ℝ (expMap g gi hC p) 0) (Pi.single i 1) a = (Pi.single i 1 : Point n) a := by
  rw [fderiv_expMap_zero, ContinuousLinearMap.id_apply]

/-- Coordinate partial differentiability from Fréchet differentiability at a point (local form,
    not needing global `ContDiff`). -/
theorem pdiffAt_of_differentiableAt (f : Point n → ℝ) (l : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f x) : PdiffAt f l x := by
  have hx : DifferentiableAt ℝ f ((Function.update x l) (x l)) := by
    rw [Function.update_eq_self]; exact hf
  exact hx.comp (x l) (hasDerivAt_update x l (x l)).differentiableAt

/-- The metric-along-exp field `x ↦ g(exp_p x)_{ab}` is Fréchet-differentiable at `0`. -/
theorem differentiableAt_metric_comp_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b : Fin n) :
    DifferentiableAt ℝ (fun x => g (expMap g gi hC p x) a b) 0 := by
  have hgd : DifferentiableAt ℝ (fun y => g y a b) (expMap g gi hC p 0) := by
    rw [expMap_apply_zero]; exact ((hg a b).differentiable (by simp)).differentiableAt
  exact hgd.comp 0 (hasStrictFDerivAt_expMap g gi hC p).hasFDerivAt.differentiableAt

/-- **Chain rule at the centre:** `∂_l (g(exp_p ·)_{ab})(0) = ∂_l g_{ab}(p)` — since `exp_p 0 = p`
    and `D exp_p 0 = id`, the pullback of the ambient partial derivative is trivial at `0`. -/
theorem pd_metric_comp_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b l : Fin n) :
    pd (fun x => g (expMap g gi hC p x) a b) l 0 = pd (fun y => g y a b) l p := by
  have hgd : HasFDerivAt (fun y => g y a b) (fderiv ℝ (fun y => g y a b) p)
      (expMap g gi hC p 0) := by
    rw [expMap_apply_zero]; exact (((hg a b).differentiable (by simp)).differentiableAt).hasFDerivAt
  have hexp : HasFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0 :=
    (hasStrictFDerivAt_expMap g gi hC p).hasFDerivAt
  have hchain : HasFDerivAt (fun x => g (expMap g gi hC p x) a b)
      ((fderiv ℝ (fun y => g y a b) p).comp (ContinuousLinearMap.id ℝ (Point n))) 0 :=
    hgd.comp 0 hexp
  rw [pd_eq_fderiv _ l 0 hchain.differentiableAt, hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (pd_eq_fderiv (fun y => g y a b) l p
    (((hg a b).differentiable (by simp)).differentiableAt)).symm

/-- **Leibniz expansion of a single `(a,b)` summand of `∂_l g̃(0)`.**  The triple product
    `g(exp·)_{ab} · (D exp·)(e_i)_a · (D exp·)(e_j)_b` differentiates by the product rule; each factor's
    value/derivative at `0` is supplied by the RNC jet lemmas. -/
theorem pd_expPullback_summand_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l a b : Fin n) :
    pd (fun x => g (expMap g gi hC p x) a b
          * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
          * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0
      = pd (fun y => g y a b) l p * (Pi.single i 1 : Point n) a * (Pi.single j 1 : Point n) b
        + g p a b * ((1 / 2) * (-christoffel g gi a i l p - christoffel g gi a l i p))
            * (Pi.single j 1 : Point n) b
        + g p a b * (Pi.single i 1 : Point n) a
            * ((1 / 2) * (-christoffel g gi b j l p - christoffel g gi b l j p)) := by
  have hpA : PdiffAt (fun x => g (expMap g gi hC p x) a b) l 0 :=
    pdiffAt_of_differentiableAt _ l 0 (differentiableAt_metric_comp_expMap_zero g gi hC p hg a b)
  have hpB : PdiffAt (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) l 0 :=
    pdiffAt_of_differentiableAt _ l 0
      (hasFDerivAt_jacobian_component_expMap_zero g gi hC p i a).differentiableAt
  have hpC : PdiffAt (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0 :=
    pdiffAt_of_differentiableAt _ l 0
      (hasFDerivAt_jacobian_component_expMap_zero g gi hC p j b).differentiableAt
  rw [pd_mul _ _ l 0 (hpA.mul hpB) hpC, pd_mul _ _ l 0 hpA hpB,
    pd_metric_comp_expMap_zero g gi hC p hg a b l,
    pd_jacobian_expMap_zero g gi hC p i a l,
    pd_jacobian_expMap_zero g gi hC p j b l,
    expMap_apply_zero, jacobian_component_expMap_at_zero g gi hC p i a,
    jacobian_component_expMap_at_zero g gi hC p j b]
  ring

/-- **`∂g̃(0) = 0` (RNC first-order flatness).**  In the exp-normal coordinates centred at `p`, every
    first partial derivative of the pullback metric vanishes at the origin:
    `∂_l g̃_{ij}(0) = 0`.  This is the defining normal-coordinate property.  Proof: the pullback is a
    triple product whose Leibniz derivative at `0` collapses (via `D exp_p 0 = id`) to
    `∂_l g_{ij}(p) − Γ_{j,·,·} − Γ_{i,·,·}` contractions; `christoffel_lower` (metric compatibility) plus
    metric symmetry make the three terms cancel identically.

    Hypotheses: `g` symmetric (`hsymm`), `gi` its inverse at `p` (`hinv`), `g ∈ C^∞` (`hg`). -/
theorem pd_expPullbackMetric_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l : Fin n) :
    pd (fun x => expPullbackMetric g gi hC p x i j) l 0 = 0 := by
  -- Per-factor / per-summand partial differentiability at `0`.
  have hpF : ∀ a b, PdiffAt (fun x => g (expMap g gi hC p x) a b
      * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
      * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0 := fun a b =>
    ((pdiffAt_of_differentiableAt _ l 0
        (differentiableAt_metric_comp_expMap_zero g gi hC p hg a b)).mul
      (pdiffAt_of_differentiableAt _ l 0
        (hasFDerivAt_jacobian_component_expMap_zero g gi hC p i a).differentiableAt)).mul
      (pdiffAt_of_differentiableAt _ l 0
        (hasFDerivAt_jacobian_component_expMap_zero g gi hC p j b).differentiableAt)
  have hpFin : ∀ a, PdiffAt (fun x => ∑ b, g (expMap g gi hC p x) a b
      * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
      * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0 := fun a =>
    PdiffAt_sum Finset.univ _ l 0 (fun b _ => hpF a b)
  -- Reduce `∂_l` of the double sum to the sum of per-summand Leibniz derivatives.
  simp only [expPullbackMetric]
  rw [pd_sum Finset.univ (fun a x => ∑ b, g (expMap g gi hC p x) a b
        * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
        * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0 (fun a _ => hpFin a),
    Finset.sum_congr rfl (fun a _ => pd_sum Finset.univ (fun b x => g (expMap g gi hC p x) a b
        * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
        * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l 0 (fun b _ => hpF a b)),
    Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
      pd_expPullback_summand_zero g gi hC p hg i j l a b))]
  -- Split into the three Leibniz sums and collapse the Kronecker `Pi.single` factors.
  simp only [Finset.sum_add_distrib]
  have hcol1 : (∑ a, ∑ b, pd (fun y => g y a b) l p
        * (Pi.single i 1 : Point n) a * (Pi.single j 1 : Point n) b)
      = pd (fun y => g y i j) l p := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcol2 : (∑ a, ∑ b, g p a b
        * ((1 / 2) * (-christoffel g gi a i l p - christoffel g gi a l i p))
        * (Pi.single j 1 : Point n) b)
      = ∑ a, g p a j * ((1 / 2) * (-christoffel g gi a i l p - christoffel g gi a l i p)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hcol3 : (∑ a, ∑ b, g p a b * (Pi.single i 1 : Point n) a
        * ((1 / 2) * (-christoffel g gi b j l p - christoffel g gi b l j p)))
      = ∑ b, g p i b * ((1 / 2) * (-christoffel g gi b j l p - christoffel g gi b l j p)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hcol1, hcol2, hcol3]
  -- Express the two contraction sums via `christoffel_lower` (metric compatibility).
  have hS2 : (∑ a, g p a j * ((1 / 2) * (-christoffel g gi a i l p - christoffel g gi a l i p)))
      = -(1 / 2) * (∑ a, g p a j * christoffel g gi a i l p)
        - (1 / 2) * ∑ a, g p a j * christoffel g gi a l i p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hS3 : (∑ b, g p i b * ((1 / 2) * (-christoffel g gi b j l p - christoffel g gi b l j p)))
      = -(1 / 2) * (∑ b, g p b i * christoffel g gi b j l p)
        - (1 / 2) * ∑ b, g p b i * christoffel g gi b l j p := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by rw [hsymm p i b]; ring
  rw [hS2, hS3,
    christoffel_lower g gi hsymm p hinv j i l, christoffel_lower g gi hsymm p hinv j l i,
    christoffel_lower g gi hsymm p hinv i j l, christoffel_lower g gi hsymm p hinv i l j]
  -- Identify partials via metric symmetry, then cancel.
  rw [show (fun y => g y j i) = (fun y => g y i j) from funext fun y => hsymm y j i,
    show (fun y => g y l i) = (fun y => g y i l) from funext fun y => hsymm y l i,
    show (fun y => g y l j) = (fun y => g y j l) from funext fun y => hsymm y l j]
  ring

/-- **`Γ̃(0) = 0` (the Christoffel symbols of `g̃` vanish at the centre).**  Immediate from
    `∂g̃(0) = 0`: every Christoffel symbol is an algebraic combination of first partials of the metric,
    all of which vanish at the origin of exp-normal coordinates.  Holds for ANY choice of inverse
    metric `gtildeInv` (the pullback's inverse), since the vanishing is entirely in the `∂g̃` factors. -/
theorem christoffel_expPullbackMetric_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (gtildeInv : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (μ ν ρ : Fin n) :
    christoffel (expPullbackMetric g gi hC p) gtildeInv μ ν ρ 0 = 0 := by
  simp only [christoffel]
  have hz : ∀ α : Fin n, gtildeInv 0 μ α
      * (pd (fun y => expPullbackMetric g gi hC p y α ρ) ν 0
        + pd (fun y => expPullbackMetric g gi hC p y α ν) ρ 0
        - pd (fun y => expPullbackMetric g gi hC p y ν ρ) α 0) = 0 := by
    intro α
    rw [pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg α ρ ν,
      pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg α ν ρ,
      pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg ν ρ α]
    ring
  rw [Finset.sum_congr rfl (fun α _ => hz α), Finset.sum_const_zero, mul_zero]

/-!
### STEP 1 — the level-2 exp-Jacobian jet at `0` (the load-bearing second-order regularity fact)
-/

/-- **Step 1 (regularity core) — the exp-map second-derivative field is Fréchet-differentiable at `0`,
    with derivative the abstract Rung-3 third-jet operator `expJetD3 … 0 Φ`.**  This is the direct
    one-order-up mirror of `hasFDerivAt_fderiv_expMap_zero` (which handled `v ↦ D exp_p v`): here the
    map is `w ↦ D²exp_p w = fderiv (fun z => fderiv exp_p z) w`, the Jacobian OF the Jacobian.

    Proof: instantiate the Rung-3 second-derivative differentiability capstone
    `expMap_fderiv2_hasFDerivAt` at `v = 0`.  The propagator `Φ` and its ODE/continuity data are
    supplied by `hasFDerivAt_expMap` at `0` (`0` lies inside the exp-ball since `0 < expRho`); the
    required `fderiv`-identity `fderiv exp_p 0 = π ∘ (Φ 1) ∘ ι` is `hFD.fderiv`.  The resulting
    derivative is the (propagator-dependent) abstract third-jet operator `expJetD3 g gi hC p 0 Φ`.
    Since `HasFDerivAt` pins the derivative uniquely, ANY admissible `Φ` gives the same value
    `fderiv ℝ (fun w => fderiv² exp_p w) 0`.

    Identifying that abstract value with the EXPLICIT cubic `a₃ = −∂Γ + ΓΓ` model of
    `expMap_value_three_jet` — i.e. reading off `∂²_{lm}(D exp_p·e_i)_a(0)` in closed Christoffel
    form — is the remaining second-order step recorded in the RNC LEDGER (the deferred
    smooth-dependence frontier). -/
theorem hasFDerivAt_fderiv2_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∃ (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (h0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p)
      (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)),
      HasFDerivAt (fun w => fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) w)
        (expJetD3 g gi hC p 0 Φ h0 hΦcont) 0 := by
  have h0lt : ‖(0 : Point n)‖ < expRho g gi hC p := by
    rw [norm_zero]; exact expRho_pos g gi hC p
  obtain ⟨Φ, hΦ0, hΦd, hFD⟩ := hasFDerivAt_expMap g gi hC p 0 h0lt
  have hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦd t ht).continuousWithinAt
  exact ⟨Φ, h0lt.le, hΦcont,
    expMap_fderiv2_hasFDerivAt g gi hC p 0 Φ h0lt hΦ0 hΦcont hΦd hFD.fderiv⟩

/-- **Step 1 (differentiability corollary).**  The exp-map second-derivative field
    `w ↦ D²exp_p w = fderiv (fun z => fderiv exp_p z) w` is differentiable at `0`.  This is the
    genuinely reusable content of `hasFDerivAt_fderiv2_expMap_zero`: it is exactly what a twice-Leibniz
    expansion of `∂²g̃(0)` (Step 2) needs from the Jacobian factors (each factor twice-differentiable
    at `0`), independent of the still-abstract value `expJetD3 … 0`. -/
theorem differentiableAt_fderiv2_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    DifferentiableAt ℝ
      (fun w => fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) w) 0 := by
  obtain ⟨Φ, h0, hΦcont, hfd⟩ := hasFDerivAt_fderiv2_expMap_zero g gi hC p
  exact hfd.differentiableAt

/-!
### The `v = 0` TRIVIALIZATION (toward the explicit `expJetD3 … 0` value)

At `v = 0` the zero-initial-velocity geodesic tube collapses to the constant equilibrium `(p,0)`
throughout `[0,1]` (`expTube_zero`, from confinement `‖Y₀(t) − (p,0)‖ ≤ expConst·‖0‖ = 0`).  Hence the
geodesic-field Jacobian along the tube is the CONSTANT nilpotent linearization
`A₀ = fderiv (geodesicField g gi) (p,0) = linF` (`fderiv_geodesicField_expTube_zero`), which satisfies
`A₀² = 0` (`linF_comp_linF`) — so the first-variation propagator solves the constant-coefficient
homogeneous equation `Φ' = A₀∘Φ`, `Φ(0) = id`, whose solution is `Φ₀(t) = exp(t·A₀) = id + t·A₀`.
These are the load-bearing structural facts that turn `expJetD3 g gi hC p 0 Φ` into an EXPLICIT
constant-coefficient integral (see the remaining-goal note in the ledger).
-/

/-- **`v = 0` tube trivialization.**  The zero-initial-velocity geodesic tube is CONSTANT at the
    equilibrium `(p,0)` throughout `[0,1]`.  Immediate from `expTube_spec`'s confinement bound
    `‖expTube p 0 t − (p,0)‖ ≤ expConst·‖0‖ = 0`. -/
theorem expTube_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p 0 t = ((p, 0) : Point n × Point n) := by
  obtain ⟨-, -, hconf⟩ :=
    expTube_spec g gi hC p 0 (by rw [norm_zero]; exact (expRho_pos g gi hC p).le)
  intro t ht
  have h := hconf t ht
  rw [norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- **`A₀ = linF` is nilpotent of order 2.**  `linF (ξ,η) = (η,0)`, hence `linF∘linF (ξ,η) = (0,0)`.
    This is why the `v = 0` propagator is the finite polynomial `Φ₀(t) = exp(t·A₀) = id + t·A₀`
    (the constant-coefficient trivialization that makes `expJetD3 … 0` an explicit integral). -/
theorem linF_comp_linF : (linF (n := n)).comp linF = 0 := by
  refine ContinuousLinearMap.ext fun z => ?_
  simp [linF_apply]

/-- **`v = 0` field constant.**  Along the constant tube `Y₀(t) = (p,0)`, the geodesic-field Jacobian
    is the CONSTANT nilpotent linearization `A₀ = linF` at the equilibrium.  Combines `expTube_zero`
    with the strict-derivative computation `hasStrictFDerivAt_geodesicField` (`fderiv F (p,0) = linF`). -/
theorem fderiv_geodesicField_expTube_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      fderiv ℝ (geodesicField g gi) (expTube g gi hC p 0 t) = (linF : (Point n × Point n) →L[ℝ] _) := by
  intro t ht
  rw [expTube_zero g gi hC p t ht]
  exact (hasStrictFDerivAt_geodesicField g gi hC p).hasFDerivAt.fderiv

/-- **Small-context CLM affine-path derivative.**  The affine path `τ ↦ 1 + τ·L` through the
    operator algebra has the CONSTANT derivative `L`: the linear part `τ·L` differentiates to `L`
    (`HasDerivWithinAt.smul_const`, then `one_smul`), and the constant `1` drops
    (`HasDerivWithinAt.const_add`).  Kept abstract in `F` (tiny context) so the CLM
    `HasDerivWithinAt`/instance search runs bare. -/
theorem hasDerivWithinAt_id_add_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] F) (s : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun τ : ℝ => ContinuousLinearMap.id ℝ F + τ • L) L s t := by
  have h1 : HasDerivWithinAt (fun τ : ℝ => τ • L) L s t := by
    simpa using (hasDerivWithinAt_id t s).smul_const L
  simpa using h1.const_add (ContinuousLinearMap.id ℝ F)

/-- **Small-context operator-propagator uniqueness for a NILPOTENT constant coefficient.**  Any
    `Φ : ℝ → (F →L[ℝ] F)` solving the homogeneous operator ODE `Φ'(t) = L∘Φ(t)`, `Φ(0) = 1`, with a
    coefficient `L` that is nilpotent of order 2 (`L∘L = 0`), equals the finite polynomial
    `Φ(t) = 1 + t·L` on `[0,1]`.

    Proof.  The model `Ψ(t) = 1 + t·L` has derivative `L` (`hasDerivWithinAt_id_add_smul`) and solves
    the same ODE: `L∘Ψ(t) = L∘1 + t·(L∘L) = L` (nilpotency).  Hence `S = Φ − Ψ` has `S(0) = 0` and the
    homogeneous derivative `S'(t) = L∘S(t)`, so `‖S'(t)‖ ≤ ‖L‖·‖S(t)‖`; the homogeneous Grönwall
    (`gronwall_Icc01_all`, `ε = δ = 0`, closed by `gronwallBound_ε0_δ0`) forces `‖S t‖ ≤ 0`, i.e.
    `Φ = Ψ`.  Abstract in `F` (tiny context) — the CLM `whnf`/instance search runs bare, away from the
    heavy `Point n × Point n` capstone context. -/
theorem clm_propagator_nilpotent_unique {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] F) (hL : L.comp L = 0)
    (Φ : ℝ → (F →L[ℝ] F))
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ F)
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (L.comp (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ t = ContinuousLinearMap.id ℝ F + t • L := by
  set S : ℝ → (F →L[ℝ] F) :=
    fun s => Φ s - (ContinuousLinearMap.id ℝ F + s • L) with hSdef
  -- `L∘Ψ(t) = L` via nilpotency `L∘L = 0`.
  have hΨfield : ∀ t : ℝ, L.comp (ContinuousLinearMap.id ℝ F + t • L) = L := by
    intro t
    rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.comp_smul, hL, smul_zero, add_zero]
  have hS0 : S 0 = 0 := by
    simp only [hSdef, zero_smul, add_zero, hΦ0, sub_self]
  -- `S` solves the homogeneous ODE `S'(t) = L∘S(t)`.
  have hSderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt S (L.comp (S t)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hΨd : HasDerivWithinAt
        (fun s => ContinuousLinearMap.id ℝ F + s • L) L (Set.Icc (0 : ℝ) 1) t :=
      hasDerivWithinAt_id_add_smul L _ t
    have hsub := (hΦd t ht).sub hΨd
    have hval : L.comp (S t) = L.comp (Φ t) - L := by
      simp only [hSdef, ContinuousLinearMap.comp_sub, hΨfield]
    rw [hval]
    exact hsub
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖L.comp (S t)‖ ≤ ‖L‖ * ‖S t‖ + 0 := by
    intro t _
    have h := L.opNorm_comp_le (S t)
    linarith [h]
  have hgr := gronwall_Icc01_all S (fun t => L.comp (S t))
    0 ‖L‖ 0 hSderiv (by rw [hS0]; simp) hbound
  intro t ht
  have hle : ‖S t‖ ≤ 0 := by
    have := hgr t ht
    rwa [gronwallBound_ε0_δ0] at this
  have hSt : S t = 0 := norm_le_zero_iff.mp hle
  rw [hSdef] at hSt
  exact sub_eq_zero.mp hSt

set_option maxHeartbeats 800000 in
/-- **(a1) — the CLOSED first-variation propagator at `v = 0`.**  ANY fundamental solution `Φ` of
    the Jacobi operator ODE `Φ' = Ψ₀(t)(Φ) = DF(Y₀ t)∘Φ`, `Φ(0) = 1`, along the constant `v = 0`
    tube is the finite polynomial `Φ₀(t) = 1 + t·A₀`, with `A₀ = linF` the nilpotent
    (`A₀² = 0`) equilibrium linearization.  This is the operator-propagator uniqueness brick (a1)
    gating the closed-form `expJetD3 … 0`.

    Proof.  Along the `v = 0` tube the Jacobi coefficient is the CONSTANT nilpotent linearization
    `Ψ₀(t)(M) = DF(Y₀ t)∘M = linF∘M` (`fderiv_geodesicField_expTube_zero`, `expJetPsi_apply`), with
    `linF∘linF = 0` (`linF_comp_linF`); the abstract nilpotent operator-propagator uniqueness
    `clm_propagator_nilpotent_unique` then gives `Φ₀(t) = 1 + t·linF`. -/
theorem expFund_zero_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p 0 t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)) := by
  -- convert the ODE coefficient to the constant nilpotent `linF∘·`, then hand to the abstract brick.
  have hΦd' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ ((linF (n := n)).comp (Φ t)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have he : expJetPsi g gi hC p 0 t (Φ t) = (linF (n := n)).comp (Φ t) := by
      rw [expJetPsi_apply, fderiv_geodesicField_expTube_zero g gi hC p t ht]
    rw [← he]; exact hΦd t ht
  exact clm_propagator_nilpotent_unique linF linF_comp_linF Φ hΦ0 hΦd'

/-!
### RNC JET LEDGER (R3→κ) — what the exp-normal coordinates give for `g̃`, and the remaining wall

* **The RNC value / first-order / connection jets of `g̃` at `0` are now PROVED** (all axiom-clean,
  from Rung 3 `exp_p ∈ C³` + `g ∈ C^∞`, `g` symmetric, `gi` its inverse at `p`):
    - `expPullbackMetric_at_zero`  : `g̃(0)_{ij} = g(p)_{ij}`  (= `δ` in a `p`-orthonormal frame).
    - `pd_expPullbackMetric_at_zero` : `∂_l g̃_{ij}(0) = 0`  — RNC first-order flatness.
    - `christoffel_expPullbackMetric_zero` : `Γ̃^μ_{νρ}(0) = 0`.
  The load-bearing analytic input is `pd_jacobian_expMap_zero`
  (`∂_l (D exp_p·e_i)_a(0) = ½(−Γ^a_{il} − Γ^a_{li})`), obtained by upgrading the one-jet big-`O`
  `hasFDerivAt_expMap_jacobian_one_jet` to a genuine `HasFDerivAt` at `0`
  (`hasFDerivAt_fderiv_expMap_zero`) and reading off `expJetOneJetModel`; the metric side uses
  `christoffel_lower` (metric compatibility) + symmetry to make the Leibniz terms cancel identically.

* **STEP 1 LANDED (the level-2 regularity mirror) — `hasFDerivAt_fderiv2_expMap_zero` /
  `differentiableAt_fderiv2_expMap_zero`.**  The Jacobian-of-Jacobian field
  `w ↦ D²exp_p w = fderiv (fun z => fderiv exp_p z) w` is now proved Fréchet-differentiable at `0`
  (axiom-clean: `[propext, Classical.choice, Quot.sound]`), the direct one-order-up mirror of
  `hasFDerivAt_fderiv_expMap_zero`.  Its derivative is the abstract Rung-3 third-jet operator
  `expJetD3 g gi hC p 0 Φ` (from `expMap_fderiv2_hasFDerivAt` instantiated at `v = 0`, propagator `Φ`
  from `hasFDerivAt_expMap`; `HasFDerivAt` pins the value, so it is `Φ`-independent as
  `fderiv (fun w => D²exp_p w) 0`).  NOTE (correction to the earlier plan): `expMap_fderiv2_hasFDerivAt`
  is ALREADY a genuine `HasFDerivAt`, not a big-`O`; the anticipated "`‖v‖³ = o(‖v‖²)` little-o upgrade"
  is unnecessary (there is no explicit-model level-2 big-`O` analogue of
  `hasFDerivAt_expMap_jacobian_one_jet` in the tree, so the value comes out as the abstract `expJetD3`,
  not the closed `a₃` form).

* **THE REMAINING WALL — the EXPLICIT VALUE identification (the sole open second-order step).**
  Every downstream piece (`∂²g̃(0)`, then `∂_l christoffel g̃(0)`, then the `rncDΓ` match) needs
  `∂²_{lm}(D exp_p·e_i)_a(0)` in CLOSED Christoffel form.  Step 1 gives this second derivative
  ABSTRACTLY as `expJetD3 g gi hC p 0 Φ`; what is missing is the single identity
    **`expJetD3 g gi hC p 0 Φ  =  <the explicit cubic `a₃ = −∂Γ + ΓΓ` operator>`**
  (equivalently `fderiv (fun w => D²exp_p w) 0` in closed Christoffel form matching
  `a3rawArr`/`expMap_value_three_jet`).  This is NOT in the tree and is a genuine multi-lemma build:
  `expJetD3` at `0` unfolds through the propagator's THIRD variation (`expJet3ValG`/`expJet2Curve`/`expJetPi`),
  and grounding it in `a₃` requires either (a) evaluating that third-variation datum at `v = 0` in
  closed form, or (b) a Taylor-uniqueness route from the VALUE 3-jet `expMap_value_three_jet` (a
  `=o[𝓝 0] ‖v‖³` little-o, which does NOT differentiate for free) to `iteratedFDeriv ℝ 3 exp_p 0` via
  Mathlib's Taylor-coefficient uniqueness, then coordinate extraction + the `a3rawArr` symmetrization.

  PROGRESS on route (a) — the `v = 0` TRIVIALIZATION is now LANDED (axiom-clean
  `[propext, Classical.choice, Quot.sound]`): `expTube_zero` (the tube is CONSTANT `(p,0)` on `[0,1]`),
  `fderiv_geodesicField_expTube_zero` (the Jacobi coefficient is the CONSTANT `A₀ = linF`), and
  `linF_comp_linF` (`A₀² = 0`, so `Φ₀(t) = id + t·A₀`).  What still blocks route (a) — the EXACT
  remaining goal — is the explicit evaluation of the two NESTED constant-coefficient inhomogeneous ODEs
  at `t = 1`:
    (a1) IDENTIFY the propagator: prove `Φ₀ = fun t => id + t·A₀` for THE `Φ` supplied by
         `hasFDerivAt_expMap … 0` — needs an operator-ODE uniqueness lemma for `Φ' = A₀∘Φ`, `Φ(0)=id`
         (Mathlib/tree has vector-valued `expJet2Fund_unique`/`expJet3Fund_unique` but NO
         operator-propagator uniqueness lemma — this is the first missing brick);
    (a2) SOLVE the 2nd variation: with `A₀`, `Φ₀` fixed, `expJet2Curve` solves `Q' = A₀∘Q + rhs₂(t)`,
         `Q(0)=0`, where `rhs₂ = expJet2Rhs` is a fixed polynomial in `A₀, D²F(p,0), Φ₀`; its `t=1`
         value is `∫₀¹ exp((1−s)A₀)·rhs₂(s) ds` — an explicit finite integral since `exp(sA₀)=id+sA₀`;
    (a3) SOLVE the 3rd variation: `R' = A₀∘R + rhs₃(t)`, `R(0)=0` (`rhs₃ = expJet3Rhs` in
         `A₀, D²F, D³F(p,0), Φ₀` and the `expJet2Curve` outputs from (a2)); `R(1) = ∫₀¹ exp((1−s)A₀)·rhs₃(s) ds`;
    (a4) MATCH: `expJetPi (R(1))` (the `.1` block) against `a3rawArr`/`expMap_value_three_jet`.
  VERDICT on the wall: route (a) is now REACHABLE-with-machinery — the analytic obstruction has been
  reduced from an abstract 3rd Fréchet derivative to (a1)+(a2)+(a3), a finite chain of
  constant-coefficient linear-ODE integrations (all coefficients are the finite polynomial
  `id + s·A₀`, `A₀²=0`), PLUS the single genuinely-missing Mathlib-adjacent brick (a1)
  (operator-propagator ODE uniqueness / `duhamel`-form representation of a linear inhomogeneous ODE
  solution).  It is NOT a deep rung-4 obstruction; it is a bounded ODE-integration build gated on that
  Duhamel/uniqueness brick.  Once (a1)+(a2)+(a3) give the closed `expJetD3 … 0 Φ`, the rest is reachable ASSEMBLY:
    (ii) twice-Leibniz + chain-rule expansion of `pd² g̃(0)` into the `∂²g` (curvature-of-`g`),
         `∂g·∂J`, `g·∂²J` blocks (mirroring `pd_expPullback_summand_zero`), collapsing the `Pi.single`
         factors with `g(p)=δ`, `∂g̃(0)=0`, `pd_jacobian_expMap_zero`, and the new explicit `∂²J`;
    (iii) `∂_l christoffel g̃(0)` reduces (via `Γ̃(0)=0`, `g̃(0)=δ`, `∂g̃(0)=0`) to a linear combination
         of `∂²g̃(0)`, which the `christoffel`/`christoffel_lower` differentiation + `a3rawArr_contract_eq_a3`
         match to `rncDΓ (christoffel g gi ·p) (pd christoffel ·p)`.
  VERDICT: the analytic content remains `C²`/third-jet (no higher rung than Rung 3 needed); the open
  work is concentrated in the single explicit-value identity above.  This is the "cited smooth-dependence
  frontier" the campaign deferred — a WALL, not reachable assembly, until that identity is built; after it,
  Steps 2–3 are assembly.  Checkpoints landed: value + first-order + connection jets (`g̃(0)=δ`,
  `∂g̃(0)=0`, `Γ̃(0)=0`) PLUS the level-2 differentiability core (`hasFDerivAt_fderiv2_expMap_zero`).

### REGULARITY LEDGER (R3→κ) — recorded, not `sorry`

* **Proved here:** `g̃ ∈ ContDiffOn ℝ 2` on the exp-ball (`contDiffOn_expPullbackMetric`), from
  `exp_p ∈ C³` (Rung 3) `+` `g ∈ C^∞`.  This is sharp for the pullback construction: `fderiv exp_p`
  costs one order, so `C³ exp_p ⟹ C² g̃`; recovering `C³ g̃` would require `exp_p ∈ C⁴` (Rung 4).

* **What `heat_a1_of_gauge` (RNCExpansion) demands of its metric argument:** `hg`/`hgi` are stated as
  `ContDiff ℝ ⊤` — i.e. `C^∞`, GLOBALLY (`ContDiff`, not `ContDiffOn` on the ball).  Feeding `g̃` in
  therefore fails on TWO counts as stated: (a) order — `g̃` is `C²` not `C^∞`; (b) domain — `g̃`'s
  regularity is only `ContDiffOn` on `ball 0 (expRho)`, not global `ContDiff`.

* **What the ANALYTIC CONTENT of the `κ = 1/6` step actually needs (finite):**
  - `hgauge` (the symmetrized cyclic `∂Γ(0)` sum): `christoffel g̃` needs `pd g̃` (1st derivatives);
    `pd (christoffel g̃)` needs `pd² g̃` (2nd derivatives).  ⟹ needs `g̃ ∈ C²` at `0`.
  - `hκgeo` (the `√det g̃` 2-jet, `½ ∂_c∂_d √det g̃(0)`): needs `pd² g̃` (2nd derivatives).  ⟹ `C²`.
  So the genuine analytic demand is `g̃ ∈ C²` (second partials existing/continuous at `0`), which the
  proved regularity `contDiffOn_expPullbackMetric` MEETS.

* **VERDICT.**  `κ = 1/6` for `g̃` is reachable from **Rung 3** at the level of analytic content
  (C² suffices for the gauge and the `√det` 2-jet).  It is NOT reachable through
  `heat_a1_of_gauge` AS CURRENTLY STATED, because that theorem's `hg`/`hgi : ContDiff ℝ ⊤`
  over-demand `C^∞` and globality.  Two admissible closes, neither needing a higher exp-map rung:
    1. **Weaken `heat_a1_of_gauge`'s metric hypotheses** to finite `ContDiffOn ℝ 2` on a neighbourhood
       of `0` (its proof only touches `christoffel`, `pd christoffel` and the `√det` 2-jet at `0`,
       i.e. ≤ 2 derivatives — it does not consume `⊤`).  This is the load-bearing follow-up.
    2. Alternatively supply the gauge/`√det`-jet facts for `g̃` directly (bypassing the `ContDiff ⊤`
       interface), which again only needs `g̃ ∈ C²`.
  A higher rung (`exp_p ∈ C⁴`, Rung 4) is **NOT** required for `κ = 1/6`; it would only be needed if
  one insisted on routing `g̃` through the current `ContDiff ⊤` signature by literally producing a
  `C^∞` (or `C³`) pullback — an over-strong path.  The true blocker is the `⊤` in
  `heat_a1_of_gauge`, weakenable to finite `C²`.
-/

end QIQTH.PullbackMetric
