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

open QIQTH.Curvature QIQTH.ExpMap
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

* **THE REMAINING WALL — the full bridge `rncDΓ = pd(christoffel g̃)(0)` (`rnc_christoffel_linearJet`)
  is NOT closed here, and the residue is a genuine SECOND-ORDER computation, not mere assembly.**
  `christoffel g̃` consumes `pd g̃` (first partials); `pd (christoffel g̃)` therefore consumes `pd² g̃`
  (SECOND partials) of the pullback.  `pd² g̃(0)` is governed by the exp map's THIRD jet — the first
  derivative of the *Jacobian's* derivative at `0`, i.e. the RNC analogue of
  `hasFDerivAt_fderiv_expMap_zero` ONE LEVEL UP (a `HasFDerivAt` for `v ↦ D²exp_p v` at `0` whose model
  value is the `a₃` combination `−∂Γ + ΓΓ` of `expMap_value_three_jet`).  The needed second-order
  regularity witnesses EXIST (`expMap_fderiv2_hasFDerivAt`, `expMap_value_three_jet`,
  `a3rawArr_contract_eq_a3`, and the abstract gauge `exp_rncGaugeJet`/`rncGaugeJet`), but the bridge
  requires:  (i) a `HasFDerivAt (fun v => fderiv (fun z => fderiv exp_p z) v) L₂ 0` with `L₂`'s value
  matching the `a₃` model (the level-2 mirror of `hasFDerivAt_fderiv_expMap_zero`, from
  `expMap_fderiv2_hasFDerivAt` + a `‖v‖³ = o(‖v‖²)` little-o upgrade);  (ii) the twice-Leibniz +
  chain-rule expansion of `pd² g̃(0)` into `∂²g`, `∂g·∂J`, `g·∂²J` blocks;  (iii) matching the resulting
  contraction to `rncDΓ` via `a3rawArr_contract_eq_a3`.  This is the "cited smooth-dependence frontier"
  the campaign deferred — reachable in PRINCIPLE from Rung 3 (the analytic content is `C²`/third-jet, no
  higher rung needed), but it is a multi-lemma second-order build, NOT a one-brick assembly.  Landing
  `Γ̃(0)=0` is the natural checkpoint: the value + first-order + connection jets are done; the
  `∂Γ̃(0)` (curvature) jet is the open second-order step.

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
