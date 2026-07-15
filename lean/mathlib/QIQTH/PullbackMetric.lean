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
import QIQTH.GeodesicFieldJets

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

/-- **Small-context inhomogeneous Duhamel for a NILPOTENT constant coefficient.**  Any `X : ℝ → F`
    solving the inhomogeneous constant-coefficient vector ODE `X'(t) = A(X t) + f(t)`, `X(0) = 0`,
    with `A` nilpotent of order 2 (`A∘A = 0`) and `f` continuous on `[0,1]`, has the CLOSED endpoint
    value the variation-of-constants formula gives, with the finite propagator `exp((1−s)A) = 1 + (1−s)A`:
      `X 1 = ∫₀¹ (1 + (1−s)•A)(f s) ds`.

    Proof.  The candidate `Y(t) = (1 + t•A)(V t)`, `V(t) = ∫₀ᵗ (1 − s•A)(f s) ds`, solves the same IVP:
    `V' = (1 − t•A)(f t)` (FTC), so by the CLM-application product rule `HasDerivWithinAt.clm_apply`
    (with the affine-path derivative `hasDerivWithinAt_id_add_smul`),
    `Y' = A(V t) + (1 + t•A)((1 − t•A)(f t)) = A(V t) + f t = A(Y t) + f t` — both simplifications use
    `A∘A = 0` — and `Y 0 = 0`.  The homogeneous vector Grönwall `gronwall_vec_residual_Icc`
    (`ρ = 0`, `K = ‖A‖`) forces `X = Y` on `[0,1]`; then `Y 1 = (1 + A)(∫₀¹(1 − s•A)(f s)ds)`, and pulling
    the CLM `1 + A` inside the integral (`ContinuousLinearMap.intervalIntegral_comp_comm`) collapses
    `(1 + A)(1 − s•A) = 1 + (1−s)•A` (again `A∘A = 0`).  Abstract in `F` (tiny context), the exact
    inhomogeneous mirror of `clm_propagator_nilpotent_unique`. -/
theorem clm_duhamel_nilpotent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] F) (hA : A.comp A = 0)
    (f : ℝ → F) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (X : ℝ → F) (hX0 : X 0 = 0)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt X (A (X t) + f t) (Set.Icc (0 : ℝ) 1) t) :
    X 1 = ∫ s in (0 : ℝ)..1, (ContinuousLinearMap.id ℝ F + (1 - s) • A) (f s) := by
  -- nilpotency in applied form.
  have hAA : ∀ x : F, A (A x) = 0 := fun x => by
    have := ContinuousLinearMap.ext_iff.mp hA x; simpa using this
  -- the integrand `gg s = (1 − s•A)(f s)` and its continuity on `[0,1]`.
  set gg : ℝ → F := fun s => (ContinuousLinearMap.id ℝ F - s • A) (f s) with hgg
  have hCfield : ContinuousOn (fun s : ℝ => ContinuousLinearMap.id ℝ F - s • A)
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.sub ((continuous_id.smul continuous_const).continuousOn)
  have hggc : ContinuousOn gg (Set.Icc (0 : ℝ) 1) := hCfield.clm_apply hf
  set V : ℝ → F := fun t => ∫ s in (0 : ℝ)..t, gg s with hVdef
  set Y : ℝ → F := fun t => (ContinuousLinearMap.id ℝ F + t • A) (V t) with hYdef
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hY0 : Y 0 = 0 := by simp [hYdef, hV0]
  -- FTC: `V' t = gg t`.
  have hVd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt V (gg t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hII : IntervalIntegrable gg MeasureTheory.volume 0 t :=
      (hggc.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    haveI : Fact (t ∈ Set.Icc (0 : ℝ) 1) := ⟨ht⟩
    have hmeas := hggc.stronglyMeasurableAtFilter_nhdsWithin (μ := MeasureTheory.volume)
      measurableSet_Icc t
    exact intervalIntegral.integral_hasDerivWithinAt_right hII hmeas (hggc t ht)
  -- `Y` solves the same IVP `Y' = A(Y) + f`, `Y 0 = 0`.
  have hYd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Y (A (Y t) + f t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hc : HasDerivWithinAt (fun τ : ℝ => ContinuousLinearMap.id ℝ F + τ • A) A
        (Set.Icc (0 : ℝ) 1) t := hasDerivWithinAt_id_add_smul A _ t
    have hclm := hc.clm_apply (hVd t ht)
    have hfterm : (ContinuousLinearMap.id ℝ F + t • A) (gg t) = f t := by
      simp only [hgg, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul,
        hAA (f t), smul_zero]
      abel
    have hAY : A (Y t) = A (V t) := by
      simp only [hYdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smul_apply, map_add, map_smul, hAA (V t), smul_zero, add_zero]
    have heq : A (V t) + (ContinuousLinearMap.id ℝ F + t • A) (gg t) = A (Y t) + f t := by
      rw [hfterm, hAY]
    rw [heq] at hclm; exact hclm
  -- Grönwall uniqueness `X = Y` on `[0,1]`.
  have huniq := gronwall_vec_residual_Icc
    (fun t => X t - Y t) (fun _ => (0 : F)) (fun _ => A) ‖A‖ 0 (norm_nonneg _) le_rfl
    (by simp only [hX0, hY0, sub_zero])
    (fun t ht => by
      have hd := (hXd t ht).sub (hYd t ht)
      have hval : (A (X t) + f t) - (A (Y t) + f t) = A (X t - Y t) + 0 := by
        rw [map_sub]; abel
      rwa [hval] at hd)
    (fun _ _ => le_refl _) (fun _ _ => by simp)
  have hXeqY : X 1 = Y 1 := by
    have h0 : ‖X 1 - Y 1‖ ≤ 0 := by
      simpa using huniq 1 (by norm_num [Set.mem_Icc])
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- evaluate `Y 1`.
  rw [hXeqY]
  have hII1 : IntervalIntegrable gg MeasureTheory.volume 0 1 :=
    hggc.intervalIntegrable_of_Icc (by norm_num)
  have hpt : ∀ s : ℝ, (ContinuousLinearMap.id ℝ F + (1 : ℝ) • A) (gg s)
      = (ContinuousLinearMap.id ℝ F + (1 - s) • A) (f s) := by
    intro s
    simp only [hgg, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul,
      hAA (f s), one_smul, sub_smul]
    abel
  simp only [hYdef, hVdef]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hII1]
  exact intervalIntegral.integral_congr (fun s _ => hpt s)

/-- **Small-context general-`t` Duhamel for a NILPOTENT constant coefficient and CONSTANT source.**
    Any `X : ℝ → F` solving the inhomogeneous constant-coefficient vector ODE `X'(t) = A(X t) + b`,
    `X(0) = 0`, with `A` nilpotent of order 2 (`A∘A = 0`) and a CONSTANT source `b`, is the explicit
    quadratic polynomial `X t = t•b + (t²/2)•(A b)` on `[0,1]`.

    Proof.  The model `Y(t) = t•b + (t²/2)•(A b)` solves the same IVP: `Y'(t) = b + t•(A b)` and
    `A(Y t) = t•(A b)` (nilpotency `A(A b)=0`), so `Y'(t) = A(Y t) + b` and `Y 0 = 0`.  The homogeneous
    vector Grönwall `gronwall_vec_residual_Icc` (`ρ = 0`, `K = ‖A‖`) forces `X = Y` on `[0,1]`.  This is
    the general-`t` (variable-endpoint), constant-source specialisation of `clm_duhamel_nilpotent`,
    needed to solve the `v = 0` second-variation curve `Q_·· t` for ALL `t ∈ [0,1]` (the integrand of
    (a3), not merely its endpoint). -/
theorem vec_ode_nilpotent_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : F →L[ℝ] F) (hA : A.comp A = 0) (b : F)
    (X : ℝ → F) (hX0 : X 0 = 0)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt X (A (X t) + b) (Set.Icc (0 : ℝ) 1) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, X t = t • b + (t ^ 2 / 2) • (A b) := by
  have hAA : ∀ x : F, A (A x) = 0 := fun x => by
    have := ContinuousLinearMap.ext_iff.mp hA x; simpa using this
  set Y : ℝ → F := fun t => t • b + (t ^ 2 / 2) • (A b) with hYdef
  have hY0 : Y 0 = 0 := by simp [hYdef]
  have hYd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Y (A (Y t) + b) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have ht1 : HasDerivWithinAt (fun τ : ℝ => τ • b) b (Set.Icc (0 : ℝ) 1) t := by
      simpa using (hasDerivWithinAt_id t (Set.Icc (0 : ℝ) 1)).smul_const b
    have hsq : HasDerivWithinAt (fun τ : ℝ => τ ^ 2 / 2) t (Set.Icc (0 : ℝ) 1) t := by
      have h := ((hasDerivAt_pow 2 t).hasDerivWithinAt (s := Set.Icc (0 : ℝ) 1)).div_const 2
      convert h using 1
      norm_num
    have ht2 : HasDerivWithinAt (fun τ : ℝ => (τ ^ 2 / 2) • (A b)) (t • (A b))
        (Set.Icc (0 : ℝ) 1) t := by
      simpa using hsq.smul_const (A b)
    have hYd0 : HasDerivWithinAt Y (b + t • (A b)) (Set.Icc (0 : ℝ) 1) t := ht1.add ht2
    have hAY : A (Y t) + b = b + t • (A b) := by
      simp only [hYdef, map_add, map_smul, hAA b, smul_zero, add_zero]
      abel
    rw [hAY]; exact hYd0
  have huniq := gronwall_vec_residual_Icc
    (fun t => X t - Y t) (fun _ => (0 : F)) (fun _ => A) ‖A‖ 0 (norm_nonneg _) le_rfl
    (by simp only [hX0, hY0, sub_zero])
    (fun t ht => by
      have hd := (hXd t ht).sub (hYd t ht)
      have hval : (A (X t) + b) - (A (Y t) + b) = A (X t - Y t) + 0 := by rw [map_sub]; abel
      rwa [hval] at hd)
    (fun _ _ => le_refl _) (fun _ _ => by simp)
  intro t ht
  have h0 : ‖X t - Y t‖ ≤ 0 := by simpa using huniq t ht
  have hXY := sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  rw [hXY]

/-- **The first variation `Φ₀ t (ι m) = (t•m, m)` at `v = 0`.**  For the affine propagator
    `Φ t = id + t•linF` (the `v = 0` fundamental solution, `expFund_zero_eq`), the first-variation
    vector is `Φ t (ι m) = (id + t•linF)(0,m) = (0,m) + t•(m,0) = (t•m, m)` (since `linF(0,m)=(m,0)`). -/
theorem expFundZero_iota
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (m : Point n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Φ t (expJetIota m) = ((t • m, m) : Point n × Point n) := by
  rw [hΦeq t ht]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, expJetIota_apply, linF_apply, Prod.smul_mk, smul_zero,
    Prod.mk_add_mk, zero_add, add_zero]

/-- **The `v = 0` second-variation SOURCE is the CONSTANT `(0, c_{kl})`.**  Along the constant tube
    `Y₀ t = (p,0)`, the Jet₂ source `Θ^{kl}(t) = D²F(p,0)(Φ t (ι k))(Φ t (ι l))` is `t`-independent:
    `D²F(p,0)` depends only on the velocity slots (`Δu = k`, `η = l`), so with `Φ t (ι·) = (t•·, ·)`
    (`expFundZero_iota`) and `fderiv2_geodesicField_apply_zero`,
    `Θ^{kl}(t) = (0, a ↦ −∑_{jm} Γ^a_{jm}(p)(l_j k_m + k_j l_m))`. -/
theorem expJet2Rhs_zero_const (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (k l : Point n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expJet2Rhs g gi hC p 0 Φ k l t
      = ((0 : Point n),
          fun a => -∑ j, ∑ m, christoffel g gi a j m p * (l j * k m + k j * l m)) := by
  rw [expJet2Rhs_apply, expTube_zero g gi hC p t ht,
      expFundZero_iota Φ hΦeq k t ht, expFundZero_iota Φ hΦeq l t ht,
      fderiv2_geodesicField_apply_zero g gi hC p (t • k) k (t • l) l]

/-- **The `v = 0` second-variation curve VELOCITY component is linear-in-`t`.**  With the constant
    source `(0, c_{kl})` (`expJet2Rhs_zero_const`) and the nilpotent coefficient `linF` along the
    constant tube (`fderiv_geodesicField_expTube_zero`), the second-variation curve solves
    `Q' = linF(Q) + (0,c_{kl})`, `Q(0)=0`; the constant-source nilpotent Duhamel `vec_ode_nilpotent_const`
    gives `Q t = t•(0,c_{kl}) + (t²/2)•(c_{kl},0)`, whose velocity component is `(Q t).2 = t•c_{kl}`. -/
theorem expJet2Curve_zero_velocity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (k l : Point n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l t).2
      = t • (fun a => -∑ j, ∑ m,
          christoffel g gi a j m p * (l j * k m + k j * l m) : Point n) := by
  obtain ⟨hQ0, -, -, hQderiv⟩ := (expJet2Fund g gi hC p 0 Φ hv0 hΦcont k l).choose_spec
  have hXd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (expJet2Fund g gi hC p 0 Φ hv0 hΦcont k l).choose
        ((linF (n := n)) ((expJet2Fund g gi hC p 0 Φ hv0 hΦcont k l).choose s)
          + ((0 : Point n),
              fun a => -∑ j, ∑ m, christoffel g gi a j m p * (l j * k m + k j * l m)))
        (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have hd := hQderiv s hs
    rw [fderiv_geodesicField_expTube_zero g gi hC p s hs,
        expJet2Rhs_zero_const g gi hC p Φ hΦeq k l s hs] at hd
    exact hd
  have hval := vec_ode_nilpotent_const (linF (n := n)) linF_comp_linF
    ((0 : Point n), fun a => -∑ j, ∑ m, christoffel g gi a j m p * (l j * k m + k j * l m))
    (expJet2Fund g gi hC p 0 Φ hv0 hΦcont k l).choose hQ0 hXd t ht
  simp only [expJet2Curve]
  rw [hval]
  simp only [linF_apply, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]

/-- **(a2) — the CLOSED second-variation value at `v = 0`.**  The genuine second-variation curve
    `Q^{hk}_0` (the `expJet2Curve` witness at `v = 0`) has the explicit endpoint value given by the
    nilpotent Duhamel formula: along the constant `v = 0` tube the Jacobi coefficient is the CONSTANT
    nilpotent `A₀ = linF` (`fderiv_geodesicField_expTube_zero`, `linF_comp_linF`), and the source is
    the fixed `expJet2Rhs`; hence `clm_duhamel_nilpotent` gives
      `Q^{hk}_0(1) = ∫₀¹ (1 + (1−s)•linF)(expJet2Rhs … 0 Φ h k s) ds`. -/
theorem expJet2Curve_zero_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k : Point n) :
    expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k 1
      = ∫ s in (0 : ℝ)..1,
          (ContinuousLinearMap.id ℝ (Point n × Point n) + (1 - s) • (linF (n := n)))
            (expJet2Rhs g gi hC p 0 Φ h k s) := by
  obtain ⟨hQ0, -, -, hQderiv⟩ := (expJet2Fund g gi hC p 0 Φ hv0 hΦcont h k).choose_spec
  have hXd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (expJet2Fund g gi hC p 0 Φ hv0 hΦcont h k).choose
        ((linF (n := n)) ((expJet2Fund g gi hC p 0 Φ hv0 hΦcont h k).choose t)
          + expJet2Rhs g gi hC p 0 Φ h k t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hd := hQderiv t ht
    rwa [fderiv_geodesicField_expTube_zero g gi hC p t ht] at hd
  have hf : ContinuousOn (fun s => expJet2Rhs g gi hC p 0 Φ h k s) (Set.Icc (0 : ℝ) 1) :=
    expJet2Rhs_continuousOn g gi hC p 0 hv0 Φ hΦcont h k
  have hdu := clm_duhamel_nilpotent (linF (n := n)) linF_comp_linF
    (fun s => expJet2Rhs g gi hC p 0 Φ h k s) hf
    (expJet2Fund g gi hC p 0 Φ hv0 hΦcont h k).choose hQ0 hXd
  simpa only [expJet2Curve] using hdu

/-- **(a3) — the CLOSED third-variation value at `v = 0`.**  The genuine third-variation datum
    `R^{hkl}_0(1) = expJet3ValG … 0` (the `expJet3Val` witness with the genuine second-variation curves
    `expJet2Curve` in the `Q··` slots) has the explicit endpoint value from the same nilpotent Duhamel:
    at `v = 0` the Jacobi coefficient is `A₀ = linF` and the source is the fixed `expJet3Rhs`, so
      `R^{hkl}_0(1) = ∫₀¹ (1 + (1−s)•linF)(expJet3Rhs … 0 Φ Q_kl Q_hl Q_hk h k l s) ds`,
    with `Q_·· = expJet2Curve …` the (themselves closed, by (a2)) genuine second-variation curves. -/
theorem expJet3ValG_zero_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l : Point n) :
    expJet3ValG g gi hC p 0 Φ hv0 hΦcont h k l
      = ∫ s in (0 : ℝ)..1,
          (ContinuousLinearMap.id ℝ (Point n × Point n) + (1 - s) • (linF (n := n)))
            (expJet3Rhs g gi hC p 0 Φ
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s) := by
  obtain ⟨hR0, -, -, hRderiv⟩ :=
    (expJet3Fund g gi hC p 0 Φ
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) hv0 hΦcont
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h k) h k l).choose_spec
  have hXd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt
        (expJet3Fund g gi hC p 0 Φ
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) hv0 hΦcont
          (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont k l)
          (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h l)
          (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h k) h k l).choose
        ((linF (n := n))
            ((expJet3Fund g gi hC p 0 Φ
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) hv0 hΦcont
              (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h k) h k l).choose t)
          + expJet3Rhs g gi hC p 0 Φ
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l t) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hd := hRderiv t ht
    rwa [fderiv_geodesicField_expTube_zero g gi hC p t ht] at hd
  have hf : ContinuousOn
      (fun s => expJet3Rhs g gi hC p 0 Φ
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s) (Set.Icc (0 : ℝ) 1) :=
    expJet3Rhs_continuousOn g gi hC p 0 hv0 Φ
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) hΦcont
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h k) h k l
  have hdu := clm_duhamel_nilpotent (linF (n := n)) linF_comp_linF _ hf _ hR0 hXd
  simpa only [expJet3ValG, expJet3Val] using hdu

/-- **`π ∘ (id + c·A₀)` pointwise, `A₀ = linF`.**  Since `linF (x,u) = (u,0)`, the affine propagator
    `(id + c•linF)` maps `w ↦ (w.1 + c•w.2, w.2)`, whose position projection is `w.1 + c•w.2`. -/
theorem expJetPi_id_add_smul_linF (c : ℝ) (w : Point n × Point n) :
    expJetPi ((ContinuousLinearMap.id ℝ (Point n × Point n) + c • (linF (n := n))) w)
      = w.1 + c • w.2 := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, linF_apply, expJetPi_apply, Prod.fst_add, Prod.smul_fst]

/-- **(a4, reduction step) — the CLOSED SCALAR-INTEGRAL form of `expJetD3 … 0`.**  Applying the
    position projection `π = expJetPi` to the nilpotent-Duhamel integral (a3) `expJet3ValG_zero_eq` and
    commuting `π` through the interval integral (`intervalIntegral_comp_comm`, the integrand continuous
    on `[0,1]` via `expJet3Rhs_continuousOn`/`expJet2Curve_continuousOn`) collapses the operator third
    jet to the explicit `Point n`-valued integral
      `expJetD3 … 0 Φ l k h = ∫₀¹ [ (Θ₃ s).1 + (1−s)•(Θ₃ s).2 ] ds`,
    `Θ₃ s = expJet3Rhs … 0 Φ Q_kl Q_hl Q_hk h k l s` (genuine second-variation curves `Q_·· =
    expJet2Curve …`).  This is the reduction half of (a4a): the remaining work is the closed
    Christoffel evaluation of `(Θ₃ s).1`, `(Θ₃ s).2` (via `fderiv{2,3}_geodesicField_apply_zero`) plus
    the polynomial-in-`s` integral. -/
theorem expJetD3_zero_integral (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (h k l : Point n) :
    expJetD3 g gi hC p 0 Φ hv0 hΦcont l k h
      = ∫ s in (0 : ℝ)..1,
          ((expJet3Rhs g gi hC p 0 Φ
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s).1
            + (1 - s) • (expJet3Rhs g gi hC p 0 Φ
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
              (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s).2) := by
  rw [expJetD3_apply, expJet3ValG_zero_eq g gi hC p Φ hv0 hΦcont h k l]
  -- continuity of the Duhamel integrand on `[0,1]`.
  have hRhs : ContinuousOn (fun s => expJet3Rhs g gi hC p 0 Φ
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s) (Set.Icc (0 : ℝ) 1) :=
    expJet3Rhs_continuousOn g gi hC p 0 hv0 Φ
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) hΦcont
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p 0 Φ hv0 hΦcont h k) h k l
  have hField : ContinuousOn
      (fun s : ℝ => ContinuousLinearMap.id ℝ (Point n × Point n) + (1 - s) • (linF (n := n)))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.add ((continuousOn_const.sub continuousOn_id).smul continuousOn_const)
  have hII : IntervalIntegrable (fun s => (ContinuousLinearMap.id ℝ (Point n × Point n)
      + (1 - s) • (linF (n := n))) (expJet3Rhs g gi hC p 0 Φ
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s))
      MeasureTheory.volume 0 1 :=
    (hField.clm_apply hRhs).intervalIntegrable_of_Icc (by norm_num)
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm expJetPi hII]
  exact intervalIntegral.integral_congr (fun s _ => expJetPi_id_add_smul_linF _ _)

/-- **The `∂Γ` (`D³F`) block of the closed RNC third-jet value** (up-index `i`, direction triple
    `h,k,l`).  This is the `−∂Γ`-type trilinear form the `D³F(p,0)` term contributes. -/
noncomputable def rncD3Block (g gi : Point n → Fin n → Fin n → ℝ) (p h k l : Point n) : Point n :=
  fun i => -∑ j, ∑ m,
    ((∑ r, pd (fun z => christoffel g gi i j m z) r p * l r) * (h j * k m + k j * h m)
      + (∑ r, pd (fun z => christoffel g gi i j m z) r p * h r) * (l j * k m + k j * l m)
      + (∑ r, pd (fun z => christoffel g gi i j m z) r p * k r) * (l j * h m + h j * l m))

/-- **The `ΓΓ` (`D²F` cross) block of the closed RNC third-jet value.**  For differentiation direction
    `dir` and second-variation source-directions `(sk, sl)`, this is the `ΓΓ`-type form the `D²F(p,0)`
    cross-term contributes (the inner `−∑ Γ(sl·sk + sk·sl)` is the second-variation velocity coefficient
    `c` from `expJet2Curve_zero_velocity`). -/
noncomputable def rncCrossBlock (g gi : Point n → Fin n → Fin n → ℝ) (p dir sk sl : Point n) :
    Point n :=
  fun i => -∑ j, ∑ m, christoffel g gi i j m p
    * ((-∑ j', ∑ m', christoffel g gi j j' m' p * (sl j' * sk m' + sk j' * sl m')) * dir m
       + dir j * (-∑ j', ∑ m', christoffel g gi m j' m' p * (sl j' * sk m' + sk j' * sl m')))

/-- **Pull a scalar out of a weighted finite sum.**  `∑ r, c_r·(s·v_r) = s·∑ r, c_r·v_r`. -/
theorem sum_mul_smul_factor (c v : Fin n → ℝ) (s : ℝ) :
    (∑ r, c r * (s * v r)) = s * ∑ r, c r * v r := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring

set_option maxHeartbeats 1600000 in
/-- **(a4a, pointwise) — the CLOSED Christoffel value of the third-jet integrand `Θ₃ s` at `v = 0`.**
    For the affine propagator `Φ t = id + t•linF` (hypothesis `hΦeq`, supplied by `expFund_zero_eq`)
    and `s ∈ [0,1]`, every one of the four terms of `expJet3Rhs` has vanishing POSITION component and a
    velocity component LINEAR in `s`:
      `Θ₃ s = (0, s • (rncD3Block + rncCrossBlock_h + rncCrossBlock_k + rncCrossBlock_l))`.
    The `D³F(p,0)` term gives `s•rncD3Block` (each first variation `Φ s (ι·) = (s•·, ·)` carries one
    `s` in its position slot, which `D³F(p,0)`'s `∂Γ·ξ` factor turns into the overall `s`); each `D²F`
    cross-term gives `s•rncCrossBlock` (the second-variation velocity `(Q s).2 = s•c` of
    `expJet2Curve_zero_velocity`).  All position components vanish because `D²F(p,0)`/`D³F(p,0)` are
    velocity-valued at the equilibrium. -/
theorem expJet3Rhs_zero_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (h k l : Point n) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    expJet3Rhs g gi hC p 0 Φ
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
        (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s
      = ((0 : Point n), s • (rncD3Block g gi p h k l + rncCrossBlock g gi p h k l
          + rncCrossBlock g gi p k h l + rncCrossBlock g gi p l h k)) := by
  -- the `D³F` term.
  have ht1 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p 0 s))
        (Φ s (expJetIota h)) (Φ s (expJetIota k)) (Φ s (expJetIota l))
      = ((0 : Point n), s • rncD3Block g gi p h k l) := by
    rw [expTube_zero g gi hC p s hs, expFundZero_iota Φ hΦeq h s hs,
        expFundZero_iota Φ hΦeq k s hs, expFundZero_iota Φ hΦeq l s hs,
        fderiv3_geodesicField_apply_zero g gi hC p (s • h) h (s • k) k (s • l) l]
    refine Prod.ext rfl ?_
    funext i
    simp only [rncD3Block, Pi.smul_apply, smul_eq_mul]
    rw [mul_neg, neg_inj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [sum_mul_smul_factor]
    ring
  -- the three `D²F` cross-terms (differentiation direction `dir`, source directions `(sk,sl)`).
  have hcross : ∀ (dir sk sl : Point n),
      (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p 0 s))
          (Φ s (expJetIota dir))
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s)
        = ((0 : Point n), s • rncCrossBlock g gi p dir sk sl) := by
    intro dir sk sl
    rw [expTube_zero g gi hC p s hs, expFundZero_iota Φ hΦeq dir s hs,
        show (expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s)
            = (((expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s).1,
                (expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s).2) : Point n × Point n) from rfl,
        fderiv2_geodesicField_apply_zero g gi hC p (s • dir) dir
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s).1
          (expJet2Curve g gi hC p 0 Φ hv0 hΦcont sk sl s).2,
        expJet2Curve_zero_velocity g gi hC p Φ hv0 hΦcont hΦeq sk sl s hs]
    refine Prod.ext rfl ?_
    funext i
    simp only [rncCrossBlock, Pi.smul_apply, smul_eq_mul]
    rw [mul_neg, neg_inj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [expJet3Rhs_apply, ht1, hcross h k l, hcross k h l, hcross l h k]
  refine Prod.ext (by simp) ?_
  simp only [Prod.snd_add, Prod.mk_add_mk, smul_add, add_zero]

set_option maxHeartbeats 1600000 in
/-- **(a4a) — THE CLOSED THIRD-JET VALUE of `exp_p` at `v = 0`.**  Composing the reduction
    `expJetD3_zero_integral` with the closed integrand `expJet3Rhs_zero_eq` and the elementary integral
    `∫₀¹ (1−s)·s ds = 1/6`, the abstract Rung-3 third-jet operator collapses to the explicit rational
    Christoffel combination
      `expJetD3 … 0 Φ l k h = (1/6)·(rncD3Block + rncCrossBlock_h + rncCrossBlock_k + rncCrossBlock_l)`.
    This is the closed `−∂Γ + ΓΓ` value (up to the `a₃`-symmetrization bookkeeping): the `1/6` is
    exactly the RNC cubic coefficient, matching `expMap_value_three_jet`. -/
theorem expJetD3_zero_closed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (h k l : Point n) :
    expJetD3 g gi hC p 0 Φ hv0 hΦcont l k h
      = (1 / 6 : ℝ) • (rncD3Block g gi p h k l + rncCrossBlock g gi p h k l
          + rncCrossBlock g gi p k h l + rncCrossBlock g gi p l h k) := by
  rw [expJetD3_zero_integral g gi hC p Φ hv0 hΦcont h k l]
  have hpt : Set.EqOn
      (fun s => ((expJet3Rhs g gi hC p 0 Φ
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s).1
          + (1 - s) • (expJet3Rhs g gi hC p 0 Φ
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont k l)
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h l)
            (expJet2Curve g gi hC p 0 Φ hv0 hΦcont h k) h k l s).2))
      (fun s => ((1 - s) * s) • (rncD3Block g gi p h k l + rncCrossBlock g gi p h k l
          + rncCrossBlock g gi p k h l + rncCrossBlock g gi p l h k))
      (Set.uIcc (0 : ℝ) 1) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    simp only [expJet3Rhs_zero_eq g gi hC p Φ hv0 hΦcont hΦeq h k l s hs', zero_add, smul_smul]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_smul_const]
  have hint : (∫ s in (0 : ℝ)..1, (1 - s) * s) = 1 / 6 := by
    have e : (fun s : ℝ => (1 - s) * s) = fun s => s ^ 1 - s ^ 2 := by funext s; ring
    rw [e, intervalIntegral.integral_sub
        ((continuous_pow 1).intervalIntegrable 0 1) ((continuous_pow 2).intervalIntegrable 0 1),
      integral_pow, integral_pow]
    norm_num
  rw [hint]

set_option maxHeartbeats 1600000 in
/-- **(a4b) — THE DIAGONAL `a₃` MATCH: the closed third jet grounds the exp-map value 3-jet.**  On the
    diagonal `l = k = h = v`, the closed third-jet operator value `expJetD3 … 0 Φ v v v` equals EXACTLY
    the honest cubic coefficient `a₃(v)` of `expMap_value_three_jet` (the `(1/6)•…` term):
      `expJetD3 … 0 v v v = −∑ ∂Γ·v³ + ∑ Γ(Γv²)v + ∑ Γ v(Γv²)`.
    Structurally: the `1/6` cancels the combinatorial `6` of the fully-symmetric `∂Γ` diagonal (three
    identical `D³F` brackets, each with a doubled `v_j v_m`), and the `1/6·3·2` of the three identical
    `D²F` cross-terms (each carrying the doubled second-variation source `∑Γ(v²+v²)=2∑Γv²`) yields the
    two `ΓΓ` blocks.  Composed with `a3rawArr_contract_eq_a3` (RNCGaugeExp) this is the third-jet =
    `a3rawArr`-contraction identity the R3→κ ledger needs. -/
theorem expJetD3_zero_diagonal (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv0 : ‖(0 : Point n)‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦeq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Φ t = ContinuousLinearMap.id ℝ (Point n × Point n) + t • (linF (n := n)))
    (v : Point n) (i : Fin n) :
    expJetD3 g gi hC p 0 Φ hv0 hΦcont v v v i
      = -(∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * (∑ a, ∑ b, christoffel g gi j a b p * v a * v b) * v k)
        + (∑ j, ∑ k, christoffel g gi i j k p
              * v j * (∑ a, ∑ b, christoffel g gi k a b p * v a * v b)) := by
  -- abbreviate the inner `Γv²` contraction so scalar-distribution never mis-targets it.
  set S : Fin n → ℝ := fun x => ∑ a, ∑ b, christoffel g gi x a b p * v a * v b with hSdef
  -- the doubled second-variation source: `∑ Γ (v²+v²) = 2·(∑ Γ v²) = 2·S x`.
  have hinner : ∀ x : Fin n,
      (∑ j', ∑ m', christoffel g gi x j' m' p * (v j' * v m' + v j' * v m')) = 2 * S x := by
    intro x
    simp only [hSdef]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  -- the `D³F` (`∂Γ`) block reduces to `−6·∑∂Γ v³`.
  have hD3 : rncD3Block g gi p v v v i
      = -6 * (∑ j, ∑ k, ∑ l, pd (fun z => christoffel g gi i j k z) l p * v j * v k * v l) := by
    simp only [rncD3Block]
    rw [neg_mul, neg_inj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finset.sum_mul]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  -- the RHS `ΓΓ`-blocks, rewritten as a single double sum (with `S` an opaque atom).
  have key : (2 : ℝ) * ((∑ j, ∑ k, christoffel g gi i j k p * S j * v k)
        + (∑ j, ∑ k, christoffel g gi i j k p * v j * S k))
      = ∑ j, ∑ m, 2 * (christoffel g gi i j m p * (S j * v m + v j * S m)) := by
    simp only [mul_add, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- each `D²F` (`ΓΓ`) cross block reduces to `2·(block₁ + block₂)`.
  have hCross : rncCrossBlock g gi p v v v i
      = 2 * ((∑ j, ∑ k, christoffel g gi i j k p * S j * v k)
             + (∑ j, ∑ k, christoffel g gi i j k p * v j * S k)) := by
    rw [key]
    simp only [rncCrossBlock, hinner]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [expJetD3_zero_closed g gi hC p Φ hv0 hΦcont hΦeq v v v]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hD3, hCross]
  ring

/-!
### (a4c) STEP 2 — the SECOND-JET backbone of `g̃` at `0` (toward `pd² g̃(0)` and the `rncDΓ` bridge)

The value / first-order / connection jets above were computed by a Leibniz expansion AT `0`
(`pd_expPullback_summand_zero`).  The second jet `∂²_{lm} g̃(0)` — encoded as the iterated partial
`pd (fun y => pd (fun x => g̃ x i j) m y) l 0`, exactly the object the metric-Christoffel derivative
`pd (christoffel g̃) l 0` consumes — needs the pullback's SECOND derivative.  Because `g̃` is only
`C²` (Rung 3: `fderiv exp_p` costs one order), the honest route is: (1) note `g̃` is `ContDiffAt ℝ 2`
at `0` (from `contDiffOn_expPullbackMetric` on the open ball); (2) reduce the iterated partial to the
second Fréchet-derivative bilinear form via a LOCAL `pd_pd` lemma valid at `ContDiffAt 2` regularity
(no global `C^∞`).  These are the reusable differentiability bricks below.
-/

/-- **Local `pd` congruence** (self-contained copy of `QIQTH.RNCExpansion.pd_congr`, to avoid pulling
    the heavy `HeatKernelA1` import chain into this file).  Two fields agreeing on a neighbourhood of
    `x` have equal partial derivatives there — `pd` sees only the germ. -/
theorem pd_congr_nhds {f h : Point n → ℝ} (i : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) : pd f i x = pd h i x := by
  simp only [pd]
  apply Filter.EventuallyEq.deriv_eq
  have htend : Filter.Tendsto (fun t => Function.update x i t) (nhds (x i)) (nhds x) := by
    have hc := (hasDerivAt_update x i (x i)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact htend.eventually hfh

/-- **Local mixed second partial = second Fréchet-derivative bilinear form** at `0`, needing only
    `ContDiffAt ℝ 2 f 0` (NOT global `C^∞`, so it applies to the `C²` pullback metric).  The direct
    `ContDiffAt`-localised analogue of `QIQTH.Curvature.pd_pd_eq`:
      `∂_i∂_j f(0) = D²f(0)(e_i, e_j)`.
    Proof: `ContDiffAt 2` gives `f` differentiable on a neighbourhood of `0` (so `∂_j f = D f(·)e_j`
    there, transported by `pd_congr_nhds`) and `fderiv f` differentiable at `0`; then `pd_eq_fderiv`
    + `fderiv_clm_apply` read off the bilinear value. -/
theorem pd_pd_eq_of_contDiffAt2 (f : Point n → ℝ) (i j : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) :
    pd (fun y => pd f j y) i 0
      = fderiv ℝ (fderiv ℝ f) 0 (Pi.single i 1) (Pi.single j 1) := by
  -- `f` is differentiable on a neighbourhood of `0`.
  have hdf_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds (0 : Point n), ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  -- `fderiv f` is differentiable at `0`.
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Replace `∂_j f` by `D f(·) e_j` on a neighbourhood of `0`.
  have e1 : (fun y => pd f j y) =ᶠ[nhds (0 : Point n)] (fun y => (fderiv ℝ f y) (Pi.single j 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f j y hy
  rw [pd_congr_nhds i 0 e1,
      pd_eq_fderiv _ i 0 (hfd2.clm_apply (differentiableAt_const _)),
      fderiv_clm_apply hfd2 (differentiableAt_const _)]
  simp [fderiv_const]

/-- **`g̃` is `ContDiffAt ℝ 2` at the centre `0`.**  Restriction of the ball-wide regularity
    `contDiffOn_expPullbackMetric` to the germ at `0` (the exp-ball is an open neighbourhood of `0`,
    `0 < expRho`). -/
theorem contDiffAt2_expPullbackMetric_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j : Fin n) :
    ContDiffAt ℝ 2 (fun x => expPullbackMetric g gi hC p x i j) 0 :=
  (contDiffOn_expPullbackMetric g gi hC p hg i j).contDiffAt
    (Metric.ball_mem_nhds 0 (expRho_pos g gi hC p))

/-- **`pd² g̃(0)` as the second Fréchet-derivative bilinear form.**  Reduction of the target iterated
    partial (the object `pd (christoffel g̃) l 0` consumes) to `D² g̃(0)(e_l, e_m)`, valid at the
    proved `C²` regularity of the pullback.  This is the STEP-2 reduction: the closed Christoffel
    value of `pd² g̃(0)` is now the single residual `D² g̃(0)(e_l,e_m) = <twice-Leibniz of the triple
    product>`, whose `g·∂²J` block is the closed `expJetD3(0)` value (a4a). -/
theorem pd2_expPullbackMetric_eq_fderiv2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l m : Fin n) :
    pd (fun y => pd (fun x => expPullbackMetric g gi hC p x i j) m y) l 0
      = fderiv ℝ (fderiv ℝ (fun x => expPullbackMetric g gi hC p x i j)) 0
          (Pi.single l 1) (Pi.single m 1) :=
  pd_pd_eq_of_contDiffAt2 _ l m (contDiffAt2_expPullbackMetric_zero g gi hC p hg i j)

/-- **`PdiffAt` congruence on a neighbourhood.**  If `f = h` near `x`, then `PdiffAt f = PdiffAt h`
    (the coordinate restriction germs agree). -/
theorem PdiffAt_congr_nhds {f h : Point n → ℝ} (l : Fin n) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) (H : PdiffAt h l x) : PdiffAt f l x := by
  unfold PdiffAt at *
  have htend : Filter.Tendsto (fun t => Function.update x l t) (nhds (x l)) (nhds x) := by
    have hc := (hasDerivAt_update x l (x l)).continuousAt.tendsto
    rw [Function.update_eq_self] at hc
    exact hc
  exact H.congr_of_eventuallyEq (htend.eventually hfh)

/-- **Second-order local partial differentiability at `0`** from `ContDiffAt ℝ 2`.  `ContDiffAt 2 f 0`
    ⟹ `fderiv f` differentiable at `0` and `f` differentiable near `0`, so `∂_m f = D f(·)e_m` near `0`
    is itself partially differentiable at `0`.  The `C²`-localised analogue of `Curvature.PdiffAt_pd`. -/
theorem PdiffAt_pd_zero_of_contDiffAt2 (f : Point n → ℝ) (m l : Fin n)
    (hf : ContDiffAt ℝ 2 f 0) : PdiffAt (fun y => pd f m y) l 0 := by
  have hfd2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdf_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ f y := by
    have hev : ∀ᶠ y in nhds (0 : Point n), ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hev] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds (0 : Point n)]
      (fun y => (fderiv ℝ f y) (Pi.single m 1)) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact PdiffAt_congr_nhds l 0 e1
    (pdiffAt_of_differentiableAt _ l 0 (hfd2.clm_apply (differentiableAt_const _)))

set_option maxHeartbeats 800000 in
/-- **THE GENERIC TWICE-LEIBNIZ AT `0`.**  The mixed second partial `∂_l∂_m(f₁·f₂·f₃)(0)` of a triple
    product of `C²`-at-`0` scalar fields expands into the nine second-order Leibniz terms.  This is the
    reusable one-order-up analogue of `pd_mul` for a triple product (mirroring the first-order
    `pd_expPullback_summand_zero`): each factor contributes a plain value, a first partial, and a second
    partial, and the nine terms are the distributions of `∂_l∂_m` across the three factors.

    Proof: on a neighbourhood of `0` (where all three factors are differentiable, from `ContDiffAt.eventually`)
    the FIRST partial `∂_m(f₁f₂f₃)` is the ordinary Leibniz three-term sum (`pd_mul` twice, pointwise),
    transported to the germ by `pd_congr_nhds`; then `∂_l` of that sum at `0` distributes (`pd_add`,
    `pd_mul`) using the plain / first- / second-order `PdiffAt` facts at `0`
    (`PdiffAt_pd_zero_of_contDiffAt2`). -/
theorem pd_pd_mul3_zero (f₁ f₂ f₃ : Point n → ℝ) (l m : Fin n)
    (h₁ : ContDiffAt ℝ 2 f₁ 0) (h₂ : ContDiffAt ℝ 2 f₂ 0) (h₃ : ContDiffAt ℝ 2 f₃ 0) :
    pd (fun y => pd (fun x => f₁ x * f₂ x * f₃ x) m y) l 0
      = pd (fun y => pd f₁ m y) l 0 * f₂ 0 * f₃ 0
        + pd f₁ m 0 * pd f₂ l 0 * f₃ 0
        + pd f₁ m 0 * f₂ 0 * pd f₃ l 0
        + pd f₁ l 0 * pd f₂ m 0 * f₃ 0
        + f₁ 0 * pd (fun y => pd f₂ m y) l 0 * f₃ 0
        + f₁ 0 * pd f₂ m 0 * pd f₃ l 0
        + pd f₁ l 0 * f₂ 0 * pd f₃ m 0
        + f₁ 0 * pd f₂ l 0 * pd f₃ m 0
        + f₁ 0 * f₂ 0 * pd (fun y => pd f₃ m y) l 0 := by
  -- factors differentiable near `0`.
  have hdiff : ∀ᶠ y in nhds (0 : Point n),
      DifferentiableAt ℝ f₁ y ∧ DifferentiableAt ℝ f₂ y ∧ DifferentiableAt ℝ f₃ y := by
    filter_upwards [h₁.eventually (by norm_num), h₂.eventually (by norm_num),
      h₃.eventually (by norm_num)] with y hy1 hy2 hy3
      using ⟨hy1.differentiableAt (by norm_num), hy2.differentiableAt (by norm_num),
        hy3.differentiableAt (by norm_num)⟩
  -- first partial is the pointwise three-term Leibniz sum near `0`.
  have hexp : (fun y => pd (fun x => f₁ x * f₂ x * f₃ x) m y) =ᶠ[nhds (0 : Point n)]
      (fun y => pd f₁ m y * f₂ y * f₃ y + f₁ y * pd f₂ m y * f₃ y + f₁ y * f₂ y * pd f₃ m y) := by
    filter_upwards [hdiff] with y hy
    obtain ⟨d1, d2, d3⟩ := hy
    have p1 : PdiffAt f₁ m y := pdiffAt_of_differentiableAt _ m y d1
    have p2 : PdiffAt f₂ m y := pdiffAt_of_differentiableAt _ m y d2
    have p3 : PdiffAt f₃ m y := pdiffAt_of_differentiableAt _ m y d3
    simp only [pd_mul (fun y => f₁ y * f₂ y) f₃ m y (p1.mul p2) p3, pd_mul f₁ f₂ m y p1 p2]
    ring
  rw [pd_congr_nhds l 0 hexp]
  -- differentiate the three-term sum at `0`.
  have pf1 : PdiffAt f₁ l 0 := pdiffAt_of_differentiableAt _ l 0 (h₁.differentiableAt (by norm_num))
  have pf2 : PdiffAt f₂ l 0 := pdiffAt_of_differentiableAt _ l 0 (h₂.differentiableAt (by norm_num))
  have pf3 : PdiffAt f₃ l 0 := pdiffAt_of_differentiableAt _ l 0 (h₃.differentiableAt (by norm_num))
  have pp1 : PdiffAt (fun y => pd f₁ m y) l 0 := PdiffAt_pd_zero_of_contDiffAt2 f₁ m l h₁
  have pp2 : PdiffAt (fun y => pd f₂ m y) l 0 := PdiffAt_pd_zero_of_contDiffAt2 f₂ m l h₂
  have pp3 : PdiffAt (fun y => pd f₃ m y) l 0 := PdiffAt_pd_zero_of_contDiffAt2 f₃ m l h₃
  have pS1 : PdiffAt (fun y => pd f₁ m y * f₂ y * f₃ y) l 0 := (pp1.mul pf2).mul pf3
  have pS2 : PdiffAt (fun y => f₁ y * pd f₂ m y * f₃ y) l 0 := (pf1.mul pp2).mul pf3
  rw [pd_add _ _ l 0 (pS1.add pS2) ((pf1.mul pf2).mul pp3), pd_add _ _ l 0 pS1 pS2,
      pd_mul (fun y => pd f₁ m y * f₂ y) f₃ l 0 (pp1.mul pf2) pf3,
      pd_mul (fun y => pd f₁ m y) f₂ l 0 pp1 pf2,
      pd_mul (fun y => f₁ y * pd f₂ m y) f₃ l 0 (pf1.mul pp2) pf3,
      pd_mul f₁ (fun y => pd f₂ m y) l 0 pf1 pp2,
      pd_mul (fun y => f₁ y * f₂ y) (fun y => pd f₃ m y) l 0 (pf1.mul pf2) pp3,
      pd_mul f₁ f₂ l 0 pf1 pf2]
  ring

set_option maxHeartbeats 1600000 in
/-- **(i) `pd² g̃(0)` — the twice-Leibniz reduction to the per-summand second jets.**  The mixed second
    partial of the pullback metric commutes with the finite `∑_{a,b}`:
      `∂_l∂_m g̃_{ij}(0) = ∑_{a,b} ∂_l∂_m (g(exp·)_{ab}·J_i^a·J_j^b)(0)`,
    and each summand's second jet is the closed nine-term twice-Leibniz of `pd_pd_mul3_zero` (whose
    factor plain/first-jets are `g(p)=δ`, `J(0)=id`, `∂J(0)=½(−Γ−Γ)` via the landed RNC lemmas, and
    whose second-jet inputs are `∂²(g∘exp)(0)` and `∂²J(0)`).  Proof: `g̃` is a double sum of `C²`-at-`0`
    triple products; `∂_m` distributes over the sum on the exp-ball (a neighbourhood of `0`, where the
    factors are differentiable) via `pd_sum`, transported to the germ by `pd_congr_nhds`; then `∂_l`
    distributes over the sum at `0` (`pd_sum`, with the second-order `PdiffAt` facts from
    `PdiffAt_pd_zero_of_contDiffAt2`). -/
theorem pd2_expPullbackMetric_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l m : Fin n) :
    pd (fun y => pd (fun x => expPullbackMetric g gi hC p x i j) m y) l 0
      = ∑ a, ∑ b, pd (fun y => pd (fun x =>
            g (expMap g gi hC p x) a b
            * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
            * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) m y) l 0 := by
  set s : Set (Point n) := Metric.ball (0 : Point n) (expRho g gi hC p) with hs
  have hsnhds : s ∈ nhds (0 : Point n) := Metric.ball_mem_nhds 0 (expRho_pos g gi hC p)
  have hsopen : IsOpen s := Metric.isOpen_ball
  have hE3 : ContDiffOn ℝ 2 (expMap g gi hC p) s :=
    (expMap_contDiffOn_three g gi hC p).of_le (by norm_num)
  -- `C²` regularity of the three factors on the ball.
  have hMc : ∀ a b, ContDiffOn ℝ 2 (fun x => g (expMap g gi hC p x) a b) s :=
    fun a b => ((hg a b).of_le (le_top)).comp_contDiffOn hE3
  have hAc : ∀ a, ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) s :=
    fun a => contDiffOn_fderiv_expMap_component g gi hC p i a
  have hBc : ∀ b, ContDiffOn ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) s :=
    fun b => contDiffOn_fderiv_expMap_component g gi hC p j b
  -- factor differentiability at each point of the (open) ball.
  have hMd : ∀ a b, ∀ x ∈ s, DifferentiableAt ℝ (fun x => g (expMap g gi hC p x) a b) x :=
    fun a b x hx => ((hMc a b).differentiableOn (by norm_num)).differentiableAt (hsopen.mem_nhds hx)
  have hAd : ∀ a, ∀ x ∈ s,
      DifferentiableAt ℝ (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) x :=
    fun a x hx => ((hAc a).differentiableOn (by norm_num)).differentiableAt (hsopen.mem_nhds hx)
  have hBd : ∀ b, ∀ x ∈ s,
      DifferentiableAt ℝ (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) x :=
    fun b x hx => ((hBc b).differentiableOn (by norm_num)).differentiableAt (hsopen.mem_nhds hx)
  -- STEP 1: the FIRST partial distributes over the double sum, pointwise on the ball ⟹ on the germ.
  have hinner : (fun x => pd (fun z => expPullbackMetric g gi hC p z i j) m x) =ᶠ[nhds 0]
      (fun x => ∑ a, ∑ b, pd (fun z =>
          g (expMap g gi hC p z) a b
          * (fderiv ℝ (expMap g gi hC p) z) (Pi.single i 1) a
          * (fderiv ℝ (expMap g gi hC p) z) (Pi.single j 1) b) m x) := by
    refine Filter.eventually_of_mem hsnhds (fun x hx => ?_)
    have hPd : ∀ a b, PdiffAt (fun z => g (expMap g gi hC p z) a b
        * (fderiv ℝ (expMap g gi hC p) z) (Pi.single i 1) a
        * (fderiv ℝ (expMap g gi hC p) z) (Pi.single j 1) b) m x := fun a b =>
      ((pdiffAt_of_differentiableAt _ m x (hMd a b x hx)).mul
        (pdiffAt_of_differentiableAt _ m x (hAd a x hx))).mul
        (pdiffAt_of_differentiableAt _ m x (hBd b x hx))
    simp only [expPullbackMetric]
    rw [pd_sum Finset.univ _ m x (fun a _ => PdiffAt_sum Finset.univ _ m x (fun b _ => hPd a b))]
    exact Finset.sum_congr rfl (fun a _ => pd_sum Finset.univ _ m x (fun b _ => hPd a b))
  rw [pd_congr_nhds l 0 hinner]
  -- STEP 2: the SECOND partial distributes over the double sum at `0`.
  have hSC : ∀ a b, ContDiffAt ℝ 2 (fun z => g (expMap g gi hC p z) a b
      * (fderiv ℝ (expMap g gi hC p) z) (Pi.single i 1) a
      * (fderiv ℝ (expMap g gi hC p) z) (Pi.single j 1) b) 0 := fun a b =>
    (((hMc a b).contDiffAt hsnhds).mul ((hAc a).contDiffAt hsnhds)).mul ((hBc b).contDiffAt hsnhds)
  have qq : ∀ a b, PdiffAt (fun x => pd (fun z => g (expMap g gi hC p z) a b
      * (fderiv ℝ (expMap g gi hC p) z) (Pi.single i 1) a
      * (fderiv ℝ (expMap g gi hC p) z) (Pi.single j 1) b) m x) l 0 := fun a b =>
    PdiffAt_pd_zero_of_contDiffAt2 _ m l (hSC a b)
  rw [pd_sum Finset.univ _ l 0 (fun a _ => PdiffAt_sum Finset.univ _ l 0 (fun b _ => qq a b))]
  exact Finset.sum_congr rfl (fun a _ => pd_sum Finset.univ _ l 0 (fun b _ => qq a b))

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

  PROGRESS on route (a) — the `v = 0` TRIVIALIZATION and the FIRST THREE VARIATION SOLVES are now
  LANDED (all axiom-clean `[propext, Classical.choice, Quot.sound]`):
    - substrate: `expTube_zero` (the tube is CONSTANT `(p,0)` on `[0,1]`),
      `fderiv_geodesicField_expTube_zero` (the Jacobi coefficient is the CONSTANT `A₀ = linF`),
      `linF_comp_linF` (`A₀² = 0`, so `exp(sA₀) = id + s·A₀`);
    - **(a1) LANDED** — `expFund_zero_eq`: THE first-variation propagator `Φ` from `hasFDerivAt_expMap … 0`
      IS the finite polynomial `Φ₀(t) = id + t·A₀`, via the operator-propagator uniqueness brick
      `clm_propagator_nilpotent_unique`;
    - **the DUHAMEL BRICK LANDED** — `clm_duhamel_nilpotent`: the constant-coeff inhomogeneous
      variation-of-constants formula `X'=A₀X+f, X 0=0, A₀²=0 ⟹ X 1 = ∫₀¹(id+(1−s)•A₀)(f s)ds`
      (F-abstract; candidate `Y=(id+t•A₀)(∫₀ᵗ(id−s•A₀)f)` + `HasDerivWithinAt.clm_apply` product rule +
      `gronwall_vec_residual_Icc` uniqueness + `intervalIntegral_comp_comm`);
    - **(a2) LANDED** — `expJet2Curve_zero_eq`: the genuine 2nd-variation curve
      `Q^{hk}_0(1) = ∫₀¹ (id+(1−s)•linF)(expJet2Rhs … 0 Φ h k s) ds`;
    - **(a3) LANDED** — `expJet3ValG_zero_eq`: the genuine 3rd-variation datum
      `R^{hkl}_0(1) = expJet3ValG … 0 = ∫₀¹ (id+(1−s)•linF)(expJet3Rhs … 0 Φ Q_kl Q_hl Q_hk h k l s) ds`
      (the `Q_·· = expJet2Curve …` being themselves closed by (a2)).
  Composing (a3) with `expJetD3_apply` gives the CLOSED INTEGRAL form of the target operator:
    `expJetD3 g gi hC p 0 Φ l k h = expJetPi (∫₀¹ (id+(1−s)•linF)(expJet3Rhs … 0 Φ … h k l s) ds)`.

  **(a4a) + (a4b) NOW LANDED (axiom-clean `[propext, Classical.choice, Quot.sound]`).**  The
  `D²F(p,0)` / `D³F(p,0)` closed-Christoffel VALUE lemmas were built in `QIQTH/GeodesicFieldJets.lean`
  (`fderiv2_geodesicField_apply_zero`, `fderiv3_geodesicField_apply_zero`); on top of them:
    - `expJetD3_zero_integral` : the `π`-reduction `expJetD3 … 0 Φ l k h = ∫₀¹[(Θ₃ s).1 + (1−s)•(Θ₃ s).2]ds`;
    - `vec_ode_nilpotent_const` : the general-`t` constant-source nilpotent Duhamel `X t = t•b + (t²/2)•(A b)`;
    - `expFundZero_iota` / `expJet2Rhs_zero_const` / `expJet2Curve_zero_velocity` : `Φ₀ s (ι m)=(s•m,m)`,
      the CONSTANT second-variation source `(0,c_{kl})`, and the linear-in-`s` velocity `(Q_{kl} s).2 = s•c_{kl}`;
    - **(a4a) `expJetD3_zero_closed`** : the EXPLICIT closed value
        `expJetD3 … 0 Φ l k h = (1/6)•(rncD3Block h k l + rncCrossBlock_h + rncCrossBlock_k + rncCrossBlock_l)`,
      obtained by substituting the closed `D²F`/`D³F` values + the `Φ₀`/`Q_··` first-and-second variations
      into `Θ₃ s`, factoring the polynomial `∫₀¹ (1−s)·s ds = 1/6`;
    - **(a4b) `expJetD3_zero_diagonal`** : the diagonal `l=k=h=v` value equals EXACTLY the honest cubic
      `a₃(v)` of `expMap_value_three_jet` (`−∑∂Γ v³ + ∑Γ(Γv²)v + ∑Γ v(Γv²)`); the `1/6` cancels the
      combinatorial `6` (∂Γ, three brackets × doubled `v_jv_m`) and the `3·2` (three cross-terms × doubled
      source).  Composed with `a3rawArr_contract_eq_a3` (RNCGaugeExp) this is the third-jet = `a3rawArr`
      contraction identity the R3→κ ledger needs.

  **(a4c) STEP 2 — `pd² g̃(0)` — NOW LANDED (axiom-clean `[propext, Classical.choice, Quot.sound]`).**
  The second-jet backbone is built, mirroring the first-order `pd_expPullback_summand_zero` one order up:
    - `pd_congr_nhds` : `pd` depends only on the germ (self-contained copy of `RNCExpansion.pd_congr`);
    - `PdiffAt_congr_nhds` / `PdiffAt_pd_zero_of_contDiffAt2` : neighbourhood congruence for `PdiffAt`,
      and the `C²`-localised second-order partial differentiability at `0` (the analogue of
      `Curvature.PdiffAt_pd`, needing only `ContDiffAt ℝ 2 f 0`, so it applies to the `C²` pullback);
    - `pd_pd_eq_of_contDiffAt2` : the `C²`-localised `pd_pd_eq` (`∂_i∂_j f(0) = D²f(0)(e_i,e_j)`);
    - `contDiffAt2_expPullbackMetric_zero` : `g̃` is `ContDiffAt ℝ 2` at `0`;
    - **`pd_pd_mul3_zero`** : THE generic twice-Leibniz at `0` — the CLOSED nine-term expansion of
      `∂_l∂_m(f₁·f₂·f₃)(0)` for `C²`-at-`0` factors (each factor contributes a plain value, a first jet,
      and a second jet);
    - **`pd2_expPullbackMetric_at_zero`** : `∂_l∂_m g̃_{ij}(0) = ∑_{a,b} ∂_l∂_m(g(exp·)_{ab}·J_i^a·J_j^b)(0)`
      (the second partial commutes with the finite `∑_{a,b}`), each summand closed by `pd_pd_mul3_zero`.
  So the CLOSED `∂²g̃(0)` is: the double sum of the nine-term twice-Leibniz, whose factor plain/first
  jets are the landed RNC values (`g(p)`, `J(0)=δ`, `∂J(0)=½(−Γ−Γ)` via `pd_jacobian_expMap_zero`) and
  whose two SECOND-jet inputs are `∂²(g∘exp)(0)` and `∂²J(0)`.

  **THE REMAINING GOAL — (a4c) STEP 3, the BRIDGE `pd (christoffel g̃)(0) = rncDΓ`.**  Two residual
  identifications, both `C²`/third-jet (no rung past Rung 3):
    (α) **the two second-jet INPUTS in closed Christoffel form.**  `∂²J(0) = ∂²_{lm}(D exp·e_i)_a(0)`
        is the third jet `D³exp(0)` = the closed `expJetD3(0)` value (a4a) — needs the SLOT MATCH
        `pd (fun y => pd (fun x => (D exp x)(e_i)_a) m y) l 0 = expJetD3 … 0 Φ e_l e_m e_i` component `a`
        (transport iterated-`pd` ↔ iterated-`fderiv` via `pd_pd_eq_of_contDiffAt2` twice + pull the
        evaluation/projection CLM through `fderiv`, then instantiate `Φ = id + t·linF` by `expFund_zero_eq`
        and apply `expJetD3_zero_closed`); and `∂²(g∘exp)(0)` is the chain-rule second derivative
        `∂²g(p)[e_l,e_m] − ∑_c ∂_c g(p)·Γ^c_{lm}(p)` (an ambient `∂²g` input + the closed `D²exp(0)=−Γ`).
    (β) **the metric-Christoffel differentiation + `rncDΓ` match.**  `∂_l Γ̃^i_{jk}(0)` reduces (via
        `Γ̃(0)=0`, `g̃(0)=δ`, `∂g̃(0)=0`, so the `∂g̃⁻¹` terms drop) to `½δ^{iα}(∂_l∂_j g̃_{αk}+∂_l∂_k g̃_{αj}
        −∂_l∂_α g̃_{jk})(0)`; substitute STEP 2 + (α) and match `rncDΓ (christoffel g gi ··p)
        (pd christoffel ··p)` via `christoffel_lower` + `a3rawArr_contract_eq_a3` (RNCGaugeExp).  The
        `∂²g` ambient blocks cancel against the metric-compatibility contractions, leaving the pure
        `Γ,∂Γ` combination `rncDΓ`.  (Requires `import QIQTH.RNCGauge`; nothing imports PullbackMetric.)
  VERDICT: STEP 2 (`pd²g̃(0)`) — the guaranteed floor — is LANDED; the bridge residual is the slot-match
  (α) + the Christoffel/`rncDΓ` match (β), a reachable assembly, not a deep obstruction.  Checkpoints
  landed: value + first-order + connection jets (`g̃(0)=δ`, `∂g̃(0)=0`, `Γ̃(0)=0`), the level-2
  differentiability core (`hasFDerivAt_fderiv2_expMap_zero`), the closed third-jet value + its `a₃`
  grounding (`expJetD3_zero_closed`/`expJetD3_zero_diagonal`), AND the closed `pd²g̃(0)` twice-Leibniz
  (`pd_pd_mul3_zero`/`pd2_expPullbackMetric_at_zero`).

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
