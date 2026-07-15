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
import QIQTH.RNCGauge
import QIQTH.RNCGaugeExp

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

/-!
### STEP (i) — block-multilinearity of `rncD3Block` / `rncCrossBlock`

The two RNC third-jet blocks are symmetric-multilinear in their `Point`-valued direction arguments.
These are pure `Finset`/`ring` identities (evaluated componentwise `… i`); they supply the missing
tree infrastructure for the two-slot NON-diagonal contraction the radial identity consumes (the
`α2` Jacobian second jet enters the contraction with two derivative slots contracted against `v` and
one slot fixed at a basis vector, so no full-diagonal shortcut applies).
-/

-- `rncD3Block` is symmetric-trilinear in `(h, k, l)`.

/-- **Additivity of `rncD3Block` in its first slot `h`.** -/
theorem rncD3Block_add_left (g gi : Point n → Fin n → Fin n → ℝ) (p h₁ h₂ k l : Point n) (i : Fin n) :
    rncD3Block g gi p (h₁ + h₂) k l i
      = rncD3Block g gi p h₁ k l i + rncD3Block g gi p h₂ k l i := by
  simp only [rncD3Block, Pi.add_apply]
  rw [← neg_add, neg_inj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : (∑ r, pd (fun z => christoffel g gi i j m z) r p * (h₁ r + h₂ r))
      = (∑ r, pd (fun z => christoffel g gi i j m z) r p * h₁ r)
        + (∑ r, pd (fun z => christoffel g gi i j m z) r p * h₂ r) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by ring
  rw [hc]; ring

/-- **Homogeneity of `rncD3Block` in its first slot `h`.** -/
theorem rncD3Block_smul_left (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p h k l : Point n)
    (i : Fin n) :
    rncD3Block g gi p (s • h) k l i = s * rncD3Block g gi p h k l i := by
  simp only [rncD3Block, Pi.smul_apply, smul_eq_mul]
  rw [mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_mul_smul_factor]; ring

/-- **Symmetry of `rncD3Block` under swapping the first two slots `h ↔ k`.** -/
theorem rncD3Block_swap12 (g gi : Point n → Fin n → Fin n → ℝ) (p h k l : Point n) (i : Fin n) :
    rncD3Block g gi p h k l i = rncD3Block g gi p k h l i := by
  simp only [rncD3Block]
  rw [neg_inj]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

/-- **Symmetry of `rncD3Block` under swapping the last two slots `k ↔ l`.** -/
theorem rncD3Block_swap23 (g gi : Point n → Fin n → Fin n → ℝ) (p h k l : Point n) (i : Fin n) :
    rncD3Block g gi p h k l i = rncD3Block g gi p h l k i := by
  simp only [rncD3Block]
  rw [neg_inj]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

/-- **Additivity of `rncD3Block` in its middle slot `k`** (via `h ↔ k` symmetry). -/
theorem rncD3Block_add_mid (g gi : Point n → Fin n → Fin n → ℝ) (p h k₁ k₂ l : Point n) (i : Fin n) :
    rncD3Block g gi p h (k₁ + k₂) l i
      = rncD3Block g gi p h k₁ l i + rncD3Block g gi p h k₂ l i := by
  rw [rncD3Block_swap12, rncD3Block_add_left, rncD3Block_swap12 g gi p k₁ h l i,
    rncD3Block_swap12 g gi p k₂ h l i]

/-- **Homogeneity of `rncD3Block` in its middle slot `k`** (via `h ↔ k` symmetry). -/
theorem rncD3Block_smul_mid (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p h k l : Point n)
    (i : Fin n) :
    rncD3Block g gi p h (s • k) l i = s * rncD3Block g gi p h k l i := by
  rw [rncD3Block_swap12, rncD3Block_smul_left, rncD3Block_swap12 g gi p k h l i]

/-- **Additivity of `rncD3Block` in its last slot `l`** (via `k ↔ l` symmetry). -/
theorem rncD3Block_add_right (g gi : Point n → Fin n → Fin n → ℝ) (p h k l₁ l₂ : Point n) (i : Fin n) :
    rncD3Block g gi p h k (l₁ + l₂) i
      = rncD3Block g gi p h k l₁ i + rncD3Block g gi p h k l₂ i := by
  rw [rncD3Block_swap23, rncD3Block_add_mid, rncD3Block_swap23 g gi p h l₁ k i,
    rncD3Block_swap23 g gi p h l₂ k i]

/-- **Homogeneity of `rncD3Block` in its last slot `l`** (via `k ↔ l` symmetry). -/
theorem rncD3Block_smul_right (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p h k l : Point n)
    (i : Fin n) :
    rncD3Block g gi p h k (s • l) i = s * rncD3Block g gi p h k l i := by
  rw [rncD3Block_swap23, rncD3Block_smul_mid, rncD3Block_swap23 g gi p h l k i]

-- `rncCrossBlock` is linear in `dir` and symmetric-bilinear in the source pair `(sk, sl)`.
-- Helpers for the inner second-variation velocity coefficient `∑_{j'm'} Γ (·⊗· + ·⊗·)`.

/-- **Additivity of the inner second-variation coefficient in the varied source direction.** -/
private theorem crossInner_add (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (q : Fin n)
    (u a b : Point n) :
    (∑ j', ∑ m', christoffel g gi q j' m' p * (u j' * (a m' + b m') + (a j' + b j') * u m'))
      = (∑ j', ∑ m', christoffel g gi q j' m' p * (u j' * a m' + a j' * u m'))
        + (∑ j', ∑ m', christoffel g gi q j' m' p * (u j' * b m' + b j' * u m')) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m' _ => by ring

/-- **Homogeneity of the inner second-variation coefficient in the varied source direction.** -/
private theorem crossInner_smul (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (q : Fin n)
    (s : ℝ) (u a : Point n) :
    (∑ j', ∑ m', christoffel g gi q j' m' p * (u j' * (s * a m') + (s * a j') * u m'))
      = s * ∑ j', ∑ m', christoffel g gi q j' m' p * (u j' * a m' + a j' * u m') := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m' _ => by ring

/-- **Symmetry of the inner second-variation coefficient in the two source directions.** -/
private theorem crossInner_symm (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (q : Fin n)
    (a b : Point n) :
    (∑ j', ∑ m', christoffel g gi q j' m' p * (a j' * b m' + b j' * a m'))
      = (∑ j', ∑ m', christoffel g gi q j' m' p * (b j' * a m' + a j' * b m')) :=
  Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun m' _ => by ring

/-- **Additivity of `rncCrossBlock` in its differentiation direction `dir`.** -/
theorem rncCrossBlock_add_dir (g gi : Point n → Fin n → Fin n → ℝ) (p dir₁ dir₂ sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p (dir₁ + dir₂) sk sl i
      = rncCrossBlock g gi p dir₁ sk sl i + rncCrossBlock g gi p dir₂ sk sl i := by
  simp only [rncCrossBlock, Pi.add_apply]
  rw [← neg_add, neg_inj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **Homogeneity of `rncCrossBlock` in its differentiation direction `dir`.** -/
theorem rncCrossBlock_smul_dir (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p dir sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p (s • dir) sk sl i = s * rncCrossBlock g gi p dir sk sl i := by
  simp only [rncCrossBlock, Pi.smul_apply, smul_eq_mul]
  rw [mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

/-- **Symmetry of `rncCrossBlock` under swapping the two source directions `sk ↔ sl`.** -/
theorem rncCrossBlock_swap_source (g gi : Point n → Fin n → Fin n → ℝ) (p dir sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir sk sl i = rncCrossBlock g gi p dir sl sk i := by
  simp only [rncCrossBlock]
  rw [neg_inj]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [crossInner_symm g gi p j sl sk, crossInner_symm g gi p m sl sk]

/-- **Additivity of `rncCrossBlock` in its first source direction `sk`.** -/
theorem rncCrossBlock_add_sk (g gi : Point n → Fin n → Fin n → ℝ) (p dir sk₁ sk₂ sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir (sk₁ + sk₂) sl i
      = rncCrossBlock g gi p dir sk₁ sl i + rncCrossBlock g gi p dir sk₂ sl i := by
  simp only [rncCrossBlock, Pi.add_apply]
  rw [← neg_add, neg_inj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [crossInner_add g gi p j sl sk₁ sk₂, crossInner_add g gi p m sl sk₁ sk₂]
  ring

/-- **Homogeneity of `rncCrossBlock` in its first source direction `sk`.** -/
theorem rncCrossBlock_smul_sk (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p dir sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir (s • sk) sl i = s * rncCrossBlock g gi p dir sk sl i := by
  simp only [rncCrossBlock, Pi.smul_apply, smul_eq_mul]
  rw [mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [crossInner_smul g gi p j s sl sk, crossInner_smul g gi p m s sl sk]
  ring

/-- **Additivity of `rncCrossBlock` in its second source direction `sl`** (via `sk ↔ sl` symmetry). -/
theorem rncCrossBlock_add_sl (g gi : Point n → Fin n → Fin n → ℝ) (p dir sk sl₁ sl₂ : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir sk (sl₁ + sl₂) i
      = rncCrossBlock g gi p dir sk sl₁ i + rncCrossBlock g gi p dir sk sl₂ i := by
  rw [rncCrossBlock_swap_source, rncCrossBlock_add_sk, rncCrossBlock_swap_source g gi p dir sl₁ sk i,
    rncCrossBlock_swap_source g gi p dir sl₂ sk i]

/-- **Homogeneity of `rncCrossBlock` in its second source direction `sl`** (via `sk ↔ sl` symmetry). -/
theorem rncCrossBlock_smul_sl (g gi : Point n → Fin n → Fin n → ℝ) (s : ℝ) (p dir sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir sk (s • sl) i = s * rncCrossBlock g gi p dir sk sl i := by
  rw [rncCrossBlock_swap_source, rncCrossBlock_smul_sk, rncCrossBlock_swap_source g gi p dir sl sk i]

/-! #### The single-slot contraction (`apply_sum`) forms.

Using multilinearity, contracting a block slot with a weight `v` (over the standard basis) reconstitutes
`v` in that slot:  `∑_a v^a · block(…e_a…) = block(…v…)`.  These are the concrete forms the two-slot
non-diagonal contraction of the radial identity consumes (the `α2` Jacobian second jet enters with two
derivative slots to be contracted against `v`).  The chain is `zero → Finset.sum → contract`. -/

/-- **Expansion of a `Point` over the standard basis:** `v = ∑ a, v^a • e_a`. -/
theorem point_eq_sum_single (v : Point n) : v = ∑ a, v a • (Pi.single a 1 : Point n) := by
  funext r
  rw [Finset.sum_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq]

theorem rncD3Block_zero_left (g gi : Point n → Fin n → Fin n → ℝ) (p k l : Point n) (i : Fin n) :
    rncD3Block g gi p 0 k l i = 0 := by
  simp only [rncD3Block, Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
    zero_add, neg_zero]

/-- **`rncD3Block` distributes over a finite sum in its first slot.** -/
theorem rncD3Block_sum_left {ι : Type*} (g gi : Point n → Fin n → Fin n → ℝ) (s : Finset ι)
    (F : ι → Point n) (p k l : Point n) (i : Fin n) :
    rncD3Block g gi p (∑ x ∈ s, F x) k l i = ∑ x ∈ s, rncD3Block g gi p (F x) k l i := by
  induction s using Finset.cons_induction with
  | empty => simp [rncD3Block_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, rncD3Block_add_left, ih, Finset.sum_cons]

/-- **First-slot contraction of `rncD3Block`:** `rncD3Block(v,k,l) = ∑_a v^a · rncD3Block(e_a,k,l)`. -/
theorem rncD3Block_contract_left (g gi : Point n → Fin n → Fin n → ℝ) (p v k l : Point n) (i : Fin n) :
    rncD3Block g gi p v k l i = ∑ a, v a * rncD3Block g gi p (Pi.single a 1) k l i := by
  conv_lhs => rw [point_eq_sum_single v]
  rw [rncD3Block_sum_left]
  exact Finset.sum_congr rfl fun a _ => rncD3Block_smul_left g gi (v a) p (Pi.single a 1) k l i

/-- **Middle-slot contraction of `rncD3Block`** (via `h ↔ k` symmetry). -/
theorem rncD3Block_contract_mid (g gi : Point n → Fin n → Fin n → ℝ) (p h v l : Point n) (i : Fin n) :
    rncD3Block g gi p h v l i = ∑ a, v a * rncD3Block g gi p h (Pi.single a 1) l i := by
  rw [rncD3Block_swap12, rncD3Block_contract_left]
  exact Finset.sum_congr rfl fun a _ => by rw [rncD3Block_swap12 g gi p (Pi.single a 1) h l i]

/-- **Last-slot contraction of `rncD3Block`** (via `k ↔ l` symmetry). -/
theorem rncD3Block_contract_right (g gi : Point n → Fin n → Fin n → ℝ) (p h k v : Point n) (i : Fin n) :
    rncD3Block g gi p h k v i = ∑ a, v a * rncD3Block g gi p h k (Pi.single a 1) i := by
  rw [rncD3Block_swap23, rncD3Block_contract_mid]
  exact Finset.sum_congr rfl fun a _ => by rw [rncD3Block_swap23 g gi p h (Pi.single a 1) k i]

theorem rncCrossBlock_zero_dir (g gi : Point n → Fin n → Fin n → ℝ) (p sk sl : Point n) (i : Fin n) :
    rncCrossBlock g gi p 0 sk sl i = 0 := by
  simp only [rncCrossBlock, Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
    neg_zero]

theorem rncCrossBlock_zero_sk (g gi : Point n → Fin n → Fin n → ℝ) (p dir sl : Point n) (i : Fin n) :
    rncCrossBlock g gi p dir 0 sl i = 0 := by
  simp only [rncCrossBlock, Pi.zero_apply, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
    neg_zero]

/-- **`rncCrossBlock` distributes over a finite sum in its differentiation direction.** -/
theorem rncCrossBlock_sum_dir {ι : Type*} (g gi : Point n → Fin n → Fin n → ℝ) (s : Finset ι)
    (F : ι → Point n) (p sk sl : Point n) (i : Fin n) :
    rncCrossBlock g gi p (∑ x ∈ s, F x) sk sl i = ∑ x ∈ s, rncCrossBlock g gi p (F x) sk sl i := by
  induction s using Finset.cons_induction with
  | empty => simp [rncCrossBlock_zero_dir]
  | cons a s ha ih => rw [Finset.sum_cons, rncCrossBlock_add_dir, ih, Finset.sum_cons]

/-- **`rncCrossBlock` distributes over a finite sum in its first source direction.** -/
theorem rncCrossBlock_sum_sk {ι : Type*} (g gi : Point n → Fin n → Fin n → ℝ) (s : Finset ι)
    (F : ι → Point n) (p dir sl : Point n) (i : Fin n) :
    rncCrossBlock g gi p dir (∑ x ∈ s, F x) sl i = ∑ x ∈ s, rncCrossBlock g gi p dir (F x) sl i := by
  induction s using Finset.cons_induction with
  | empty => simp [rncCrossBlock_zero_sk]
  | cons a s ha ih => rw [Finset.sum_cons, rncCrossBlock_add_sk, ih, Finset.sum_cons]

/-- **Direction contraction of `rncCrossBlock`.** -/
theorem rncCrossBlock_contract_dir (g gi : Point n → Fin n → Fin n → ℝ) (p v sk sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p v sk sl i = ∑ a, v a * rncCrossBlock g gi p (Pi.single a 1) sk sl i := by
  conv_lhs => rw [point_eq_sum_single v]
  rw [rncCrossBlock_sum_dir]
  exact Finset.sum_congr rfl fun a _ => rncCrossBlock_smul_dir g gi (v a) p (Pi.single a 1) sk sl i

/-- **First source-direction contraction of `rncCrossBlock`.** -/
theorem rncCrossBlock_contract_sk (g gi : Point n → Fin n → Fin n → ℝ) (p dir v sl : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir v sl i = ∑ a, v a * rncCrossBlock g gi p dir (Pi.single a 1) sl i := by
  conv_lhs => rw [point_eq_sum_single v]
  rw [rncCrossBlock_sum_sk]
  exact Finset.sum_congr rfl fun a _ => rncCrossBlock_smul_sk g gi (v a) p dir (Pi.single a 1) sl i

/-- **Second source-direction contraction of `rncCrossBlock`** (via `sk ↔ sl` symmetry). -/
theorem rncCrossBlock_contract_sl (g gi : Point n → Fin n → Fin n → ℝ) (p dir sk v : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p dir sk v i = ∑ a, v a * rncCrossBlock g gi p dir sk (Pi.single a 1) i := by
  rw [rncCrossBlock_swap_source, rncCrossBlock_contract_sk]
  exact Finset.sum_congr rfl fun a _ => by
    rw [rncCrossBlock_swap_source g gi p dir (Pi.single a 1) sk i]

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
### (α) STEP 3 residual — the two second-jet INPUTS in closed Christoffel form

The twice-Leibniz `pd_pd_mul3_zero` reduces each `(a,b)`-summand of `∂²g̃(0)` to nine terms whose two
genuine second-jet inputs are `∂²(g∘exp)(0)` (the metric-along-exp Hessian) and `∂²J(0)` (the exp-map
Jacobian's second jet, i.e. the third jet of `exp`).  Here we land the FIRST of the two — the clean
chain-rule Hessian of `g∘exp_p` at the centre — as `pd2_metric_comp_expMap_zero`.
-/

/-- **Expansion of a scalar functional on `Point n` over the standard basis.**  For a continuous linear
    functional `L` and a vector `w`, `L w = ∑_c w_c · L(e_c)` — the coordinate expansion of `L` acting
    on `w = ∑_c w_c • e_c`. -/
theorem clm_functional_pi_expand (L : Point n →L[ℝ] ℝ) (w : Point n) :
    L w = ∑ c, w c * L (Pi.single c 1) := by
  have hw : w = ∑ c, w c • (Pi.single c 1 : Point n) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  conv_lhs => rw [hw]
  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [map_smul, smul_eq_mul]

/-- **Generic chain rule at the exp-centre.**  For any scalar field `F` differentiable at `p`, the
    pullback of its first partial through `exp_p` is trivial at `0`: `∂_l(F∘exp_p)(0) = ∂_l F(p)`.
    (Since `exp_p 0 = p` and `D exp_p 0 = id`.)  The generalisation of `pd_metric_comp_expMap_zero`
    from `g_{ab}` to an arbitrary differentiable `F` — used to transport `∂_c g(p)` back through the
    Jacobian's second jet. -/
theorem pd_comp_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (F : Point n → ℝ) (hF : DifferentiableAt ℝ F p) (l : Fin n) :
    pd (fun x => F (expMap g gi hC p x)) l 0 = pd F l p := by
  have hFp : HasFDerivAt F (fderiv ℝ F p) (expMap g gi hC p 0) := by
    rw [expMap_apply_zero]; exact hF.hasFDerivAt
  have hexp : HasFDerivAt (expMap g gi hC p) (ContinuousLinearMap.id ℝ (Point n)) 0 :=
    (hasStrictFDerivAt_expMap g gi hC p).hasFDerivAt
  have hchain : HasFDerivAt (fun x => F (expMap g gi hC p x))
      ((fderiv ℝ F p).comp (ContinuousLinearMap.id ℝ (Point n))) 0 := hFp.comp 0 hexp
  rw [pd_eq_fderiv _ l 0 hchain.differentiableAt, hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact (pd_eq_fderiv F l p hF).symm

set_option maxHeartbeats 800000 in
/-- **(α1) — the chain-rule Hessian of `g∘exp_p` at the centre.**  The mixed second partial of the
    metric-along-exp field is the ambient metric's own Hessian at `p` plus a `∂g·(∂²exp)` correction:
      `∂_l∂_m(g(exp·)_{ab})(0) = ∂_l∂_m g_{ab}(p) + ∑_c ∂_c g_{ab}(p)·½(−Γ^c_{ml}(p) − Γ^c_{lm}(p))`.
    The `∑_c ∂_c g · Γ` term is the pullback correction: the exp-Jacobian's linear jet
    `∂_l(D exp·e_m)_c(0) = ½(−Γ^c_{ml} − Γ^c_{lm})` (`pd_jacobian_expMap_zero`) contracts against the
    ambient gradient.  Proof: near `0` the first partial `∂_m(g∘exp)` is (chain rule + basis expansion)
    `∑_c ∂_c g(exp·)·(D exp·e_m)_c`; differentiating this sum at `0` (`pd_sum`/`pd_mul`), the
    `∂_c g(exp·)` factor pulls back to `∂_l∂_c g(p)` (via `pd_comp_expMap_zero`, contracted by the
    Kronecker `(D exp 0·e_m)_c = δ_{mc}`) and the Jacobian factor contributes its RNC first jet. -/
theorem pd2_metric_comp_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b l m : Fin n) :
    pd (fun y => pd (fun x => g (expMap g gi hC p x) a b) m y) l 0
      = pd (fun z => pd (fun y => g y a b) m z) l p
        + ∑ c, pd (fun y => g y a b) c p
            * (1 / 2 * (-christoffel g gi c m l p - christoffel g gi c l m p)) := by
  have hgabdiff : Differentiable ℝ (fun z => g z a b) := (hg a b).differentiable (by simp)
  have hgabF : Differentiable ℝ (fun z => fderiv ℝ (fun z => g z a b) z) :=
    ((hg a b).fderiv_right (m := 1) le_top).differentiable (by norm_num)
  have hpdc : ∀ c : Fin n, (fun z => pd (fun y => g y a b) c z)
      = (fun z => (fderiv ℝ (fun y => g y a b) z) (Pi.single c 1)) :=
    fun c => funext fun z => pd_eq_fderiv _ c z (hgabdiff z)
  have hpdc_diff : ∀ c : Fin n, DifferentiableAt ℝ (fun z => pd (fun y => g y a b) c z) p := by
    intro c; rw [hpdc c]; exact (hgabF p).clm_apply (differentiableAt_const _)
  have hball : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ nhds (0 : Point n) :=
    Metric.ball_mem_nhds 0 (expRho_pos g gi hC p)
  have hE0 : DifferentiableAt ℝ (expMap g gi hC p) 0 :=
    (hasStrictFDerivAt_expMap g gi hC p).hasFDerivAt.differentiableAt
  -- STEP 1: the first partial `∂_m(g∘exp)` as a basis-expanded product sum near `0`.
  have hstep1 : (fun y => pd (fun x => g (expMap g gi hC p x) a b) m y) =ᶠ[nhds 0]
      (fun y => ∑ c, pd (fun z => g z a b) c (expMap g gi hC p y)
          * (fderiv ℝ (expMap g gi hC p) y) (Pi.single m 1) c) := by
    filter_upwards [hball] with y hy
    have hEy : DifferentiableAt ℝ (expMap g gi hC p) y :=
      ((expMap_contDiffOn_three g gi hC p).differentiableOn (by norm_num)).differentiableAt
        (Metric.isOpen_ball.mem_nhds hy)
    have hgy : DifferentiableAt ℝ (fun z => g z a b) (expMap g gi hC p y) := hgabdiff _
    have hcomp : HasFDerivAt (fun x => g (expMap g gi hC p x) a b)
        ((fderiv ℝ (fun z => g z a b) (expMap g gi hC p y)).comp
          (fderiv ℝ (expMap g gi hC p) y)) y :=
      hgy.hasFDerivAt.comp y hEy.hasFDerivAt
    rw [pd_eq_fderiv _ m y hcomp.differentiableAt, hcomp.fderiv, ContinuousLinearMap.comp_apply,
      clm_functional_pi_expand (fderiv ℝ (fun z => g z a b) (expMap g gi hC p y))
        ((fderiv ℝ (expMap g gi hC p) y) (Pi.single m 1))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, ← pd_eq_fderiv _ c (expMap g gi hC p y) hgy]
  rw [pd_congr_nhds l 0 hstep1]
  -- differentiability of the two per-`c` factors at `0`.
  have hpA : ∀ c : Fin n,
      PdiffAt (fun y => pd (fun z => g z a b) c (expMap g gi hC p y)) l 0 := by
    intro c
    refine pdiffAt_of_differentiableAt _ l 0 ?_
    have hout : DifferentiableAt ℝ (fun z => pd (fun y => g y a b) c z) (expMap g gi hC p 0) := by
      rw [expMap_apply_zero]; exact hpdc_diff c
    exact hout.comp 0 hE0
  have hpB : ∀ c : Fin n,
      PdiffAt (fun y => (fderiv ℝ (expMap g gi hC p) y) (Pi.single m 1) c) l 0 := fun c =>
    pdiffAt_of_differentiableAt _ l 0
      (hasFDerivAt_jacobian_component_expMap_zero g gi hC p m c).differentiableAt
  -- STEP 2: `∂_l` distributes over the finite `∑_c` and each summand is a two-term Leibniz.
  rw [pd_sum Finset.univ (fun c y => pd (fun z => g z a b) c (expMap g gi hC p y)
        * (fderiv ℝ (expMap g gi hC p) y) (Pi.single m 1) c) l 0
      (fun c _ => (hpA c).mul (hpB c))]
  have hsummand : ∀ c : Fin n,
      pd (fun y => pd (fun z => g z a b) c (expMap g gi hC p y)
          * (fderiv ℝ (expMap g gi hC p) y) (Pi.single m 1) c) l 0
        = pd (fun z => pd (fun y => g y a b) c z) l p * (Pi.single m 1 : Point n) c
          + pd (fun y => g y a b) c p
              * (1 / 2 * (-christoffel g gi c m l p - christoffel g gi c l m p)) := by
    intro c
    rw [pd_mul _ _ l 0 (hpA c) (hpB c)]
    congr 1
    · congr 1
      · exact pd_comp_expMap_zero g gi hC p (fun z => pd (fun y => g y a b) c z) (hpdc_diff c) l
      · exact jacobian_component_expMap_at_zero g gi hC p m c
    · congr 1
      · rw [expMap_apply_zero]
      · exact pd_jacobian_expMap_zero g gi hC p m c l
  rw [Finset.sum_congr rfl (fun c _ => hsummand c), Finset.sum_add_distrib]
  congr 1
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **Scalar CLM-composition `HasFDerivAt`** (small-context helper).  For a scalar-valued continuous
    linear functional `Θ` on an arbitrary normed space `G` and a field `F : Point n → G` differentiable
    at `0`, the composite `x ↦ Θ(F x)` is differentiable at `0` with derivative `Θ ∘ F'`.  Abstracting
    `G` keeps the `HasFDerivAt.comp` instance/unification search away from the deeply-nested concrete
    CLM tower — Lean's instance search stalls on `NormedSpace` for iterated `→L` codomains, but the
    abstract `G` sidesteps it, and the concrete instances (already witnessed by `hF`) discharge on
    application. -/
theorem hasFDerivAt_scalar_clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Θ : G →L[ℝ] ℝ) (F : Point n → G) (X : Point n →L[ℝ] G) (hF : HasFDerivAt F X 0) :
    HasFDerivAt (fun x => Θ (F x)) (Θ.comp X) 0 :=
  Θ.hasFDerivAt.comp (0 : Point n) hF

set_option maxHeartbeats 1600000 in
/-- **(α2) — the second jet of the exp-map Jacobian component (the SLOT-MATCH).**  The mixed second
    partial of the scalar Jacobian component `x ↦ (D exp_p x·e_i)_a` at `0` is the `a`-component of the
    closed Rung-3 third-jet value `expJetD3(0)` on the basis triple `(e_l, e_m, e_i)`:
      `∂_l∂_m (D exp_p·e_i)_a(0) = [ (1/6)·(rncD3Block + rncCrossBlock ×3) ]_a`.
    Proof (the iterated-`pd` ↔ `fderiv` transport, via a SCALAR composition to dodge the nested-CLM
    instance wall): the first partial `∂_m(D exp_p·e_i)_a` equals `Θ(D²exp_p ·)` for the scalar CLM
    `Θ T = (T e_m e_i)_a` (chain rule: `fderiv φ = Λ ∘ D²exp_p`, `Λ T = T(e_i)_a`, then contract `e_m`);
    differentiating that scalar composite at `0` (`hasFDerivAt_scalar_clm_comp` with the abstract
    intermediate space) gives `Θ ∘ D(fun w => D²exp_p w)(0) = Θ ∘ expJetD3(0)Φ`
    (`hasFDerivAt_fderiv2_expMap_zero` internals), pinned to the affine propagator `Φ = id + t·linF`
    (`expFund_zero_eq`) and read off in closed Christoffel form by `expJetD3_zero_closed`. -/
theorem pd2_jacobian_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a l m : Fin n) :
    pd (fun y => pd (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) m y) l 0
      = ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
          + rncCrossBlock g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
          + rncCrossBlock g gi p (Pi.single m 1) (Pi.single i 1) (Pi.single l 1)
          + rncCrossBlock g gi p (Pi.single l 1) (Pi.single i 1) (Pi.single m 1))) a := by
  -- the affine `v = 0` propagator `Φ`, its ODE data, and the closed third-jet HasFDerivAt.
  have h0lt : ‖(0 : Point n)‖ < expRho g gi hC p := by
    rw [norm_zero]; exact expRho_pos g gi hC p
  obtain ⟨Φ, hΦ0, hΦd, hFD⟩ := hasFDerivAt_expMap g gi hC p 0 h0lt
  have hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1) := fun t ht => (hΦd t ht).continuousWithinAt
  have hΦeq := expFund_zero_eq g gi hC p Φ hΦ0 hΦd
  set X : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
    expJetD3 g gi hC p 0 Φ h0lt.le hΦcont with hXdef
  have hfd2 : HasFDerivAt (fun w => fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) w) X 0 :=
    expMap_fderiv2_hasFDerivAt g gi hC p 0 Φ h0lt hΦ0 hΦcont hΦd hFD.fderiv
  -- the evaluation-then-projection CLMs: `Λ T = T(e_i)_a` and `Θ T = (T e_m e_i)_a`.
  set Λ : (Point n →L[ℝ] Point n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a).comp (ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1))
    with hΛdef
  set Θ : (Point n →L[ℝ] (Point n →L[ℝ] Point n)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a).comp
      ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single i 1)).comp
        (ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n) (Pi.single m 1))) with hΘdef
  have hball : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ nhds (0 : Point n) :=
    Metric.ball_mem_nhds 0 (expRho_pos g gi hC p)
  -- `∂_m(D exp_p·e_i)_a = Θ(D² exp_p)` near `0` (chain rule + `e_m`-contraction).
  have hΘeq : (fun y => pd (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) m y)
      =ᶠ[nhds 0] (fun y => Θ (fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) y)) := by
    filter_upwards [hball] with y hy
    have hGy : DifferentiableAt ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) y :=
      ((contDiffOn_fderiv_expMap g gi hC p).differentiableOn (by norm_num)).differentiableAt
        (Metric.isOpen_ball.mem_nhds hy)
    have hΛcomp : HasFDerivAt (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
        (Λ.comp (fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) y)) y := by
      refine (Λ.hasFDerivAt.comp y hGy.hasFDerivAt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [hΛdef, Function.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply]
    rw [pd_eq_fderiv _ m y hΛcomp.differentiableAt, hΛcomp.fderiv]
    simp only [hΘdef, hΛdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.proj_apply]
  -- differentiate the scalar composite at `0` via the abstract-`G` helper.
  have hstep : HasFDerivAt (fun y => Θ (fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) y))
      (Θ.comp X) 0 :=
    hasFDerivAt_scalar_clm_comp Θ
      (fun w => fderiv ℝ (fun z => fderiv ℝ (expMap g gi hC p) z) w) X hfd2
  rw [pd_congr_nhds l 0 hΘeq, pd_eq_fderiv _ l 0 hstep.differentiableAt, hstep.fderiv]
  -- pull `Θ` through the evaluation, then substitute the closed third-jet value.
  simp only [hΘdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.proj_apply]
  rw [hXdef, expJetD3_zero_closed g gi hC p Φ h0lt.le hΦcont hΦeq
    (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)]

/-- **`C²`-at-`0` regularity of the metric-along-exp factor `x ↦ g(exp_p x)_{ab}`.**  Restriction of
    the ball-wide `ContDiffOn 2` (composition of the `C^∞` metric with the `C³` exp map) to the germ. -/
theorem contDiffAt2_metric_comp_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (a b : Fin n) :
    ContDiffAt ℝ 2 (fun x => g (expMap g gi hC p x) a b) 0 :=
  (((hg a b).of_le le_top).comp_contDiffOn
      ((expMap_contDiffOn_three g gi hC p).of_le (by norm_num))).contDiffAt
    (Metric.ball_mem_nhds 0 (expRho_pos g gi hC p))

/-- **`C²`-at-`0` regularity of the exp-map Jacobian component `x ↦ (D exp_p x·e_i)_a`.**  Restriction
    of the ball-wide `ContDiffOn 2` (`contDiffOn_fderiv_expMap_component`) to the germ. -/
theorem contDiffAt2_jacobian_component_expMap_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (i a : Fin n) :
    ContDiffAt ℝ 2 (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a) 0 :=
  (contDiffOn_fderiv_expMap_component g gi hC p i a).contDiffAt
    (Metric.ball_mem_nhds 0 (expRho_pos g gi hC p))

set_option maxHeartbeats 1600000 in
/-- **FLOOR — the closed nine-term second jet of one `(a,b)` summand of `g̃`.**  The mixed second
    partial of the triple product `g(exp·)_{ab}·(D exp·e_i)_a·(D exp·e_j)_b` at `0`, with every factor
    jet substituted by its landed RNC closed form: the value `g(p)_{ab}`, the Kronecker `J(0)=δ`, the
    first jet `∂J(0)=½(−Γ−Γ)` (`pd_jacobian_expMap_zero`), the metric first jet `∂g(p)`
    (`pd_metric_comp_expMap_zero`), the metric Hessian (α1, `pd2_metric_comp_expMap_zero`) and the
    Jacobian second jet (α2, `pd2_jacobian_expMap_zero`).  Pure `rw` + `ring`; the one-order-up analogue
    of `pd_expPullback_summand_zero`. -/
theorem pd2_expPullback_summand_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l m a b : Fin n) :
    pd (fun y => pd (fun x =>
          g (expMap g gi hC p x) a b
          * (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a
          * (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) m y) l 0
      = (pd (fun z => pd (fun y => g y a b) m z) l p
            + ∑ c, pd (fun y => g y a b) c p
                * (1 / 2 * (-christoffel g gi c m l p - christoffel g gi c l m p)))
          * (Pi.single i 1 : Point n) a * (Pi.single j 1 : Point n) b
        + pd (fun y => g y a b) m p
            * (1 / 2 * (-christoffel g gi a i l p - christoffel g gi a l i p))
            * (Pi.single j 1 : Point n) b
        + pd (fun y => g y a b) m p * (Pi.single i 1 : Point n) a
            * (1 / 2 * (-christoffel g gi b j l p - christoffel g gi b l j p))
        + pd (fun y => g y a b) l p
            * (1 / 2 * (-christoffel g gi a i m p - christoffel g gi a m i p))
            * (Pi.single j 1 : Point n) b
        + g p a b
            * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single m 1) (Pi.single i 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single i 1) (Pi.single m 1))) a)
            * (Pi.single j 1 : Point n) b
        + g p a b
            * (1 / 2 * (-christoffel g gi a i m p - christoffel g gi a m i p))
            * (1 / 2 * (-christoffel g gi b j l p - christoffel g gi b l j p))
        + pd (fun y => g y a b) l p * (Pi.single i 1 : Point n) a
            * (1 / 2 * (-christoffel g gi b j m p - christoffel g gi b m j p))
        + g p a b
            * (1 / 2 * (-christoffel g gi a i l p - christoffel g gi a l i p))
            * (1 / 2 * (-christoffel g gi b j m p - christoffel g gi b m j p))
        + g p a b * (Pi.single i 1 : Point n) a
            * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single m 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single m 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single m 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single m 1))) b) := by
  rw [pd_pd_mul3_zero
      (fun x => g (expMap g gi hC p x) a b)
      (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single i 1) a)
      (fun x => (fderiv ℝ (expMap g gi hC p) x) (Pi.single j 1) b) l m
      (contDiffAt2_metric_comp_expMap_zero g gi hC p hg a b)
      (contDiffAt2_jacobian_component_expMap_zero g gi hC p i a)
      (contDiffAt2_jacobian_component_expMap_zero g gi hC p j b)]
  simp only [expMap_apply_zero, jacobian_component_expMap_at_zero,
    pd_metric_comp_expMap_zero g gi hC p hg, pd_jacobian_expMap_zero,
    pd2_metric_comp_expMap_zero g gi hC p hg, pd2_jacobian_expMap_zero]

set_option maxHeartbeats 1600000 in
/-- **FLOOR — the CLOSED `∂²g̃(0)` twice-Leibniz form.**  Assembling `pd2_expPullbackMetric_at_zero`
    (the mixed second partial commutes with the finite `∑_{a,b}`) with the per-summand closed nine-term
    `pd2_expPullback_summand_zero`, the pullback metric's second jet at the centre is the explicit double
    sum of the nine substituted-jet terms.  This is the closed `∂²g̃(0)` the radial identity consumes;
    every factor jet is now in closed Christoffel / `rncD3Block`+`rncCrossBlock` form. -/
theorem expPullbackMetric_pd2_closed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (i j l m : Fin n) :
    pd (fun y => pd (fun x => expPullbackMetric g gi hC p x i j) m y) l 0
      = ∑ a, ∑ b,
          ((pd (fun z => pd (fun y => g y a b) m z) l p
              + ∑ c, pd (fun y => g y a b) c p
                  * (1 / 2 * (-christoffel g gi c m l p - christoffel g gi c l m p)))
            * (Pi.single i 1 : Point n) a * (Pi.single j 1 : Point n) b
          + pd (fun y => g y a b) m p
              * (1 / 2 * (-christoffel g gi a i l p - christoffel g gi a l i p))
              * (Pi.single j 1 : Point n) b
          + pd (fun y => g y a b) m p * (Pi.single i 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b j l p - christoffel g gi b l j p))
          + pd (fun y => g y a b) l p
              * (1 / 2 * (-christoffel g gi a i m p - christoffel g gi a m i p))
              * (Pi.single j 1 : Point n) b
          + g p a b
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single i 1) (Pi.single m 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single m 1) (Pi.single i 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single i 1) (Pi.single m 1))) a)
              * (Pi.single j 1 : Point n) b
          + g p a b
              * (1 / 2 * (-christoffel g gi a i m p - christoffel g gi a m i p))
              * (1 / 2 * (-christoffel g gi b j l p - christoffel g gi b l j p))
          + pd (fun y => g y a b) l p * (Pi.single i 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b j m p - christoffel g gi b m j p))
          + g p a b
              * (1 / 2 * (-christoffel g gi a i l p - christoffel g gi a l i p))
              * (1 / 2 * (-christoffel g gi b j m p - christoffel g gi b m j p))
          + g p a b * (Pi.single i 1 : Point n) a
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single m 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single j 1) (Pi.single m 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single m 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single m 1))) b)) := by
  rw [pd2_expPullbackMetric_at_zero g gi hC p hg i j l m]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    pd2_expPullback_summand_zero g gi hC p hg i j l m a b

/-!
### (β) STEP 3 — the metric-Christoffel differentiation reduction (the analytic half of the bridge)

The first partial of the pullback Christoffel at the centre reduces, via `∂g̃(0) = 0` and the value of
the inverse metric at `0`, to `½ g⁻¹(p)^{iα}·(∂²g̃ combination)` — the pure second-jet input the `rncDΓ`
match consumes.  This is the load-bearing analytic step of `(β)`: it needs only that the supplied
pullback inverse `gtildeInv` restricts at `0` to `gi p` and is differentiable there (`∂g̃⁻¹(0)` never
appears, because it multiplies the vanishing `∂g̃(0)`).
-/

set_option maxHeartbeats 1600000 in
/-- **(β), analytic half — `∂_l Γ̃^i_{jk}(0)` in terms of the pullback's second jet.**  For the pullback
    metric `g̃ = exp_p^* g` and ANY inverse field `gtildeInv` that equals `gi p` at the centre and is
    differentiable there, the first derivative of the pullback Christoffel at `0` is
      `∂_l Γ̃^i_{jk}(0) = ½ ∑_α g⁻¹(p)^{iα}·(∂_l∂_j g̃_{αk} + ∂_l∂_k g̃_{αj} − ∂_l∂_α g̃_{jk})(0)`.
    Proof: unfold `christoffel`, pull `∂_l` through the `½·∑_α` (`pd_const_mul`/`pd_sum`) and the
    Leibniz product `gtildeInv·(∂g̃-bracket)` (`pd_mul`); the `∂g̃⁻¹·(∂g̃-bracket)` term vanishes because
    `∂g̃(0)=0` (`pd_expPullbackMetric_at_zero`), and the surviving `gtildeInv(0)=gi p` factor multiplies
    the second-jet bracket `∂_l(∂g̃-bracket)(0)` (`pd_add`/`pd_sub`, with the `C²`-localised
    second-order partial differentiability `PdiffAt_pd_zero_of_contDiffAt2`). -/
theorem pd_christoffel_expPullback_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (gtildeInv : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi0 : ∀ μ α, gtildeInv 0 μ α = gi p μ α)
    (hgi_diff : ∀ μ α, DifferentiableAt ℝ (fun x => gtildeInv x μ α) 0)
    (i j k l : Fin n) :
    pd (fun x => christoffel (expPullbackMetric g gi hC p) gtildeInv i j k x) l 0
      = (1 / 2) * ∑ α, gi p i α *
          (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
            + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
            - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0) := by
  -- `C²`-at-`0` regularity of each pullback-metric component.
  have hC2 : ∀ μ ν, ContDiffAt ℝ 2 (fun x => expPullbackMetric g gi hC p x μ ν) 0 :=
    fun μ ν => contDiffAt2_expPullbackMetric_zero g gi hC p hg μ ν
  -- second-order partial differentiability of the three bracket pieces.
  have hpT1 : ∀ α, PdiffAt (fun x => pd (fun y => expPullbackMetric g gi hC p y α k) j x) l 0 :=
    fun α => PdiffAt_pd_zero_of_contDiffAt2 _ j l (hC2 α k)
  have hpT2 : ∀ α, PdiffAt (fun x => pd (fun y => expPullbackMetric g gi hC p y α j) k x) l 0 :=
    fun α => PdiffAt_pd_zero_of_contDiffAt2 _ k l (hC2 α j)
  have hpT3 : ∀ α, PdiffAt (fun x => pd (fun y => expPullbackMetric g gi hC p y j k) α x) l 0 :=
    fun α => PdiffAt_pd_zero_of_contDiffAt2 _ α l (hC2 j k)
  -- the bracket `Br α` is partially differentiable at `0`.
  have hpBr : ∀ α, PdiffAt (fun x => pd (fun y => expPullbackMetric g gi hC p y α k) j x
      + pd (fun y => expPullbackMetric g gi hC p y α j) k x
      - pd (fun y => expPullbackMetric g gi hC p y j k) α x) l 0 :=
    fun α => ((hpT1 α).add (hpT2 α)).sub (hpT3 α)
  -- each `α`-summand is partially differentiable at `0`.
  have hpGi : ∀ α, PdiffAt (fun x => gtildeInv x i α) l 0 :=
    fun α => pdiffAt_of_differentiableAt _ l 0 (hgi_diff i α)
  have hpS : ∀ α, PdiffAt (fun x => gtildeInv x i α
      * (pd (fun y => expPullbackMetric g gi hC p y α k) j x
        + pd (fun y => expPullbackMetric g gi hC p y α j) k x
        - pd (fun y => expPullbackMetric g gi hC p y j k) α x)) l 0 :=
    fun α => (hpGi α).mul (hpBr α)
  -- per-`α` Leibniz value.
  have key : ∀ α, pd (fun x => gtildeInv x i α
        * (pd (fun y => expPullbackMetric g gi hC p y α k) j x
          + pd (fun y => expPullbackMetric g gi hC p y α j) k x
          - pd (fun y => expPullbackMetric g gi hC p y j k) α x)) l 0
      = gi p i α *
          (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
            + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
            - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0) := by
    intro α
    rw [pd_mul _ _ l 0 (hpGi α) (hpBr α)]
    have hBr0 : (pd (fun y => expPullbackMetric g gi hC p y α k) j 0
        + pd (fun y => expPullbackMetric g gi hC p y α j) k 0
        - pd (fun y => expPullbackMetric g gi hC p y j k) α 0) = 0 := by
      rw [pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg α k j,
        pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg α j k,
        pd_expPullbackMetric_at_zero g gi hC p hsymm hinv hg j k α]
      ring
    rw [hBr0, mul_zero, zero_add, hgi0]
    congr 1
    rw [pd_sub _ _ l 0 ((hpT1 α).add (hpT2 α)) (hpT3 α), pd_add _ _ l 0 (hpT1 α) (hpT2 α)]
  simp only [christoffel]
  rw [pd_const_mul _ _ l 0 (PdiffAt_sum Finset.univ _ l 0 (fun α _ => hpS α)),
    pd_sum Finset.univ _ l 0 (fun α _ => hpS α)]
  congr 1
  exact Finset.sum_congr rfl (fun α _ => key α)

/-!
### (β1) — THE SMOOTH PULLBACK INVERSE `expPullbackMetricInv` (the guaranteed floor)

We build the matrix inverse of the pullback metric `g̃(x)` near `0`, using the operator ring
`Point n →L[ℝ] Point n` (which carries the standard global `NormedRing`/`NormedAlgebra`/`CompleteSpace`
instances, hence `HasSummableGeomSeries`, avoiding all matrix-norm-instance headaches).  We assemble the
metric matrix `g̃(x)` into a continuous linear operator `matToCLM (g̃ x)`, invert it with `Ring.inverse`
(which is `C^∞` at the invertible point `matToCLM (g p)`, `contDiffAt_ringInverse`), and read off the
`(μ,α)` entry.  The value at `0` is `gi p` (`matToCLM (g p)` is a unit with inverse `matToCLM (gi p)`),
and the entry field is differentiable at `0` (`Ring.inverse` composed with the differentiable operator
field, then evaluated).  These two facts discharge the `hgi0`/`hgi_diff` hypotheses of
`pd_christoffel_expPullback_zero`.
-/

/-- The elementary operator `e_{ab} : v ↦ (v b) • e_a` on `Point n`
    (`e_a = Pi.single a 1`).  Its matrix is the `(a,b)` matrix unit. -/
noncomputable def elemCLM (a b : Fin n) : Point n →L[ℝ] Point n :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) b).smulRight (Pi.single a (1 : ℝ))

@[simp] theorem elemCLM_apply (a b : Fin n) (v : Point n) (i : Fin n) :
    elemCLM a b v i = v b * (Pi.single a (1 : ℝ) : Point n) i := by
  simp only [elemCLM, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Assemble a matrix `M : Fin n → Fin n → ℝ` into the continuous linear operator `v ↦ M ·ᵥ v`
    on `Point n` (as a finite sum of scaled matrix units, so it is manifestly `C^∞` in `M`). -/
noncomputable def matToCLM (M : Fin n → Fin n → ℝ) : Point n →L[ℝ] Point n :=
  ∑ a, ∑ b, M a b • elemCLM a b

/-- The operator `matToCLM M` acts as the matrix `M`: `(matToCLM M · v)_i = ∑_b M_{ib} v_b`. -/
theorem matToCLM_apply (M : Fin n → Fin n → ℝ) (v : Point n) (i : Fin n) :
    matToCLM M v i = ∑ b, M i b * v b := by
  simp only [matToCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, elemCLM_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- If `M` is a matrix inverse of `N` (`∑_b M_{ib} N_{bc} = δ_{ic}`), then `matToCLM M ∘ matToCLM N = 1`
    as operators.  (The operator ring's `*` is composition.) -/
theorem matToCLM_mul_eq_one (M N : Fin n → Fin n → ℝ)
    (h : ∀ i c, (∑ b, M i b * N b c) = if i = c then (1 : ℝ) else 0) :
    matToCLM M * matToCLM N = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  funext i
  rw [matToCLM_apply]
  calc ∑ b, M i b * (matToCLM N v b)
      = ∑ b, M i b * (∑ c, N b c * v c) := by
        refine Finset.sum_congr rfl fun b _ => by rw [matToCLM_apply]
    _ = ∑ b, ∑ c, M i b * (N b c * v c) := by simp only [Finset.mul_sum]
    _ = ∑ c, ∑ b, M i b * (N b c * v c) := Finset.sum_comm
    _ = ∑ c, (∑ b, M i b * N b c) * v c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ c, (if i = c then (1 : ℝ) else 0) * v c := by
        refine Finset.sum_congr rfl fun c _ => by rw [h i c]
    _ = v i := by
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The inverse metric `gi p` is a LEFT inverse of `g p` too: `∑_b (gi p)_{ib} (g p)_{bc} = δ_{ic}`.
    (For square matrices over a commutative ring a right inverse is a two-sided inverse,
    `Matrix.mul_eq_one_comm`.) -/
theorem gi_mul_g_eq (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0) (i c : Fin n) :
    (∑ b, gi p i b * g p b c) = if i = c then (1 : ℝ) else 0 := by
  have hR : (Matrix.of (g p) : Matrix (Fin n) (Fin n) ℝ) * Matrix.of (gi p) = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Matrix.of_apply] using hinv a b
  have hL : (Matrix.of (gi p) : Matrix (Fin n) (Fin n) ℝ) * Matrix.of (g p) = 1 :=
    mul_eq_one_comm.mp hR
  have h2 : (Matrix.of (gi p) * Matrix.of (g p) : Matrix (Fin n) (Fin n) ℝ) i c
      = (1 : Matrix (Fin n) (Fin n) ℝ) i c := by rw [hL]
  rw [Matrix.mul_apply, Matrix.one_apply] at h2
  simpa only [Matrix.of_apply] using h2

/-- **The smooth pullback inverse metric** `g̃⁻¹`, in component form: the `(μ,α)` entry of the operator
    inverse of `matToCLM (g̃ x)`.  Near `0` (where `g̃(0) = g(p)` is invertible) this is the genuine
    matrix inverse of the pullback metric `g̃(x)`. -/
noncomputable def expPullbackMetricInv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (x : Point n) (μ α : Fin n) : ℝ :=
  (Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b))) (Pi.single α (1 : ℝ)) μ

/-- `matToCLM (g p)` is a unit in the operator ring, with inverse `matToCLM (gi p)`. -/
noncomputable def metricCLMUnit0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0) :
    (Point n →L[ℝ] Point n)ˣ where
  val := matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b)
  inv := matToCLM (gi p)
  val_inv := matToCLM_mul_eq_one _ _ (by
    intro i c; simp only [expPullbackMetric_at_zero]; exact hinv i c)
  inv_val := matToCLM_mul_eq_one _ _ (by
    intro i c; simp only [expPullbackMetric_at_zero]; exact gi_mul_g_eq g gi p hinv i c)

/-- `Ring.inverse (matToCLM (g̃ 0)) = matToCLM (gi p)` (the operator inverse of `g̃(0) = g(p)`). -/
theorem ringInverse_metricCLM_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0) :
    Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b)) = matToCLM (gi p) := by
  rw [show (matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b))
        = ↑(metricCLMUnit0 g gi hC p hinv) from rfl, Ring.inverse_unit]
  rfl

/-- **(β1)a — the 0-jet value of the pullback inverse.**  `g̃⁻¹(0) = g⁻¹(p) = gi p`. -/
theorem expPullbackMetricInv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0) (μ α : Fin n) :
    expPullbackMetricInv g gi hC p 0 μ α = gi p μ α := by
  simp only [expPullbackMetricInv]
  rw [ringInverse_metricCLM_zero g gi hC p hinv, matToCLM_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **(β1)b — differentiability of the pullback inverse at `0`.**  Each entry `x ↦ g̃⁻¹(x)_{μα}` is
    differentiable at `0`: `matToCLM (g̃ ·)` is differentiable (its entries are `C²`), `matToCLM (g̃ 0)`
    is invertible, `Ring.inverse` is `C^∞` at a unit (`contDiffAt_ringInverse`), and entry-evaluation is
    continuous-linear. -/
theorem expPullbackMetricInv_differentiableAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (μ α : Fin n) :
    DifferentiableAt ℝ (fun x => expPullbackMetricInv g gi hC p x μ α) 0 := by
  -- the operator field `x ↦ matToCLM (g̃ x)` is differentiable at `0` (its entries are `C²`).
  have hmet_diff : DifferentiableAt ℝ
      (fun x => matToCLM (fun a b => expPullbackMetric g gi hC p x a b)) 0 := by
    show DifferentiableAt ℝ
      (fun x => ∑ a, ∑ b, expPullbackMetric g gi hC p x a b • elemCLM a b) 0
    apply DifferentiableAt.fun_sum
    intro a _
    apply DifferentiableAt.fun_sum
    intro b _
    exact ((contDiffAt2_expPullbackMetric_zero g gi hC p hg a b).differentiableAt
      (by norm_num)).smul (differentiableAt_const _)
  -- `Ring.inverse` is `C^∞` at the unit `matToCLM (g̃ 0)`.
  have hinv_cd : ContDiffAt ℝ (1 : WithTop ℕ∞) Ring.inverse
      (matToCLM (fun a b => expPullbackMetric g gi hC p 0 a b)) :=
    contDiffAt_ringInverse ℝ (metricCLMUnit0 g gi hC p hinv)
  have hcomp := (hinv_cd.differentiableAt (by norm_num)).comp 0 hmet_diff
  have hfull := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ).differentiableAt).comp
    0 (((ContinuousLinearMap.apply ℝ (Point n)
      (Pi.single α (1 : ℝ) : Point n)).differentiableAt).comp 0 hcomp)
  have heq : (fun x => expPullbackMetricInv g gi hC p x μ α)
      = fun x => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ)
          ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single α (1 : ℝ) : Point n))
            (Ring.inverse (matToCLM (fun a b => expPullbackMetric g gi hC p x a b)))) := by
    funext x
    simp only [expPullbackMetricInv, ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply]
  rw [heq]
  exact hfull

/-- **(β2), STEP 1 — the pullback Christoffel derivative, with the smooth inverse discharged.**
    Instantiating `pd_christoffel_expPullback_zero` at `gtildeInv := expPullbackMetricInv` (the genuine
    matrix inverse of `g̃`, built in (β1)) and discharging its `hgi0`/`hgi_diff` hypotheses by
    `expPullbackMetricInv_zero` / `expPullbackMetricInv_differentiableAt`:
      `∂_l Γ̃^i_{jk}(0) = ½ ∑_α g⁻¹(p)^{iα}·(∂_l∂_j g̃_{αk} + ∂_l∂_k g̃_{αj} − ∂_l∂_α g̃_{jk})(0)`.
    This is the fully-instantiated analytic half of the bridge — the LHS is now the derivative of the
    ACTUAL Christoffel symbol of the pullback metric `g̃` (with its own inverse), no carried inverse
    field.  The remaining step to `rnc_christoffel_linearJet` is the pure `rncDΓ` `Finset` algebra
    (substitute the closed `∂²g̃(0)` and match `rncDΓ` via `christoffel_lower` + `a3rawArr_contract_eq_a3`). -/
theorem pd_christoffel_expPullbackInv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (i j k l : Fin n) :
    pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i j k x) l 0
      = (1 / 2) * ∑ α, gi p i α *
          (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
            + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
            - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0) :=
  pd_christoffel_expPullback_zero g gi hC p (expPullbackMetricInv g gi hC p) hsymm hinv hg
    (expPullbackMetricInv_zero g gi hC p hinv)
    (expPullbackMetricInv_differentiableAt g gi hC p hinv hg) i j k l

/-!
### (β3) — THE CYCLIC NORMAL-COORDINATE GAUGE (the `heat_a1_of_gauge` consumer)

The structural half of the endgame: `g̃` is symmetric (so its Christoffel symbol is lower-symmetric),
and the six-fold `GaugeJet` (symmetrized normal-coordinate gauge, `QIQTH.RNCGauge.GaugeJet`) collapses,
via that lower-symmetry, to the three-term CYCLIC gauge that `heat_a1_of_gauge` consumes.
-/

open QIQTH.RNCGauge in
/-- **The pullback metric is symmetric.**  `g̃_{ij} = g̃_{ji}` (as component fields), for a symmetric
    ambient metric `g`.  Immediate from the tensorial pullback formula: swapping `i,j` swaps the two
    Jacobian factors, and `∑_{a,b} g_{ab} J_j^a J_i^b = ∑_{a,b} g_{ab} J_i^a J_j^b` by relabelling the
    dummy pair and using `g_{ab} = g_{ba}`. -/
theorem expPullbackMetric_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (x : Point n) (i j : Fin n) :
    expPullbackMetric g gi hC p x i j = expPullbackMetric g gi hC p x j i := by
  simp only [expPullbackMetric]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsymm (expMap g gi hC p x) a b]
  ring

/-- **The pullback Christoffel derivative is symmetric in its lower pair.**  Since `g̃` is symmetric,
    `Γ̃^i_{jk} = Γ̃^i_{kj}` (`christoffel_symm`), hence the same holds after `∂_l` at `0`. -/
theorem pd_christoffel_expPullbackInv_lower_symm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a) (i j k l : Fin n) :
    pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i j k x) l 0
      = pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i k j x) l 0 := by
  have hfun : (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
        i j k x)
      = (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
        i k j x) := by
    funext x
    exact christoffel_symm (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
      (fun y a b => expPullbackMetric_symm g gi hC p hsymm y a b) i j k x
  rw [hfun]

open QIQTH.RNCGauge in
/-- **From the six-fold gauge to the three-fold cyclic gauge.**  For ANY Christoffel first-jet array
    `dΓ` that is symmetric in its lower pair (`dΓ l i j k = dΓ l i k j`) and satisfies the symmetrized
    six-fold `GaugeJet`, the three-term cyclic sum vanishes:
      `dΓ a i b c + dΓ b i c a + dΓ c i a b = 0`.
    Proof: lower-symmetry pairs the six permutation terms into `2×` the cyclic sum. -/
theorem cyclic_of_gaugeJet_lower_symm (dΓ : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hsym : ∀ l i j k, dΓ l i j k = dΓ l i k j) (hgauge : GaugeJet dΓ) (i a b c : Fin n) :
    dΓ a i b c + dΓ b i c a + dΓ c i a b = 0 := by
  have h := hgauge i a b c
  rw [hsym a i c b, hsym b i a c, hsym c i b a] at h
  linarith

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

  **STEP 3 — the BRIDGE `pd (christoffel g̃)(0) = rncDΓ`.**  Now decomposed into (α1)+(α2) [LANDED] +
  (β)-analytic-half [LANDED] + the pure `rncDΓ` algebra [remaining].
    (α1) **`pd2_metric_comp_expMap_zero` — LANDED (axiom-clean).**  The chain-rule Hessian of `g∘exp` at
        the centre: `∂_l∂_m(g(exp·)_{ab})(0) = ∂_l∂_m g_{ab}(p) + ∑_c ∂_c g_{ab}(p)·½(−Γ^c_{ml} − Γ^c_{lm})`.
        Proof: near `0`, `∂_m(g∘exp)` is the basis-expanded product sum `∑_c ∂_c g(exp·)·(D exp·e_m)_c`
        (`clm_functional_pi_expand`); differentiating (`pd_sum`/`pd_mul`), the `∂_c g(exp·)` factor pulls
        back to `∂_l∂_c g(p)` (`pd_comp_expMap_zero`, Kronecker-collapsed by `(D exp 0·e_m)_c = δ_{mc}`)
        and the Jacobian factor gives its RNC first jet (`pd_jacobian_expMap_zero`).
    (α2) **`pd2_jacobian_expMap_zero` — LANDED (axiom-clean).**  The SLOT-MATCH:
        `∂_l∂_m (D exp·e_i)_a(0) = [ (1/6)·(rncD3Block + rncCrossBlock ×3) ]_a`.  Proof (via a SCALAR
        composition to dodge the nested-CLM `NormedSpace`-instance wall): `∂_m(D exp·e_i)_a = Θ(D²exp·)`
        for the scalar CLM `Θ T = (T e_m e_i)_a` (chain rule + `e_m`-contraction); differentiating that
        scalar composite (`hasFDerivAt_scalar_clm_comp` with abstract intermediate space) gives
        `Θ ∘ expJetD3(0)Φ` (`hasFDerivAt_fderiv2_expMap_zero`), pinned to `Φ = id + t·linF`
        (`expFund_zero_eq`) and read off by `expJetD3_zero_closed`.
    (β-analytic) **`pd_christoffel_expPullback_zero` — LANDED (axiom-clean).**  For any inverse field
        `gtildeInv` with `gtildeInv(0) = gi p` (differentiable at `0`),
        `∂_l Γ̃^i_{jk}(0) = ½ ∑_α g⁻¹(p)^{iα}·(∂_l∂_j g̃_{αk} + ∂_l∂_k g̃_{αj} − ∂_l∂_α g̃_{jk})(0)`.  The
        `∂g̃⁻¹` terms drop because they multiply `∂g̃(0)=0`; the surviving `gi p` factor multiplies the
        second-jet bracket.
  **THE REMAINING (β) RESIDUAL — the pure `rncDΓ` algebra.  (β1) LANDED; (β2) CHECKPOINTED.**
    (β1) **LANDED axiom-clean** — the smooth pullback inverse `expPullbackMetricInv` (the `(μ,α)` entry of
         the operator inverse `Ring.inverse (matToCLM g̃(x))` in the ring `Point n →L[ℝ] Point n`) with
         `expPullbackMetricInv_zero` (`g̃⁻¹(0) = gi p`, via `matToCLM (g p)` being a unit with inverse
         `matToCLM (gi p)`, `gi_mul_g_eq` supplying the left-inverse from `mul_eq_one_comm`) and
         `expPullbackMetricInv_differentiableAt` (`Ring.inverse` is `C^∞` at the unit,
         `contDiffAt_ringInverse`, composed with the differentiable operator field whose entries are
         `C²`).  These discharge `hgi0`/`hgi_diff`, giving **`pd_christoffel_expPullbackInv_zero`** — the
         fully-instantiated analytic half:
           `∂_l Γ̃^i_{jk}(0) = ½ ∑_α g⁻¹(p)^{iα}·(∂_l∂_j g̃_{αk} + ∂_l∂_k g̃_{αj} − ∂_l∂_α g̃_{jk})(0)`,
         with `Γ̃` the ACTUAL Christoffel symbol of `g̃` paired with its own inverse `g̃⁻¹`.
    (β3) **STRUCTURAL HALF LANDED axiom-clean (`import QIQTH.RNCGauge`/`RNCGaugeExp` now added).**  Three
         reusable lemmas reduce the full cyclic gauge to a SINGLE scalar identity:
           - `expPullbackMetric_symm` : `g̃_{ij} = g̃_{ji}` (from `g` symmetric) — so `g̃`'s Christoffel is
             lower-symmetric (`christoffel_symm`).
           - `pd_christoffel_expPullbackInv_lower_symm` : `∂_l Γ̃^i_{jk}(0) = ∂_l Γ̃^i_{kj}(0)`.
           - `cyclic_of_gaugeJet_lower_symm` : for ANY lower-symmetric first-jet array satisfying the
             six-fold `QIQTH.RNCGauge.GaugeJet`, the three-term CYCLIC gauge vanishes (the six permutations
             pair into `2×` the cyclic sum).
         Hence the target `heat_a1_of_gauge` consumer
           `∂_a Γ̃^i_{bc}(0) + ∂_b Γ̃^i_{ca}(0) + ∂_c Γ̃^i_{ab}(0) = 0`
         follows from `cyclic_of_gaugeJet_lower_symm` applied to `dΓ := fun l i j k => pd (christoffel g̃
         g̃⁻¹ i j k) l 0`, whose lower-symmetry is `pd_christoffel_expPullbackInv_lower_symm` — leaving the
         SOLE remaining obligation `GaugeJet dΓ`.  By `QIQTH.RNCGauge.gaugeJet_of_diag`, `GaugeJet dΓ`
         reduces to the pullback RNC RADIAL-GEODESIC identity (a single scalar per `(v,i)`):
           **`∑_l ∑_j ∑_k pd (fun x => christoffel g̃ g̃⁻¹ i j k x) l 0 · v^l · v^j · v^k = 0`.**
    (β3′) **THE RADIAL REDUCTION + THE MECHANICAL CYCLIC-GAUGE CAPSTONE — NOW LANDED axiom-clean
         (`[propext, Classical.choice, Quot.sound]`).**  Two lemmas at the very end of this file:
           - `dGammaDiag_pd_christoffel_expPullbackInv_reduce` : substituting the analytic half
             `pd_christoffel_expPullbackInv_zero` into the radial diagonal `dGammaDiag` and using the
             `j ↔ k` contraction symmetry, the radial-geodesic contraction becomes the CRISP pure
             second-jet form
               `dGammaDiag (…pd Γ̃…) v i
                  = ½ ∑_α gi(p)^{iα}·(2·⟨∂_l∂_j g̃_{αk}⟩ − ⟨∂_l∂_α g̃_{jk}⟩)`,
             where `⟨·⟩ := ∑_{l,j,k} · v^l v^j v^k`.  (Pure `Finset` algebra; helper `pull_alpha_out`.)
           - `gauge_pd_christoffel_expPullbackInv_zero` : GIVEN the radial identity `hrad` (i.e.
             `expPullback_radial_gauge`, the LHS of the reduction set to `0`), the full three-term CYCLIC
             normal-coordinate gauge for `g̃`
               `∂_c Γ̃^i_{ab}(0) + ∂_a Γ̃^i_{bc}(0) + ∂_b Γ̃^i_{ca}(0) = 0`
             follows MECHANICALLY (`gaugeJet_of_diag` ⟹ six-fold `GaugeJet`, then
             `pd_christoffel_expPullbackInv_lower_symm` + `cyclic_of_gaugeJet_lower_symm`).  This is
             `heat_a1_of_gauge`'s `hgauge` for the pullback metric, discharged MODULO the single
             hypothesis `hrad`.  So the endgame is now wired end-to-end: the ONLY missing input is the
             radial scalar identity below.
    (β2) **PARTIALLY LANDED — the closed `∂²g̃(0)` FLOOR is now built; the contraction/cancellation
         remains.**  NEW axiom-clean lemmas (`[propext, Classical.choice, Quot.sound]`):
           - `contDiffAt2_metric_comp_expMap_zero` / `contDiffAt2_jacobian_component_expMap_zero` : the
             two `C²`-at-`0` factor-regularity facts that feed `pd_pd_mul3_zero`.
           - **`pd2_expPullback_summand_zero`** : THE per-`(a,b)`-summand closed nine-term second jet, with
             every factor jet substituted by its landed RNC form (value `g(p)`, `J(0)=δ`, `∂J(0)=½(−Γ−Γ)`,
             the metric first jet `∂g(p)`, the metric Hessian (α1), the Jacobian second jet (α2) =
             `(1/6)(rncD3Block + 3·rncCrossBlock)`).  Pure `rw [pd_pd_mul3_zero …]` + `simp only [<all jets>]`.
           - **`expPullbackMetric_pd2_closed`** : the ASSEMBLED closed `∂_l∂_m g̃_{ij}(0) = ∑_{a,b}(nine
             terms)` (`pd2_expPullbackMetric_at_zero` + the summand, `Finset.sum_congr`).  This is the
             full closed `∂²g̃(0)` the radial identity consumes.
         WHAT STILL REMAINS to discharge `expPullback_radial_gauge` (drop `hrad`): the CONTRACTION of the
         closed `∂²g̃(0)` and the two cancellations.  Precisely — after `rw
         [dGammaDiag_pd_christoffel_expPullbackInv_reduce]` the goal is
           **`∑_α gi(p)^{iα}·(2·⟨∂_l∂_j g̃_{αk}⟩ − ⟨∂_l∂_α g̃_{jk}⟩) = 0`     (∀ v, i)**,
         and substituting `expPullbackMetric_pd2_closed` for the two brackets leaves THREE mechanical but
         sizeable finite steps, none present in the tree yet:
           (i)  **block multilinear contraction** — `∑_l ∑_j rncD3Block/rncCrossBlock(…e_l…e_j…) v^l v^j
                = block(…v…v…)`.  The `α2` second jet enters the contraction with its metric slot fixed at
                a BASIS vector (`e_α` for `A`, `e_j`/`e_k` for `B`) and its two derivative slots contracted
                with `v`, so this is a TWO-SLOT (not full-diagonal) contraction — `expJetD3_zero_diagonal`
                does NOT apply; one must prove `rncD3Block`/`rncCrossBlock` linear in each `Point` argument.
           (ii) **the `∂²g(p)` cancellation** — the ONLY `∂²g(p)` term in `A_α` is `⟨∂_l∂_j g_{αk}(p)⟩`
                (from the `α1` block of the summand's `t1`); it does NOT vanish inside `A_α` alone, but the
                combination `∑_α gi(p)^{iα}(2·⟨∂_l∂_j g_{αk}⟩ − ⟨∂_l∂_α g_{jk}⟩)` collapses under
                `christoffel_lower` (metric compatibility) — the same cancellation that made `∂g̃(0)=0` in
                `pd_expPullbackMetric_at_zero`, one order up.
           (iii)**the `Γ,∂Γ` reindex/vanish** — the surviving cubic (the `α2` blocks + the `∂g·Γ` and `Γ·Γ`
                terms) contracts, via `a3rawArr_contract_eq_a3` + `sum3_sym_contract`, onto
                `dGammaDiag (rncDΓ …) v i`, which is `0` by `expMap_rncDΓ_diag_zero`.
         (Equivalently the reduced scalar identity below.)
           **`∑_α gi(p)^{iα}·(2·⟨∂_l∂_j g̃_{αk}⟩ − ⟨∂_l∂_α g̃_{jk}⟩) = 0`     (∀ v, i)**,
         `⟨·⟩ := ∑_{l,j,k} · v^l v^j v^k` — the RHS of `dGammaDiag_pd_christoffel_expPullbackInv_reduce`.
         Equivalently the radial identity of (β3) OR the pointwise bridge `rnc_christoffel_linearJet`:
           `pd (fun x => christoffel g̃ g̃⁻¹ i j k x) l 0
             = rncDΓ (fun i j k => christoffel g gi i j k p)
                     (fun l i j k => pd (fun z => christoffel g gi i j k z) l p) l i j k`.
         (Given the pointwise bridge, `exp_rncGaugeJet` transfers `GaugeJet` directly; given the radial
         identity, `gaugeJet_of_diag` does — the radial route is a single scalar contraction, likely the
         shorter path, since `dGammaDiag (rncDΓ …) v i = 0` is `expMap_rncDΓ_diag_zero` already.)
         ROUTE (all inputs present, PURE finite `Finset` algebra, NO analytic input past Rung 3):
         start from `pd_christoffel_expPullbackInv_zero` (RHS ⟶ `½ ∑_α gi p^{iα}·(…∂²g̃…)`), then
         expand each of the three `∂²g̃(0)` brackets via `pd2_expPullbackMetric_at_zero`
         (`∂_l∂_m g̃_{ij}(0) = ∑_{a,b} ∂_l∂_m(g(exp·)_{ab}·J_i^a·J_j^b)(0)`) and `pd_pd_mul3_zero` (the
         nine-term twice-Leibniz), substituting the factor jets: value `g(p)` / `J(0)=δ` (`fderiv_expMap_zero`),
         first jets `∂g(p)` (chain, `pd_comp_expMap_zero`) and `∂J(0)=½(−Γ−Γ)` (`pd_jacobian_expMap_zero`),
         and the two SECOND jets `∂²(g∘exp)(0)` = (α1) `pd2_metric_comp_expMap_zero` and `∂²J(0)` = (α2)
         `pd2_jacobian_expMap_zero`.  Then the `∂²g` ambient blocks (the `∂_l∂_m g_{ab}(p)` term of (α1))
         cancel against the metric-compatibility contraction `christoffel_lower`, and the surviving
         `Γ,∂Γ` cubic reindexes onto `rncDΓ`/`a₃` via `a3rawArr_contract_eq_a3` (`QIQTH.RNCGaugeExp`) — for
         the radial route, `expJetD3_zero_diagonal` already gives the `∂²J` contraction in closed `−∂Γ+ΓΓ`
         form.  This is a LARGE multi-lemma `Finset`/`ring` collection (≈ the size of
         `pd2_expPullbackMetric_at_zero` times the nine `pd_pd_mul3` terms times two brackets `⟨T1⟩,⟨T3⟩`),
         a reachable finite assembly, NOT a deep obstruction — but not closed in this session (the
         `∂²J` term enters via the GENERAL, non-diagonal `pd2_jacobian_expMap_zero` =
         `(1/6)(rncD3Block+3·rncCrossBlock)` at directions `(e_α, v, v)`, so the `expJetD3_zero_diagonal`
         full-diagonal shortcut does NOT apply and the general contraction must be carried).
  VERDICT: (α1), (α2) [the two irreducible second-jet inputs], (β)-analytic-half
  [`pd_christoffel_expPullback_zero`] AND (β1) [`expPullbackMetricInv` + its 0-jet/differentiability +
  the instantiated `pd_christoffel_expPullbackInv_zero`] AND (β3) [the structural cyclic-gauge reduction:
  `expPullbackMetric_symm`, `pd_christoffel_expPullbackInv_lower_symm`, `cyclic_of_gaugeJet_lower_symm`]
  AND (β3′) [the radial reduction `dGammaDiag_pd_christoffel_expPullbackInv_reduce` + the mechanical
  cyclic-gauge capstone `gauge_pd_christoffel_expPullbackInv_zero` (modulo `hrad`)]
  are all LANDED axiom-clean, exceeding the guaranteed floor.  **The (β2) FLOOR is now ALSO landed**
  (`contDiffAt2_metric_comp_expMap_zero`, `contDiffAt2_jacobian_component_expMap_zero`,
  `pd2_expPullback_summand_zero`, `expPullbackMetric_pd2_closed` — the CLOSED `∂²g̃(0)` twice-Leibniz).
  What remains for the full cyclic gauge is the CONTRACTION of that closed `∂²g̃(0)` and its two
  cancellations — the three steps (i) block multilinear contraction, (ii) `∂²g` cancellation via
  `christoffel_lower`, (iii) `Γ,∂Γ` reindex to `rncDΓ` via `a3rawArr_contract_eq_a3` +
  `expMap_rncDΓ_diag_zero` — spelled out in the (β2) checkpoint above.  Discharging all three removes the
  `hrad` hypothesis of `gauge_pd_christoffel_expPullbackInv_zero`, making the cyclic gauge UNCONDITIONAL.
  **STEP (i) IS NOW LANDED axiom-clean** (`[propext, Classical.choice, Quot.sound]`) — the block
  (symmetric-)multilinearity + contraction infrastructure, absent from the tree until now:
    - `rncD3Block` symmetric-trilinear in `(h,k,l)`: `rncD3Block_add_left`/`_mid`/`_right`,
      `rncD3Block_smul_left`/`_mid`/`_right`, `rncD3Block_swap12`/`_swap23`;
    - `rncCrossBlock` linear in `dir` and symmetric-bilinear in `(sk,sl)`: `rncCrossBlock_add_dir`/`_sk`/
      `_sl`, `rncCrossBlock_smul_dir`/`_sk`/`_sl`, `rncCrossBlock_swap_source`;
    - the `apply_sum`/basis-reconstitution CONTRACTION forms (`point_eq_sum_single`, the `_zero_*`/`_sum_*`
      distributions, and `rncD3Block_contract_left`/`_mid`/`_right`,
      `rncCrossBlock_contract_dir`/`_sk`/`_sl`), which perform EXACTLY the TWO-SLOT non-diagonal
      contraction `∑_a v^a · block(…e_a…) = block(…v…)` that the `α2` Jacobian second jet requires.
  **REMAINING (precise, for a future brick):** substitute `expPullbackMetric_pd2_closed` into the two
  brackets of `dGammaDiag_pd_christoffel_expPullbackInv_reduce`'s RHS, contract the `α2` blocks via the
  `_contract_*` lemmas above, then discharge (ii) [`christoffel_lower` metric-compatibility cancellation
  of the lone `∂²g(p)` term across the `gi`-weighted `2A−B` combination] and (iii) [reindex the surviving
  `Γ,∂Γ` cubic onto `rncDΓ` via `a3rawArr_contract_eq_a3` + `sum3_sym_contract`, vanishing by
  `expMap_rncDΓ_diag_zero`].  These close `expPullback_radial_gauge` and the unconditional gauge.

  **AUDIT CORRECTION (2026-07 brick, on the (ii) mechanism — recorded, no proof landed this pass):**
  On close inspection the (ii) cancellation is NOT "cancel the lone `∂²g(p)` term" — it is subtler, and
  this is very likely why the final assembly has resisted several bricks.  The `α1` metric-Hessian is the
  ONLY source of an EXPLICIT ambient `∂²g(p)` (it enters `A` as `⟨∂_l∂_j g_{αk}⟩` and `B` as
  `⟨∂_l∂_α g_{jk}⟩`).  These two do NOT cancel each other under the `v`-contraction (they are genuinely
  different contractions of the `∂²g` tensor — `α` sits in a metric slot for `A` but in a derivative slot
  for `B`), and there is no second EXPLICIT `∂²g` term to pair them with.  The `∂²g` they must cancel is
  the one sitting IMPLICITLY inside the `α2` blocks: `rncD3Block` carries `pd (christoffel g gi ·) · p`
  (`∂Γ`), and `∂Γ = ½(∂gi·∂g + gi·∂²g)`.  Exposing that implicit `∂²g` needs either (a) `gi ∈ C¹` at `0`
  (to product-rule `pd (christoffel g gi)` open), or — cleaner, and reusing existing machinery — (b) the
  AMBIENT inverse relation on a NEIGHBOURHOOD, `hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = …`, which is
  what `QIQTH.Curvature.lowered_riemann_eq`/`metric_compat`/the `prod`/`hmc` helpers already consume.
  The current `expPullback_radial_gauge` target lists `hinv` only AT `p`, which is INSUFFICIENT for (ii);
  the future brick should strengthen it to `∀ y` (a legitimate, non-trivialising regularity input — the
  ambient metric inverse is global).  RECOMMENDED ROUTE: work in the `g̃`-LOWERED radial form.  Lowering
  the upper index `i` by `g̃(0)=g(p)` (invertible) and using `∂g̃(0)=0` + `Γ̃(0)=0`, the radial identity
  becomes the intrinsic scalar `X_i := ⟨2·∂_l∂_j g̃_{ik} − ∂_l∂_i g̃_{jk}⟩ = 0`
  (`= ∂_l Γ̃_{lower,i,jk}(0)` contracted, via `christoffel_lower` for `g̃`, which needs `g̃·g̃⁻¹ = δ` only
  at `0`).  Then expand `∂²g̃` (`expPullbackMetric_pd2_closed`), contract the `α2` blocks (`_contract_*`),
  and convert each block's `g(p)·∂Γ` via the `prod`+`hmc` identity
  `∑_α g(p)_{iα}·pd(christoffel g gi α c d) e p = pd(∑_α g_· iα·Γ^α_{cd})(e)(p) − ∑_α ∂_e g_{iα}·Γ^α_{cd}`
  (pure product rule, no `hinv`) followed by `∑_α g_·_{iα}·Γ^α_{cd} = ½(∂g+∂g−∂g)` as a FUNCTION
  (`christoffel_lower` at each `y` — the `∀ y` `hinv`); the resulting `∂²g` cancels the EXPLICIT `α1`
  `∂²g(p)`, leaving the `Γ,∂Γ` cubic for step (iii).  (Step (i) block infra and step (iii)
  `a3rawArr_contract_eq_a3`/`expMap_rncDΓ_diag_zero` are already landed and unaffected by this correction.)
  Checkpoints landed:
  value + first-order + connection jets (`g̃(0)=g(p)`, `∂g̃(0)=0`, `Γ̃(0)=0`), the level-2
  differentiability core (`hasFDerivAt_fderiv2_expMap_zero`), the closed third-jet value + its `a₃`
  grounding (`expJetD3_zero_closed`/`expJetD3_zero_diagonal`), the closed `pd²g̃(0)` twice-Leibniz
  (`pd_pd_mul3_zero`/`pd2_expPullbackMetric_at_zero`), the two second-jet closed forms
  (`pd2_metric_comp_expMap_zero`/`pd2_jacobian_expMap_zero`), the Christoffel-derivative reduction
  (`pd_christoffel_expPullback_zero`), and (β1) the smooth pullback inverse + its instantiation
  (`expPullbackMetricInv`, `expPullbackMetricInv_zero`, `expPullbackMetricInv_differentiableAt`,
  `pd_christoffel_expPullbackInv_zero`).

  STEP 2 NOW LANDED (this brick, axiom-clean [propext, Classical.choice, Quot.sound]) —
  `pd_christoffel_lower_fn`.  The differentiated lowered-Christoffel FUNCTION identity, the
  `g·dGamma -> dd(g) - d(g)·Gamma` conversion the (ii) cancellation needs.  christoffel_lower holds at
  EVERY `y` (function form, via the NEIGHBOURHOOD inverse relation `hinvF : forall y a b, ... = delta`
  — the legitimate strengthening the AUDIT CORRECTION called for, since the ambient inverse metric is
  global); differentiate both sides at `p` (Leibniz `pd_sum`/`pd_mul` on the left, `pd_const_mul`/
  `pd_add`/`pd_sub` on the right), solve.  This EXPOSES the second metric derivative implicit inside the
  ambient `g·dGamma`, exactly the term that cancels the explicit alpha1 metric-Hessian in step (ii).

  THE ENDGAME REDUCTION NOW LANDED (this brick, axiom-clean) — the SOLE remaining wall is a pure
  second-jet identity `hpd2`.  Two reduction lemmas collapse the whole cyclic-gauge target onto a
  Christoffel-free, inverse-free second-jet contraction of the pullback metric:
    - `expPullback_radial_gauge_of_pd2` : GIVEN the pure second-jet identity
        hpd2 : forall a v, 2·<d_l d_j g~_{a k}> = <d_l d_a g~_{j k}>   (<·> = sum_{l,j,k} · v^l v^j v^k),
      the radial diagonal dGammaDiag(...pd Gamma~...) v i = 0 for every v,i (= expPullback_radial_gauge
      / hrad).  Immediate from dGammaDiag_pd_christoffel_expPullbackInv_reduce (whose RHS is
      (1/2) sum_a gi(p)^{i a}·(2<d_l d_j g~_{a k}> - <d_l d_a g~_{j k}>)), zeroing each a-bracket by hpd2.
    - `gauge_pd_christoffel_expPullbackInv_zero_of_pd2` : composing that with the mechanical
      `gauge_pd_christoffel_expPullbackInv_zero`, the FULL cyclic gauge follows from the single hpd2.
  So expPullback_radial_gauge (and the unconditional cyclic gauge) is now reduced END-TO-END to the ONE
  obligation hpd2 — a statement PURELY about the pullback metric's second jet, no pullback Christoffel,
  no pullback inverse.  PRECISE FINAL GRIND (unchanged in content, now crisply targeted): substitute
  `expPullbackMetric_pd2_closed` into the two brackets of hpd2, contract the alpha2 blocks via the
  `_contract_*` lemmas (step i), convert each block's ambient g(p)·dGamma via the NOW-LANDED
  `pd_christoffel_lower_fn` (step ii — the dd(g) it exposes cancels the explicit alpha1 dd(g)(p)), and
  reindex the surviving Gamma,dGamma cubic onto rncDGamma via `a3rawArr_contract_eq_a3` +
  `sum3_sym_contract`, vanishing by `expMap_rncDΓ_diag_zero` (step iii).  This large-but-finite
  Finset/ring assembly remains the open step, now with ALL its inputs (including step 2) present.

  CHECKPOINT (2026-07 brick — analysis pass; goal shape VERIFIED, assembly NOT landed, file GREEN):
  * The rewrite `simp only [expPullbackMetric_pd2_closed g gi hC p hg]` fires cleanly on BOTH brackets
    of `expPullback_hpd2`, turning each into the explicit 9-term double sum `∑_a ∑_b (T1+…+T9)` under
    the triple v-contraction `∑_l ∑_j ∑_k · v^l v^j v^k` (dumped and confirmed; sum-index map for the
    A-bracket is x=l [outer ∂], x_1=j [inner ∂ = m], x_2=k [metric b-slot], so the metric second index
    of the closed call is `k` and the inner-derivative index is `j`).  There is NO analytic gap left in
    the substitution — the whole obligation is now a PURELY AMBIENT finite identity in the atoms
    `pd(pd g)(p)` (∂²g), `pd g (p)` (∂g), `christoffel … p` (Γ), `pd(christoffel …) p` (∂Γ, only inside
    the α2 blocks), `g p`, and `Pi.single` (Kronecker).
  * The α2 blocks contract EXACTLY as follows (worked out, ready to encode via the landed `_contract_*`
    lemmas + `rncD3Block`/`rncCrossBlock` (sym-)multilinearity): for the A-bracket T5-block
    `∑_l ∑_j ∑_k g_{ak}(p)·(1/6•(D3(e_α,e_j,e_l)+Cross(e_α,e_j,e_l)+Cross(e_j,e_α,e_l)+Cross(e_l,e_α,e_j)))_a v^l v^j v^k`
    contracts the two derivative slots (j via mid/source, l via right/source) leaving the k-slot free:
    `= ∑_k v^k ∑_a g_{ak}(p)·(1/6•(D3(e_α,v,v)+Cross(e_α,v,v)+2·Cross(v,e_α,v)))_a`
    (the last two Cross terms coincide under sk↔sl `rncCrossBlock_swap_source`).  T9 (metric slot `α`
    fixed, both other slots contracted) and the two B-bracket α2 blocks contract by the same recipe.
  * NO INVERTIBILITY SHORTCUT.  hpd2 (`W_α := 2A_α − B_α = 0`), the upper-index radial identity
    `dGammaDiag(pd Γ̃) v i = 0`, and the differentiated-lowering relation
    `W_α = 2 ∑_σ g(p)_{ασ}·dGammaDiag(pd Γ̃) v σ` are ALL mutually derivable through the invertible
    pair g(p)/gi(p) (via `hinvF`: `∑_i g(p)_{βi} gi(p)_{iα} = δ_{βα}`, and the reduce-lemma identity
    `dGammaDiag(pd Γ̃) v i = ½ ∑_α gi(p)^{iα} W_α`).  Hence NONE of the three is a shortcut for another:
    the analytic content — that the ∂²g̃ combination actually vanishes — MUST enter through the closed
    form `expPullbackMetric_pd2_closed` together with the abstract `expMap_rncDΓ_diag_zero` (the
    `−∂Γ+ΓΓ` cancellation).  The remaining work is precisely the term-by-term (i)/(ii)/(iii) grind
    above; no cheaper route exists.
  * PRECISE REMAINING RING-IDENTITY: after (i) all α2 blocks are contracted (as above) and all the
    Kronecker `Pi.single` sums collapsed, the goal is `2·⟨A-terms⟩ − ⟨B-terms⟩ = 0` where the surviving
    pieces are: the explicit α1 Hessian `2⟨∂_l∂_j g_{αk}(p)⟩ − ⟨∂_l∂_α g_{jk}(p)⟩`; the ∂g·Γ terms
    (T1's `∑_c`, T2, T3, T4, T7 of each bracket); the ΓΓ terms (T6, T8); and the contracted α2 blocks
    (∂Γ inside D3, ΓΓ inside Cross).  Step (ii): apply `pd_christoffel_lower_fn` to each contracted
    `∑_a g_{ak}(p)·∂Γ^a_{··}` inside the D3-blocks, exposing `∂²g(p)` that CANCELS the explicit α1
    Hessian (this is the crux cancellation — the α1 term does NOT self-cancel).  Step (iii): the
    residual ∂g·Γ + ΓΓ cubic reindexes onto `dGammaDiag (rncDΓ (christoffel … p) (pd(christoffel …) p)) v ?`
    via `a3rawArr_contract_eq_a3` + `sum3_sym_contract` and vanishes by `expMap_rncDΓ_diag_zero`.
    This is the several-hundred-line disciplined `Finset`/`ring` assembly; it is finite and unblocked
    but was NOT completed in this pass.

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

/-!
### (β2) — THE RADIAL-GAUGE ENDGAME

The reduction of the pullback RNC radial-geodesic identity to a pure second-jet contraction, and the
mechanical assembly of the full cyclic normal-coordinate gauge for `g̃`.
-/

/-- **Generic `α`-pull for a triple radial contraction.**  `∑_{l,j,k} (∑_α c_α F_{α l j k}) v^l v^j v^k
    = ∑_α c_α (∑_{l,j,k} F_{α l j k} v^l v^j v^k)`.  Pure `Finset` reordering. -/
private lemma pull_alpha_out (c : Fin n → ℝ) (F : Fin n → Fin n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, (∑ α, c α * F α l j k) * v l * v j * v k)
      = ∑ α, c α * (∑ l, ∑ j, ∑ k, F α l j k * v l * v j * v k) := by
  have hL : (∑ l, ∑ j, ∑ k, (∑ α, c α * F α l j k) * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, ∑ α, c α * F α l j k * v l * v j * v k :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  have hR : (∑ l, ∑ j, ∑ k, ∑ α, c α * F α l j k * v l * v j * v k)
      = ∑ α, c α * (∑ l, ∑ j, ∑ k, F α l j k * v l * v j * v k) := by
    rw [show (∑ l, ∑ j, ∑ k, ∑ α, c α * F α l j k * v l * v j * v k)
          = ∑ l, ∑ j, ∑ α, ∑ k, c α * F α l j k * v l * v j * v k from
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm]
    rw [show (∑ l, ∑ j, ∑ α, ∑ k, c α * F α l j k * v l * v j * v k)
          = ∑ l, ∑ α, ∑ j, ∑ k, c α * F α l j k * v l * v j * v k from
        Finset.sum_congr rfl fun l _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hL, hR]

open QIQTH.RNCGauge in
/-- **Reduction of the radial contraction to the pullback second-jet.**  Substituting the analytic
    half `pd_christoffel_expPullbackInv_zero` into the radial diagonal `dGammaDiag` and using the
    `j ↔ k` symmetry of the contraction (which merges the first two bracket terms into a doubled one),
    the radial-geodesic contraction becomes the pure `∂²g̃`-contraction combination
      `½ ∑_α g⁻¹(p)^{iα}·(2·⟨∂_l∂_j g̃_{αk}⟩ − ⟨∂_l∂_α g̃_{jk}⟩)`,
    where `⟨·⟩` denotes the radial contraction `∑_{l,j,k} · v^l v^j v^k`.  Pure `Finset` algebra
    (distribute `½∑_α`, pull the `α`-sum out via `pull_alpha_out`, relabel `j ↔ k`); no analytic input
    beyond the landed `pd_christoffel_expPullbackInv_zero`. -/
theorem dGammaDiag_pd_christoffel_expPullbackInv_reduce (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (v : Point n) (i : Fin n) :
    dGammaDiag (fun l i j k =>
        pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i j k x) l 0) v i
      = (1 / 2) * ∑ α, gi p i α *
          (2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
                  expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
            - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
                  expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k)) := by
  -- Unfold the diagonal contraction and the Christoffel first-jet.
  simp only [dGammaDiag, pd_christoffel_expPullbackInv_zero g gi hC p hsymm hinv hg]
  -- Fold the leading `½` into the `α`-coefficient, then pull the `α`-sum out (`pull_alpha_out`).
  rw [show (∑ l, ∑ j, ∑ k, (1 / 2 * ∑ α, gi p i α *
          (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
            + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
            - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0))
          * v l * v j * v k)
        = ∑ l, ∑ j, ∑ k, (∑ α, (1 / 2 * gi p i α) *
          (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
            + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
            - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0))
          * v l * v j * v k from
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]; ring_nf]
  rw [pull_alpha_out (fun α => 1 / 2 * gi p i α)
    (fun α l j k =>
      pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
        + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
        - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0) v]
  -- Split the bracket contraction; merge the two `T1`-type blocks by `j ↔ k` relabelling.
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hsplit : (∑ l, ∑ j, ∑ k,
        (pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0
          + pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0
          - pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0)
          * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k,
          pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k,
          pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0 * v l * v j * v k)
        - (∑ l, ∑ j, ∑ k,
          pd (fun y => pd (fun x => expPullbackMetric g gi hC p x j k) α y) l 0
            * v l * v j * v k) := by
    simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hswap : (∑ l, ∑ j, ∑ k,
        pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α j) k y) l 0 * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k,
        pd (fun y => pd (fun x => expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, hswap]; ring

open QIQTH.RNCGauge in
/-- **THE CYCLIC NORMAL-COORDINATE GAUGE for `g̃` (the `heat_a1_of_gauge` consumer).**  Given the
    pullback RNC radial-geodesic identity `hrad` (the sole analytic wall, `expPullback_radial_gauge`),
    the three-term cyclic sum of the pullback Christoffel first-jet at the centre vanishes:
      `∂_c Γ̃^i_{ab}(0) + ∂_a Γ̃^i_{bc}(0) + ∂_b Γ̃^i_{ca}(0) = 0`.
    Mechanical assembly: the radial diagonal vanishing `hrad` gives the six-fold `GaugeJet` via
    `QIQTH.RNCGauge.gaugeJet_of_diag`; the lower-symmetry `pd_christoffel_expPullbackInv_lower_symm`
    (from `g̃` symmetric) collapses the six permutations to `2×` the cyclic sum via
    `cyclic_of_gaugeJet_lower_symm`.  This is `heat_a1_of_gauge`'s `hgauge` for the pullback metric,
    modulo the single hypothesis `hrad` (which is `dGammaDiag_pd_christoffel_expPullbackInv_reduce`'s
    left-hand side set to zero — the checkpointed radial identity). -/
theorem gauge_pd_christoffel_expPullbackInv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hrad : ∀ (v : Point n) (i : Fin n),
      dGammaDiag (fun l i j k =>
        pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i j k x) l 0) v i = 0)
    (i a b c : Fin n) :
    pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i a b x) c 0
      + pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i b c x) a 0
      + pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i c a x) b 0 = 0 := by
  have hgj : GaugeJet (fun l i j k =>
      pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
        i j k x) l 0) :=
    gaugeJet_of_diag _ hrad
  have hsym : ∀ l i' j k,
      (fun l i j k => pd (fun x => christoffel (expPullbackMetric g gi hC p)
          (expPullbackMetricInv g gi hC p) i j k x) l 0) l i' j k
        = (fun l i j k => pd (fun x => christoffel (expPullbackMetric g gi hC p)
          (expPullbackMetricInv g gi hC p) i j k x) l 0) l i' k j :=
    fun l i' j k => pd_christoffel_expPullbackInv_lower_symm g gi hC p hsymm i' j k l
  have hcyc := cyclic_of_gaugeJet_lower_symm _ hsym hgj i a b c
  linarith [hcyc]

/-! ### STEP 2 — the differentiated lowered-Christoffel identity (`g·∂Γ → ∂²g − ∂g·Γ`) -/

set_option maxHeartbeats 3200000 in
/-- **Differentiated lowered-Christoffel FUNCTION identity** (the step-2 `g·∂Γ → ∂²g − ∂g·Γ`
    conversion).  `christoffel_lower` holds at EVERY point `y` (function form, from the neighbourhood
    inverse relation `hinvF`), so it is an identity of FUNCTIONS of `y`:
      `(∑_σ g_{σν}·Γ^σ_{λμ})(y) = ½(∂_λ g_{νμ} + ∂_μ g_{νλ} − ∂_ν g_{λμ})(y)`.
    Differentiating both sides at `p` in direction `r` (Leibniz on the left, `∂` through the ½ and the
    three second-partials on the right) and solving for the `g·∂Γ` term gives
      `∑_σ g_{σν}(p)·∂_r Γ^σ_{λμ}(p)
         = ½·(∂_r∂_λ g_{νμ} + ∂_r∂_μ g_{νλ} − ∂_r∂_ν g_{λμ})(p) − ∑_σ ∂_r g_{σν}(p)·Γ^σ_{λμ}(p)`.
    This EXPOSES the second metric derivative `∂²g` hiding inside `g·∂Γ`, which is the term that cancels
    the explicit `α1` metric-Hessian in the radial-gauge assembly.  Pure product-rule algebra; the sole
    input past `christoffel_lower` is that the ambient inverse relation holds on a neighbourhood
    (`hinvF : ∀ y`), a legitimate global regularity fact about the ambient inverse metric. -/
theorem pd_christoffel_lower_fn (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (ν lam mu r : Fin n) :
    (∑ σ, g p σ ν * pd (fun y => christoffel g gi σ lam mu y) r p)
      = (1 / 2) * (pd (fun y => pd (fun z => g z ν mu) lam y) r p
                    + pd (fun y => pd (fun z => g z ν lam) mu y) r p
                    - pd (fun y => pd (fun z => g z lam mu) ν y) r p)
        - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ lam mu p := by
  -- (1) The lowered-Christoffel identity as an equality of FUNCTIONS of `y`.
  have hfun : (fun y => ∑ σ, g y σ ν * christoffel g gi σ lam mu y)
      = (fun y => (1 / 2) * (pd (fun z => g z ν mu) lam y + pd (fun z => g z ν lam) mu y
                    - pd (fun z => g z lam mu) ν y)) :=
    funext fun y => christoffel_lower g gi hsymm y (fun a b => hinvF y a b) ν lam mu
  -- (2) Differentiate both sides at `p` in direction `r`.
  have hd : pd (fun y => ∑ σ, g y σ ν * christoffel g gi σ lam mu y) r p
      = pd (fun y => (1 / 2) * (pd (fun z => g z ν mu) lam y + pd (fun z => g z ν lam) mu y
                    - pd (fun z => g z lam mu) ν y)) r p := by rw [hfun]
  -- (3) LHS via `pd_sum` + `pd_mul`.
  have hLHS : pd (fun y => ∑ σ, g y σ ν * christoffel g gi σ lam mu y) r p
      = (∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ lam mu p)
        + (∑ σ, g p σ ν * pd (fun y => christoffel g gi σ lam mu y) r p) := by
    rw [pd_sum Finset.univ (fun σ y => g y σ ν * christoffel g gi σ lam mu y) r p
          (fun σ _ => (PdiffAt_of_contDiff _ (hg σ ν) r p).mul
            (PdiffAt_of_contDiff _ (hC σ lam mu) r p)),
        Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) =>
          pd_mul (fun y => g y σ ν) (fun y => christoffel g gi σ lam mu y) r p
            (PdiffAt_of_contDiff _ (hg σ ν) r p) (PdiffAt_of_contDiff _ (hC σ lam mu) r p)),
        Finset.sum_add_distrib]
  -- (4) RHS via `pd_const_mul`, `pd_sub`, `pd_add`; the three factors are `∂g`, differentiable by `hg`.
  have hp1 : PdiffAt (fun y => pd (fun z => g z ν mu) lam y) r p := PdiffAt_pd _ (hg ν mu) lam r p
  have hp2 : PdiffAt (fun y => pd (fun z => g z ν lam) mu y) r p := PdiffAt_pd _ (hg ν lam) mu r p
  have hp3 : PdiffAt (fun y => pd (fun z => g z lam mu) ν y) r p := PdiffAt_pd _ (hg lam mu) ν r p
  have hRHS : pd (fun y => (1 / 2) * (pd (fun z => g z ν mu) lam y + pd (fun z => g z ν lam) mu y
                    - pd (fun z => g z lam mu) ν y)) r p
      = (1 / 2) * (pd (fun y => pd (fun z => g z ν mu) lam y) r p
                    + pd (fun y => pd (fun z => g z ν lam) mu y) r p
                    - pd (fun y => pd (fun z => g z lam mu) ν y) r p) := by
    rw [pd_const_mul (1 / 2) _ r p (by exact (hp1.add hp2).sub hp3),
        pd_sub _ _ r p (hp1.add hp2) hp3, pd_add _ _ r p hp1 hp2]
  -- (5) Combine and solve for the `g·∂Γ` term.
  rw [hLHS, hRHS] at hd
  linarith [hd]

open QIQTH.RNCGauge in
/-- **Radial gauge from the pure second-jet identity.**  Discharging `hrad` (i.e.
    `expPullback_radial_gauge`) is EQUIVALENT — via the already-proven reduction
    `dGammaDiag_pd_christoffel_expPullbackInv_reduce` — to the Christoffel-free, inverse-free
    pure `∂²g̃(0)` contraction identity
      `2·⟨∂_l∂_j g̃_{αk}⟩ = ⟨∂_l∂_α g̃_{jk}⟩`   (∀ α, v),
    where `⟨·⟩` is the radial contraction `∑_{l,j,k} · v^l v^j v^k`.  Given that pure second-jet
    identity `hpd2`, the radial diagonal `dGammaDiag (…pd Γ̃…) v i` vanishes for every `v, i`.
    This isolates the SOLE remaining analytic wall as a statement purely about the pullback metric's
    second jet — no pullback Christoffel, no pullback inverse. -/
theorem expPullback_radial_gauge_of_pd2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hpd2 : ∀ (α : Fin n) (v : Point n),
      2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
              expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
        - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
              expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k) = 0)
    (v : Point n) (i : Fin n) :
    dGammaDiag (fun l i j k =>
        pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i j k x) l 0) v i = 0 := by
  rw [dGammaDiag_pd_christoffel_expPullbackInv_reduce g gi hC p hsymm hinv hg v i]
  rw [Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => by rw [hpd2 α v, mul_zero]]
  simp

open QIQTH.RNCGauge in
/-- **The cyclic normal-coordinate gauge for `g̃`, modulo the pure second-jet identity.**  Combining
    `expPullback_radial_gauge_of_pd2` (which discharges `hrad` from the pure `∂²g̃` contraction
    identity) with `gauge_pd_christoffel_expPullbackInv_zero`, the full three-term cyclic gauge
    `∂_c Γ̃^i_{ab}(0) + ∂_a Γ̃^i_{bc}(0) + ∂_b Γ̃^i_{ca}(0) = 0` follows from the SINGLE pure second-jet
    hypothesis `hpd2`.  This is the endgame wired to its final obligation: closing `hpd2` (the
    `∂²g̃` contraction `2⟨∂_l∂_j g̃_{αk}⟩ = ⟨∂_l∂_α g̃_{jk}⟩`) makes the gauge unconditional. -/
theorem gauge_pd_christoffel_expPullbackInv_zero_of_pd2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ a b, (∑ σ, g p a σ * gi p σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hpd2 : ∀ (α : Fin n) (v : Point n),
      2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
              expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
        - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
              expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k) = 0)
    (i a b c : Fin n) :
    pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i a b x) c 0
      + pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i b c x) a 0
      + pd (fun x => christoffel (expPullbackMetric g gi hC p) (expPullbackMetricInv g gi hC p)
          i c a x) b 0 = 0 :=
  gauge_pd_christoffel_expPullbackInv_zero g gi hC p hsymm
    (fun v i => expPullback_radial_gauge_of_pd2 g gi hC p hsymm hinv hg hpd2 v i) i a b c

/-! ### (β3) — the two bounded second-jet expansion sub-lemmas for `hpd2`

Substituting `expPullbackMetric_pd2_closed` into each of the two brackets of `hpd2` and reordering the
radial contraction `⟨·⟩ = ∑_{l,j,k} · v^l v^j v^k` to the canonical `∑_a∑_b`-outer form (the shape the
metric-compatibility step (ii) consumes).  Pure `Finset` reindexing over the landed closed second jet.
-/

/-- **Bring the two closed-jet sum indices `a,b` to the front of a five-fold sum.**  Pure
    `Finset.sum_comm` reindexing. -/
private lemma reorder_ab_front (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, ∑ a, ∑ b, F l j k a b)
      = ∑ a, ∑ b, ∑ l, ∑ j, ∑ k, F l j k a b := by
  rw [show (∑ l, ∑ j, ∑ k, ∑ a, ∑ b, F l j k a b)
        = ∑ l, ∑ j, ∑ a, ∑ k, ∑ b, F l j k a b from
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [show (∑ l, ∑ j, ∑ a, ∑ k, ∑ b, F l j k a b)
        = ∑ l, ∑ a, ∑ j, ∑ k, ∑ b, F l j k a b from
      Finset.sum_congr rfl fun l _ => Finset.sum_comm]
  rw [show (∑ l, ∑ a, ∑ j, ∑ k, ∑ b, F l j k a b)
        = ∑ a, ∑ l, ∑ j, ∑ k, ∑ b, F l j k a b from Finset.sum_comm]
  rw [show (∑ a, ∑ l, ∑ j, ∑ k, ∑ b, F l j k a b)
        = ∑ a, ∑ l, ∑ j, ∑ b, ∑ k, F l j k a b from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [show (∑ a, ∑ l, ∑ j, ∑ b, ∑ k, F l j k a b)
        = ∑ a, ∑ l, ∑ b, ∑ j, ∑ k, F l j k a b from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm]
  rw [show (∑ a, ∑ l, ∑ b, ∑ j, ∑ k, F l j k a b)
        = ∑ a, ∑ b, ∑ l, ∑ j, ∑ k, F l j k a b from
      Finset.sum_congr rfl fun a _ => Finset.sum_comm]

/-- **Distribute-and-reorder the radial contraction of a closed `∑_a∑_b` second jet.**  For any summand
    `H a b l j k`, `∑_{l,j,k}(∑_a∑_b H)·v^l v^j v^k = ∑_a∑_b∑_{l,j,k} H·v^l v^j v^k`. -/
private lemma contract_ab_expand (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (v : Point n) :
    (∑ l, ∑ j, ∑ k, (∑ a, ∑ b, H a b l j k) * v l * v j * v k)
      = ∑ a, ∑ b, ∑ l, ∑ j, ∑ k, H a b l j k * v l * v j * v k := by
  have hd : (∑ l, ∑ j, ∑ k, (∑ a, ∑ b, H a b l j k) * v l * v j * v k)
      = ∑ l, ∑ j, ∑ k, ∑ a, ∑ b, H a b l j k * v l * v j * v k := by
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  rw [hd]
  exact reorder_ab_front (fun l j k a b => H a b l j k * v l * v j * v k)

set_option maxHeartbeats 3200000 in
/-- **`hpd2_A_expand` — the closed expansion of the A-bracket of `hpd2`.**  Substituting the landed
    closed second jet `expPullbackMetric_pd2_closed` (with `i:=α`, metric second index `k`, inner
    derivative `j`, outer derivative `l`) into the radial contraction
    `A_α = ∑_{l,j,k} ∂_l∂_j g̃_{αk}(0)·v^l v^j v^k` and reordering to the canonical `∑_a∑_b`-outer form,
    `A_α` equals the explicit finite expression in `{∂²g(p), ∂g(p), Γ(p), ∂Γ(p), g(p)}` (the nine
    substituted-jet terms of the twice-Leibniz, with the two `α2` blocks `rncD3Block`/`rncCrossBlock`
    still in basis-vector form, ready for the step-(i) `_contract_*` folding). -/
theorem hpd2_A_expand (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (α : Fin n) (v : Point n) :
    (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
      = ∑ a, ∑ b, ∑ l, ∑ j, ∑ k,
          ((pd (fun z => pd (fun y => g y a b) j z) l p
              + ∑ c, pd (fun y => g y a b) c p
                  * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
            * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b
          + pd (fun y => g y a b) j p
              * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
              * (Pi.single k 1 : Point n) b
          + pd (fun y => g y a b) j p * (Pi.single α 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p))
          + pd (fun y => g y a b) l p
              * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
              * (Pi.single k 1 : Point n) b
          + g p a b
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1))) a)
              * (Pi.single k 1 : Point n) b
          + g p a b
              * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p))
          + pd (fun y => g y a b) l p * (Pi.single α 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p))
          + g p a b
              * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
              * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p))
          + g p a b * (Pi.single α 1 : Point n) a
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1))) b))
          * v l * v j * v k := by
  simp only [expPullbackMetric_pd2_closed g gi hC p hg]
  exact contract_ab_expand _ v

set_option maxHeartbeats 3200000 in
/-- **`hpd2_B_expand` — the closed expansion of the B-bracket of `hpd2`.**  Substituting the landed
    closed second jet `expPullbackMetric_pd2_closed` (with `i:=j`, metric second index `k`, inner
    derivative `α`, outer derivative `l`) into the radial contraction
    `B_α = ∑_{l,j,k} ∂_l∂_α g̃_{jk}(0)·v^l v^j v^k` and reordering to the canonical `∑_a∑_b`-outer form,
    `B_α` equals the explicit finite expression in `{∂²g(p), ∂g(p), Γ(p), ∂Γ(p), g(p)}`.  Note the
    two-slot structure the ledger flags: in the closed second jet `α` is the INNER-derivative `m`-slot
    (fixed), so the `α2` blocks carry `α` in a fixed derivative slot while `j` occupies the metric/first
    lower slot — distinct from A's three-derivative-slot pattern. -/
theorem hpd2_B_expand (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (α : Fin n) (v : Point n) :
    (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k)
      = ∑ a, ∑ b, ∑ l, ∑ j, ∑ k,
          ((pd (fun z => pd (fun y => g y a b) α z) l p
              + ∑ c, pd (fun y => g y a b) c p
                  * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
            * (Pi.single j 1 : Point n) a * (Pi.single k 1 : Point n) b
          + pd (fun y => g y a b) α p
              * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
              * (Pi.single k 1 : Point n) b
          + pd (fun y => g y a b) α p * (Pi.single j 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p))
          + pd (fun y => g y a b) l p
              * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
              * (Pi.single k 1 : Point n) b
          + g p a b
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1))) a)
              * (Pi.single k 1 : Point n) b
          + g p a b
              * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p))
          + pd (fun y => g y a b) l p * (Pi.single j 1 : Point n) a
              * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p))
          + g p a b
              * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
              * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p))
          + g p a b * (Pi.single j 1 : Point n) a
              * (((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1)
                    + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1))) b))
          * v l * v j * v k := by
  simp only [expPullbackMetric_pd2_closed g gi hC p hg]
  exact contract_ab_expand _ v

/-! ### (β3) — TWO-SLOT block contractions (the FLOOR helpers for the α2-block folding)

These are the two-slot analogues of the step-(i) single-slot `rncD3Block_contract_{left,mid,right}` /
`rncCrossBlock_contract_{dir,sk,sl}`.  Each fixes ONE block slot at a basis vector `e` and contracts the
OTHER two slots against weights `w`/`u` over the standard basis — exactly the shape the α2 second jet
enters with in `hpd2_A_expand`/`hpd2_B_expand` (two derivative slots run against `v`, one slot stays at
the fixed `e_α`).  Same proof style: compose the two relevant single-slot `_contract_*` lemmas and pull
the first weight into the inner sum. -/

/-- **Two-slot contraction of `rncD3Block`, LEFT slot fixed** (contract mid + right against `w`/`u`).
    Produces the `D3(e, w, u)` fold (`e_α` in the first slot, the other two contracted). -/
theorem rncD3Block_contract2_leftfix (g gi : Point n → Fin n → Fin n → ℝ) (p e w u : Point n)
    (i : Fin n) :
    rncD3Block g gi p e w u i
      = ∑ x, ∑ y, w x * u y * rncD3Block g gi p e (Pi.single x 1) (Pi.single y 1) i := by
  rw [rncD3Block_contract_mid]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncD3Block_contract_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Two-slot contraction of `rncD3Block`, MID slot fixed** (contract left + right against `w`/`u`).
    Produces the `D3(w, e, u)` fold (`e_α` in the middle slot, the other two contracted) — the two-slot
    analogue of `rncD3Block_contract_mid`, per the ledger's B-structure. -/
theorem rncD3Block_contract2_mid (g gi : Point n → Fin n → Fin n → ℝ) (p w e u : Point n)
    (i : Fin n) :
    rncD3Block g gi p w e u i
      = ∑ x, ∑ y, w x * u y * rncD3Block g gi p (Pi.single x 1) e (Pi.single y 1) i := by
  rw [rncD3Block_contract_left]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncD3Block_contract_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Two-slot contraction of `rncCrossBlock`, DIRECTION slot fixed** (contract both sources `sk`,`sl`).
    Produces the `Cross(e, w, u)` fold. -/
theorem rncCrossBlock_contract2_sources (g gi : Point n → Fin n → Fin n → ℝ) (p e w u : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p e w u i
      = ∑ x, ∑ y, w x * u y * rncCrossBlock g gi p e (Pi.single x 1) (Pi.single y 1) i := by
  rw [rncCrossBlock_contract_sk]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncCrossBlock_contract_sl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Two-slot contraction of `rncCrossBlock`, one SOURCE slot (`sk`) fixed** (contract `dir` + `sl`).
    Produces the `Cross(w, e, u)` fold — the fixed derivative-source-slot two-slot contraction the
    ledger flags for the `A`/`B` cross terms. -/
theorem rncCrossBlock_contract2_dirsource (g gi : Point n → Fin n → Fin n → ℝ) (p w e u : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p w e u i
      = ∑ x, ∑ y, w x * u y * rncCrossBlock g gi p (Pi.single x 1) e (Pi.single y 1) i := by
  rw [rncCrossBlock_contract_dir]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncCrossBlock_contract_sl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Two-slot contraction of `rncCrossBlock`, second SOURCE slot (`sl`) fixed** (contract `dir` + `sk`).
    Produces the `Cross(w, u, e)` fold — the `Cross(v,v,e_α)` shape B's T5 needs. -/
theorem rncCrossBlock_contract2_dirsk (g gi : Point n → Fin n → Fin n → ℝ) (p w u e : Point n)
    (i : Fin n) :
    rncCrossBlock g gi p w u e i
      = ∑ x, ∑ y, w x * u y * rncCrossBlock g gi p (Pi.single x 1) (Pi.single y 1) e i := by
  rw [rncCrossBlock_contract_dir]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncCrossBlock_contract_sk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **4-index reorder lining up the pulled `j` index next to the `b` factor** (per the ledger's
    B-structure note: the `g_{jb}` factor of the T9 block wants `j` adjacent to `b`).  Pure inner
    `Finset.sum_comm`. -/
private lemma reorder4_jb (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ l, ∑ j, F a b l j) = ∑ a, ∑ b, ∑ j, ∑ l, F a b l j :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ### (β3) — the block-folding + Kronecker-collapse infrastructure for `hpd2_A_folded`

The reorders, `Pi.single` collapse helpers, three-slot contractions and the two- and three-slot folds
that turn the `∑_a∑_b`-outer closed second jet of `hpd2_A_expand` into its fully `v`-contracted form.
All pure `Finset`/`ring` scalar identities. -/

-- reorders
private lemma reorder_b_inner (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ b, ∑ l, ∑ j, ∑ k, F b l j k) = ∑ l, ∑ j, ∑ k, ∑ b, F b l j k := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

private lemma reorder3_last_first (H : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, H l j k) = ∑ k, ∑ l, ∑ j, H l j k := by
  rw [show (∑ l, ∑ j, ∑ k, H l j k) = ∑ l, ∑ k, ∑ j, H l j k from
      Finset.sum_congr rfl fun l _ => Finset.sum_comm]
  rw [Finset.sum_comm]

private lemma reorder_a_inner5 (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, F a b l j k) = ∑ b, ∑ l, ∑ j, ∑ k, ∑ a, F a b l j k := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

private lemma reorder3_rev (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, F l j k) = ∑ k, ∑ j, ∑ l, F l j k := by
  rw [show (∑ l, ∑ j, ∑ k, F l j k) = ∑ l, ∑ k, ∑ j, F l j k from
      Finset.sum_congr rfl fun l _ => Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _ => Finset.sum_comm

private lemma reorder3_jkl (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, F l j k) = ∑ j, ∑ k, ∑ l, F l j k := by
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => Finset.sum_comm

private lemma reorder3_lkj (F : Fin n → Fin n → Fin n → ℝ) :
    (∑ l, ∑ j, ∑ k, F l j k) = ∑ l, ∑ k, ∑ j, F l j k :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

-- collapse helpers
private lemma sum_mul_single_right (F : Fin n → ℝ) (k : Fin n) :
    (∑ b, F b * (Pi.single k 1 : Point n) b) = F k := by
  simp [Pi.single_apply, Finset.sum_ite_eq']

private lemma collapse_single_mul (F : Fin n → ℝ) (k : Fin n) (R : ℝ) :
    (∑ b, F b * (Pi.single k 1 : Point n) b * R) = F k * R := by
  rw [show (∑ b, F b * (Pi.single k 1 : Point n) b * R)
        = (∑ b, F b * (Pi.single k 1 : Point n) b) * R from by rw [Finset.sum_mul]]
  rw [sum_mul_single_right]

private lemma sum_single_mul_left (H : Fin n → ℝ) (α : Fin n) :
    (∑ a, (Pi.single α 1 : Point n) a * H a) = H α := by
  simp [Pi.single_apply, Finset.sum_ite_eq']

private lemma double_collapse (G : Fin n → Fin n → ℝ) (α k : Fin n) (R : ℝ) :
    (∑ a, ∑ b, G a b * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * R)
      = G α k * R := by
  rw [show (∑ a, ∑ b, G a b * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * R)
        = ∑ a, (Pi.single α 1 : Point n) a * (∑ b, G a b * (Pi.single k 1 : Point n) b * R) from
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring]
  rw [sum_single_mul_left (fun a => ∑ b, G a b * (Pi.single k 1 : Point n) b * R) α]
  exact collapse_single_mul (fun b => G α b) k R

private lemma double_collapse3 (G : Fin n → Fin n → ℝ) (α k : Fin n) (r1 r2 r3 : ℝ) :
    (∑ a, ∑ b, G a b * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * r1 * r2 * r3)
      = G α k * r1 * r2 * r3 := by
  rw [show (∑ a, ∑ b,
        G a b * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * r1 * r2 * r3)
        = ∑ a, ∑ b,
          G a b * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * (r1 * r2 * r3) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring]
  rw [double_collapse]; ring

private lemma reorder_ab_inner5 (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, F a b l j k) = ∑ l, ∑ j, ∑ k, ∑ a, ∑ b, F a b l j k := by
  rw [reorder_a_inner5 (fun a b l j k => F a b l j k)]
  rw [reorder_a_inner5 (fun b l j k a => F a b l j k)]

/-- **Full three-slot (diagonal) contraction of `rncD3Block`.** -/
theorem rncD3Block_contract3 (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (i : Fin n) :
    rncD3Block g gi p v v v i
      = ∑ x, ∑ y, ∑ z, v x * v y * v z *
          rncD3Block g gi p (Pi.single x 1) (Pi.single y 1) (Pi.single z 1) i := by
  rw [rncD3Block_contract_left]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncD3Block_contract_mid, Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_
  rw [rncD3Block_contract_right, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- **Full three-slot (diagonal) contraction of `rncCrossBlock`.** -/
theorem rncCrossBlock_contract3 (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (i : Fin n) :
    rncCrossBlock g gi p v v v i
      = ∑ x, ∑ y, ∑ z, v x * v y * v z *
          rncCrossBlock g gi p (Pi.single x 1) (Pi.single y 1) (Pi.single z 1) i := by
  rw [rncCrossBlock_contract_dir]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [rncCrossBlock_contract_sk, Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_
  rw [rncCrossBlock_contract_sl, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z _ => by ring

-- 2-slot folds (l outer, j inner; weights v l v j)
private lemma foldD3_leftfix (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a * v l * v j)
      = rncD3Block g gi p (Pi.single α 1) v v a := by
  rw [rncD3Block_contract2_leftfix g gi p (Pi.single α 1) v v a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_sources (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a * v l * v j)
      = rncCrossBlock g gi p (Pi.single α 1) v v a := by
  rw [rncCrossBlock_contract2_sources g gi p (Pi.single α 1) v v a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_dirsource_jl (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a * v l * v j)
      = rncCrossBlock g gi p v (Pi.single α 1) v a := by
  rw [rncCrossBlock_contract2_dirsource g gi p v (Pi.single α 1) v a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_dirsource_lj (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1) a * v l * v j)
      = rncCrossBlock g gi p v (Pi.single α 1) v a := by
  rw [rncCrossBlock_contract2_dirsource g gi p v (Pi.single α 1) v a]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

-- 2-slot folds with the MIDDLE slot fixed (for the B-bracket's `α`-in-mid-slot blocks)
private lemma foldD3_midfix (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a * v l * v j)
      = rncD3Block g gi p v (Pi.single α 1) v a := by
  rw [rncD3Block_contract2_mid g gi p v (Pi.single α 1) v a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_dirsk (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n)
    (v : Point n) (a : Fin n) :
    (∑ l, ∑ j, rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1) a * v l * v j)
      = rncCrossBlock g gi p v v (Pi.single α 1) a := by
  rw [rncCrossBlock_contract2_dirsk g gi p v v (Pi.single α 1) a]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

-- 3-slot folds (l outer, j mid, k inner; weights v l v j v k)
private lemma foldD3_all (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (b : Fin n) :
    (∑ l, ∑ j, ∑ k,
        rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b * v l * v j * v k)
      = rncD3Block g gi p v v v b := by
  rw [rncD3Block_contract3 g gi p v b, reorder3_rev]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_all_kjl (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (b : Fin n) :
    (∑ l, ∑ j, ∑ k,
        rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b * v l * v j * v k)
      = rncCrossBlock g gi p v v v b := by
  rw [rncCrossBlock_contract3 g gi p v b, reorder3_rev]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_all_jkl (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (b : Fin n) :
    (∑ l, ∑ j, ∑ k,
        rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) b * v l * v j * v k)
      = rncCrossBlock g gi p v v v b := by
  rw [rncCrossBlock_contract3 g gi p v b, reorder3_jkl]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

private lemma foldCross_all_lkj (g gi : Point n → Fin n → Fin n → ℝ) (p v : Point n) (b : Fin n) :
    (∑ l, ∑ j, ∑ k,
        rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1) b * v l * v j * v k)
      = rncCrossBlock g gi p v v v b := by
  rw [rncCrossBlock_contract3 g gi p v b, reorder3_lkj]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 6400000 in
/-- **`hpd2_A_folded` — the FOLDED closed form of the A-bracket of `hpd2`.**  Starting from
    `hpd2_A_expand`, the `∑_a∑_b` Kronecker `Pi.single` couplings are collapsed (a=α / b=k where they
    occur) and the two `α2` blocks are folded against `v`: the metric-jet block reduces to the ledger
    form `1/6•(D3(e_α,v,v) + Cross(e_α,v,v) + 2·Cross(v,e_α,v))` (T5) and the Jacobian block to the
    full-diagonal `1/6•(D3(v,v,v) + 3·Cross(v,v,v))` (T9).  RHS is the explicit scalar sum in
    `{∂²g(p), ∂g(p), Γ(p), ∂Γ(p), g(p)}` fully contracted with `v` (no residual `Pi.single` in
    derivative slots).  NO α1-cancellation / cubic reindex / 2A−B assembly — those are later bricks. -/
theorem hpd2_A_folded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (α : Fin n) (v : Point n) :
    (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
      = -- fold1 (a=α,b=k)
        (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y α k) j z) l p
              + ∑ c, pd (fun y => g y α k) c p
                  * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
            * v l * v j * v k)
        -- fold2 (b=k)
        + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) j p
            * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p)) * v l * v j * v k)
        -- fold3 (a=α)
        + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) j p
            * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        -- fold4 (b=k)
        + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
            * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p)) * v l * v j * v k)
        -- fold5 (block, b=k)
        + (∑ a, ∑ k, g p a k * v k *
            ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) v v a
                + rncCrossBlock g gi p (Pi.single α 1) v v a
                + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a)))
        -- fold6 = S6 (no Kronecker)
        + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
            * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
            * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        -- fold7 (a=α)
        + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) l p
            * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
        -- fold8 = S8 (no Kronecker)
        + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
            * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
            * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
        -- fold9 (block, a=α, 3-slot fold)
        + (∑ b, g p α b *
            ((1 / 6 : ℝ) * (rncD3Block g gi p v v v b + 3 * rncCrossBlock g gi p v v v b))) := by
  have hS1 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k,
        (pd (fun z => pd (fun y => g y a b) j z) l p
            + ∑ c, pd (fun y => g y a b) c p
                * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
          * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y α k) j z) l p
              + ∑ c, pd (fun y => g y α k) c p
                  * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
            * v l * v j * v k) := by
    rw [reorder_ab_inner5 (fun a b l j k =>
        (pd (fun z => pd (fun y => g y a b) j z) l p
            + ∑ c, pd (fun y => g y a b) c p
                * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
          * (Pi.single α 1 : Point n) a * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    exact double_collapse3 (fun a b => pd (fun z => pd (fun y => g y a b) j z) l p
          + ∑ c, pd (fun y => g y a b) c p
              * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p))) α k
        (v l) (v j) (v k)
  have hS2 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) j p
        * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) j p
          * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p)) * v l * v j * v k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => pd (fun y => g y a b) j p
        * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun b _ => show pd (fun y => g y a b) j p
          * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
          * (Pi.single k 1 : Point n) b * v l * v j * v k
        = pd (fun y => g y a b) j p * (Pi.single k 1 : Point n) b
          * ((1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun b => pd (fun y => g y a b) j p) k
        ((1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p)) * v l * v j * v k)]
    ring
  have hS3 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) j p * (Pi.single α 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
      = (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) j p
          * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k) := by
    rw [reorder_a_inner5 (fun a b l j k => pd (fun y => g y a b) j p * (Pi.single α 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun a _ => show pd (fun y => g y a b) j p * (Pi.single α 1 : Point n) a
          * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k
        = pd (fun y => g y a b) j p * (Pi.single α 1 : Point n) a
          * ((1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun a => pd (fun y => g y a b) j p) α
        ((1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)]
    ring
  have hS4 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) l p
        * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
          * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p)) * v l * v j * v k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => pd (fun y => g y a b) l p
        * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun b _ => show pd (fun y => g y a b) l p
          * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
          * (Pi.single k 1 : Point n) b * v l * v j * v k
        = pd (fun y => g y a b) l p * (Pi.single k 1 : Point n) b
          * ((1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun b => pd (fun y => g y a b) l p) k
        ((1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p)) * v l * v j * v k)]
    ring
  have hS5 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b *
          ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1))) a
          * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ k, g p a k * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) v v a
              + rncCrossBlock g gi p (Pi.single α 1) v v a
              + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => g p a b *
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1))) a
        * (Pi.single k 1 : Point n) b * v l * v j * v k),
      reorder3_last_first]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hstep : ∀ l j : Fin n,
        (∑ b, g p a b *
            ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1))) a
            * (Pi.single k 1 : Point n) b * v l * v j * v k)
          = g p a k * v k *
              ((1 / 6 : ℝ) *
                (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1) a))
                * v l * v j := by
      intro l j
      set B : ℝ :=
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1))) a with hBdef
      rw [Finset.sum_congr rfl (fun b _ => show g p a b * B * (Pi.single k 1 : Point n) b * v l * v j * v k
            = (g p a b * (Pi.single k 1 : Point n) b) * (B * v l * v j * v k) from by ring)]
      rw [← Finset.sum_mul, sum_mul_single_right, hBdef]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    simp only [hstep]
    rw [show (∑ l, ∑ j, g p a k * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1) a)) * v l * v j)
        = g p a k * v k * (1 / 6 : ℝ) *
          (∑ l, ∑ j,
            (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1) a) * v l * v j)
        from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    rw [show (∑ l, ∑ j,
          (rncD3Block g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single α 1) (Pi.single j 1) a) * v l * v j)
        = rncD3Block g gi p (Pi.single α 1) v v a + rncCrossBlock g gi p (Pi.single α 1) v v a
          + rncCrossBlock g gi p v (Pi.single α 1) v a + rncCrossBlock g gi p v (Pi.single α 1) v a
        from by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [foldD3_leftfix, foldCross_sources, foldCross_dirsource_jl, foldCross_dirsource_lj]]
    ring
  have hS7 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) l p * (Pi.single α 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
      = (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) l p
          * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k) := by
    rw [reorder_a_inner5 (fun a b l j k => pd (fun y => g y a b) l p * (Pi.single α 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun a _ => show pd (fun y => g y a b) l p * (Pi.single α 1 : Point n) a
          * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k
        = pd (fun y => g y a b) l p * (Pi.single α 1 : Point n) a
          * ((1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun a => pd (fun y => g y a b) l p) α
        ((1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)]
    ring
  have hS9 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b * (Pi.single α 1 : Point n) a
          * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1))) b
          * v l * v j * v k)
      = (∑ b, g p α b *
          ((1 / 6 : ℝ) * (rncD3Block g gi p v v v b + 3 * rncCrossBlock g gi p v v v b))) := by
    rw [reorder_a_inner5 (fun a b l j k => g p a b * (Pi.single α 1 : Point n) a
        * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1))) b
        * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hcol : ∀ l j k : Fin n,
        (∑ a, g p a b * (Pi.single α 1 : Point n) a
            * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1))) b
            * v l * v j * v k)
          = g p α b * v l * v j * v k *
              ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1) b)) := by
      intro l j k
      set B : ℝ :=
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1))) b with hBdef
      rw [Finset.sum_congr rfl (fun a _ => show g p a b * (Pi.single α 1 : Point n) a * B * v l * v j * v k
            = g p a b * (Pi.single α 1 : Point n) a * (B * v l * v j * v k) from by ring)]
      rw [show (∑ a, g p a b * (Pi.single α 1 : Point n) a * (B * v l * v j * v k))
            = (∑ a, (Pi.single α 1 : Point n) a * (g p a b)) * (B * v l * v j * v k) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring]
      rw [sum_single_mul_left (fun a => g p a b) α, hBdef]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    simp only [hcol]
    rw [show (∑ l, ∑ j, ∑ k, g p α b * v l * v j * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1) b)))
        = g p α b * (1 / 6 : ℝ) *
            (∑ l, ∑ j, ∑ k,
              (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1) b)
              * v l * v j * v k) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ l, ∑ j, ∑ k,
          (rncD3Block g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single j 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single k 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single j 1) b)
          * v l * v j * v k)
        = rncD3Block g gi p v v v b + rncCrossBlock g gi p v v v b
          + rncCrossBlock g gi p v v v b + rncCrossBlock g gi p v v v b from by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [foldD3_all, foldCross_all_kjl, foldCross_all_jkl, foldCross_all_lkj]]
    ring
  rw [hpd2_A_expand g gi hC p hg α v, ← hS1, ← hS2, ← hS3, ← hS4, ← hS5, ← hS7, ← hS9]
  simp only [add_mul, Finset.sum_add_distrib]

set_option maxHeartbeats 6400000 in
/-- **`hpd2_B_folded` — the FOLDED closed form of the B-bracket of `hpd2`.**  Same treatment as
    `hpd2_A_folded`, applied to `hpd2_B_expand`.  Note the B-structure: the metric first index is the
    contraction index `j` (a bound variable), so the `∑_a` Kronecker collapses to `a=j` (not the fixed
    `α`); the two `α2` blocks carry `α` in the MIDDLE (source/mid) slot.  T5 folds (over `j,l`, free `k`)
    to `1/6•(D3(v,e_α,v) + Cross(v,e_α,v) + Cross(e_α,v,v) + Cross(v,v,e_α))`; T9 folds (over `k,l`, with
    `j` a FREE index — a two-slot fold, NOT the full-diagonal three-slot fold of A's T9) to the same
    block combination indexed at `b`.  RHS is the explicit `v`-contracted scalar sum. -/
theorem hpd2_B_folded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b)) (α : Fin n) (v : Point n) :
    (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y j k) α z) l p
              + ∑ c, pd (fun y => g y j k) c p
                  * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
            * v l * v j * v k)
        + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) α p
            * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p)) * v l * v j * v k)
        + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) α p
            * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
            * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p)) * v l * v j * v k)
        + (∑ a, ∑ k, g p a k * v k *
            ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v a
                + rncCrossBlock g gi p v (Pi.single α 1) v a
                + rncCrossBlock g gi p (Pi.single α 1) v v a
                + rncCrossBlock g gi p v v (Pi.single α 1) a)))
        + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
            * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
            * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) l p
            * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
        + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
            * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
            * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
        + (∑ b, ∑ j, g p j b * v j *
            ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v b
                + rncCrossBlock g gi p v (Pi.single α 1) v b
                + rncCrossBlock g gi p (Pi.single α 1) v v b
                + rncCrossBlock g gi p v v (Pi.single α 1) b))) := by
  have hS1 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k,
        (pd (fun z => pd (fun y => g y a b) α z) l p
            + ∑ c, pd (fun y => g y a b) c p
                * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
          * (Pi.single j 1 : Point n) a * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y j k) α z) l p
              + ∑ c, pd (fun y => g y j k) c p
                  * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
            * v l * v j * v k) := by
    rw [reorder_ab_inner5 (fun a b l j k =>
        (pd (fun z => pd (fun y => g y a b) α z) l p
            + ∑ c, pd (fun y => g y a b) c p
                * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
          * (Pi.single j 1 : Point n) a * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    exact double_collapse3 (fun a b => pd (fun z => pd (fun y => g y a b) α z) l p
          + ∑ c, pd (fun y => g y a b) c p
              * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p))) j k
        (v l) (v j) (v k)
  have hS2 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) α p
        * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) α p
          * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p)) * v l * v j * v k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => pd (fun y => g y a b) α p
        * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun b _ => show pd (fun y => g y a b) α p
          * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
          * (Pi.single k 1 : Point n) b * v l * v j * v k
        = pd (fun y => g y a b) α p * (Pi.single k 1 : Point n) b
          * ((1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun b => pd (fun y => g y a b) α p) k
        ((1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p)) * v l * v j * v k)]
    ring
  have hS3 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) α p * (Pi.single j 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
      = (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) α p
          * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k) := by
    rw [reorder_a_inner5 (fun a b l j k => pd (fun y => g y a b) α p * (Pi.single j 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun a _ => show pd (fun y => g y a b) α p * (Pi.single j 1 : Point n) a
          * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k
        = pd (fun y => g y a b) α p * (Pi.single j 1 : Point n) a
          * ((1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun a => pd (fun y => g y a b) α p) j
        ((1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)]
    ring
  have hS4 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) l p
        * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
          * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p)) * v l * v j * v k) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => pd (fun y => g y a b) l p
        * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
        * (Pi.single k 1 : Point n) b * v l * v j * v k)]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun b _ => show pd (fun y => g y a b) l p
          * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
          * (Pi.single k 1 : Point n) b * v l * v j * v k
        = pd (fun y => g y a b) l p * (Pi.single k 1 : Point n) b
          * ((1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun b => pd (fun y => g y a b) l p) k
        ((1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p)) * v l * v j * v k)]
    ring
  have hS5 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b *
          ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1))) a
          * (Pi.single k 1 : Point n) b * v l * v j * v k)
      = (∑ a, ∑ k, g p a k * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v a
              + rncCrossBlock g gi p v (Pi.single α 1) v a
              + rncCrossBlock g gi p (Pi.single α 1) v v a
              + rncCrossBlock g gi p v v (Pi.single α 1) a))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [reorder_b_inner (fun b l j k => g p a b *
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1))) a
        * (Pi.single k 1 : Point n) b * v l * v j * v k),
      reorder3_last_first]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hstep : ∀ l j : Fin n,
        (∑ b, g p a b *
            ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1))) a
            * (Pi.single k 1 : Point n) b * v l * v j * v k)
          = g p a k * v k *
              ((1 / 6 : ℝ) *
                (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1) a))
                * v l * v j := by
      intro l j
      set B : ℝ :=
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1))) a with hBdef
      rw [Finset.sum_congr rfl (fun b _ => show g p a b * B * (Pi.single k 1 : Point n) b * v l * v j * v k
            = (g p a b * (Pi.single k 1 : Point n) b) * (B * v l * v j * v k) from by ring)]
      rw [← Finset.sum_mul, sum_mul_single_right, hBdef]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    simp only [hstep]
    rw [show (∑ l, ∑ j, g p a k * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1) a)) * v l * v j)
        = g p a k * v k * (1 / 6 : ℝ) *
          (∑ l, ∑ j,
            (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1) a) * v l * v j)
        from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    rw [show (∑ l, ∑ j,
          (rncD3Block g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single j 1) (Pi.single α 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single j 1) (Pi.single l 1) a
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single j 1) (Pi.single α 1) a) * v l * v j)
        = rncD3Block g gi p v (Pi.single α 1) v a + rncCrossBlock g gi p v (Pi.single α 1) v a
          + rncCrossBlock g gi p (Pi.single α 1) v v a + rncCrossBlock g gi p v v (Pi.single α 1) a
        from by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [foldD3_midfix, foldCross_dirsource_jl, foldCross_sources, foldCross_dirsk]]
    ring
  have hS7 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y a b) l p * (Pi.single j 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
      = (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) l p
          * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k) := by
    rw [reorder_a_inner5 (fun a b l j k => pd (fun y => g y a b) l p * (Pi.single j 1 : Point n) a
        * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun a _ => show pd (fun y => g y a b) l p * (Pi.single j 1 : Point n) a
          * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k
        = pd (fun y => g y a b) l p * (Pi.single j 1 : Point n) a
          * ((1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
        from by ring)]
    rw [collapse_single_mul (fun a => pd (fun y => g y a b) l p) j
        ((1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)]
    ring
  have hS9 : (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b * (Pi.single j 1 : Point n) a
          * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1)
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1))) b
          * v l * v j * v k)
      = (∑ b, ∑ j, g p j b * v j *
          ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v b
              + rncCrossBlock g gi p v (Pi.single α 1) v b
              + rncCrossBlock g gi p (Pi.single α 1) v v b
              + rncCrossBlock g gi p v v (Pi.single α 1) b))) := by
    rw [reorder_a_inner5 (fun a b l j k => g p a b * (Pi.single j 1 : Point n) a
        * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1)
              + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1))) b
        * v l * v j * v k)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hcol : ∀ l j k : Fin n,
        (∑ a, g p a b * (Pi.single j 1 : Point n) a
            * ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1)
                  + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1))) b
            * v l * v j * v k)
          = g p j b * v l * v j * v k *
              ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1) b)) := by
      intro l j k
      set B : ℝ :=
        ((1 / 6 : ℝ) • (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1)
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1))) b with hBdef
      rw [Finset.sum_congr rfl (fun a _ => show g p a b * (Pi.single j 1 : Point n) a * B * v l * v j * v k
            = g p a b * (Pi.single j 1 : Point n) a * (B * v l * v j * v k) from by ring)]
      rw [show (∑ a, g p a b * (Pi.single j 1 : Point n) a * (B * v l * v j * v k))
            = (∑ a, (Pi.single j 1 : Point n) a * (g p a b)) * (B * v l * v j * v k) from by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by ring]
      rw [sum_single_mul_left (fun a => g p a b) j, hBdef]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    simp only [hcol]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (∑ l, ∑ k, g p j b * v l * v j * v k *
          ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1) b)))
        = g p j b * v j * (1 / 6 : ℝ) *
            (∑ l, ∑ k,
              (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1) b
                + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1) b)
              * v l * v k) from by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ l, ∑ k,
          (rncD3Block g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single k 1) (Pi.single α 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single α 1) (Pi.single k 1) (Pi.single l 1) b
            + rncCrossBlock g gi p (Pi.single l 1) (Pi.single k 1) (Pi.single α 1) b)
          * v l * v k)
        = rncD3Block g gi p v (Pi.single α 1) v b + rncCrossBlock g gi p v (Pi.single α 1) v b
          + rncCrossBlock g gi p (Pi.single α 1) v v b + rncCrossBlock g gi p v v (Pi.single α 1) b
        from by
      simp only [add_mul, Finset.sum_add_distrib]
      rw [foldD3_midfix, foldCross_dirsource_jl, foldCross_sources, foldCross_dirsk]]
    ring
  rw [hpd2_B_expand g gi hC p hg α v, ← hS1, ← hS2, ← hS3, ← hS4, ← hS5, ← hS7, ← hS9]
  simp only [add_mul, Finset.sum_add_distrib]

/-! ### STEP (ii) — the block-`∂²g` conversion + the α1 cancellation (`hpd2_alpha1_cancel`) -/

set_option maxHeartbeats 3200000 in
/-- **`hpd2_block_dd_g` — the `w`-weighted metric contraction of `pd_christoffel_lower_fn`.**
    Contracting a directional `∂Γ`-block `∑_r (∂_r Γ^σ_{λμ})·w^r` against the metric `∑_σ g_{σν}(p)·(·)`
    and applying the differentiated lowered-Christoffel identity term-by-term, the `g·∂Γ` block becomes
      `∑_r w^r·(½(∂_r∂_λ g_{νμ} + ∂_r∂_μ g_{νλ} − ∂_r∂_ν g_{λμ})(p) − ∑_σ ∂_r g_{σν}(p)·Γ^σ_{λμ}(p))`.
    This is the metric-lowered `g·∂Γ → ∂²g − ∂g·Γ` conversion in the exact shape the folded RNC `D³`
    blocks feed it (each block's inner `∂Γ` contraction is a `∑_r (∂_rΓ)·w^r`).  Pure `Finset`/`ring`
    reindex on top of the landed `pd_christoffel_lower_fn`. -/
theorem hpd2_block_dd_g (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (ν lam mu : Fin n) (w : Point n) :
    (∑ σ, g p σ ν * (∑ r, pd (fun y => christoffel g gi σ lam mu y) r p * w r))
      = ∑ r, w r * ((1 / 2) * (pd (fun y => pd (fun z => g z ν mu) lam y) r p
                    + pd (fun y => pd (fun z => g z ν lam) mu y) r p
                    - pd (fun y => pd (fun z => g z lam mu) ν y) r p)
          - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ lam mu p) := by
  -- (1) Pull the `σ`-metric sum inside the `r`-direction sum.
  have hswap : (∑ σ, g p σ ν * (∑ r, pd (fun y => christoffel g gi σ lam mu y) r p * w r))
      = ∑ r, w r * (∑ σ, g p σ ν * pd (fun y => christoffel g gi σ lam mu y) r p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => by ring
  -- (2) Convert each inner `∑_σ g_{σν}·∂_rΓ^σ_{λμ}` by the landed differentiated-lowering identity.
  rw [hswap]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pd_christoffel_lower_fn g gi hsymm hinvF hg hC p ν lam mu r]

set_option maxHeartbeats 6400000 in
/-- **`hpd2_D3_metric_contract` — the metric contraction of the RNC `D³` block into `∂²g − ∂g·Γ`.**
    Contracting `rncD3Block` against `∑_a g_{aν}(p)·(·)` and applying `hpd2_block_dd_g` to each of the
    block's three inner `∂Γ`-directional contractions EXPOSES the hidden second metric derivative:
    the block, which is manifestly `∂Γ` in its raw form, becomes a `∂²g` piece (the metric-Hessian the
    α1 fold1 term must cancel against) minus a `∂g·Γ` piece.  This is the load-bearing "step (ii)"
    conversion that turns the folded `D³` blocks into `∂²g`-carrying terms. -/
theorem hpd2_D3_metric_contract (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (ν : Fin n) (h k l : Point n) :
    (∑ a, g p a ν * rncD3Block g gi p h k l a)
      = -∑ j, ∑ m,
          ((∑ r, l r * ((1 / 2) * (pd (fun y => pd (fun z => g z ν m) j y) r p
                    + pd (fun y => pd (fun z => g z ν j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) ν y) r p)
              - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ j m p))
            * (h j * k m + k j * h m)
          + (∑ r, h r * ((1 / 2) * (pd (fun y => pd (fun z => g z ν m) j y) r p
                    + pd (fun y => pd (fun z => g z ν j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) ν y) r p)
              - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ j m p))
            * (l j * k m + k j * l m)
          + (∑ r, k r * ((1 / 2) * (pd (fun y => pd (fun z => g z ν m) j y) r p
                    + pd (fun y => pd (fun z => g z ν j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) ν y) r p)
              - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ j m p))
            * (l j * h m + h j * l m)) := by
  have hBC : ∀ (w : Point n) (j m : Fin n),
      (∑ a, g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * w r))
        = ∑ r, w r * ((1 / 2) * (pd (fun y => pd (fun z => g z ν m) j y) r p
                    + pd (fun y => pd (fun z => g z ν j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) ν y) r p)
            - ∑ σ, pd (fun y => g y σ ν) r p * christoffel g gi σ j m p) :=
    fun w j m => hpd2_block_dd_g g gi hsymm hinvF hg hC p ν j m w
  simp only [rncD3Block]
  -- Move the metric sum through the `-∑_j∑_m`, reorder to `∑_j∑_m∑_a`, distribute onto the 3 blocks.
  rw [show (∑ a, g p a ν * -∑ j, ∑ m,
        ((∑ r, pd (fun y => christoffel g gi a j m y) r p * l r) * (h j * k m + k j * h m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r) * (l j * k m + k j * l m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r) * (l j * h m + h j * l m)))
      = -∑ j, ∑ m, ∑ a, g p a ν *
        ((∑ r, pd (fun y => christoffel g gi a j m y) r p * l r) * (h j * k m + k j * h m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r) * (l j * k m + k j * l m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r) * (l j * h m + h j * l m))
      from by
    simp only [mul_neg, Finset.mul_sum]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  -- For fixed `j,m`: distribute `∑_a g_{aν}·(A+B+C)` and pull the `a`-free factors out.
  rw [show (∑ a, g p a ν *
        ((∑ r, pd (fun y => christoffel g gi a j m y) r p * l r) * (h j * k m + k j * h m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r) * (l j * k m + k j * l m)
          + (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r) * (l j * h m + h j * l m)))
      = (h j * k m + k j * h m)
          * (∑ a, g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * l r))
        + (l j * k m + k j * l m)
          * (∑ a, g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r))
        + (l j * h m + h j * l m)
          * (∑ a, g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r))
      from by
    have e1 : ∀ a : Fin n, g p a ν *
          ((∑ r, pd (fun y => christoffel g gi a j m y) r p * l r) * (h j * k m + k j * h m)
            + (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r) * (l j * k m + k j * l m)
            + (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r) * (l j * h m + h j * l m))
        = ((h j * k m + k j * h m) * (g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * l r))
            + (l j * k m + k j * l m) * (g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * h r)))
          + (l j * h m + h j * l m) * (g p a ν * (∑ r, pd (fun y => christoffel g gi a j m y) r p * k r)) :=
      fun a => by ring
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]]
  rw [hBC l j m, hBC h j m, hBC k j m]
  ring

/-- **`hpd2_fold5A_split` — isolate the D³ block of `A`'s `fold5` (contract-ready) from its Cross terms.** -/
theorem hpd2_fold5A_split (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ a, ∑ k, g p a k * v k * ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) v v a
        + rncCrossBlock g gi p (Pi.single α 1) v v a
        + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a)))
      = (1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p (Pi.single α 1) v v a)
        + (1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k
            * (rncCrossBlock g gi p (Pi.single α 1) v v a
              + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a)) := by
  have h1 : ∀ a k : Fin n, g p a k * v k * ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) v v a
        + rncCrossBlock g gi p (Pi.single α 1) v v a
        + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a))
      = (1 / 6 : ℝ) * (g p a k * v k * rncD3Block g gi p (Pi.single α 1) v v a)
        + (1 / 6 : ℝ) * (g p a k * v k
            * (rncCrossBlock g gi p (Pi.single α 1) v v a
              + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a)) := fun a k => by ring
  simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`hpd2_fold9A_split` — isolate the D³ block of `A`'s `fold9` (contract-ready) from its Cross term.** -/
theorem hpd2_fold9A_split (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, g p α b * ((1 / 6 : ℝ) * (rncD3Block g gi p v v v b + 3 * rncCrossBlock g gi p v v v b)))
      = (1 / 6 : ℝ) * (∑ b, g p α b * rncD3Block g gi p v v v b)
        + (1 / 2 : ℝ) * (∑ b, g p α b * rncCrossBlock g gi p v v v b) := by
  have h1 : ∀ b : Fin n, g p α b * ((1 / 6 : ℝ) * (rncD3Block g gi p v v v b + 3 * rncCrossBlock g gi p v v v b))
      = (1 / 6 : ℝ) * (g p α b * rncD3Block g gi p v v v b)
        + (1 / 2 : ℝ) * (g p α b * rncCrossBlock g gi p v v v b) := fun b => by ring
  simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`hpd2_fold5B_split` — isolate the D³ block of `B`'s `fold5` (contract-ready) from its Cross terms.** -/
theorem hpd2_fold5B_split (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ a, ∑ k, g p a k * v k * ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v a
        + rncCrossBlock g gi p v (Pi.single α 1) v a
        + rncCrossBlock g gi p (Pi.single α 1) v v a
        + rncCrossBlock g gi p v v (Pi.single α 1) a)))
      = (1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a)
        + (1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k
            * (rncCrossBlock g gi p v (Pi.single α 1) v a
              + rncCrossBlock g gi p (Pi.single α 1) v v a
              + rncCrossBlock g gi p v v (Pi.single α 1) a)) := by
  have h1 : ∀ a k : Fin n, g p a k * v k * ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v a
        + rncCrossBlock g gi p v (Pi.single α 1) v a
        + rncCrossBlock g gi p (Pi.single α 1) v v a
        + rncCrossBlock g gi p v v (Pi.single α 1) a))
      = (1 / 6 : ℝ) * (g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a)
        + (1 / 6 : ℝ) * (g p a k * v k
            * (rncCrossBlock g gi p v (Pi.single α 1) v a
              + rncCrossBlock g gi p (Pi.single α 1) v v a
              + rncCrossBlock g gi p v v (Pi.single α 1) a)) := fun a k => by ring
  simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`hpd2_fold9B_split` — isolate the D³ block of `B`'s `fold9` (contract-ready) from its Cross terms.** -/
theorem hpd2_fold9B_split (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, ∑ j, g p j b * v j * ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v b
        + rncCrossBlock g gi p v (Pi.single α 1) v b
        + rncCrossBlock g gi p (Pi.single α 1) v v b
        + rncCrossBlock g gi p v v (Pi.single α 1) b)))
      = (1 / 6 : ℝ) * (∑ b, ∑ j, g p j b * v j * rncD3Block g gi p v (Pi.single α 1) v b)
        + (1 / 6 : ℝ) * (∑ b, ∑ j, g p j b * v j
            * (rncCrossBlock g gi p v (Pi.single α 1) v b
              + rncCrossBlock g gi p (Pi.single α 1) v v b
              + rncCrossBlock g gi p v v (Pi.single α 1) b)) := by
  have h1 : ∀ b j : Fin n, g p j b * v j * ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v b
        + rncCrossBlock g gi p v (Pi.single α 1) v b
        + rncCrossBlock g gi p (Pi.single α 1) v v b
        + rncCrossBlock g gi p v v (Pi.single α 1) b))
      = (1 / 6 : ℝ) * (g p j b * v j * rncD3Block g gi p v (Pi.single α 1) v b)
        + (1 / 6 : ℝ) * (g p j b * v j
            * (rncCrossBlock g gi p v (Pi.single α 1) v b
              + rncCrossBlock g gi p (Pi.single α 1) v v b
              + rncCrossBlock g gi p v v (Pi.single α 1) b)) := fun b j => by ring
  simp only [h1, Finset.sum_add_distrib, Finset.mul_sum]

/-- **`hpd2_fold5A_D3ready`** — reorder `A.fold5`'s isolated D³ sum into `hpd2_D3_metric_contract` LHS
    shape (`∑_k v^k·∑_a g_{ak}·D3(e_α,v,v)_a`), one contraction per outer index `k`. -/
theorem hpd2_fold5A_D3ready (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p (Pi.single α 1) v v a)
      = ∑ k, v k * (∑ a, g p a k * rncD3Block g gi p (Pi.single α 1) v v a) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **`hpd2_fold5B_D3ready`** — reorder `B.fold5`'s isolated D³ sum into contract LHS shape
    (`∑_k v^k·∑_a g_{ak}·D3(v,e_α,v)_a`). -/
theorem hpd2_fold5B_D3ready (g gi : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a)
      = ∑ k, v k * (∑ a, g p a k * rncD3Block g gi p v (Pi.single α 1) v a) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **`hpd2_fold9A_D3ready`** — swap the metric symmetry so `A.fold9`'s D³ sum is in contract LHS shape
    (`∑_a g_{aα}·D3(v,v,v)_a`, `ν=α`). -/
theorem hpd2_fold9A_D3ready (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, g p α b * rncD3Block g gi p v v v b)
      = ∑ a, g p a α * rncD3Block g gi p v v v a :=
  Finset.sum_congr rfl fun b _ => by rw [hsymm p α b]

/-- **`hpd2_fold9B_D3ready`** — reorder + metric-symmetry swap so `B.fold9`'s D³ sum is in contract LHS
    shape (`∑_j v^j·∑_b g_{bj}·D3(v,e_α,v)_b`, `ν=j` free). -/
theorem hpd2_fold9B_D3ready (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, ∑ j, g p j b * v j * rncD3Block g gi p v (Pi.single α 1) v b)
      = ∑ j, v j * (∑ b, g p b j * rncD3Block g gi p v (Pi.single α 1) v b) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [hsymm p j b]; ring

set_option maxHeartbeats 6400000 in
/-- **`hpd2_fold9A_blockconv`** — apply `hpd2_D3_metric_contract` to `A.fold9`'s (reordered) D³ sum,
    EXPOSING the second metric derivative: the manifestly-`∂Γ` block `∑_b g_{αb}·D3(v,v,v)_b` becomes
    the explicit `∂²g − ∂g·Γ` form (three identical `BC(v;α,j,m)·2v^j v^m` terms, `ν=α`, `h=k=l=v`).
    This is the end-to-end block-conversion for the simplest (full-diagonal, single-sum) fold; the other
    three blocks (`fold5A`, `fold5B`, `fold9B`) convert identically via their `*_D3ready` reshapes. -/
theorem hpd2_fold9A_blockconv (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, g p α b * rncD3Block g gi p v v v b)
      = -∑ j, ∑ m,
          ((∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z α m) j y) r p
                    + pd (fun y => pd (fun z => g z α j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) α y) r p)
              - ∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
            * (v j * v m + v j * v m)
          + (∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z α m) j y) r p
                    + pd (fun y => pd (fun z => g z α j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) α y) r p)
              - ∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
            * (v j * v m + v j * v m)
          + (∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z α m) j y) r p
                    + pd (fun y => pd (fun z => g z α j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) α y) r p)
              - ∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
            * (v j * v m + v j * v m)) := by
  rw [hpd2_fold9A_D3ready g gi hsymm p α v]
  exact hpd2_D3_metric_contract g gi hsymm hinvF hg hC p α v v v

set_option maxHeartbeats 6400000 in
/-- **`hpd2_fold5A_blockconv`** — `hpd2_D3_metric_contract` applied per outer `k` to `A.fold5`'s
    (reshaped) D³ sum (`ν=k`, `h=e_α`, `k'=l'=v`), exposing `∂²g − ∂g·Γ`. -/
theorem hpd2_fold5A_blockconv (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    (∑ k, v k * (∑ a, g p a k * rncD3Block g gi p (Pi.single α 1) v v a))
      = ∑ k, v k * (-∑ j, ∑ m,
          ((∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * ((Pi.single α 1 : Point n) j * v m + v j * (Pi.single α 1 : Point n) m)
          + (∑ r, (Pi.single α 1 : Point n) r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * (v j * v m + v j * v m)
          + (∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * (v j * (Pi.single α 1 : Point n) m + (Pi.single α 1 : Point n) j * v m))) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact hpd2_D3_metric_contract g gi hsymm hinvF hg hC p k (Pi.single α 1) v v

set_option maxHeartbeats 6400000 in
/-- **`hpd2_fold5B_blockconv`** — `hpd2_D3_metric_contract` applied per outer `k` to `B.fold5`'s
    (reshaped) D³ sum (`ν=k`, `h=l'=v`, `k'=e_α`), exposing `∂²g − ∂g·Γ`. -/
theorem hpd2_fold5B_blockconv (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    (∑ k, v k * (∑ a, g p a k * rncD3Block g gi p v (Pi.single α 1) v a))
      = ∑ k, v k * (-∑ j, ∑ m,
          ((∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * (v j * (Pi.single α 1 : Point n) m + (Pi.single α 1 : Point n) j * v m)
          + (∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * (v j * (Pi.single α 1 : Point n) m + (Pi.single α 1 : Point n) j * v m)
          + (∑ r, (Pi.single α 1 : Point n) r * ((1 / 2) * (pd (fun y => pd (fun z => g z k m) j y) r p
                    + pd (fun y => pd (fun z => g z k j) m y) r p
                    - pd (fun y => pd (fun z => g z j m) k y) r p)
              - ∑ σ, pd (fun y => g y σ k) r p * christoffel g gi σ j m p))
            * (v j * v m + v j * v m))) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  exact hpd2_D3_metric_contract g gi hsymm hinvF hg hC p k v (Pi.single α 1) v

set_option maxHeartbeats 6400000 in
/-- **`hpd2_fold9B_blockconv`** — `hpd2_D3_metric_contract` applied per free outer `j` to `B.fold9`'s
    (reshaped) D³ sum (`ν=j`, `h=l'=v`, `k'=e_α`), exposing `∂²g − ∂g·Γ`. -/
theorem hpd2_fold9B_blockconv (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    (∑ j, v j * (∑ b, g p b j * rncD3Block g gi p v (Pi.single α 1) v b))
      = ∑ j, v j * (-∑ s, ∑ t,
          ((∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z j t) s y) r p
                    + pd (fun y => pd (fun z => g z j s) t y) r p
                    - pd (fun y => pd (fun z => g z s t) j y) r p)
              - ∑ σ, pd (fun y => g y σ j) r p * christoffel g gi σ s t p))
            * (v s * (Pi.single α 1 : Point n) t + (Pi.single α 1 : Point n) s * v t)
          + (∑ r, v r * ((1 / 2) * (pd (fun y => pd (fun z => g z j t) s y) r p
                    + pd (fun y => pd (fun z => g z j s) t y) r p
                    - pd (fun y => pd (fun z => g z s t) j y) r p)
              - ∑ σ, pd (fun y => g y σ j) r p * christoffel g gi σ s t p))
            * (v s * (Pi.single α 1 : Point n) t + (Pi.single α 1 : Point n) s * v t)
          + (∑ r, (Pi.single α 1 : Point n) r * ((1 / 2) * (pd (fun y => pd (fun z => g z j t) s y) r p
                    + pd (fun y => pd (fun z => g z j s) t y) r p
                    - pd (fun y => pd (fun z => g z s t) j y) r p)
              - ∑ σ, pd (fun y => g y σ j) r p * christoffel g gi σ s t p))
            * (v s * v t + v s * v t))) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact hpd2_D3_metric_contract g gi hsymm hinvF hg hC p j v (Pi.single α 1) v

/-- **`hpd2_hessian_regroup` — the `∂²g` cancellation identity (recipe step (3), NO Clairaut).**
    The metric-Hessian content produced by the fully-symmetric `v`-weighted contraction of the
    (converted) `α2` `D³` block regroups — by pure dummy-index reindexing under the symmetric `v³`
    weights (`Finset.sum_comm`, no equality of mixed partials) — into exactly the combination
    `2·⟨∂_l∂_j g_{αk}⟩ − ⟨∂_l∂_α g_{jk}⟩` that the folded `α1` `fold1` term (`2·fold1_A − fold1_B`)
    cancels.  The LHS is the fully-symmetrized block-Hessian core (`∑_{jm} (∑_r v^r·½(∂_r∂_j g_{αm}
    + ∂_r∂_m g_{αj} − ∂_r∂_α g_{jm}))·v^j v^m`, without the `½`/`3`/`−6` block prefactors, which the
    assembly carries), the RHS is `2·P − Q` with `P` = `fold1_A`'s Hessian and `Q` = `fold1_B`'s. -/
theorem hpd2_hessian_regroup (g : Point n → Fin n → Fin n → ℝ) (p : Point n) (α : Fin n) (v : Point n) :
    (∑ j, ∑ m, (∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
      = 2 * (∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y α k) j z) l p * v l * v j * v k)
        - (∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y j k) α z) l p * v l * v j * v k) := by
  -- (1) distribute the inner product and split into three triple sums A3 + B3 − C3.
  have hdist : (∑ j, ∑ m, (∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
      = (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z α m) j y) r p)
        + (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z α j) m y) r p)
        - (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z j m) α y) r p) := by
    have h1 : (∑ j, ∑ m, (∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
        = ∑ j, ∑ m, ∑ r, (v r * v j * v m * pd (fun y => pd (fun z => g z α m) j y) r p
              + v r * v j * v m * pd (fun y => pd (fun z => g z α j) m y) r p
              - v r * v j * v m * pd (fun y => pd (fun z => g z j m) α y) r p) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- (2) reindex each triple sum to the `fold1` `⟨·⟩` shape (pure `sum_comm`).
  have hA3 : (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z α m) j y) r p)
      = ∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y α k) j z) l p * v l * v j * v k := by
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_comm (f := fun m r => v r * v j * v m * pd (fun y => pd (fun z => g z α m) j y) r p))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun m _ => by ring
  have hB3 : (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z α j) m y) r p)
      = ∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y α k) j z) l p * v l * v j * v k := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun m (_ : m ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_comm (f := fun j r => v r * v j * v m * pd (fun y => pd (fun z => g z α j) m y) r p))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun m _ => by ring
  have hC3 : (∑ j, ∑ m, ∑ r, v r * v j * v m * pd (fun y => pd (fun z => g z j m) α y) r p)
      = ∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y j k) α z) l p * v l * v j * v k := by
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_comm (f := fun m r => v r * v j * v m * pd (fun y => pd (fun z => g z j m) α y) r p))]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun m _ => by ring
  rw [hdist, hA3, hB3, hC3]
  ring

/-- **`hpd2_fold5_blocks_cancel` — the raw `D³`-block cancellation (recipe step (2), full symmetry).**
    Because `rncD3Block` is fully symmetric in its three direction arguments (`rncD3Block_swap12`), the
    `α2` `D³` blocks of `A.fold5` (`D3(e_α,v,v)`) and of `B.fold5`/`B.fold9` (`D3(v,e_α,v)`) are
    literally EQUAL after the metric symmetry `hsymm` swap; with the `A`-block entering `2A` with weight
    `2` and the two `B`-blocks entering `−B` with weight `1` each, they cancel identically at the RAW
    block level — no `∂²g` conversion needed.  (The only surviving `D³` block is `A.fold9`'s
    `D3(v,v,v)`, handled by `hpd2_fold9A_blockconv` + `hpd2_hessian_regroup`.) -/
theorem hpd2_fold5_blocks_cancel (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (p : Point n) (α : Fin n) (v : Point n) :
    2 * ((1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p (Pi.single α 1) v v a))
      - ((1 / 6 : ℝ) * (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a))
      - ((1 / 6 : ℝ) * (∑ b, ∑ j, g p j b * v j * rncD3Block g gi p v (Pi.single α 1) v b)) = 0 := by
  have e1 : (∑ a, ∑ k, g p a k * v k * rncD3Block g gi p (Pi.single α 1) v v a)
      = ∑ a, ∑ k, g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by
      rw [rncD3Block_swap12]
  have e3 : (∑ b, ∑ j, g p j b * v j * rncD3Block g gi p v (Pi.single α 1) v b)
      = ∑ a, ∑ k, g p a k * v k * rncD3Block g gi p v (Pi.single α 1) v a :=
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => by
      rw [hsymm p j b]
  rw [e1, e3]; ring

set_option maxHeartbeats 6400000 in
/-- **`hpd2_fold9A_D3_hessian_christ` — factor `A.fold9`'s converted `D3(v,v,v)` block into the
    `hpd2_hessian_regroup` core plus the `∂g·Γ` residual.**  Applying `hpd2_fold9A_blockconv` and
    factoring each `BC = ∑_r w^r(½(∂²g-triple) − ∑_σ ∂g·Γ)` into its Hessian and Christoffel parts,
    the (single surviving) `D³` block `∑_b g_{αb}·D3(v,v,v)_b` equals `−3·⟨Hessian core⟩ + 6·⟨∂g·Γ core⟩`,
    where `⟨Hessian core⟩` is EXACTLY `hpd2_hessian_regroup`'s LHS and `⟨∂g·Γ core⟩` is the `∂²g`-free
    Christoffel residual.  This is the bridge that turns the last block into `hessian_regroup`-ready form
    (`−3·(2P−Q)`) while depositing its `∂g·Γ` piece into the residual. -/
theorem hpd2_fold9A_D3_hessian_christ (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    (∑ b, g p α b * rncD3Block g gi p v v v b)
      = -3 * (∑ j, ∑ m, (∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
        + 6 * (∑ j, ∑ m, (∑ r, v r * (∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
              * (v j * v m)) := by
  rw [hpd2_fold9A_blockconv g gi hsymm hinvF hg hC p α v]
  rw [show (-3 * (∑ j, ∑ m, (∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
        + 6 * (∑ j, ∑ m, (∑ r, v r * (∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
              * (v j * v m)))
      = ∑ j, ∑ m,
          (-3 * ((∑ r, v r * (pd (fun y => pd (fun z => g z α m) j y) r p
                + pd (fun y => pd (fun z => g z α j) m y) r p
                - pd (fun y => pd (fun z => g z j m) α y) r p)) * (v j * v m))
           + 6 * ((∑ r, v r * (∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p))
                * (v j * v m))) from by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  set DDsum : Fin n → ℝ := fun r => pd (fun y => pd (fun z => g z α m) j y) r p
              + pd (fun y => pd (fun z => g z α j) m y) r p
              - pd (fun y => pd (fun z => g z j m) α y) r p with hDD
  set Csum : Fin n → ℝ := fun r => ∑ σ, pd (fun y => g y σ α) r p * christoffel g gi σ j m p with hCs
  have hsplit : (∑ r, v r * ((1 / 2) * DDsum r - Csum r))
      = (1 / 2) * (∑ r, v r * DDsum r) - (∑ r, v r * Csum r) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  show -(((∑ r, v r * ((1 / 2) * DDsum r - Csum r))) * (v j * v m + v j * v m)
        + (∑ r, v r * ((1 / 2) * DDsum r - Csum r)) * (v j * v m + v j * v m)
        + (∑ r, v r * ((1 / 2) * DDsum r - Csum r)) * (v j * v m + v j * v m))
      = -3 * ((∑ r, v r * DDsum r) * (v j * v m)) + 6 * ((∑ r, v r * Csum r) * (v j * v m))
  rw [hsplit]
  ring

set_option maxHeartbeats 12800000 in
/-- **`hpd2_alpha1_cancel` — the `∂²g` (α1-Hessian) cancellation in `2·A − B` (recipe steps (1)–(4)).**
    Starting from `2·(A-bracket) − (B-bracket)` of `hpd2` (in `expPullbackMetric` second-partial form),
    fold via `hpd2_A_folded`/`hpd2_B_folded`, then convert ONLY `A.fold9`'s `D3(v,v,v)` block (the sole
    block carrying `∂²g` that must be matched) via `hpd2_fold9A_D3_hessian_christ` into `−3·⟨Hessian core⟩
    + 6·⟨∂g·Γ core⟩`, and regroup the Hessian core by `hpd2_hessian_regroup` (`= 2P − Q`).  The metric
    Hessians `P = fold1_A` and `Q = fold1_B` (split off explicitly) then cancel the block Hessian
    (`2P + (−(2P−Q)) − Q = 0`), leaving a fully `∂²g`-FREE residual in `{∂g, Γ, ∂Γ, g}`: the `fold1`
    `∂g·Γ` parts, `fold2/3/4/6/7/8` (`∂g·Γ` and `ΓΓ`), the `fold5` `∂Γ`-blocks (`rncD3Block`/`rncCrossBlock`,
    left intact — `∂Γ` is admissible), the `fold9` Cross (`ΓΓ`) block, and the `∂g·Γ` Christoffel core
    from the converted `A.fold9` block.  Axiom-clean; `ring` closes after the four landed rewrites. -/
theorem hpd2_alpha1_cancel (g gi : Point n → Fin n → Fin n → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) (α : Fin n) (v : Point n) :
    2 * (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x α k) j y) l 0 * v l * v j * v k)
      - (∑ l, ∑ j, ∑ k, pd (fun y => pd (fun x =>
        expPullbackMetric g gi hC p x j k) α y) l 0 * v l * v j * v k)
      = 2 * (
          -- fold1_A ∂g·Γ part (the α1 Hessian cancels against the block Hessian)
          (∑ l, ∑ j, ∑ k, (∑ c, pd (fun y => g y α k) c p
                * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p))) * v l * v j * v k)
          -- fold2_A
          + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) j p
              * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p)) * v l * v j * v k)
          -- fold3_A
          + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) j p
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
          -- fold4_A
          + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
              * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p)) * v l * v j * v k)
          -- fold5_A (∂Γ block, allowed in residual)
          + (∑ a, ∑ k, g p a k * v k *
              ((1 / 6 : ℝ) * (rncD3Block g gi p (Pi.single α 1) v v a
                  + rncCrossBlock g gi p (Pi.single α 1) v v a
                  + 2 * rncCrossBlock g gi p v (Pi.single α 1) v a)))
          -- fold6_A
          + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
              * (1 / 2 * (-christoffel g gi a α j p - christoffel g gi a j α p))
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
          -- fold7_A
          + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y α b) l p
              * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
          -- fold8_A
          + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
              * (1 / 2 * (-christoffel g gi a α l p - christoffel g gi a l α p))
              * (1 / 2 * (-christoffel g gi b k j p - christoffel g gi b j k p)) * v l * v j * v k)
          -- fold9_A ∂g·Γ (Christoffel residual from converting its D3(v,v,v) block)
          + (∑ j, ∑ m, (∑ r, v r * (∑ σ, pd (fun y => g y σ α) r p
                * christoffel g gi σ j m p)) * (v j * v m))
          -- fold9_A Cross part
          + (1 / 2 : ℝ) * (∑ b, g p α b * rncCrossBlock g gi p v v v b))
      - (
          -- fold1_B ∂g·Γ part
          (∑ l, ∑ j, ∑ k, (∑ c, pd (fun y => g y j k) c p
                * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p))) * v l * v j * v k)
          -- fold2_B
          + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) α p
              * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p)) * v l * v j * v k)
          -- fold3_B
          + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) α p
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
          -- fold4_B
          + (∑ a, ∑ l, ∑ j, ∑ k, pd (fun y => g y a k) l p
              * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p)) * v l * v j * v k)
          -- fold5_B (∂Γ block)
          + (∑ a, ∑ k, g p a k * v k *
              ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v a
                  + rncCrossBlock g gi p v (Pi.single α 1) v a
                  + rncCrossBlock g gi p (Pi.single α 1) v v a
                  + rncCrossBlock g gi p v v (Pi.single α 1) a)))
          -- fold6_B
          + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
              * (1 / 2 * (-christoffel g gi a j α p - christoffel g gi a α j p))
              * (1 / 2 * (-christoffel g gi b k l p - christoffel g gi b l k p)) * v l * v j * v k)
          -- fold7_B
          + (∑ b, ∑ l, ∑ j, ∑ k, pd (fun y => g y j b) l p
              * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
          -- fold8_B
          + (∑ a, ∑ b, ∑ l, ∑ j, ∑ k, g p a b
              * (1 / 2 * (-christoffel g gi a j l p - christoffel g gi a l j p))
              * (1 / 2 * (-christoffel g gi b k α p - christoffel g gi b α k p)) * v l * v j * v k)
          -- fold9_B (∂Γ block)
          + (∑ b, ∑ j, g p j b * v j *
              ((1 / 6 : ℝ) * (rncD3Block g gi p v (Pi.single α 1) v b
                  + rncCrossBlock g gi p v (Pi.single α 1) v b
                  + rncCrossBlock g gi p (Pi.single α 1) v v b
                  + rncCrossBlock g gi p v v (Pi.single α 1) b)))) := by
  rw [hpd2_A_folded g gi hC p hg α v, hpd2_B_folded g gi hC p hg α v]
  rw [hpd2_fold9A_split g gi p α v]
  rw [hpd2_fold9A_D3_hessian_christ g gi hsymm hinvF hg hC p α v]
  rw [hpd2_hessian_regroup g p α v]
  -- split fold1_A and fold1_B into Hessian + ∂g·Γ so the Hessian atoms cancel.
  have split1A : (∑ l, ∑ j, ∑ k,
        (pd (fun z => pd (fun y => g y α k) j z) l p
            + ∑ c, pd (fun y => g y α k) c p
                * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
          * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y α k) j z) l p * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, (∑ c, pd (fun y => g y α k) c p
              * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p))) * v l * v j * v k) := by
    rw [show (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y α k) j z) l p
              + ∑ c, pd (fun y => g y α k) c p
                  * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p)))
            * v l * v j * v k)
        = ∑ l, ∑ j, ∑ k, (pd (fun z => pd (fun y => g y α k) j z) l p * v l * v j * v k
            + (∑ c, pd (fun y => g y α k) c p
                * (1 / 2 * (-christoffel g gi c j l p - christoffel g gi c l j p))) * v l * v j * v k)
        from Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
  have split1B : (∑ l, ∑ j, ∑ k,
        (pd (fun z => pd (fun y => g y j k) α z) l p
            + ∑ c, pd (fun y => g y j k) c p
                * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
          * v l * v j * v k)
      = (∑ l, ∑ j, ∑ k, pd (fun z => pd (fun y => g y j k) α z) l p * v l * v j * v k)
        + (∑ l, ∑ j, ∑ k, (∑ c, pd (fun y => g y j k) c p
              * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p))) * v l * v j * v k) := by
    rw [show (∑ l, ∑ j, ∑ k,
          (pd (fun z => pd (fun y => g y j k) α z) l p
              + ∑ c, pd (fun y => g y j k) c p
                  * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p)))
            * v l * v j * v k)
        = ∑ l, ∑ j, ∑ k, (pd (fun z => pd (fun y => g y j k) α z) l p * v l * v j * v k
            + (∑ c, pd (fun y => g y j k) c p
                * (1 / 2 * (-christoffel g gi c α l p - christoffel g gi c l α p))) * v l * v j * v k)
        from Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => by ring]
    simp only [Finset.sum_add_distrib]
  rw [split1A, split1B]
  ring


/-!
### CHECKPOINT — step (ii) block-`∂²g` conversion LANDED; `hpd2_alpha1_cancel` remaining matching

LANDED (this brick, both axiom-clean `[propext, Classical.choice, Quot.sound]`, file GREEN):
* `hpd2_block_dd_g` — the `w`-weighted metric contraction of the differentiated lowered-Christoffel
  identity: `∑_σ g_{σν}(p)·(∑_r ∂_rΓ^σ_{λμ}(p)·w^r) = ∑_r w^r·(½(∂_r∂_λ g_{νμ}+∂_r∂_μ g_{νλ}−∂_r∂_ν g_{λμ})
  − ∑_σ ∂_r g_{σν}·Γ^σ_{λμ})`.  This is exactly the shape each RNC `D³` inner `∂Γ`-contraction feeds.
* `hpd2_D3_metric_contract` — the full metric contraction of `rncD3Block` into `∂²g − ∂g·Γ`:
  `∑_a g_{aν}(p)·rncD3Block g gi p h k l a = −∑_j∑_m ( BC(l,j,m)·(h^j k^m+k^j h^m)
    + BC(h,j,m)·(l^j k^m+k^j l^m) + BC(k,j,m)·(l^j h^m+h^j l^m) )`, where `BC(w,j,m)` is the
  `hpd2_block_dd_g` bracket at `(ν, λ=j, μ=m, w)`.  This EXPOSES the hidden second metric derivative
  the α1 `fold1` term cancels against (the block is manifestly `∂Γ` in raw form; contracted with the
  metric it becomes `∂²g − ∂g·Γ`).

LANDED (this brick — recipe steps (1)–(2) COMPLETE for ALL four `D³` blocks; each axiom-clean
`[propext, Classical.choice, Quot.sound]`, file GREEN):
* `hpd2_fold5A_split`, `hpd2_fold9A_split`, `hpd2_fold5B_split`, `hpd2_fold9B_split` — split each
  folded `α2` block `(1/6)•(D3 + Cross…)` into its `D³` part (contract-ready) plus its `Cross` part
  (pure `ΓΓ`, carries no `∂²g`, stays in the residual).  `fold9A` peels as `(1/6)·D3 + (1/2)·Cross`.
* `hpd2_fold5A_D3ready`, `hpd2_fold5B_D3ready`, `hpd2_fold9A_D3ready`, `hpd2_fold9B_D3ready` — reshape
  each isolated `D³` sum into the EXACT `hpd2_D3_metric_contract` LHS `∑_a g_{aν}·D3(…)_a`:
  - `fold5A`: `∑_k v^k·(∑_a g_{ak}·D3(e_α,v,v)_a)` (`ν=k`).
  - `fold5B`: `∑_k v^k·(∑_a g_{ak}·D3(v,e_α,v)_a)` (`ν=k`).
  - `fold9A`: `∑_a g_{aα}·D3(v,v,v)_a` (`ν=α`, via `hsymm`).
  - `fold9B`: `∑_j v^j·(∑_b g_{bj}·D3(v,e_α,v)_b)` (`ν=j` FREE, via `hsymm`).
* `hpd2_fold9A_blockconv`, `hpd2_fold5A_blockconv`, `hpd2_fold5B_blockconv`, `hpd2_fold9B_blockconv` —
  apply `hpd2_D3_metric_contract` to the reshaped sums, EXPOSING the second metric derivative: each
  block is now the explicit `∂²g − ∂g·Γ` form `−∑_j∑_m (BC(·)·(slot-products))`, `BC` the
  `hpd2_block_dd_g` bracket at the block's `ν` and directions.  `fold9A` has all three `BC(v;α,j,m)`
  identical (h=k=l=v); `fold5A`/`fold5B` carry one `BC(e_α;k,j,m)` (the `α`-selected `∑_r δ_{αr}`
  piece) among two `BC(v;k,j,m)`; `fold9B` likewise with free `ν=j`.

LANDED (this brick — recipe steps (3)–(4) COMPLETE; each axiom-clean `[propext, Classical.choice,
Quot.sound]`, file GREEN — `hpd2_alpha1_cancel` FULLY CLOSED, `2·A − B` is now `∂²g`-free):
* `hpd2_hessian_regroup` — the `∂²g` cancellation IDENTITY (recipe step (3), NO Clairaut): the
  fully-symmetrized block-Hessian core `∑_{jm}(∑_r v^r·(∂_r∂_j g_{αm}+∂_r∂_m g_{αj}−∂_r∂_α g_{jm}))·v^j v^m`
  `= 2·⟨∂_l∂_j g_{αk}⟩ − ⟨∂_l∂_α g_{jk}⟩ = 2P − Q`, by pure dummy reindex under the symmetric `v³` weights
  (`Finset.sum_comm`; no equality of mixed partials).
* `hpd2_fold5_blocks_cancel` — the RAW `D³`-block cancellation via full `rncD3Block` symmetry
  (`rncD3Block_swap12` + `hsymm`): `2·A.fold5_D³ − B.fold5_D³ − B.fold9_D³ = 0` at the block level.  (This
  bonus fact is NOT needed for the `∂²g`-free residual — the `fold5` `D³` blocks are `∂Γ`, admissible in
  the residual — but records that they in fact cancel identically.)
* `hpd2_fold9A_D3_hessian_christ` — factor `A.fold9`'s converted `D3(v,v,v)` block into
  `−3·⟨Hessian core⟩ + 6·⟨∂g·Γ core⟩` (the bridge from `hpd2_fold9A_blockconv` to `hpd2_hessian_regroup`).
* `hpd2_alpha1_cancel` — the assembly: `rw [hpd2_A_folded, hpd2_B_folded, hpd2_fold9A_split,
  hpd2_fold9A_D3_hessian_christ, hpd2_hessian_regroup]`, split `fold1_A/fold1_B` into Hessian + `∂g·Γ`,
  then `ring`.  Only `A.fold9`'s `D3(v,v,v)` needs conversion (the sole block carrying the `∂²g` that must
  be MATCHED); the Hessians `2P` (`fold1_A`), `−Q` (`fold1_B`) and the block Hessian `−(2P−Q)` cancel to 0,
  leaving the `∂²g`-FREE residual in `{∂g, Γ, ∂Γ, g}` (fold1 `∂g·Γ`, fold2/3/4/6/7/8, the fold5 `∂Γ`-blocks
  intact, the fold9 Cross `ΓΓ`, and the fold9 `∂g·Γ` Christoffel core).  NOTE `hpd2_cubic_vanish` / the
  full `2A−B=0` assembly are the NEXT bricks (NOT attempted here).
-/

end QIQTH.PullbackMetric
