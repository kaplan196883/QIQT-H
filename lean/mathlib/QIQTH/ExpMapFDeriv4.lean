/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderUnif
import QIQTH.ExpJet5Residual
import QIQTH.ExpJet5D5
import QIQTH.ExpMapFDeriv3

/-!
# JET-5 TOWER -- rung J5-5(d): `fderiv^4 exp_p` is Frechet-differentiable with derivative `D5_v`.

Faithful one-Frechet-order-up mirror of the Rung-4 capstone `expMap_fderiv3_hasFDerivAt`
(`ExpMapFDeriv3.lean`).  For `||v|| < expRho` and the first-variation propagator witness `Phi` at `v`,

  `HasFDerivAt (w -> fderiv^4 exp_p w) (expJetD5 ... v Phi) v`.

The `HasFDerivAt` is DERIVED -- never carried -- by the genuine little-o argument: the `r`-uniform
`||h|| ||k|| ||l|| ||m||`-separated Jet5 source bound (`expJet5_remainder_quadratic_bound_unif`) fed
through the order-5 residual Groenwall (`expJet5_residual_bound`) and projected by `pi` gives, for
every direction quadruple `(h,k,l,m)`, `||A_r h k l m|| <= (C0 e^{Kstar}) ||r||^2 ||m|| ||l|| ||k||
||h||`; hence `||A_r|| <= Mc ||r||^2` (`Mc = C0 e^{Kstar}`, two nested `opNorm_le_bound` + one
`opNorm_le_bound2`) where `A_r = fderiv^4 exp_p(v+r) - fderiv^4 exp_p(v) - D5_v r`; then
`Mc ||r||^2 = o(||r||)` as `r -> 0`.

## Honest firewall (binding)

This is brick (d) of J5-5 ONLY: the fourth-derivative differentiability datum of `exp_p`.  It does
NOT by itself give `ContDiff^5` (continuity of `v -> D5_v` is brick (e)), NOT `kappa = 1/6`, NOT the
heat kernel / `a_1 = R/6` (CONDITIONAL: curved still owes the J5-6 weld + Duhamel carry + fat-K
carriers + capstone co-instantiation), NOT QG.  Axiom-free.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 65536
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **Rung-5(d) capstone: `fderiv^4 exp_p` is Frechet-differentiable with derivative `D5_v`.**
    For `||v|| < expRho` and the first-variation propagator witness `Phi` at `v`,
    `HasFDerivAt (w -> fderiv^4 exp_p w) (D5_v) v` with `D5_v = expJetD5 ... v Phi`.  Faithful mirror
    of `expMap_fderiv3_hasFDerivAt` one Frechet order up: the `r`-UNIFORM
    `||h|| ||k|| ||l|| ||m||`-separated Jet5 source bound fed through the residual Groenwall and
    projected by `pi` gives `||A_r h k l m|| <= (C0 e^{Kstar}) ||r||^2 ||m|| ||l|| ||k|| ||h||`; hence
    `||A_r|| <= Mc ||r||^2` where `A_r = fderiv^4 exp_p(v+r) - fderiv^4 exp_p(v) - D5_v r`; then
    `Mc ||r||^2 = o(||r||)`.  Brick (d) of J5-5; NOT `ContDiff^5`, NOT `kappa = 1/6`, NOT `a_1 = R/6`,
    NOT QG. -/
theorem expMap_fderiv4_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ < expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hfdv : fderiv ℝ (expMap g gi hC p) v
      = expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) :
    HasFDerivAt
      (fun w => fderiv ℝ (fun x => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) x) w)
      (expJetD5 g gi hC p v Φ hv.le hΦcont) v := by
  obtain ⟨C₀, hC₀0, hrbdU⟩ :=
    expJet5_remainder_quadratic_bound_unif g gi hC p v Φ hv.le hΦ0 hΦcont hΦderiv
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv.le
  set Mc : ℝ := C₀ * Real.exp Kstar with hMcdef
  have hMc0 : 0 ≤ Mc := mul_nonneg hC₀0 (Real.exp_pos _).le
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min (expRho g gi hC p - ‖v‖) (c / (Mc + 1)),
    lt_min (by linarith [hv]) (div_pos hc (by linarith)), fun r hm => ?_⟩
  rw [dist_eq_norm, sub_zero] at hm
  have hm1 : ‖r‖ < expRho g gi hC p - ‖v‖ := lt_of_lt_of_le hm (min_le_left _ _)
  have hmM : ‖r‖ ≤ c / (Mc + 1) := (lt_of_lt_of_le hm (min_le_right _ _)).le
  have hvm_lt : ‖v + r‖ < expRho g gi hC p :=
    lt_of_le_of_lt (norm_add_le v r) (by linarith)
  have hvm_le : ‖v + r‖ ≤ expRho g gi hC p := hvm_lt.le
  obtain ⟨Φ', hΦ'0, hΦ'deriv, hfdvm'⟩ := hasFDerivAt_expMap g gi hC p (v + r) hvm_lt
  have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦ'deriv t ht).continuousWithinAt
  have hfd_vm : fderiv ℝ (expMap g gi hC p) (v + r)
      = expJetPi.comp ((Φ' 1).comp (expJetIota (n := n))) := hfdvm'.fderiv
  have hfd4_v : fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) v
      = expJetD4 g gi hC p v Φ hv.le hΦcont :=
    (expMap_fderiv3_hasFDerivAt g gi hC p v Φ hv hΦ0 hΦcont hΦderiv hfdv).fderiv
  have hfd4_vm : fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) (v + r)
      = expJetD4 g gi hC p (v + r) Φ' hvm_le hΦ'cont :=
    (expMap_fderiv3_hasFDerivAt g gi hC p (v + r) Φ' hvm_lt hΦ'0 hΦ'cont hΦ'deriv hfd_vm).fderiv
  have hAm : ‖fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) (v + r)
      - fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) v
      - expJetD5 g gi hC p v Φ hv.le hΦcont r‖ ≤ Mc * ‖r‖ ^ 2 := by
    rw [hfd4_v, hfd4_vm]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hMc0 (sq_nonneg _)) (fun m => ?_)
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg hMc0 (sq_nonneg _)) (norm_nonneg _)) (fun l => ?_)
    refine ContinuousLinearMap.opNorm_le_bound₂ _
      (mul_nonneg (mul_nonneg (mul_nonneg hMc0 (sq_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
      (fun k h => ?_)
    obtain ⟨hQv0, -, -, hQvd⟩ :=
      (expJet4Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
        hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m)
        h k l m).choose_spec
    obtain ⟨hQw0, -, -, hQwd⟩ :=
      (expJet4Fund g gi hC p (v + r) Φ'
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h k)
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h l)
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h m)
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont k l)
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont k m)
        (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont l m)
        (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l)
        (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k m)
        (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h l m)
        (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont k l m)
        hvm_le hΦ'cont
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h k)
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h l)
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h m)
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont k l)
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont k m)
        (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont l m)
        (expJet3CurveG_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l)
        (expJet3CurveG_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h k m)
        (expJet3CurveG_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont h l m)
        (expJet3CurveG_continuousOn g gi hC p (v + r) Φ' hvm_le hΦ'cont k l m)
        h k l m).choose_spec
    obtain ⟨hR0, -, -, hRd⟩ :=
      (expJet5Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont l m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l m)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h l m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont k l m r)
        hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont l m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l m)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m r)
        h k l m r).choose_spec
    have hρ0 : (0 : ℝ) ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀0 (norm_nonneg _))
        (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)) (sq_nonneg _)
    have hres := expJet5_residual_bound g gi hC p v (v + r) Φ Φ'
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l m)
      (expJet4CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h k)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h l)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont h m)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont k l)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont k m)
      (expJet2Curve g gi hC p (v + r) Φ' hvm_le hΦ'cont l m)
      (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l)
      (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k m)
      (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont h l m)
      (expJet3CurveG g gi hC p (v + r) Φ' hvm_le hΦ'cont k l m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h r)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k r)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont l r)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont m r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h m r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont k m r)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont l m r)
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l m)
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l r)
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k m r)
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont h l m r)
      (expJet4CurveG g gi hC p v Φ hv.le hΦcont k l m r)
      (expJet5Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l r)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k m r)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont l m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l m)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k l r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h k m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont h l m r)
        (expJet4CurveG g gi hC p v Φ hv.le hΦcont k l m r)
        hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l r)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k m r)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont l m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l m)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m r)
        (expJet4CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m r)
        h k l m r).choose
      h k l m r
      hQv0 hQw0 hR0 hQvd hQwd hRd Kstar
      (C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2) hKstar0 hρ0 hKstar
      (fun t ht => hrbdU r hvm_le Φ' hΦ'0 hΦ'cont hΦ'deriv h k l m t ht)
    simp only [ContinuousLinearMap.sub_apply]
    rw [expJetD4_apply, expJetD4_apply, expJetD5_apply]
    calc ‖expJetPi (expJet4ValG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m)
            - expJetPi (expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m)
            - expJetPi (expJet5ValG g gi hC p v Φ hv.le hΦcont h k l m r)‖
        = ‖expJetPi (expJet4ValG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m
              - expJet5ValG g gi hC p v Φ hv.le hΦcont h k l m r)‖ := by rw [map_sub, map_sub]
      _ ≤ ‖expJetPi (n := n)‖ * ‖expJet4ValG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m
              - expJet5ValG g gi hC p v Φ hv.le hΦcont h k l m r‖ :=
          (expJetPi (n := n)).le_opNorm _
      _ ≤ 1 * ‖expJet4ValG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m
              - expJet5ValG g gi hC p v Φ hv.le hΦcont h k l m r‖ :=
          mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
      _ = ‖expJet4ValG g gi hC p (v + r) Φ' hvm_le hΦ'cont h k l m
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m
              - expJet5ValG g gi hC p v Φ hv.le hΦcont h k l m r‖ := one_mul _
      _ ≤ (C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2) * Real.exp Kstar := hres
      _ = Mc * ‖r‖ ^ 2 * ‖m‖ * ‖l‖ * ‖k‖ * ‖h‖ := by rw [hMcdef]; ring
  have hMc : Mc * ‖r‖ ≤ c := by
    have h1 : Mc * ‖r‖ ≤ Mc * (c / (Mc + 1)) := mul_le_mul_of_nonneg_left hmM hMc0
    have h2 : Mc * (c / (Mc + 1)) ≤ c := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < Mc + 1)]
      nlinarith [hc, hMc0]
    linarith
  show ‖fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) (v + r)
      - fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) v
      - expJetD5 g gi hC p v Φ hv.le hΦcont r‖ ≤ c * ‖r‖
  calc ‖fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) (v + r)
          - fderiv ℝ (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w) v
          - expJetD5 g gi hC p v Φ hv.le hΦcont r‖
      ≤ Mc * ‖r‖ ^ 2 := hAm
    _ = (Mc * ‖r‖) * ‖r‖ := by ring
    _ ≤ c * ‖r‖ := mul_le_mul_of_nonneg_right hMc (norm_nonneg _)

end QIQTH.ExpMap
