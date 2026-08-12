/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5D5ValG
import QIQTH.ExpJet5Phase5Gate
import Mathlib

/-!
# JET-5 TOWER — the `expJetD5` quintilinear CLM packaging (J5-4, brick J4-651)

Faithful mirror, one Fréchet order up, of the `expJetD4` packaging chain in `ExpJet4DFull.lean`:
* `expJetD5Inner`/`expJetD5Mid3`/`expJetD5Mid2`/`expJetD5` — the packaged quintilinear continuous map
  `Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n`
  (`D⁵_v(r)(m)(l)(k)(h) = π(R^{hklmr}_v(1))`), via one `mkContinuous₂` + three nested `mkContinuous`,
  from the banked 5-linear multilinearity `expJet5ValG_{add,smul}_*` and the uniform bound
  `expJet5ValG_norm_le`.
* `expJetD5_two_pt_diff` — the operator-norm two-point bound `‖D⁵_v − D⁵_w‖ ≤ expJet5VtpConst·‖v−w‖`,
  the consumer form the J5-5 `hfd4` assembly will need, from the ★ J5-3 value two-point bound
  `expJet5Val_v_two_pt_diff` projected by `π` and lifted through the five CLM layers.
* `expJetD5_two_pt_diff_gate` — curved non-vacuity at `curvedRNCMetric (−1)`.

## Honest firewall (binding)
This is J5-4 ONLY.  It does NOT establish `exp_p ∈ C⁵` (that is J5-5/J5-6), does NOT reach
`κ = 1/6`, and does NOT establish `a₁ = R/6` (CONDITIONAL: flat non-vacuous; curved still owes
J5-5/J5-6 + the Duhamel carry + fat-K carriers + capstone co-instantiation).  Axiom-free packaging.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 8000

variable {n : ℕ}

/-! ### (3) The packaged quintilinear continuous map `expJetD5` -/

/-- Inner `(k,h)`-bilinear slice `D⁵_v(l,m,r)` = `π(R^{hklmr}_v(1))`. -/
noncomputable def expJetD5Inner (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m r : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun k h => expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r))
      (fun k₁ k₂ h => by
        simp only [expJet5ValG_add_k g gi hC p v Φ hv hΦcont h k₁ k₂ l m r, map_add])
      (fun c k h => by
        simp only [expJet5ValG_smul_k g gi hC p v Φ hv hΦcont c h k l m r, map_smul])
      (fun k h₁ h₂ => by
        simp only [expJet5ValG_add_h g gi hC p v Φ hv hΦcont h₁ h₂ k l m r, map_add])
      (fun c k h => by
        simp only [expJet5ValG_smul_h g gi hC p v Φ hv hΦcont c h k l m r, map_smul]))
    ((expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖ * ‖r‖)
    (fun k h => by
      have hb := (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.2 h k l m r
      simp only [LinearMap.mk₂_apply]
      calc ‖expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r)‖
          ≤ ‖expJetPi (n := n)‖ * ‖expJet5ValG g gi hC p v Φ hv hΦcont h k l m r‖ :=
            (expJetPi (n := n)).le_opNorm _
        _ ≤ 1 * ‖expJet5ValG g gi hC p v Φ hv hΦcont h k l m r‖ :=
            mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
        _ = ‖expJet5ValG g gi hC p v Φ hv hΦcont h k l m r‖ := one_mul _
        _ ≤ (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := hb
        _ = (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖ * ‖r‖ * ‖k‖ * ‖h‖ := by ring)

@[simp] theorem expJetD5Inner_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m r k h : Point n) :
    expJetD5Inner g gi hC p v Φ hv hΦcont l m r k h
      = expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r) := rfl

theorem expJetD5Inner_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (l m r : Point n) :
    ‖expJetD5Inner g gi hC p v Φ hv hΦcont l m r‖
      ≤ (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖l‖ * ‖m‖ * ‖r‖ := by
  unfold expJetD5Inner
  exact LinearMap.mkContinuous₂_norm_le _
    (mul_nonneg (mul_nonneg (mul_nonneg (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1 (norm_nonneg _)) (norm_nonneg _))
      (norm_nonneg _)) _

/-- `l`-slot wrap `D⁵_v(m,r)`. -/
noncomputable def expJetD5Mid3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m r : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun l => expJetD5Inner g gi hC p v Φ hv hΦcont l m r
      map_add' := fun l₁ l₂ => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD5Inner_apply,
          expJet5ValG_add_l g gi hC p v Φ hv hΦcont h k l₁ l₂ m r, map_add]
      map_smul' := fun c l => by
        refine ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD5Inner_apply,
          expJet5ValG_smul_l g gi hC p v Φ hv hΦcont c h k l m r, map_smul] }
    ((expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖m‖ * ‖r‖)
    (fun l => (expJetD5Inner_norm_le g gi hC p v Φ hv hΦcont l m r).trans (le_of_eq (by ring)))

@[simp] theorem expJetD5Mid3_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m r l k h : Point n) :
    expJetD5Mid3 g gi hC p v Φ hv hΦcont m r l k h
      = expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r) := by
  simp only [expJetD5Mid3, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD5Inner_apply]

theorem expJetD5Mid3_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (m r : Point n) :
    ‖expJetD5Mid3 g gi hC p v Φ hv hΦcont m r‖
      ≤ (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖m‖ * ‖r‖ := by
  unfold expJetD5Mid3
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (mul_nonneg (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1 (norm_nonneg _)) (norm_nonneg _)) _

/-- `m`-slot wrap `D⁵_v(r)`. -/
noncomputable def expJetD5Mid2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (r : Point n) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun m => expJetD5Mid3 g gi hC p v Φ hv hΦcont m r
      map_add' := fun m₁ m₂ => by
        refine ContinuousLinearMap.ext fun l => ContinuousLinearMap.ext fun k =>
          ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD5Mid3_apply,
          expJet5ValG_add_m g gi hC p v Φ hv hΦcont h k l m₁ m₂ r, map_add]
      map_smul' := fun c m => by
        refine ContinuousLinearMap.ext fun l => ContinuousLinearMap.ext fun k =>
          ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD5Mid3_apply,
          expJet5ValG_smul_m g gi hC p v Φ hv hΦcont c h k l m r, map_smul] }
    ((expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖r‖)
    (fun m => (expJetD5Mid3_norm_le g gi hC p v Φ hv hΦcont m r).trans (le_of_eq (by ring)))

@[simp] theorem expJetD5Mid2_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (r m l k h : Point n) :
    expJetD5Mid2 g gi hC p v Φ hv hΦcont r m l k h
      = expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r) := by
  simp only [expJetD5Mid2, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD5Mid3_apply]

theorem expJetD5Mid2_norm_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (r : Point n) :
    ‖expJetD5Mid2 g gi hC p v Φ hv hΦcont r‖ ≤ (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose * ‖r‖ := by
  unfold expJetD5Mid2
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose_spec.1 (norm_nonneg _)) _

/-- **(5-datum) The packaged fifth-derivative operator** `D⁵_v`. -/
noncomputable def expJetD5 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) :
    Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
  LinearMap.mkContinuous
    { toFun := fun r => expJetD5Mid2 g gi hC p v Φ hv hΦcont r
      map_add' := fun r₁ r₂ => by
        refine ContinuousLinearMap.ext fun m => ContinuousLinearMap.ext fun l =>
          ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.add_apply, expJetD5Mid2_apply,
          expJet5ValG_add_r g gi hC p v Φ hv hΦcont h k l m r₁ r₂, map_add]
      map_smul' := fun c r => by
        refine ContinuousLinearMap.ext fun m => ContinuousLinearMap.ext fun l =>
          ContinuousLinearMap.ext fun k => ContinuousLinearMap.ext fun h => ?_
        simp only [ContinuousLinearMap.smul_apply, RingHom.id_apply, expJetD5Mid2_apply,
          expJet5ValG_smul_r g gi hC p v Φ hv hΦcont c h k l m r, map_smul] }
    (expJet5ValG_norm_le g gi hC p v Φ hv hΦcont).choose
    (fun r => expJetD5Mid2_norm_le g gi hC p v Φ hv hΦcont r)

/-- **`expJetD5` application form.**  `D⁵_v(r)(m)(l)(k)(h) = π(R^{hklmr}_v(1))`. -/
@[simp] theorem expJetD5_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p) (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1)) (r m l k h : Point n) :
    expJetD5 g gi hC p v Φ hv hΦcont r m l k h
      = expJetPi (expJet5ValG g gi hC p v Φ hv hΦcont h k l m r) := by
  simp only [expJetD5, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    expJetD5Mid2_apply]

set_option maxHeartbeats 12000000 in
theorem expJetD5_two_pt_diff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Kf Ldf Ld2f Ld3f Ld4f Ld5f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ)
    (hKstar0 : 0 ≤ Kstar) (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3)
    (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi)) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD2F : LipschitzOnWith Ld2f (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD3F : LipschitzOnWith Ld3f (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD4F : LipschitzOnWith Ld4f (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipD5F : LipschitzOnWith Ld5f (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))) (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstar : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p u t)‖ ≤ Kstar)
    (hKstar2f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p u t)‖ ≤ Kstar2)
    (hKstar3f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p u t)‖ ≤ Kstar3)
    (hKstar4f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p u t)‖ ≤ Kstar4)
    (hKstar5f : ∀ u : Point n, ‖u‖ ≤ expRho g gi hC p → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p u t)‖ ≤ Kstar5)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦvcont : ContinuousOn Φv (Set.Icc (0 : ℝ) 1))
    (hΦwcont : ContinuousOn Φw (Set.Icc (0 : ℝ) 1)) :
    ‖expJetD5 g gi hC p v Φv hv hΦvcont - expJetD5 g gi hC p w Φw hw hΦwcont‖
      ≤ expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
          Kstar Kstar2 Kstar3 Kstar4 Kstar5 * ‖v - w‖ := by
  set C : ℝ := expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
    Kstar Kstar2 Kstar3 Kstar4 Kstar5 with hCdef
  have hC0 : 0 ≤ C :=
    expJet5VtpConst_nonneg _ _ _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2 Ld5f.2
      hKstar20 hKstar30 hKstar40 hKstar50
  have hval : ∀ r m l k h : Point n,
      ‖expJetPi (expJet5ValG g gi hC p v Φv hv hΦvcont h k l m r)
          - expJetPi (expJet5ValG g gi hC p w Φw hw hΦwcont h k l m r)‖
        ≤ C * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by
    intro r m l k h
    obtain ⟨hQhkv0, -, -, hQhkvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h k).choose_spec
    obtain ⟨hQhlv0, -, -, hQhlvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h l).choose_spec
    obtain ⟨hQhmv0, -, -, hQhmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h m).choose_spec
    obtain ⟨hQhrv0, -, -, hQhrvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont h r).choose_spec
    obtain ⟨hQklv0, -, -, hQklvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont k l).choose_spec
    obtain ⟨hQkmv0, -, -, hQkmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont k m).choose_spec
    obtain ⟨hQkrv0, -, -, hQkrvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont k r).choose_spec
    obtain ⟨hQlmv0, -, -, hQlmvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont l m).choose_spec
    obtain ⟨hQlrv0, -, -, hQlrvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont l r).choose_spec
    obtain ⟨hQmrv0, -, -, hQmrvd⟩ := (expJet2Fund g gi hC p v Φv hv hΦvcont m r).choose_spec
    obtain ⟨hQhklv0, -, -, hQhklvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h k) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) h k l).choose_spec
    obtain ⟨hQhkmv0, -, -, hQhkmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h k) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) h k m).choose_spec
    obtain ⟨hQhkrv0, -, -, hQhkrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont h k) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) h k r).choose_spec
    obtain ⟨hQhlmv0, -, -, hQhlmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) h l m).choose_spec
    obtain ⟨hQhlrv0, -, -, hQhlrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) h l r).choose_spec
    obtain ⟨hQhmrv0, -, -, hQhmrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) h m r).choose_spec
    obtain ⟨hQklmv0, -, -, hQklmvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) k l m).choose_spec
    obtain ⟨hQklrv0, -, -, hQklrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) k l r).choose_spec
    obtain ⟨hQkmrv0, -, -, hQkmrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) k m r).choose_spec
    obtain ⟨hQlmrv0, -, -, hQlmrvd⟩ :=
      (expJet3Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) l m r).choose_spec
    obtain ⟨hQhklmv0, -, -, hQhklmvd⟩ :=
      (expJet4Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) h k l m).choose_spec
    obtain ⟨hQhklrv0, -, -, hQhklrvd⟩ :=
      (expJet4Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l r) h k l r).choose_spec
    obtain ⟨hQhkmrv0, -, -, hQhkmrvd⟩ :=
      (expJet4Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k m r) h k m r).choose_spec
    obtain ⟨hQhlmrv0, -, -, hQhlmrvd⟩ :=
      (expJet4Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont l m r) h l m r).choose_spec
    obtain ⟨hQklmrv0, -, -, hQklmrvd⟩ :=
      (expJet4Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont l m r) k l m r).choose_spec
    obtain ⟨hRv0, -, -, hRvd⟩ :=
      (expJet5Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont k l m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m r) h k l m r).choose_spec
    obtain ⟨hQhkw0, -, -, hQhkwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h k).choose_spec
    obtain ⟨hQhlw0, -, -, hQhlwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h l).choose_spec
    obtain ⟨hQhmw0, -, -, hQhmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h m).choose_spec
    obtain ⟨hQhrw0, -, -, hQhrwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont h r).choose_spec
    obtain ⟨hQklw0, -, -, hQklwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont k l).choose_spec
    obtain ⟨hQkmw0, -, -, hQkmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont k m).choose_spec
    obtain ⟨hQkrw0, -, -, hQkrwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont k r).choose_spec
    obtain ⟨hQlmw0, -, -, hQlmwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont l m).choose_spec
    obtain ⟨hQlrw0, -, -, hQlrwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont l r).choose_spec
    obtain ⟨hQmrw0, -, -, hQmrwd⟩ := (expJet2Fund g gi hC p w Φw hw hΦwcont m r).choose_spec
    obtain ⟨hQhklw0, -, -, hQhklwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h k) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) h k l).choose_spec
    obtain ⟨hQhkmw0, -, -, hQhkmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h k) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) h k m).choose_spec
    obtain ⟨hQhkrw0, -, -, hQhkrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont h k) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) h k r).choose_spec
    obtain ⟨hQhlmw0, -, -, hQhlmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) h l m).choose_spec
    obtain ⟨hQhlrw0, -, -, hQhlrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) h l r).choose_spec
    obtain ⟨hQhmrw0, -, -, hQhmrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) h m r).choose_spec
    obtain ⟨hQklmw0, -, -, hQklmwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) k l m).choose_spec
    obtain ⟨hQklrw0, -, -, hQklrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) k l r).choose_spec
    obtain ⟨hQkmrw0, -, -, hQkmrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) k m r).choose_spec
    obtain ⟨hQlmrw0, -, -, hQlmrwd⟩ :=
      (expJet3Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) l m r).choose_spec
    obtain ⟨hQhklmw0, -, -, hQhklmwd⟩ :=
      (expJet4Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) h k l m).choose_spec
    obtain ⟨hQhklrw0, -, -, hQhklrwd⟩ :=
      (expJet4Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l r) h k l r).choose_spec
    obtain ⟨hQhkmrw0, -, -, hQhkmrwd⟩ :=
      (expJet4Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k m r) h k m r).choose_spec
    obtain ⟨hQhlmrw0, -, -, hQhlmrwd⟩ :=
      (expJet4Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont l m r) h l m r).choose_spec
    obtain ⟨hQklmrw0, -, -, hQklmrwd⟩ :=
      (expJet4Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont l m r) k l m r).choose_spec
    obtain ⟨hRw0, -, -, hRwd⟩ :=
      (expJet5Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont k l m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m r) h k l m r).choose_spec
    have hb := expJet5Val_v_two_pt_diff g gi hC p v w hv hw Kf Ldf Ld2f Ld3f Ld4f Ld5f
      Kstar Kstar2 Kstar3 Kstar4 Kstar5 hKstar0 hKstar20 hKstar30 hKstar40 hKstar50
      hLipF hLipDF hLipD2F hLipD3F hLipD4F hLipD5F
      hKstar hKstar2f hKstar3f hKstar4f hKstar5f
      Φv Φw hΦv0 hΦw0 hΦvd hΦwd
      (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r)
      (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r)
      (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r)
      (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r)
      (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont k l m r)
      (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont k l m r)
      (expJet5Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont k l m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m r) h k l m r).choose (expJet5Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont k l m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m r) h k l m r).choose h k l m r
      hQhkv0 hQhlv0 hQhmv0 hQhrv0 hQklv0 hQkmv0 hQkrv0 hQlmv0 hQlrv0 hQmrv0
      hQhkw0 hQhlw0 hQhmw0 hQhrw0 hQklw0 hQkmw0 hQkrw0 hQlmw0 hQlrw0 hQmrw0
      hQhklv0 hQhkmv0 hQhkrv0 hQhlmv0 hQhlrv0 hQhmrv0 hQklmv0 hQklrv0 hQkmrv0 hQlmrv0
      hQhklw0 hQhkmw0 hQhkrw0 hQhlmw0 hQhlrw0 hQhmrw0 hQklmw0 hQklrw0 hQkmrw0 hQlmrw0
      hQhklmv0 hQhklrv0 hQhkmrv0 hQhlmrv0 hQklmrv0
      hQhklmw0 hQhklrw0 hQhkmrw0 hQhlmrw0 hQklmrw0
      hRv0 hRw0
      hQhkvd hQhlvd hQhmvd hQhrvd hQklvd hQkmvd hQkrvd hQlmvd hQlrvd hQmrvd
      hQhkwd hQhlwd hQhmwd hQhrwd hQklwd hQkmwd hQkrwd hQlmwd hQlrwd hQmrwd
      hQhklvd hQhkmvd hQhkrvd hQhlmvd hQhlrvd hQhmrvd hQklmvd hQklrvd hQkmrvd hQlmrvd
      hQhklwd hQhkmwd hQhkrwd hQhlmwd hQhlrwd hQhmrwd hQklmwd hQklrwd hQkmrwd hQlmrwd
      hQhklmvd hQhklrvd hQhkmrvd hQhlmrvd hQklmrvd
      hQhklmwd hQhklrwd hQhkmrwd hQhlmrwd hQklmrwd
      hRvd hRwd
    have hπ : expJetPi (expJet5ValG g gi hC p v Φv hv hΦvcont h k l m r)
          - expJetPi (expJet5ValG g gi hC p w Φw hw hΦwcont h k l m r)
        = expJetPi ((expJet5Fund g gi hC p v Φv (expJet2Curve g gi hC p v Φv hv hΦvcont h k) (expJet2Curve g gi hC p v Φv hv hΦvcont h l) (expJet2Curve g gi hC p v Φv hv hΦvcont h m) (expJet2Curve g gi hC p v Φv hv hΦvcont h r) (expJet2Curve g gi hC p v Φv hv hΦvcont k l) (expJet2Curve g gi hC p v Φv hv hΦvcont k m) (expJet2Curve g gi hC p v Φv hv hΦvcont k r) (expJet2Curve g gi hC p v Φv hv hΦvcont l m) (expJet2Curve g gi hC p v Φv hv hΦvcont l r) (expJet2Curve g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG g gi hC p v Φv hv hΦvcont k l m r) hv hΦvcont (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h k) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont h r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k l) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont k r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l m) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont l r) (expJet2Curve_continuousOn g gi hC p v Φv hv hΦvcont m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont h m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont k m r) (expJet3CurveG_continuousOn g gi hC p v Φv hv hΦvcont l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l m) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k l r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h k m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont h l m r) (expJet4CurveG_continuousOn g gi hC p v Φv hv hΦvcont k l m r) h k l m r).choose 1
          - (expJet5Fund g gi hC p w Φw (expJet2Curve g gi hC p w Φw hw hΦwcont h k) (expJet2Curve g gi hC p w Φw hw hΦwcont h l) (expJet2Curve g gi hC p w Φw hw hΦwcont h m) (expJet2Curve g gi hC p w Φw hw hΦwcont h r) (expJet2Curve g gi hC p w Φw hw hΦwcont k l) (expJet2Curve g gi hC p w Φw hw hΦwcont k m) (expJet2Curve g gi hC p w Φw hw hΦwcont k r) (expJet2Curve g gi hC p w Φw hw hΦwcont l m) (expJet2Curve g gi hC p w Φw hw hΦwcont l r) (expJet2Curve g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG g gi hC p w Φw hw hΦwcont k l m r) hw hΦwcont (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h k) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont h r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k l) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont k r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l m) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont l r) (expJet2Curve_continuousOn g gi hC p w Φw hw hΦwcont m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont h m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont k m r) (expJet3CurveG_continuousOn g gi hC p w Φw hw hΦwcont l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l m) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k l r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h k m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont h l m r) (expJet4CurveG_continuousOn g gi hC p w Φw hw hΦwcont k l m r) h k l m r).choose 1) := by
      rw [map_sub]; rfl
    rw [hπ]
    refine ((expJetPi (n := n)).le_opNorm _).trans ?_
    refine (mul_le_mul expJetPi_opNorm_le hb (norm_nonneg _) (by norm_num)).trans ?_
    exact le_of_eq (by ring)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun r => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun m => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun l => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, expJetD5_apply, expJetD5_apply]
  calc ‖expJetPi (expJet5ValG g gi hC p v Φv hv hΦvcont h k l m r)
          - expJetPi (expJet5ValG g gi hC p w Φw hw hΦwcont h k l m r)‖
      ≤ C * ‖v - w‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := hval r m l k h
    _ = C * ‖v - w‖ * ‖r‖ * ‖m‖ * ‖l‖ * ‖k‖ * ‖h‖ := by ring

/-! ### (5) Curved non-vacuity gate at `curvedRNCMetric (-1)` -/

set_option maxHeartbeats 6400000 in
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Curved non-vacuity gate.**  All antecedents of `expJetD5_two_pt_diff` are jointly
    DISCHARGED at `gᵏ = curvedRNCMetric (−1)`, `p = v = w = 0`, so the operator-norm two-point
    bound holds (trivially, `‖·‖ = 0 = C·‖0−0‖`).  Mirror of `expJet5Val_v_two_pt_diff_gate`. -/
theorem expJetD5_two_pt_diff_gate (_z : Point n) :
    ∃ (Kf Ldf Ld2f Ld3f Ld4f Ld5f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ)
      (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
      (hv : ‖(0 : Point n)‖ ≤ expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n)),
      ‖expJetD5 (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont
          - expJetD5 (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont‖
        ≤ expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
            Kstar Kstar2 Kstar3 Kstar4 Kstar5 * ‖(0 : Point n) - 0‖ := by
  have hv : ‖(0 : Point n)‖ ≤ expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n) := by
    simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0).le
  obtain ⟨Kf, hLipF⟩ :=
    ((contDiff_geodesicField (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num))).contDiffOn
        (s := Metric.closedBall ((0, 0) : Point n × Point n)
          (expConst (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 * expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n)))).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Ld2f, hLipD2F⟩ := expJet_fderiv2_lipschitzOnWith (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Ld3f, hLipD3F⟩ := expJet_fderiv3_lipschitzOnWith (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Ld4f, hLipD4F⟩ := expJet_fderiv4_lipschitzOnWith (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Ld5f, hLipD5F⟩ := expJet_fderiv5_lipschitzOnWith (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove_unif (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Kstar2, hKstar20, hKstar2f⟩ := expJet_fderiv2_tube_bddAbove_unif (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Kstar3, hKstar30, hKstar3f⟩ := expJet_fderiv3_tube_bddAbove_unif (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Kstar4, hKstar40, hKstar4f⟩ := expJet_fderiv4_tube_bddAbove_unif (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Kstar5, hKstar50, hKstar5f⟩ := expJet_fderiv5_tube_bddAbove_unif (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0
  obtain ⟨Φ, hΦ0, hΦcont, _, hΦd⟩ := expJetFund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 hv
  refine ⟨Kf, Ldf, Ld2f, Ld3f, Ld4f, Ld5f, Kstar, Kstar2, Kstar3, Kstar4, Kstar5, Φ, hΦcont, hv, ?_⟩
  exact expJetD5_two_pt_diff (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 0 hv hv
    Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5
    hKstar0 hKstar20 hKstar30 hKstar40 hKstar50
    hLipF hLipDF hLipD2F hLipD3F hLipD4F hLipD5F
    hKstar hKstar2f hKstar3f hKstar4f hKstar5f
    Φ Φ hΦ0 hΦ0 hΦd hΦd hΦcont hΦcont

end QIQTH.ExpMap
