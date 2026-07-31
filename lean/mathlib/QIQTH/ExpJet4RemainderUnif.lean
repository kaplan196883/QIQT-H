/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4RemainderP
import QIQTH.ExpJet3SecondVarResidual
import QIQTH.ExpMapContDiff3

/-!
# JET-4 TOWER — rung J4-5d2: the `m`-UNIFORM order-4 quadratic remainder bound

This file lands `expJet4_remainder_quadratic_bound_unif`, the `m`-uniform mirror of
`expJet3_remainder_quadratic_bound_unif` (`ExpMapContDiff3.lean:3576`) one Fréchet order up.  A SINGLE
`C₀ ≥ 0` — independent of the varied direction `m`, of the `v+m`-propagator `Φ'`, and of the fixed
probe directions `(h,k,l)` — bounds the Jet₄ residual ODE source by `C₀·‖h‖·‖k‖·‖l‖·‖m‖²` for every
small `m`, written against the GENUINE second- and third-variation curves (`expJet2Curve`,
`expJet3Curve`).

The `O(…‖m‖²)` conclusion is DERIVED — never carried — by the same real five-block telescope as
`expJet4_remainder_quadratic_bound'` (`ExpJet4RemainderP.lean`), but with the witness constant chosen
UP FRONT (before `m`) from the `m`-independent uniform tube/Lipschitz data.  The `m`-uniformity
replaces the per-point compactness DF-tube bound at `v+m` (`expJet_fderiv_tube_bddAbove`, which is
`m`-dependent) by the uniform `expJet_fderiv_tube_bddAbove_unif`, and every carried INPUT of
`expJet4_remainder_quadratic_bound'` is DISCHARGED internally from a proved uniform lemma:

* first→second residuals (`hFP·`) ← `expJet2FirstVar_residual_Icc_unif`;
* second→third residuals (`hFQ··`) ← `expJet3SecondVar_residual_Icc_unif`;
* second-variation two-point Lipschitz (`hQlip··`) ← `expJet2_v_two_pt_Icc_unif`;
* third-variation two-point Lipschitz (`hQlip`) ← `expJet3Val_v_two_pt_Icc_unif` (built here from
  `expJet3Val_v_two_pt_Icc_const`);
* curve value bounds (`hV·`, `hVw·`) ← `expJet2Fund_value_bound_Icc`;
* the `Qw` value bound ← `expJet3Fund_value_bound_Icc`;
* the ODE data of the genuine third-variation solution ← `expJet3Fund … .choose_spec`.

This is the source-level datum the CLM `HasFDerivAt` of `fderiv³ exp_p` consumes (J4-5e, via the
residual Grönwall + `π`).  It is NOT `exp_p ∈ C⁴`, NOT `κ = 1/6`, NOT the heat kernel / `a₁ = R/6`,
NOT QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-! ### Generic multilinear CLM-application norm bounds (local private copies)

The `ExpJet4RemainderP` helpers are `private`; re-declare local copies exactly as `ExpJet4Rhs.lean`
does. -/

/-- **Generic CLM-application norm bound.**  `‖C a‖ ≤ KC · Ka`. -/
private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

/-- **Generic bilinear CLM-application norm bound.** -/
private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

/-- **Generic trilinear CLM-application norm bound.** -/
private theorem clmApply3_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H) (a : E) (b : F) (c : G) {KB Ka Kb Kc : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) :
    ‖B a b c‖ ≤ KB * Ka * Kb * Kc := by
  have h1 : ‖B a‖ ≤ KB * Ka := (B.le_opNorm a).trans (mul_le_mul hB ha (norm_nonneg _) hKB)
  have h2 : ‖B a b‖ ≤ KB * Ka * Kb :=
    ((B a).le_opNorm b).trans (mul_le_mul h1 hb (norm_nonneg _) (mul_nonneg hKB hKa))
  exact ((B a b).le_opNorm c).trans
    (mul_le_mul h2 hc (norm_nonneg _) (mul_nonneg (mul_nonneg hKB hKa) hKb))

/-- **Generic quadrilinear CLM-application norm bound.**  `‖B a b c d‖ ≤ KB · Ka · Kb · Kc · Kd`. -/
private theorem clmApply4_norm_le {E F G H I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup I] [NormedSpace ℝ I]
    (B : E →L[ℝ] F →L[ℝ] G →L[ℝ] H →L[ℝ] I) (a : E) (b : F) (c : G) (d : H)
    {KB Ka Kb Kc Kd : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) (hc : ‖c‖ ≤ Kc) (hd : ‖d‖ ≤ Kd) :
    ‖B a b c d‖ ≤ KB * Ka * Kb * Kc * Kd := by
  have h1 : ‖B a‖ ≤ KB * Ka := (B.le_opNorm a).trans (mul_le_mul hB ha (norm_nonneg _) hKB)
  have h2 : ‖B a b‖ ≤ KB * Ka * Kb :=
    ((B a).le_opNorm b).trans (mul_le_mul h1 hb (norm_nonneg _) (mul_nonneg hKB hKa))
  have h3 : ‖B a b c‖ ≤ KB * Ka * Kb * Kc :=
    ((B a b).le_opNorm c).trans
      (mul_le_mul h2 hc (norm_nonneg _) (mul_nonneg (mul_nonneg hKB hKa) hKb))
  exact ((B a b c).le_opNorm d).trans
    (mul_le_mul h3 hd (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg hKB hKa) hKb) hKc))

set_option maxHeartbeats 1600000 in
/-- **The `m`-UNIFORM `‖h‖‖k‖‖l‖`-separated third-variation two-point Lipschitz bound.**  The
    `m`-uniform packaging of `expJet3Val_v_two_pt_Icc_const`: a single `Ce ≥ 0` bounds the genuine
    third-variation two-point difference `‖R^{hkl}_{v+m}(t) − R^{hkl}_v(t)‖ ≤ Ce·‖h‖·‖k‖·‖l‖·‖m‖` for
    every varied direction `m` (`‖v+m‖ ≤ expRho`) and every `v+m`-propagator `Φ'`, on all of `[0,1]`.
    `R^{hkl}` is the genuine third-variation curve `expJet3Curve` whose second-variation inputs are the
    `expJet2Curve` pairs.  This is the `hQlip` datum the order-4 `_unif` remainder brick consumes. -/
theorem expJet3Val_v_two_pt_Icc_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ (m : Point n) (hvm : ‖v + m‖ ≤ expRho g gi hC p)
      (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (_hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
      (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
      (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + m) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
      (h k l : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet3Curve g gi hC p (v + m) Φ'
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
            hvm hΦ'cont
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
            h k l t
          - expJet3Curve g gi hC p v Φ
            (expJet2Curve g gi hC p v Φ hv hΦcont k l)
            (expJet2Curve g gi hC p v Φ hv hΦcont h l)
            (expJet2Curve g gi hC p v Φ hv hΦcont h k)
            hv hΦcont
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
            h k l t‖
        ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := by
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Kstar, hKstar0, hKstaru⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hK2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hK3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  refine ⟨expJet3VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) Kstar Kstar2 Kstar3,
    expJet3VtpConst_nonneg _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 hKstar20 hKstar30, ?_⟩
  intro m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k l
  obtain ⟨hQklv0, -, -, hQklvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨hQhlv0, -, -, hQhlvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨hQhkv0, -, -, hQhkvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQklw0, -, -, hQklwd⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont k l).choose_spec
  obtain ⟨hQhlw0, -, -, hQhlwd⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont h l).choose_spec
  obtain ⟨hQhkw0, -, -, hQhkwd⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont h k).choose_spec
  obtain ⟨hRv0, -, -, hRvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  obtain ⟨hRw0, -, -, hRwd⟩ := (expJet3Fund g gi hC p (v + m) Φ'
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) hvm hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l).choose_spec
  have hconst := expJet3Val_v_two_pt_Icc_const g gi hC p v (v + m) hv hvm
    Kf Ldf Ld2f Ld3f Kstar Kstar2 Kstar3 hKstar0 hKstar20 hKstar30
    hLipF hLipDF hLipD2 hLipD3 hKstaru hK2u hK3u Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
    (expJet3Curve g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
    (expJet3Curve g gi hC p (v + m) Φ'
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) hvm hΦ'cont
      (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
      (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
      (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l)
    h k l hQklv0 hQhlv0 hQhkv0 hQklw0 hQhlw0 hQhkw0 hRv0 hRw0
    hQklvd hQhlvd hQhkvd hQklwd hQhlwd hQhkwd hRvd hRwd
  intro t ht
  rw [norm_sub_rev]
  refine (hconst t ht).trans (le_of_eq ?_)
  rw [show v - (v + m) = -m by abel, norm_neg]; ring

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The `m`-UNIFORM order-4 quadratic remainder bound** (mirror of
    `expJet3_remainder_quadratic_bound_unif`, one Fréchet order up).  A SINGLE `C₀ ≥ 0` — independent
    of the varied direction `m`, of the `v+m`-propagator `Φ'`, and of the fixed probes `(h,k,l)` —
    bounds the Jet₄ residual ODE source by `C₀·‖h‖·‖k‖·‖l‖·‖m‖²` for every small `m`, against the
    GENUINE second/third-variation curves.  Every carried INPUT of
    `expJet4_remainder_quadratic_bound'` is DISCHARGED internally from a proved uniform lemma; the
    witness constant is chosen UP FRONT from the `m`-independent uniform tube/Lipschitz data. -/
theorem expJet4_remainder_quadratic_bound_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (m : Point n) (hvm : ‖v + m‖ ≤ expRho g gi hC p)
      (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (_hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
      (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
      (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + m) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
      (h k l : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + m) t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
          (expJet3Curve g gi hC p (v + m) Φ'
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
             hvm hΦ'cont
             (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
             (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
             (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
             h k l t)
         + (expJet3Rhs g gi hC p (v + m) Φ'
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l t
            - expJet3Rhs g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h k) h k l t
            - expJet4Rhs g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont h k)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
                h k l m t)‖
        ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
  have hCst₀ := expConst_nonneg g gi hC p
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Ld4f, hLipD4⟩ := expJet_fderiv4_lipschitzOnWith g gi hC p
  obtain ⟨Kstar, hKstar0, hKstaru⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hK2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hK3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hK4u⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Cd_fp, hCd_fp0, hFPU⟩ := expJet2FirstVar_residual_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Cd_fq, hCd_fq0, hFQU⟩ :=
    expJet3SecondVar_residual_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Ce_2, hCe_20, hQlip2U⟩ := expJet2_v_two_pt_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Ce_3, hCe_30, hQlip3U⟩ := expJet3Val_v_two_pt_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := (Real.exp_pos _).le
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := Ldf.coe_nonneg
  set L2 : ℝ := (Ld2f : ℝ) with hL2def
  have hL2_0 : 0 ≤ L2 := Ld2f.coe_nonneg
  set L3 : ℝ := (Ld3f : ℝ) with hL3def
  have hL3_0 : 0 ≤ L3 := Ld3f.coe_nonneg
  set L4 : ℝ := (Ld4f : ℝ) with hL4def
  have hL4_0 : 0 ≤ L4 := Ld4f.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by rw [hC2def]; positivity
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by rw [hC3def]; positivity
  set Cq2 : ℝ := Kstar2 * eKs ^ 2 * Real.exp Kstar with hCq2def
  have hCq20 : 0 ≤ Cq2 := by rw [hCq2def]; positivity
  set Cd : ℝ := max Cd_fp Cd_fq with hCddef
  have hCd0 : 0 ≤ Cd := le_max_of_le_left hCd_fp0
  set Ce : ℝ := max Ce_2 Ce_3 with hCedef
  have hCe0 : 0 ≤ Ce := le_max_of_le_left hCe_20
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar := hKstaru v hv
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 := hK2u v hv
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    hK3u v hv
  have hK4v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4 := hK4u v hv
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hLipD2R : LipschitzOnWith L2.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL2def, Real.toNNReal_coe]; exact hLipD2
  have hLipD3R : LipschitzOnWith L3.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL3def, Real.toNNReal_coe]; exact hLipD3
  have hLipD4R : LipschitzOnWith L4.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL4def, Real.toNNReal_coe]; exact hLipD4
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hCst₀)
  set M3 : ℝ := (Kstar3 * eKs ^ 3
      + Kstar2 * eKs * Cq2 + Kstar2 * eKs * Cq2 + Kstar2 * eKs * Cq2) * Real.exp Kstar with hM3def
  have hM30 : 0 ≤ M3 := by rw [hM3def]; positivity
  set CB0 : ℝ := L2 * eKf ^ 2 * M3 + Kstar2 * C2 * M3 + Kstar2 * eKs * Ce with hCB0def
  have hCB00 : 0 ≤ CB0 := by rw [hCB0def]; positivity
  set CB2 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
      + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd with hCB2def
  have hCB20 : 0 ≤ CB2 := by rw [hCB2def]; positivity
  set CB3 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
      + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd with hCB3def
  have hCB30 : 0 ≤ CB3 := by rw [hCB3def]; positivity
  set CB4 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
      + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd with hCB4def
  have hCB40 : 0 ≤ CB4 := by rw [hCB4def]; positivity
  set CB1 : ℝ := L4 * eKf ^ 2 * eKs ^ 3
      + Kstar4 * C2 * eKs ^ 3
      + Kstar4 * eKs ^ 3 * C3 + Kstar4 * eKs ^ 3 * C3
      + Kstar4 * eKs ^ 3 * C3
      + Kstar3 * Cd * eKs ^ 2
      + Kstar3 * C3 ^ 2 * eKs
      + Kstar3 * Cd * (eKs + eKs) * eKs
      + Kstar3 * C3 ^ 2 * eKs
      + Kstar3 * Cd * (eKs + eKs) * eKs
      + Kstar3 * eKs ^ 2 * Cd
      + Kstar3 * eKs * C3 ^ 2
      + Kstar3 * eKs * Cd * (eKs + eKs)
      + Kstar3 * eKs ^ 2 * Cd with hCB1def
  have hCB10 : 0 ≤ CB1 := by rw [hCB1def]; positivity
  refine ⟨CB0 + CB1 + CB2 + CB3 + CB4, by positivity, ?_⟩
  intro m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k l
  -- ── genuine curve abbreviations ──
  set Qwkl := expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l with hQwkldef
  set Qwhl := expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l with hQwhldef
  set Qwhk := expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k with hQwhkdef
  set Qkl := expJet2Curve g gi hC p v Φ hv hΦcont k l with hQkldef
  set Qhl := expJet2Curve g gi hC p v Φ hv hΦcont h l with hQhldef
  set Qhk := expJet2Curve g gi hC p v Φ hv hΦcont h k with hQhkdef
  set Qhm := expJet2Curve g gi hC p v Φ hv hΦcont h m with hQhmdef
  set Qkm := expJet2Curve g gi hC p v Φ hv hΦcont k m with hQkmdef
  set Qlm := expJet2Curve g gi hC p v Φ hv hΦcont l m with hQlmdef
  set Qw := expJet3Curve g gi hC p (v + m) Φ' Qwkl Qwhl Qwhk hvm hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l with hQwdef
  set Qhkl := expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l with hQhkldef
  set Qhkm := expJet3Curve g gi hC p v Φ Qkm Qhm Qhk hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m with hQhkmdef
  set Qhlm := expJet3Curve g gi hC p v Φ Qlm Qhm Qhl hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m with hQhlmdef
  set Qklm := expJet3Curve g gi hC p v Φ Qlm Qkm Qkl hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m with hQklmdef
  -- ── ODE data of the genuine curves ──
  obtain ⟨hQkl0, -, -, hQkld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨hQhl0, -, -, hQhld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨hQhk0, -, -, hQhkd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQwkl0, -, -, hQwkld⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont k l).choose_spec
  obtain ⟨hQwhl0, -, -, hQwhld⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont h l).choose_spec
  obtain ⟨hQwhk0, -, -, hQwhkd⟩ := (expJet2Fund g gi hC p (v + m) Φ' hvm hΦ'cont h k).choose_spec
  obtain ⟨hQw0, -, -, hQwd⟩ := (expJet3Fund g gi hC p (v + m) Φ' Qwkl Qwhl Qwhk hvm hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l).choose_spec
  -- ── w-side uniform bounds ──
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + m) t)‖ ≤ Kstar := hKstaru (v + m) hvm
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + m) t)‖ ≤ Kstar2 :=
    hK2u (v + m) hvm
  have hK3w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + m) t)‖ ≤ Kstar3 :=
    hK3u (v + m) hvm
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + m) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + m) hvm
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + m) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hvm hCst₀)
  -- ── separation / Taylor / accuracy / two-point ──
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + m) t - expTube g gi hC p v t‖ ≤ ‖m‖ * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + m) 0) (expTube g gi hC p v 0) = ‖m‖ := by
      rw [hY0w, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _)]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdw t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + m) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + m) t - expTube g gi hC p v t)‖
        ≤ L2 * ‖expTube g gi hC p (v + m) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L2 hL2_0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + m) t) (hmemv t ht) (hmemw t ht)
  have hD2tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + m) t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + m) t - expTube g gi hC p v t)‖
        ≤ L3 * ‖expTube g gi hC p (v + m) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D2F_second_order_taylor g gi hC p L3 hL3_0 hLipD3R
      (expTube g gi hC p v t) (expTube g gi hC p (v + m) t) (hmemv t ht) (hmemw t ht)
  have hD3tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + m) t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + m) t - expTube g gi hC p v t)‖
        ≤ L4 * ‖expTube g gi hC p (v + m) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D3F_second_order_taylor g gi hC p L4 hL4_0 hLipD4R
      (expTube g gi hC p v t) (expTube g gi hC p (v + m) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + m) t - expTube g gi hC p v t - Φ t (expJetIota m)‖ ≤ C2 * ‖m‖ ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v m hvm hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖m‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + m) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hvm Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + m) = -m by abel, norm_neg] at hb
    exact hb
  -- ── value bounds (Cq2 = second-variation value constant) ──
  have hVkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ k l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0
      hKstarv hK2v hΦnorm Qkl hQkl0 hQkld
  have hVhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0
      hKstarv hK2v hΦnorm Qhl hQhl0 hQhld
  have hVhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h k Kstar Kstar2 eKs hKstar0 hKstar20 heKs0
      hKstarv hK2v hΦnorm Qhk hQhk0 hQhkd
  have hVwkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + m) Φ' k l Kstar Kstar2 eKs hKstar0 hKstar20
      heKs0 hKstarw hK2w hΦ'norm Qwkl hQwkl0 hQwkld
  have hVwhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + m) Φ' h l Kstar Kstar2 eKs hKstar0 hKstar20
      heKs0 hKstarw hK2w hΦ'norm Qwhl hQwhl0 hQwhld
  have hVwhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + m) Φ' h k Kstar Kstar2 eKs hKstar0 hKstar20
      heKs0 hKstarw hK2w hΦ'norm Qwhk hQwhk0 hQwhkd
  have hqwval : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qw t‖ ≤ (Kstar3 * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖)
        + Kstar2 * (eKs * ‖h‖) * (Cq2 * ‖k‖ * ‖l‖) + Kstar2 * (eKs * ‖k‖) * (Cq2 * ‖h‖ * ‖l‖)
        + Kstar2 * (eKs * ‖l‖) * (Cq2 * ‖h‖ * ‖k‖)) * Real.exp Kstar :=
    expJet3Fund_value_bound_Icc g gi hC p (v + m) Φ' Qwkl Qwhl Qwhk h k l
      Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖l‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖k‖)
      hKstar0 hKstar30 hKstar20 heKs0 hKstarw hK3w hK2w hΦ'norm hVwkl hVwhl hVwhk Qw hQw0 hQwd
  -- ── first→second residual discharges (hFP·) ──
  have hFPh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhm t‖ ≤ Cd * ‖h‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFPU m hvm Φ' hΦ'0 hΦ'cont hΦ'd h t ht).trans (by gcongr; exact le_max_left _ _)
  have hFPk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkm t‖ ≤ Cd * ‖k‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFPU m hvm Φ' hΦ'0 hΦ'cont hΦ'd k t ht).trans (by gcongr; exact le_max_left _ _)
  have hFPl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota l) - Φ t (expJetIota l) - Qlm t‖ ≤ Cd * ‖l‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFPU m hvm Φ' hΦ'0 hΦ'cont hΦ'd l t ht).trans (by gcongr; exact le_max_left _ _)
  -- ── second→third residual discharges (hFQ··) ──
  have hFQkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t - Qkl t - Qklm t‖ ≤ Cd * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFQU m hvm Φ' hΦ'0 hΦ'cont hΦ'd k l t ht).trans (by gcongr; exact le_max_right _ _)
  have hFQhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t - Qhl t - Qhlm t‖ ≤ Cd * ‖h‖ * ‖l‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFQU m hvm Φ' hΦ'0 hΦ'cont hΦ'd h l t ht).trans (by gcongr; exact le_max_right _ _)
  have hFQhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t - Qhk t - Qhkm t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖m‖ ^ 2 := fun t ht =>
    (hFQU m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k t ht).trans (by gcongr; exact le_max_right _ _)
  -- ── third-variation two-point (hQlip) ──
  have hQlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t - Qhkl t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ := fun t ht =>
    (hQlip3U m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k l t ht).trans (by gcongr; exact le_max_right _ _)
  -- ── second-variation two-point (hQlip··) ──
  have hQlipkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t - Qkl t‖ ≤ Ce * ‖k‖ * ‖l‖ * ‖m‖ := fun t ht =>
    (hQlip2U m hvm Φ' hΦ'0 hΦ'cont hΦ'd k l t ht).trans (by gcongr; exact le_max_left _ _)
  have hQliphl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t - Qhl t‖ ≤ Ce * ‖h‖ * ‖l‖ * ‖m‖ := fun t ht =>
    (hQlip2U m hvm Φ' hΦ'0 hΦ'cont hΦ'd h l t ht).trans (by gcongr; exact le_max_left _ _)
  have hQliphk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t - Qhk t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖m‖ := fun t ht =>
    (hQlip2U m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k t ht).trans (by gcongr; exact le_max_left _ _)
  -- ── iota norm bounds ──
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  have hιm : ‖expJetIota (n := n) m‖ ≤ ‖m‖ :=
    ((expJetIota (n := n)).le_opNorm m).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg m))
  -- ── per-`t` chain (mirror of `expJet4_remainder_quadratic_bound'`) ──
  intro t ht
  simp only [expJet3Rhs_apply, expJet4Rhs_apply]
  set yv := expTube g gi hC p v t with hyvE
  set yw := expTube g gi hC p (v + m) t with hywE
  set dv := fderiv ℝ (geodesicField g gi) yv with hdvE
  set dw := fderiv ℝ (geodesicField g gi) yw with hdwE
  set d2v := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yv with hd2vE
  set d2w := fderiv ℝ (fderiv ℝ (geodesicField g gi)) yw with hd2wE
  set d3v := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yv with hd3vE
  set d3w := fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) yw with hd3wE
  set d4v := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) yv with hd4vE
  set Ph := Φ t (expJetIota h) with hPhE
  set Pk := Φ t (expJetIota k) with hPkE
  set Pl := Φ t (expJetIota l) with hPlE
  set Pm := Φ t (expJetIota m) with hPmE
  set Ph' := Φ' t (expJetIota h) with hPh'E
  set Pk' := Φ' t (expJetIota k) with hPk'E
  set Pl' := Φ' t (expJetIota l) with hPl'E
  set qw := Qw t with hqwE
  set qv := Qhkl t with hqvE
  have hmaster :
      (dw - dv) qw
        + ((d3w Ph' Pk' Pl' + d2w Ph' (Qwkl t) + d2w Pk' (Qwhl t) + d2w Pl' (Qwhk t))
           - (d3v Ph Pk Pl + d2v Ph (Qkl t) + d2v Pk (Qhl t) + d2v Pl (Qhk t))
           - (d4v Ph Pk Pl Pm
              + d3v Pl Pm (Qhk t) + d3v Pk Pm (Qhl t) + d3v Pk Pl (Qhm t)
              + d3v Ph Pm (Qkl t) + d3v Ph Pl (Qkm t) + d3v Ph Pk (Qlm t)
              + d2v (Qhk t) (Qlm t) + d2v (Qhl t) (Qkm t) + d2v (Qhm t) (Qkl t)
              + d2v Ph (Qklm t) + d2v Pk (Qhlm t) + d2v Pl (Qhkm t) + d2v Pm qv))
      = ((dw - dv) qw - d2v Pm qv)
        + (d3w Ph' Pk' Pl' - d3v Ph Pk Pl - d4v Ph Pk Pl Pm
            - d3v Pk Pl (Qhm t) - d3v Ph Pl (Qkm t) - d3v Ph Pk (Qlm t))
        + (d2w Ph' (Qwkl t) - d2v Ph (Qkl t) - d3v Ph Pm (Qkl t)
            - d2v (Qhm t) (Qkl t) - d2v Ph (Qklm t))
        + (d2w Pk' (Qwhl t) - d2v Pk (Qhl t) - d3v Pk Pm (Qhl t)
            - d2v (Qhl t) (Qkm t) - d2v Pk (Qhlm t))
        + (d2w Pl' (Qwhk t) - d2v Pl (Qhk t) - d3v Pl Pm (Qhk t)
            - d2v (Qhk t) (Qlm t) - d2v Pl (Qhkm t)) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [hmaster]
  have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
  have hqwn : ‖qw‖ ≤ M3 * (‖h‖ * ‖k‖ * ‖l‖) := by
    refine (hqwval t ht).trans (le_of_eq ?_); rw [hM3def]; ring
  have hbB0 : ‖(dw - dv) qw - d2v Pm qv‖ ≤ CB0 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
    have heq0 : (dw - dv) qw - d2v Pm qv
        = (dw - dv - d2v (yw - yv)) qw + d2v (yw - yv - Pm) qw + d2v Pm (qw - qv) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [heq0]
    have hPmn : ‖Pm‖ ≤ eKs * ‖m‖ := by
      rw [hPmE]; exact clmApply_norm_le (Φ t) (expJetIota m) heKs0 (hΦnorm t ht) hιm
    have hA0 : ‖(dw - dv - d2v (yw - yv)) qw‖ ≤ (L2 * eKf ^ 2 * M3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      calc ‖(dw - dv - d2v (yw - yv)) qw‖
          ≤ ‖dw - dv - d2v (yw - yv)‖ * ‖qw‖ := (dw - dv - d2v (yw - yv)).le_opNorm _
        _ ≤ (L2 * ‖yw - yv‖ ^ 2) * (M3 * (‖h‖ * ‖k‖ * ‖l‖)) :=
            mul_le_mul (htay t ht) hqwn (norm_nonneg _) (by positivity)
        _ ≤ (L2 * (‖m‖ * eKf) ^ 2) * (M3 * (‖h‖ * ‖k‖ * ‖l‖)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL2_0)
              (mul_nonneg hM30 (by positivity))
        _ = (L2 * eKf ^ 2 * M3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring
    have hB0 : ‖d2v (yw - yv - Pm) qw‖ ≤ (Kstar2 * C2 * M3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (yw - yv - Pm) qw hKstar20 (by positivity) hd2n
        (hacc t ht) hqwn).trans (le_of_eq (by ring))
    have hC0 : ‖d2v Pm (qw - qv)‖ ≤ (Kstar2 * eKs * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pm (qw - qv) hKstar20 (by positivity) hd2n hPmn
        (hQlip t ht)).trans (le_of_eq (by ring))
    rw [hCB0def, show (L2 * eKf ^ 2 * M3 + Kstar2 * C2 * M3 + Kstar2 * eKs * Ce)
        * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
      = (L2 * eKf ^ 2 * M3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        + (Kstar2 * C2 * M3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        + (Kstar2 * eKs * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hA0 hB0)) hC0)
  have hd3n : ‖d3v‖ ≤ Kstar3 := hK3v t ht
  have hsep2 : ‖yw - yv‖ ^ 2 ≤ eKf ^ 2 * ‖m‖ ^ 2 := by
    calc ‖yw - yv‖ ^ 2 ≤ (‖m‖ * eKf) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2
      _ = eKf ^ 2 * ‖m‖ ^ 2 := by ring
  have hPhn : ‖Ph‖ ≤ eKs * ‖h‖ := by
    rw [hPhE]; exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιh
  have hPh'n : ‖Ph'‖ ≤ eKs * ‖h‖ := by
    rw [hPh'E]; exact clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιh
  have hPmn : ‖Pm‖ ≤ eKs * ‖m‖ := by
    rw [hPmE]; exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιm
  have hδh : ‖Ph' - Ph‖ ≤ C3 * ‖m‖ * ‖h‖ := by
    have he : Ph' - Ph = (Φ' t - Φ t) (expJetIota h) := by
      rw [hPh'E, hPhE, ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota h)‖ ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ :=
          (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * ‖m‖) * ‖h‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
      _ = C3 * ‖m‖ * ‖h‖ := by ring
  have hQwklV : ‖Qwkl t - Qkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖ :=
    (norm_sub_le _ _).trans (add_le_add (hVwkl t ht) (hVkl t ht))
  have hPkn : ‖Pk‖ ≤ eKs * ‖k‖ := by
    rw [hPkE]; exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιk
  have hPk'n : ‖Pk'‖ ≤ eKs * ‖k‖ := by
    rw [hPk'E]; exact clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιk
  have hPln : ‖Pl‖ ≤ eKs * ‖l‖ := by
    rw [hPlE]; exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιl
  have hPl'n : ‖Pl'‖ ≤ eKs * ‖l‖ := by
    rw [hPl'E]; exact clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιl
  have hδk : ‖Pk' - Pk‖ ≤ C3 * ‖m‖ * ‖k‖ := by
    have he : Pk' - Pk = (Φ' t - Φ t) (expJetIota k) := by
      rw [hPk'E, hPkE, ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota k)‖ ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ :=
          (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * ‖m‖) * ‖k‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
      _ = C3 * ‖m‖ * ‖k‖ := by ring
  have hδl : ‖Pl' - Pl‖ ≤ C3 * ‖m‖ * ‖l‖ := by
    have he : Pl' - Pl = (Φ' t - Φ t) (expJetIota l) := by
      rw [hPl'E, hPlE, ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota l)‖ ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) l‖ :=
          (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * ‖m‖) * ‖l‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιl (norm_nonneg _) (by positivity)
      _ = C3 * ‖m‖ * ‖l‖ := by ring
  have hQwhlV : ‖Qwhl t - Qhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖ :=
    (norm_sub_le _ _).trans (add_le_add (hVwhl t ht) (hVhl t ht))
  have hQwhkV : ‖Qwhk t - Qhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖ :=
    (norm_sub_le _ _).trans (add_le_add (hVwhk t ht) (hVhk t ht))
  -- ── Block 2 (kl-cross) ──
  have hbB2 : ‖d2w Ph' (Qwkl t) - d2v Ph (Qkl t) - d3v Ph Pm (Qkl t)
      - d2v (Qhm t) (Qkl t) - d2v Ph (Qklm t)‖ ≤ CB2 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
    have hsA : d3v Pm Ph (Qkl t) = d3v Ph Pm (Qkl t) :=
      fderiv3_geodesicField_symm_ab g gi hC yv Pm Ph (Qkl t)
    have heq2 : d2w Ph' (Qwkl t) - d2v Ph (Qkl t) - d3v Ph Pm (Qkl t)
        - d2v (Qhm t) (Qkl t) - d2v Ph (Qklm t)
        = (d2w - d2v - d3v (yw - yv)) Ph' (Qwkl t)
          + d3v (yw - yv - Pm) Ph' (Qwkl t)
          + d3v Pm (Ph' - Ph) (Qwkl t)
          + d3v Pm Ph (Qwkl t - Qkl t)
          + d2v (Ph' - Ph) (Qwkl t - Qkl t)
          + d2v (Ph' - Ph - Qhm t) (Qkl t - Qwkl t)
          + d2v (Ph' - Ph - Qhm t) (Qwkl t)
          + d2v Ph (Qwkl t - Qkl t - Qklm t) := by
      simp only [map_sub, map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      rw [hsA]; abel
    rw [heq2]
    have hR21 : ‖(d2w - d2v - d3v (yw - yv)) Ph' (Qwkl t)‖
        ≤ (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Ph' (Qwkl t) (by positivity)
        (by positivity) (hD2tay t ht) hPh'n (hVwkl t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * (Cq2 * ‖k‖ * ‖l‖)
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖h‖) * (Cq2 * ‖k‖ * ‖l‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Ph' (Qwkl t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Ph' (Qwkl t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPh'n (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Ph' - Ph) (Qwkl t)‖
        ≤ (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Ph' - Ph) (Qwkl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδh (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Ph (Qwkl t - Qkl t)‖
        ≤ (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Ph (Qwkl t - Qkl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPhn (hQlipkl t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Ph' - Ph) (Qwkl t - Qkl t)‖
        ≤ (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Ph' - Ph) (Qwkl t - Qkl t) hKstar20 (by positivity)
        hd2n hδh (hQlipkl t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Ph' - Ph - Qhm t) (Qkl t - Qwkl t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      have hb : ‖Qkl t - Qwkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖ := by
        rw [norm_sub_rev]; exact hQwklV
      exact (clmApply2_norm_le d2v (Ph' - Ph - Qhm t) (Qkl t - Qwkl t) hKstar20 (by positivity)
        hd2n (hFPh t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Ph' - Ph - Qhm t) (Qwkl t)‖
        ≤ (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Ph' - Ph - Qhm t) (Qwkl t) hKstar20 (by positivity)
        hd2n (hFPh t ht) (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Ph (Qwkl t - Qkl t - Qklm t)‖
        ≤ (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Ph (Qwkl t - Qkl t - Qklm t) hKstar20 (by positivity)
        hd2n hPhn (hFQkl t ht)).trans (le_of_eq (by ring))
    rw [hCB2def, show (L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
          + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd)
          * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 3 (hl-cross) ──
  have hbB3 : ‖d2w Pk' (Qwhl t) - d2v Pk (Qhl t) - d3v Pk Pm (Qhl t)
      - d2v (Qhl t) (Qkm t) - d2v Pk (Qhlm t)‖ ≤ CB3 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
    have hsA : d3v Pm Pk (Qhl t) = d3v Pk Pm (Qhl t) :=
      fderiv3_geodesicField_symm_ab g gi hC yv Pm Pk (Qhl t)
    have hsB : d2v (Qkm t) (Qhl t) = d2v (Qhl t) (Qkm t) :=
      fderiv2_geodesicField_symm g gi hC yv (Qkm t) (Qhl t)
    have heq3 : d2w Pk' (Qwhl t) - d2v Pk (Qhl t) - d3v Pk Pm (Qhl t)
        - d2v (Qhl t) (Qkm t) - d2v Pk (Qhlm t)
        = (d2w - d2v - d3v (yw - yv)) Pk' (Qwhl t)
          + d3v (yw - yv - Pm) Pk' (Qwhl t)
          + d3v Pm (Pk' - Pk) (Qwhl t)
          + d3v Pm Pk (Qwhl t - Qhl t)
          + d2v (Pk' - Pk) (Qwhl t - Qhl t)
          + d2v (Pk' - Pk - Qkm t) (Qhl t - Qwhl t)
          + d2v (Pk' - Pk - Qkm t) (Qwhl t)
          + d2v Pk (Qwhl t - Qhl t - Qhlm t) := by
      simp only [map_sub, map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      rw [hsA, hsB]; abel
    rw [heq3]
    have hR21 : ‖(d2w - d2v - d3v (yw - yv)) Pk' (Qwhl t)‖
        ≤ (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Pk' (Qwhl t) (by positivity)
        (by positivity) (hD2tay t ht) hPk'n (hVwhl t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖k‖) * (Cq2 * ‖h‖ * ‖l‖)
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖k‖) * (Cq2 * ‖h‖ * ‖l‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Pk' (Qwhl t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Pk' (Qwhl t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPk'n (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Pk' - Pk) (Qwhl t)‖
        ≤ (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Pk' - Pk) (Qwhl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδk (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Pk (Qwhl t - Qhl t)‖
        ≤ (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Pk (Qwhl t - Qhl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPkn (hQliphl t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Pk' - Pk) (Qwhl t - Qhl t)‖
        ≤ (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pk' - Pk) (Qwhl t - Qhl t) hKstar20 (by positivity)
        hd2n hδk (hQliphl t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Pk' - Pk - Qkm t) (Qhl t - Qwhl t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      have hb : ‖Qhl t - Qwhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖ := by
        rw [norm_sub_rev]; exact hQwhlV
      exact (clmApply2_norm_le d2v (Pk' - Pk - Qkm t) (Qhl t - Qwhl t) hKstar20 (by positivity)
        hd2n (hFPk t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Pk' - Pk - Qkm t) (Qwhl t)‖
        ≤ (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pk' - Pk - Qkm t) (Qwhl t) hKstar20 (by positivity)
        hd2n (hFPk t ht) (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Pk (Qwhl t - Qhl t - Qhlm t)‖
        ≤ (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pk (Qwhl t - Qhl t - Qhlm t) hKstar20 (by positivity)
        hd2n hPkn (hFQhl t ht)).trans (le_of_eq (by ring))
    rw [hCB3def, show (L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
          + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd)
          * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 4 (hk-cross) ──
  have hbB4 : ‖d2w Pl' (Qwhk t) - d2v Pl (Qhk t) - d3v Pl Pm (Qhk t)
      - d2v (Qhk t) (Qlm t) - d2v Pl (Qhkm t)‖ ≤ CB4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
    have hsA : d3v Pm Pl (Qhk t) = d3v Pl Pm (Qhk t) :=
      fderiv3_geodesicField_symm_ab g gi hC yv Pm Pl (Qhk t)
    have hsB : d2v (Qlm t) (Qhk t) = d2v (Qhk t) (Qlm t) :=
      fderiv2_geodesicField_symm g gi hC yv (Qlm t) (Qhk t)
    have heq4 : d2w Pl' (Qwhk t) - d2v Pl (Qhk t) - d3v Pl Pm (Qhk t)
        - d2v (Qhk t) (Qlm t) - d2v Pl (Qhkm t)
        = (d2w - d2v - d3v (yw - yv)) Pl' (Qwhk t)
          + d3v (yw - yv - Pm) Pl' (Qwhk t)
          + d3v Pm (Pl' - Pl) (Qwhk t)
          + d3v Pm Pl (Qwhk t - Qhk t)
          + d2v (Pl' - Pl) (Qwhk t - Qhk t)
          + d2v (Pl' - Pl - Qlm t) (Qhk t - Qwhk t)
          + d2v (Pl' - Pl - Qlm t) (Qwhk t)
          + d2v Pl (Qwhk t - Qhk t - Qhkm t) := by
      simp only [map_sub, map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      rw [hsA, hsB]; abel
    rw [heq4]
    have hR21 : ‖(d2w - d2v - d3v (yw - yv)) Pl' (Qwhk t)‖
        ≤ (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Pl' (Qwhk t) (by positivity)
        (by positivity) (hD2tay t ht) hPl'n (hVwhk t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖l‖) * (Cq2 * ‖h‖ * ‖k‖)
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖l‖) * (Cq2 * ‖h‖ * ‖k‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Pl' (Qwhk t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Pl' (Qwhk t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPl'n (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Pl' - Pl) (Qwhk t)‖
        ≤ (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Pl' - Pl) (Qwhk t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδl (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Pl (Qwhk t - Qhk t)‖
        ≤ (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Pl (Qwhk t - Qhk t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPln (hQliphk t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Pl' - Pl) (Qwhk t - Qhk t)‖
        ≤ (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pl' - Pl) (Qwhk t - Qhk t) hKstar20 (by positivity)
        hd2n hδl (hQliphk t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Pl' - Pl - Qlm t) (Qhk t - Qwhk t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      have hb : ‖Qhk t - Qwhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖ := by
        rw [norm_sub_rev]; exact hQwhkV
      exact (clmApply2_norm_le d2v (Pl' - Pl - Qlm t) (Qhk t - Qwhk t) hKstar20 (by positivity)
        hd2n (hFPl t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Pl' - Pl - Qlm t) (Qwhk t)‖
        ≤ (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pl' - Pl - Qlm t) (Qwhk t) hKstar20 (by positivity)
        hd2n (hFPl t ht) (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Pl (Qwhk t - Qhk t - Qhkm t)‖
        ≤ (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pl (Qwhk t - Qhk t - Qhkm t) hKstar20 (by positivity)
        hd2n hPln (hFQhk t ht)).trans (le_of_eq (by ring))
    rw [hCB4def, show (L3 * eKf ^ 2 * eKs * Cq2 + Kstar3 * C2 * eKs * Cq2
          + Kstar3 * eKs * C3 * Cq2 + Kstar3 * eKs ^ 2 * Ce + Kstar2 * C3 * Ce
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd)
          * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * C2 * eKs * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar2 * eKs * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 1 (pure D³F/D⁴F) ──
  have hd4n : ‖d4v‖ ≤ Kstar4 := hK4v t ht
  have hPkPk'V : ‖Pk - Pk'‖ ≤ eKs * ‖k‖ + eKs * ‖k‖ :=
    (norm_sub_le _ _).trans (add_le_add hPkn hPk'n)
  have hPlPl'V : ‖Pl - Pl'‖ ≤ eKs * ‖l‖ + eKs * ‖l‖ :=
    (norm_sub_le _ _).trans (add_le_add hPln hPl'n)
  have hbB1 : ‖d3w Ph' Pk' Pl' - d3v Ph Pk Pl - d4v Ph Pk Pl Pm
      - d3v Pk Pl (Qhm t) - d3v Ph Pl (Qkm t) - d3v Ph Pk (Qlm t)‖
        ≤ CB1 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
    have hcyc4 : d4v Pm Ph Pk Pl = d4v Ph Pk Pl Pm :=
      fderiv4_geodesicField_symm_cyc g gi hC yv Pm Ph Pk Pl
    have hcyc3 : d3v (Qhm t) Pk Pl = d3v Pk Pl (Qhm t) :=
      fderiv3_geodesicField_symm_cyc g gi hC yv (Qhm t) Pk Pl
    have hbc3 : d3v Ph (Qkm t) Pl = d3v Ph Pl (Qkm t) :=
      fderiv3_geodesicField_symm_bc g gi hC yv Ph (Qkm t) Pl
    have heq1 : d3w Ph' Pk' Pl' - d3v Ph Pk Pl - d4v Ph Pk Pl Pm
        - d3v Pk Pl (Qhm t) - d3v Ph Pl (Qkm t) - d3v Ph Pk (Qlm t)
        = (d3w - d3v - d4v (yw - yv)) Ph' Pk' Pl'
          + d4v (yw - yv - Pm) Ph' Pk' Pl'
          + d4v Pm (Ph' - Ph) Pk' Pl'
          + d4v Pm Ph (Pk' - Pk) Pl'
          + d4v Pm Ph Pk (Pl' - Pl)
          + d3v (Ph' - Ph - Qhm t) Pk' Pl'
          + d3v (Ph' - Ph) (Pk' - Pk) Pl'
          + d3v (Ph' - Ph - Qhm t) (Pk - Pk') Pl'
          + d3v (Ph' - Ph) Pk (Pl' - Pl)
          + d3v (Ph' - Ph - Qhm t) Pk (Pl - Pl')
          + d3v Ph (Pk' - Pk - Qkm t) Pl'
          + d3v Ph (Pk' - Pk) (Pl' - Pl)
          + d3v Ph (Pk' - Pk - Qkm t) (Pl - Pl')
          + d3v Ph Pk (Pl' - Pl - Qlm t) := by
      simp only [map_sub, map_add, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
      rw [hcyc4, hcyc3, hbc3]; abel
    rw [heq1]
    have hRa : ‖(d3w - d3v - d4v (yw - yv)) Ph' Pk' Pl'‖
        ≤ (L4 * eKf ^ 2 * eKs ^ 3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      refine (clmApply3_norm_le (d3w - d3v - d4v (yw - yv)) Ph' Pk' Pl' (by positivity)
        (by positivity) (by positivity) (hD3tay t ht) hPh'n hPk'n hPl'n).trans ?_
      calc (L4 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖)
          ≤ (L4 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL4_0) (by positivity)) (by positivity))
              (by positivity)
        _ = (L4 * eKf ^ 2 * eKs ^ 3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring
    have hRb : ‖d4v (yw - yv - Pm) Ph' Pk' Pl'‖
        ≤ (Kstar4 * C2 * eKs ^ 3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v (yw - yv - Pm) Ph' Pk' Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n (hacc t ht) hPh'n hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRc : ‖d4v Pm (Ph' - Ph) Pk' Pl'‖
        ≤ (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm (Ph' - Ph) Pk' Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hδh hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRd : ‖d4v Pm Ph (Pk' - Pk) Pl'‖
        ≤ (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm Ph (Pk' - Pk) Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hPhn hδk hPl'n).trans (le_of_eq (by ring))
    have hRe : ‖d4v Pm Ph Pk (Pl' - Pl)‖
        ≤ (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm Ph Pk (Pl' - Pl) hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hPhn hPkn hδl).trans (le_of_eq (by ring))
    have hRf : ‖d3v (Ph' - Ph - Qhm t) Pk' Pl'‖
        ≤ (Kstar3 * Cd * eKs ^ 2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) Pk' Pl' hKstar30 (by positivity) (by positivity)
        hd3n (hFPh t ht) hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRg1 : ‖d3v (Ph' - Ph) (Pk' - Pk) Pl'‖
        ≤ (Kstar3 * C3 ^ 2 * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph) (Pk' - Pk) Pl' hKstar30 (by positivity) (by positivity)
        hd3n hδh hδk hPl'n).trans (le_of_eq (by ring))
    have hRg2 : ‖d3v (Ph' - Ph - Qhm t) (Pk - Pk') Pl'‖
        ≤ (Kstar3 * Cd * (eKs + eKs) * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) (Pk - Pk') Pl' hKstar30 (by positivity)
        (by positivity) hd3n (hFPh t ht) hPkPk'V hPl'n).trans (le_of_eq (by ring))
    have hRh1 : ‖d3v (Ph' - Ph) Pk (Pl' - Pl)‖
        ≤ (Kstar3 * C3 ^ 2 * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph) Pk (Pl' - Pl) hKstar30 (by positivity) (by positivity)
        hd3n hδh hPkn hδl).trans (le_of_eq (by ring))
    have hRh2 : ‖d3v (Ph' - Ph - Qhm t) Pk (Pl - Pl')‖
        ≤ (Kstar3 * Cd * (eKs + eKs) * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
      refine (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) Pk (Pl - Pl') hKstar30 (by positivity)
        (by positivity) hd3n (hFPh t ht) hPkn hPlPl'V).trans (le_of_eq ?_)
      ring
    have hRj : ‖d3v Ph (Pk' - Pk - Qkm t) Pl'‖
        ≤ (Kstar3 * eKs ^ 2 * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk - Qkm t) Pl' hKstar30 (by positivity) (by positivity)
        hd3n hPhn (hFPk t ht) hPl'n).trans (le_of_eq (by ring))
    have hRk1 : ‖d3v Ph (Pk' - Pk) (Pl' - Pl)‖
        ≤ (Kstar3 * eKs * C3 ^ 2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk) (Pl' - Pl) hKstar30 (by positivity) (by positivity)
        hd3n hPhn hδk hδl).trans (le_of_eq (by ring))
    have hRk2 : ‖d3v Ph (Pk' - Pk - Qkm t) (Pl - Pl')‖
        ≤ (Kstar3 * eKs * Cd * (eKs + eKs)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk - Qkm t) (Pl - Pl') hKstar30 (by positivity)
        (by positivity) hd3n hPhn (hFPk t ht) hPlPl'V).trans (le_of_eq (by ring))
    have hRl : ‖d3v Ph Pk (Pl' - Pl - Qlm t)‖
        ≤ (Kstar3 * eKs ^ 2 * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph Pk (Pl' - Pl - Qlm t) hKstar30 (by positivity) (by positivity)
        hd3n hPhn hPkn (hFPl t ht)).trans (le_of_eq (by ring))
    rw [hCB1def, show (L4 * eKf ^ 2 * eKs ^ 3
          + Kstar4 * C2 * eKs ^ 3
          + Kstar4 * eKs ^ 3 * C3 + Kstar4 * eKs ^ 3 * C3
          + Kstar4 * eKs ^ 3 * C3
          + Kstar3 * Cd * eKs ^ 2
          + Kstar3 * C3 ^ 2 * eKs
          + Kstar3 * Cd * (eKs + eKs) * eKs
          + Kstar3 * C3 ^ 2 * eKs
          + Kstar3 * Cd * (eKs + eKs) * eKs
          + Kstar3 * eKs ^ 2 * Cd
          + Kstar3 * eKs * C3 ^ 2
          + Kstar3 * eKs * Cd * (eKs + eKs)
          + Kstar3 * eKs ^ 2 * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
        = (L4 * eKf ^ 2 * eKs ^ 3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar4 * C2 * eKs ^ 3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * Cd * eKs ^ 2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * C3 ^ 2 * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * Cd * (eKs + eKs) * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * C3 ^ 2 * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * Cd * (eKs + eKs) * eKs) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 ^ 2) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs * Cd * (eKs + eKs)) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Cd) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hRl)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRk2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRk1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRj)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRh2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRh1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRg2)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRg1)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRf)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRe)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRd)
    refine (norm_add_le _ _).trans (add_le_add ?_ hRc)
    exact (norm_add_le _ _).trans (add_le_add hRa hRb)
  -- ── final assembly ──
  rw [show (CB0 + CB1 + CB2 + CB3 + CB4) * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
    = CB0 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 + CB1 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
      + CB2 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 + CB3 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2
      + CB4 * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB4)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB3)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB2)
  exact (norm_add_le _ _).trans (add_le_add hbB0 hbB1)

end QIQTH.ExpMap
