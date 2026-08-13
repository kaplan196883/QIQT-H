/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase4
import QIQTH.ExpJet4RemainderUnif

/-!
# JET-5 TOWER — rung J5-5c: the `r`-uniform fourth-variation two-point feeder

This file lands `expJet4Val_v_two_pt_Icc_unif`, the `r`-uniform packaging of the banked
`expJet4Val_v_two_pt_Icc_const` (`ExpJet5Phase4.lean`): a single `Ce ≥ 0` bounds the genuine
fourth-variation two-point difference
`‖S^{hklm}_{v+r}(t) − S^{hklm}_v(t)‖ ≤ Ce·‖h‖·‖k‖·‖l‖·‖m‖·‖r‖`
for every varied base direction `r` (`‖v+r‖ ≤ expRho`) and every `v+r`-propagator `Φ'`, on all of
`[0,1]`.  `S^{hklm}` is the genuine fourth-variation curve `expJet4Curve` whose six pair inputs are
`expJet2Curve` and four triple inputs are the genuine `expJet3Curve`.

This is the `hQlipTop` datum the order-5 `_unif` remainder brick (J5-5d) consumes in
`expJet5_remainder_quadratic_bound_P` (`ExpJet5RemainderP.lean`).  It is the exact one-Fréchet-order-up
mirror of `expJet3Val_v_two_pt_Icc_unif` (`ExpJet4RemainderUnif.lean`).

## Honest firewall (binding)

Uniform-feeder layer ONLY.  Does NOT prove `expJet5_remainder_quadratic_bound_unif`,
`expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`
(CONDITIONAL).  The constant is chosen up front from `r`-independent uniform tube/Lipschitz data and
the value bound is discharged from the proved `expJet4Val_v_two_pt_Icc_const`.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 6

variable {n : ℕ}

set_option maxHeartbeats 6400000 in
/-- **The `r`-UNIFORM `‖h‖‖k‖‖l‖‖m‖`-separated fourth-variation two-point Lipschitz bound.**  The
    `r`-uniform packaging of `expJet4Val_v_two_pt_Icc_const`: a single `Ce ≥ 0` bounds the genuine
    fourth-variation two-point difference `‖S^{hklm}_{v+r}(t) − S^{hklm}_v(t)‖ ≤ Ce·‖h‖·‖k‖·‖l‖·‖m‖·‖r‖`
    for every varied direction `r` (`‖v+r‖ ≤ expRho`) and every `v+r`-propagator `Φ'`, on `[0,1]`.
    `S^{hklm}` is the genuine fourth-variation curve `expJet4Curve` whose six pair inputs are the
    `expJet2Curve` pairs and four triple inputs are the genuine `expJet3Curve` triples.  This is the
    `hQlipTop` datum the order-5 `_unif` remainder brick consumes; the exact one-order-up mirror of
    `expJet3Val_v_two_pt_Icc_unif`. -/
theorem expJet4Val_v_two_pt_Icc_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ (r : Point n) (hvr : ‖v + r‖ ≤ expRho g gi hC p)
      (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (_hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
      (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
      (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + r) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
      (h k l m : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expJet4Curve g gi hC p (v + r) Φ'
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k)
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
            (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
            (expJet3Curve g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
            (expJet3Curve g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
            (expJet3Curve g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
            (expJet3Curve g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
            hvr hΦ'cont
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k)
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
            (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
            (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
            (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
            (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
            (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
               (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
            h k l m t
          - expJet4Curve g gi hC p v Φ
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
            hv hΦcont
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
            (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
            (expJet3Curve_continuousOn g gi hC p v Φ
               (expJet2Curve g gi hC p v Φ hv hΦcont k l)
               (expJet2Curve g gi hC p v Φ hv hΦcont h l)
               (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
            (expJet3Curve_continuousOn g gi hC p v Φ
               (expJet2Curve g gi hC p v Φ hv hΦcont k m)
               (expJet2Curve g gi hC p v Φ hv hΦcont h m)
               (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
            (expJet3Curve_continuousOn g gi hC p v Φ
               (expJet2Curve g gi hC p v Φ hv hΦcont l m)
               (expJet2Curve g gi hC p v Φ hv hΦcont h m)
               (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
            (expJet3Curve_continuousOn g gi hC p v Φ
               (expJet2Curve g gi hC p v Φ hv hΦcont l m)
               (expJet2Curve g gi hC p v Φ hv hΦcont k m)
               (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
               (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
            h k l m t‖
        ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by
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
  refine ⟨expJet4VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ)
      Kstar Kstar2 Kstar3 Kstar4,
    expJet4VtpConst_nonneg _ _ _ _ _ _ _ _ _ Ldf.2 Ld2f.2 Ld3f.2 Ld4f.2
      hKstar20 hKstar30 hKstar40, ?_⟩
  intro r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k l m
  -- ── pair-curve ODE/init data at `v` ──
  obtain ⟨hQhkv0, -, -, hQhkvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQhlv0, -, -, hQhlvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨hQhmv0, -, -, hQhmvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h m).choose_spec
  obtain ⟨hQklv0, -, -, hQklvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨hQkmv0, -, -, hQkmvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k m).choose_spec
  obtain ⟨hQlmv0, -, -, hQlmvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont l m).choose_spec
  -- ── pair-curve ODE/init data at `v + r` ──
  obtain ⟨hQhkw0, -, -, hQhkwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h k).choose_spec
  obtain ⟨hQhlw0, -, -, hQhlwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h l).choose_spec
  obtain ⟨hQhmw0, -, -, hQhmwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h m).choose_spec
  obtain ⟨hQklw0, -, -, hQklwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont k l).choose_spec
  obtain ⟨hQkmw0, -, -, hQkmwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont k m).choose_spec
  obtain ⟨hQlmw0, -, -, hQlmwd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont l m).choose_spec
  -- ── triple-curve ODE/init data at `v` ──
  obtain ⟨hQhklv0, -, -, hQhklvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  obtain ⟨hQhkmv0, -, -, hQhkmvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m).choose_spec
  obtain ⟨hQhlmv0, -, -, hQhlmvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m).choose_spec
  obtain ⟨hQklmv0, -, -, hQklmvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m).choose_spec
  -- ── triple-curve ODE/init data at `v + r` ──
  obtain ⟨hQhklw0, -, -, hQhklwd⟩ := (expJet3Fund g gi hC p (v + r) Φ'
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l).choose_spec
  obtain ⟨hQhkmw0, -, -, hQhkmwd⟩ := (expJet3Fund g gi hC p (v + r) Φ'
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m).choose_spec
  obtain ⟨hQhlmw0, -, -, hQhlmwd⟩ := (expJet3Fund g gi hC p (v + r) Φ'
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m).choose_spec
  obtain ⟨hQklmw0, -, -, hQklmwd⟩ := (expJet3Fund g gi hC p (v + r) Φ'
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m).choose_spec
  -- ── quadruple-curve ODE/init data at `v` and `v + r` ──
  obtain ⟨hRv0, -, -, hRvd⟩ := (expJet4Fund g gi hC p v Φ
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
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
    h k l m).choose_spec
  obtain ⟨hRw0, -, -, hRwd⟩ := (expJet4Fund g gi hC p (v + r) Φ'
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
    hvr hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
    (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
    (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
    (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
    (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
    h k l m).choose_spec
  have hconst := expJet4Val_v_two_pt_Icc_const g gi hC p v (v + r) hv hvr
    Kf Ldf Ld2f Ld3f Ld4f Kstar Kstar2 Kstar3 Kstar4
    hKstar0 hKstar20 hKstar30 hKstar40
    hLipF hLipDF hLipD2 hLipD3 hLipD4 hKstaru hK2u hK3u hK4u Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
    (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
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
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
    (expJet3Curve g gi hC p (v + r) Φ'
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
       (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
    (expJet4Curve g gi hC p v Φ
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
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
      (expJet3Curve_continuousOn g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont k l)
         (expJet2Curve g gi hC p v Φ hv hΦcont h l)
         (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
      (expJet3Curve_continuousOn g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
      (expJet3Curve_continuousOn g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
      (expJet3Curve_continuousOn g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
      h k l m)
    (expJet4Curve g gi hC p (v + r) Φ'
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k)
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
      (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
      (expJet3Curve g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
      (expJet3Curve g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
      (expJet3Curve g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
      (expJet3Curve g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
      hvr hΦ'cont
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k)
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
      (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
      (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l)
      (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m)
      (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m)
      (expJet3Curve_continuousOn g gi hC p (v + r) Φ'
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m)
         (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m)
      h k l m)
    h k l m
    hQhkv0 hQhlv0 hQhmv0 hQklv0 hQkmv0 hQlmv0
    hQhkw0 hQhlw0 hQhmw0 hQklw0 hQkmw0 hQlmw0
    hQhklv0 hQhkmv0 hQhlmv0 hQklmv0
    hQhklw0 hQhkmw0 hQhlmw0 hQklmw0
    hRv0 hRw0
    hQhkvd hQhlvd hQhmvd hQklvd hQkmvd hQlmvd
    hQhkwd hQhlwd hQhmwd hQklwd hQkmwd hQlmwd
    hQhklvd hQhkmvd hQhlmvd hQklmvd
    hQhklwd hQhkmwd hQhlmwd hQklmwd
    hRvd hRwd
  intro t ht
  rw [norm_sub_rev]
  refine (hconst t ht).trans (le_of_eq ?_)
  rw [show v - (v + r) = -r by abel, norm_neg]; ring

end QIQTH.ExpMap
