/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Phase5
import Mathlib

/-!
# JET-5 phase 5 gate (J4-649): curved non-vacuity of `expJet5Val_v_two_pt_diff`

The antecedent set of the ★ J5-3 crux `expJet5Val_v_two_pt_diff` (`ExpJet5Phase5.lean`) is
jointly SATISFIABLE at the genuinely curved witness `g^κ = curvedRNCMetric (−1)`
(`p = v = w = 0`): every hypothesis is discharged by a GENUINE witness — the Lipschitz data
by `ContDiffOn.exists_lipschitzOnWith` on the compact tube ball
(`expJet_fderiv{,2,3,4,5}_lipschitzOnWith`), the tube bounds by
`expJet_fderiv{,2,3,4,5}_tube_bddAbove_unif`, the propagator by `expJetFund`, the ten pair /
ten triple / five quadruple variations by `expJet2Fund` / `expJet3Fund` / `expJet4Fund`, and
the fifth variation by `expJet5Fund` — and the theorem fires.  This certifies the J5-3 layer
is non-vacuous at curved data (both parameter slots take the same witness, `v = w = 0`; this
is a SATISFIABILITY gate, NOT a curvature computation and NOT `a₁ = R/6`).

## Honest firewall (binding)

`a₁ = R/6` remains CONDITIONAL (flat tower non-vacuous; curved owes the remaining Jet-5
packaging J5-4/5/6 + the Duhamel carry + fat-K carriers + capstone co-instantiation + the
prior labelled piles).
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic

set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ}

set_option maxHeartbeats 6400000 in
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
/-- **Non-vacuity gate: the ★ J5-3 crux fires at the genuinely curved witness.**  At
    `g^κ = curvedRNCMetric (−1)`, `p = v = w = 0`, with the full genuine witness tower
    (`expJetFund` propagator, `expJet2Fund`/`expJet3Fund`/`expJet4Fund` lower variations,
    `expJet5Fund` fifth variation, compactness Lipschitz/tube data), every antecedent of
    `expJet5Val_v_two_pt_diff` holds and the conclusion is produced. -/
theorem expJet5Val_v_two_pt_diff_gate (h k l m r : Point n) :
    ∃ (Kf Ldf Ld2f Ld3f Ld4f Ld5f : NNReal) (Kstar Kstar2 Kstar3 Kstar4 Kstar5 : ℝ)
      (R : ℝ → (Point n × Point n)),
      ‖R 1 - R 1‖
        ≤ expJet5VtpConst (Kf : ℝ) (Ldf : ℝ) (Ld2f : ℝ) (Ld3f : ℝ) (Ld4f : ℝ) (Ld5f : ℝ)
            Kstar Kstar2 Kstar3 Kstar4 Kstar5
          * ‖(0 : Point n) - 0‖ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := by
  have hv : ‖(0 : Point n)‖ ≤ expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) (0 : Point n) := by
    simpa using (expRho_pos (n := n) (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0).le
  obtain ⟨Kf, hLipF⟩ :=
    ((contDiff_geodesicField (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num))).contDiffOn
        (s := Metric.closedBall ((0, 0) : Point n × Point n)
          (expConst (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 * expRho (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0))).exists_lipschitzOnWith
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
  obtain ⟨Qhk, hQhk0, hQhkc, _, hQhkd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont h k
  obtain ⟨Qhl, hQhl0, hQhlc, _, hQhld⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont h l
  obtain ⟨Qhm, hQhm0, hQhmc, _, hQhmd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont h m
  obtain ⟨Qhr, hQhr0, hQhrc, _, hQhrd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont h r
  obtain ⟨Qkl, hQkl0, hQklc, _, hQkld⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont k l
  obtain ⟨Qkm, hQkm0, hQkmc, _, hQkmd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont k m
  obtain ⟨Qkr, hQkr0, hQkrc, _, hQkrd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont k r
  obtain ⟨Qlm, hQlm0, hQlmc, _, hQlmd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont l m
  obtain ⟨Qlr, hQlr0, hQlrc, _, hQlrd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont l r
  obtain ⟨Qmr, hQmr0, hQmrc, _, hQmrd⟩ := expJet2Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ hv hΦcont m r
  obtain ⟨Qhkl, hQhkl0, hQhklc, _, hQhkld⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qkl Qhl Qhk hv hΦcont hQklc hQhlc hQhkc h k l
  obtain ⟨Qhkm, hQhkm0, hQhkmc, _, hQhkmd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qkm Qhm Qhk hv hΦcont hQkmc hQhmc hQhkc h k m
  obtain ⟨Qhkr, hQhkr0, hQhkrc, _, hQhkrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qkr Qhr Qhk hv hΦcont hQkrc hQhrc hQhkc h k r
  obtain ⟨Qhlm, hQhlm0, hQhlmc, _, hQhlmd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qlm Qhm Qhl hv hΦcont hQlmc hQhmc hQhlc h l m
  obtain ⟨Qhlr, hQhlr0, hQhlrc, _, hQhlrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qlr Qhr Qhl hv hΦcont hQlrc hQhrc hQhlc h l r
  obtain ⟨Qhmr, hQhmr0, hQhmrc, _, hQhmrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qmr Qhr Qhm hv hΦcont hQmrc hQhrc hQhmc h m r
  obtain ⟨Qklm, hQklm0, hQklmc, _, hQklmd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qlm Qkm Qkl hv hΦcont hQlmc hQkmc hQklc k l m
  obtain ⟨Qklr, hQklr0, hQklrc, _, hQklrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qlr Qkr Qkl hv hΦcont hQlrc hQkrc hQklc k l r
  obtain ⟨Qkmr, hQkmr0, hQkmrc, _, hQkmrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qmr Qkr Qkm hv hΦcont hQmrc hQkrc hQkmc k m r
  obtain ⟨Qlmr, hQlmr0, hQlmrc, _, hQlmrd⟩ := expJet3Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qmr Qlr Qlm hv hΦcont hQmrc hQlrc hQlmc l m r
  obtain ⟨Qhklm, hQhklm0, hQhklmc, _, hQhklmd⟩ := expJet4Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont hQhkc hQhlc hQhmc hQklc hQkmc hQlmc hQhklc hQhkmc hQhlmc hQklmc h k l m
  obtain ⟨Qhklr, hQhklr0, hQhklrc, _, hQhklrd⟩ := expJet4Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qhk Qhl Qhr Qkl Qkr Qlr Qhkl Qhkr Qhlr Qklr hv hΦcont hQhkc hQhlc hQhrc hQklc hQkrc hQlrc hQhklc hQhkrc hQhlrc hQklrc h k l r
  obtain ⟨Qhkmr, hQhkmr0, hQhkmrc, _, hQhkmrd⟩ := expJet4Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qhk Qhm Qhr Qkm Qkr Qmr Qhkm Qhkr Qhmr Qkmr hv hΦcont hQhkc hQhmc hQhrc hQkmc hQkrc hQmrc hQhkmc hQhkrc hQhmrc hQkmrc h k m r
  obtain ⟨Qhlmr, hQhlmr0, hQhlmrc, _, hQhlmrd⟩ := expJet4Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qhl Qhm Qhr Qlm Qlr Qmr Qhlm Qhlr Qhmr Qlmr hv hΦcont hQhlc hQhmc hQhrc hQlmc hQlrc hQmrc hQhlmc hQhlrc hQhmrc hQlmrc h l m r
  obtain ⟨Qklmr, hQklmr0, hQklmrc, _, hQklmrd⟩ := expJet4Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ Qkl Qkm Qkr Qlm Qlr Qmr Qklm Qklr Qkmr Qlmr hv hΦcont hQklc hQkmc hQkrc hQlmc hQlrc hQmrc hQklmc hQklrc hQkmrc hQlmrc k l m r
  obtain ⟨R, hR0, hRc, _, hRd⟩ := expJet5Fund (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 Φ
    Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr
    hv hΦcont
    hQhkc hQhlc hQhmc hQhrc hQklc hQkmc hQkrc hQlmc hQlrc hQmrc hQhklc hQhkmc hQhkrc hQhlmc hQhlrc hQhmrc hQklmc hQklrc hQkmrc hQlmrc hQhklmc hQhklrc hQhkmrc hQhlmrc hQklmrc
    h k l m r
  refine ⟨Kf, Ldf, Ld2f, Ld3f, Ld4f, Ld5f, Kstar, Kstar2, Kstar3, Kstar4, Kstar5, R, ?_⟩
  exact expJet5Val_v_two_pt_diff (curvedRNCMetric (-1)) (curvedRNCInv (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 0 hv hv
    Kf Ldf Ld2f Ld3f Ld4f Ld5f Kstar Kstar2 Kstar3 Kstar4 Kstar5
    hKstar0 hKstar20 hKstar30 hKstar40 hKstar50
    hLipF hLipDF hLipD2F hLipD3F hLipD4F hLipD5F
    hKstar hKstar2f hKstar3f hKstar4f hKstar5f
    Φ Φ hΦ0 hΦ0 hΦd hΦd
    Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr
    Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr
    Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr
    Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr
    Qhklm Qhklr Qhkmr Qhlmr Qklmr
    Qhklm Qhklr Qhkmr Qhlmr Qklmr
    R R h k l m r
    hQhk0 hQhl0 hQhm0 hQhr0 hQkl0 hQkm0 hQkr0 hQlm0 hQlr0 hQmr0
    hQhk0 hQhl0 hQhm0 hQhr0 hQkl0 hQkm0 hQkr0 hQlm0 hQlr0 hQmr0
    hQhkl0 hQhkm0 hQhkr0 hQhlm0 hQhlr0 hQhmr0 hQklm0 hQklr0 hQkmr0 hQlmr0
    hQhkl0 hQhkm0 hQhkr0 hQhlm0 hQhlr0 hQhmr0 hQklm0 hQklr0 hQkmr0 hQlmr0
    hQhklm0 hQhklr0 hQhkmr0 hQhlmr0 hQklmr0
    hQhklm0 hQhklr0 hQhkmr0 hQhlmr0 hQklmr0
    hR0 hR0
    hQhkd hQhld hQhmd hQhrd hQkld hQkmd hQkrd hQlmd hQlrd hQmrd
    hQhkd hQhld hQhmd hQhrd hQkld hQkmd hQkrd hQlmd hQlrd hQmrd
    hQhkld hQhkmd hQhkrd hQhlmd hQhlrd hQhmrd hQklmd hQklrd hQkmrd hQlmrd
    hQhkld hQhkmd hQhkrd hQhlmd hQhlrd hQhmrd hQklmd hQklrd hQkmrd hQlmrd
    hQhklmd hQhklrd hQhkmrd hQhlmrd hQklmrd
    hQhklmd hQhklrd hQhkmrd hQhlmrd hQklmrd
    hRd hRd

end QIQTH.ExpMap
