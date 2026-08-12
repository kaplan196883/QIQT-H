/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5TeleA
import Mathlib
/-!
# JET-5 phase-5 split, family file A (J4-650): abstract per-arity peel telescope

Brick **J4-650** of the JET-5 campaign toward the truly-unconditional `a₁ = R/6`
(`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Split of the timed-out monolith: this file
holds ABSTRACT D² partial telescopes of the 202-sub-term `ρ₅`-bound, over abstract
multilinear maps / atoms / OPAQUE scalar-bound blocks (`E, eKf, CPD, B2..B5, T2..T4`); NO
geometry, NO `Real.exp`/`^`/`VtpConst` in scope, so every `isDefEq`/`positivity` is trivial.
Consumed (with the blocks instantiated to their concrete `set`-values) by `ExpJet5Phase5.lean`.

## Honest firewall (binding)

Pure normed-space combinatorics.  Closes part of J5-3 only.  Does NOT establish
`exp_p ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`; `a₁ = R/6` remains
CONDITIONAL (flat tower non-vacuous; curved owes the remaining Jet-5 packaging + the Duhamel
carry + fat-K carriers + capstone co-instantiation + the prior labelled piles).
-/
namespace QIQTH.ExpMap

set_option maxSynthPendingDepth 5
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 65536

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
theorem expJet5TeleA0 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d2v d2w : V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qkmv qkmw : V)
    (qkrv qkrw : V)
    (qlmv qlmw : V)
    (qlrv qlrw : V)
    (qmrv qmrw : V)
    (qhklv qhklw : V)
    (qhkmv qhkmw : V)
    (qhkrv qhkrw : V)
    (qhlmv qhlmw : V)
    (qhlrv qhlrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd2diff : ‖d2v - d2w‖ ≤ Ld2f * (vw * eKf))
    (hd2n : ‖d2v‖ ≤ Kstar2)
    (hpn_h : ‖ph‖ ≤ E * nh) (hpn'_h : ‖ph'‖ ≤ E * nh)
    (hpn_k : ‖pk‖ ≤ E * nk) (hpn'_k : ‖pk'‖ ≤ E * nk)
    (hpn_l : ‖pl‖ ≤ E * nl) (hpn'_l : ‖pl'‖ ≤ E * nl)
    (hpn_m : ‖pm‖ ≤ E * nm) (hpn'_m : ‖pm'‖ ≤ E * nm)
    (hpn_r : ‖pr‖ ≤ E * nr) (hpn'_r : ‖pr'‖ ≤ E * nr)
    (hpd_h : ‖ph - ph'‖ ≤ CPD * vw * nh)
    (hpd_k : ‖pk - pk'‖ ≤ CPD * vw * nk)
    (hpd_l : ‖pl - pl'‖ ≤ CPD * vw * nl)
    (hpd_m : ‖pm - pm'‖ ≤ CPD * vw * nm)
    (hpd_r : ‖pr - pr'‖ ≤ CPD * vw * nr)
    (hval_km : ‖qkmv‖ ≤ B2 * nk * nm) (hval'_km : ‖qkmw‖ ≤ B2 * nk * nm)
    (hval_kr : ‖qkrv‖ ≤ B2 * nk * nr) (hval'_kr : ‖qkrw‖ ≤ B2 * nk * nr)
    (hval_lm : ‖qlmv‖ ≤ B2 * nl * nm) (hval'_lm : ‖qlmw‖ ≤ B2 * nl * nm)
    (hval_lr : ‖qlrv‖ ≤ B2 * nl * nr) (hval'_lr : ‖qlrw‖ ≤ B2 * nl * nr)
    (hval_mr : ‖qmrv‖ ≤ B2 * nm * nr) (hval'_mr : ‖qmrw‖ ≤ B2 * nm * nr)
    (hval_hkl : ‖qhklv‖ ≤ B3 * nh * nk * nl) (hval'_hkl : ‖qhklw‖ ≤ B3 * nh * nk * nl)
    (hval_hkm : ‖qhkmv‖ ≤ B3 * nh * nk * nm) (hval'_hkm : ‖qhkmw‖ ≤ B3 * nh * nk * nm)
    (hval_hkr : ‖qhkrv‖ ≤ B3 * nh * nk * nr) (hval'_hkr : ‖qhkrw‖ ≤ B3 * nh * nk * nr)
    (hval_hlm : ‖qhlmv‖ ≤ B3 * nh * nl * nm) (hval'_hlm : ‖qhlmw‖ ≤ B3 * nh * nl * nm)
    (hval_hlr : ‖qhlrv‖ ≤ B3 * nh * nl * nr) (hval'_hlr : ‖qhlrw‖ ≤ B3 * nh * nl * nr)
    (htp_km : ‖qkmv - qkmw‖ ≤ T2 * vw * nk * nm)
    (htp_kr : ‖qkrv - qkrw‖ ≤ T2 * vw * nk * nr)
    (htp_lm : ‖qlmv - qlmw‖ ≤ T2 * vw * nl * nm)
    (htp_lr : ‖qlrv - qlrw‖ ≤ T2 * vw * nl * nr)
    (htp_mr : ‖qmrv - qmrw‖ ≤ T2 * vw * nm * nr)
    (htp_hkl : ‖qhklv - qhklw‖ ≤ T3 * vw * nh * nk * nl)
    (htp_hkm : ‖qhkmv - qhkmw‖ ≤ T3 * vw * nh * nk * nm)
    (htp_hkr : ‖qhkrv - qhkrw‖ ≤ T3 * vw * nh * nk * nr)
    (htp_hlm : ‖qhlmv - qhlmw‖ ≤ T3 * vw * nh * nl * nm)
    (htp_hlr : ‖qhlrv - qhlrw‖ ≤ T3 * vw * nh * nl * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d2v qhklv qmrv - d2w qhklw qmrw) + (d2v qhkmv qlrv - d2w qhkmw qlrw) + (d2v qhkrv qlmv - d2w qhkrw qlmw) + (d2v qhlmv qkrv - d2w qhlmw qkrw) + (d2v qhlrv qkmv - d2w qhlrw qkmw)‖ ≤ c + (Kstar2 * (T3 * vw * nh * nk * nl) * (B2 * nm * nr) + Kstar2 * (B3 * nh * nk * nl) * (T2 * vw * nm * nr) + (Ld2f * (vw * eKf)) * (B3 * nh * nk * nl) * (B2 * nm * nr)) + (Kstar2 * (T3 * vw * nh * nk * nm) * (B2 * nl * nr) + Kstar2 * (B3 * nh * nk * nm) * (T2 * vw * nl * nr) + (Ld2f * (vw * eKf)) * (B3 * nh * nk * nm) * (B2 * nl * nr)) + (Kstar2 * (T3 * vw * nh * nk * nr) * (B2 * nl * nm) + Kstar2 * (B3 * nh * nk * nr) * (T2 * vw * nl * nm) + (Ld2f * (vw * eKf)) * (B3 * nh * nk * nr) * (B2 * nl * nm)) + (Kstar2 * (T3 * vw * nh * nl * nm) * (B2 * nk * nr) + Kstar2 * (B3 * nh * nl * nm) * (T2 * vw * nk * nr) + (Ld2f * (vw * eKf)) * (B3 * nh * nl * nm) * (B2 * nk * nr)) + (Kstar2 * (T3 * vw * nh * nl * nr) * (B2 * nk * nm) + Kstar2 * (B3 * nh * nl * nr) * (T2 * vw * nk * nm) + (Ld2f * (vw * eKf)) * (B3 * nh * nl * nr) * (B2 * nk * nm)) := by
  have hD37 := expJet5TelePeel2 d2v d2w qhklv qmrv qhklw qmrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hkl hval'_hkl hval_mr hval'_mr htp_hkl htp_mr
  have hD38 := expJet5TelePeel2 d2v d2w qhkmv qlrv qhkmw qlrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hkm hval'_hkm hval_lr hval'_lr htp_hkm htp_lr
  have hD39 := expJet5TelePeel2 d2v d2w qhkrv qlmv qhkrw qlmw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hkr hval'_hkr hval_lm hval'_lm htp_hkr htp_lm
  have hD40 := expJet5TelePeel2 d2v d2w qhlmv qkrv qhlmw qkrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hlm hval'_hlm hval_kr hval'_kr htp_hlm htp_kr
  have hD41 := expJet5TelePeel2 d2v d2w qhlrv qkmv qhlrw qkmw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hlr hval'_hlr hval_km hval'_km htp_hlr htp_km
  refine (norm_add_le _ _).trans (add_le_add ?_ hD41)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD40)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD39)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD38)
  exact (norm_add_le _ _).trans (add_le_add hX hD37)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleA1 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d2v d2w : V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhkv qhkw : V)
    (qhlv qhlw : V)
    (qhmv qhmw : V)
    (qhrv qhrw : V)
    (qklv qklw : V)
    (qhmrv qhmrw : V)
    (qklmv qklmw : V)
    (qklrv qklrw : V)
    (qkmrv qkmrw : V)
    (qlmrv qlmrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd2diff : ‖d2v - d2w‖ ≤ Ld2f * (vw * eKf))
    (hd2n : ‖d2v‖ ≤ Kstar2)
    (hpn_h : ‖ph‖ ≤ E * nh) (hpn'_h : ‖ph'‖ ≤ E * nh)
    (hpn_k : ‖pk‖ ≤ E * nk) (hpn'_k : ‖pk'‖ ≤ E * nk)
    (hpn_l : ‖pl‖ ≤ E * nl) (hpn'_l : ‖pl'‖ ≤ E * nl)
    (hpn_m : ‖pm‖ ≤ E * nm) (hpn'_m : ‖pm'‖ ≤ E * nm)
    (hpn_r : ‖pr‖ ≤ E * nr) (hpn'_r : ‖pr'‖ ≤ E * nr)
    (hpd_h : ‖ph - ph'‖ ≤ CPD * vw * nh)
    (hpd_k : ‖pk - pk'‖ ≤ CPD * vw * nk)
    (hpd_l : ‖pl - pl'‖ ≤ CPD * vw * nl)
    (hpd_m : ‖pm - pm'‖ ≤ CPD * vw * nm)
    (hpd_r : ‖pr - pr'‖ ≤ CPD * vw * nr)
    (hval_hk : ‖qhkv‖ ≤ B2 * nh * nk) (hval'_hk : ‖qhkw‖ ≤ B2 * nh * nk)
    (hval_hl : ‖qhlv‖ ≤ B2 * nh * nl) (hval'_hl : ‖qhlw‖ ≤ B2 * nh * nl)
    (hval_hm : ‖qhmv‖ ≤ B2 * nh * nm) (hval'_hm : ‖qhmw‖ ≤ B2 * nh * nm)
    (hval_hr : ‖qhrv‖ ≤ B2 * nh * nr) (hval'_hr : ‖qhrw‖ ≤ B2 * nh * nr)
    (hval_kl : ‖qklv‖ ≤ B2 * nk * nl) (hval'_kl : ‖qklw‖ ≤ B2 * nk * nl)
    (hval_hmr : ‖qhmrv‖ ≤ B3 * nh * nm * nr) (hval'_hmr : ‖qhmrw‖ ≤ B3 * nh * nm * nr)
    (hval_klm : ‖qklmv‖ ≤ B3 * nk * nl * nm) (hval'_klm : ‖qklmw‖ ≤ B3 * nk * nl * nm)
    (hval_klr : ‖qklrv‖ ≤ B3 * nk * nl * nr) (hval'_klr : ‖qklrw‖ ≤ B3 * nk * nl * nr)
    (hval_kmr : ‖qkmrv‖ ≤ B3 * nk * nm * nr) (hval'_kmr : ‖qkmrw‖ ≤ B3 * nk * nm * nr)
    (hval_lmr : ‖qlmrv‖ ≤ B3 * nl * nm * nr) (hval'_lmr : ‖qlmrw‖ ≤ B3 * nl * nm * nr)
    (htp_hk : ‖qhkv - qhkw‖ ≤ T2 * vw * nh * nk)
    (htp_hl : ‖qhlv - qhlw‖ ≤ T2 * vw * nh * nl)
    (htp_hm : ‖qhmv - qhmw‖ ≤ T2 * vw * nh * nm)
    (htp_hr : ‖qhrv - qhrw‖ ≤ T2 * vw * nh * nr)
    (htp_kl : ‖qklv - qklw‖ ≤ T2 * vw * nk * nl)
    (htp_hmr : ‖qhmrv - qhmrw‖ ≤ T3 * vw * nh * nm * nr)
    (htp_klm : ‖qklmv - qklmw‖ ≤ T3 * vw * nk * nl * nm)
    (htp_klr : ‖qklrv - qklrw‖ ≤ T3 * vw * nk * nl * nr)
    (htp_kmr : ‖qkmrv - qkmrw‖ ≤ T3 * vw * nk * nm * nr)
    (htp_lmr : ‖qlmrv - qlmrw‖ ≤ T3 * vw * nl * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d2v qhmrv qklv - d2w qhmrw qklw) + (d2v qklmv qhrv - d2w qklmw qhrw) + (d2v qklrv qhmv - d2w qklrw qhmw) + (d2v qkmrv qhlv - d2w qkmrw qhlw) + (d2v qlmrv qhkv - d2w qlmrw qhkw)‖ ≤ c + (Kstar2 * (T3 * vw * nh * nm * nr) * (B2 * nk * nl) + Kstar2 * (B3 * nh * nm * nr) * (T2 * vw * nk * nl) + (Ld2f * (vw * eKf)) * (B3 * nh * nm * nr) * (B2 * nk * nl)) + (Kstar2 * (T3 * vw * nk * nl * nm) * (B2 * nh * nr) + Kstar2 * (B3 * nk * nl * nm) * (T2 * vw * nh * nr) + (Ld2f * (vw * eKf)) * (B3 * nk * nl * nm) * (B2 * nh * nr)) + (Kstar2 * (T3 * vw * nk * nl * nr) * (B2 * nh * nm) + Kstar2 * (B3 * nk * nl * nr) * (T2 * vw * nh * nm) + (Ld2f * (vw * eKf)) * (B3 * nk * nl * nr) * (B2 * nh * nm)) + (Kstar2 * (T3 * vw * nk * nm * nr) * (B2 * nh * nl) + Kstar2 * (B3 * nk * nm * nr) * (T2 * vw * nh * nl) + (Ld2f * (vw * eKf)) * (B3 * nk * nm * nr) * (B2 * nh * nl)) + (Kstar2 * (T3 * vw * nl * nm * nr) * (B2 * nh * nk) + Kstar2 * (B3 * nl * nm * nr) * (T2 * vw * nh * nk) + (Ld2f * (vw * eKf)) * (B3 * nl * nm * nr) * (B2 * nh * nk)) := by
  have hD42 := expJet5TelePeel2 d2v d2w qhmrv qklv qhmrw qklw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_hmr hval'_hmr hval_kl hval'_kl htp_hmr htp_kl
  have hD43 := expJet5TelePeel2 d2v d2w qklmv qhrv qklmw qhrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_klm hval'_klm hval_hr hval'_hr htp_klm htp_hr
  have hD44 := expJet5TelePeel2 d2v d2w qklrv qhmv qklrw qhmw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_klr hval'_klr hval_hm hval'_hm htp_klr htp_hm
  have hD45 := expJet5TelePeel2 d2v d2w qkmrv qhlv qkmrw qhlw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_kmr hval'_kmr hval_hl hval'_hl htp_kmr htp_hl
  have hD46 := expJet5TelePeel2 d2v d2w qlmrv qhkv qlmrw qhkw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hval_lmr hval'_lmr hval_hk hval'_hk htp_lmr htp_hk
  refine (norm_add_le _ _).trans (add_le_add ?_ hD46)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD45)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD44)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD43)
  exact (norm_add_le _ _).trans (add_le_add hX hD42)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleA2 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d2v d2w : V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhklmv qhklmw : V)
    (qhklrv qhklrw : V)
    (qhkmrv qhkmrw : V)
    (qhlmrv qhlmrw : V)
    (qklmrv qklmrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd2diff : ‖d2v - d2w‖ ≤ Ld2f * (vw * eKf))
    (hd2n : ‖d2v‖ ≤ Kstar2)
    (hpn_h : ‖ph‖ ≤ E * nh) (hpn'_h : ‖ph'‖ ≤ E * nh)
    (hpn_k : ‖pk‖ ≤ E * nk) (hpn'_k : ‖pk'‖ ≤ E * nk)
    (hpn_l : ‖pl‖ ≤ E * nl) (hpn'_l : ‖pl'‖ ≤ E * nl)
    (hpn_m : ‖pm‖ ≤ E * nm) (hpn'_m : ‖pm'‖ ≤ E * nm)
    (hpn_r : ‖pr‖ ≤ E * nr) (hpn'_r : ‖pr'‖ ≤ E * nr)
    (hpd_h : ‖ph - ph'‖ ≤ CPD * vw * nh)
    (hpd_k : ‖pk - pk'‖ ≤ CPD * vw * nk)
    (hpd_l : ‖pl - pl'‖ ≤ CPD * vw * nl)
    (hpd_m : ‖pm - pm'‖ ≤ CPD * vw * nm)
    (hpd_r : ‖pr - pr'‖ ≤ CPD * vw * nr)
    (hval_hklm : ‖qhklmv‖ ≤ B4 * nh * nk * nl * nm) (hval'_hklm : ‖qhklmw‖ ≤ B4 * nh * nk * nl * nm)
    (hval_hklr : ‖qhklrv‖ ≤ B4 * nh * nk * nl * nr) (hval'_hklr : ‖qhklrw‖ ≤ B4 * nh * nk * nl * nr)
    (hval_hkmr : ‖qhkmrv‖ ≤ B4 * nh * nk * nm * nr) (hval'_hkmr : ‖qhkmrw‖ ≤ B4 * nh * nk * nm * nr)
    (hval_hlmr : ‖qhlmrv‖ ≤ B4 * nh * nl * nm * nr) (hval'_hlmr : ‖qhlmrw‖ ≤ B4 * nh * nl * nm * nr)
    (hval_klmr : ‖qklmrv‖ ≤ B4 * nk * nl * nm * nr) (hval'_klmr : ‖qklmrw‖ ≤ B4 * nk * nl * nm * nr)
    (htp_hklm : ‖qhklmv - qhklmw‖ ≤ T4 * vw * nh * nk * nl * nm)
    (htp_hklr : ‖qhklrv - qhklrw‖ ≤ T4 * vw * nh * nk * nl * nr)
    (htp_hkmr : ‖qhkmrv - qhkmrw‖ ≤ T4 * vw * nh * nk * nm * nr)
    (htp_hlmr : ‖qhlmrv - qhlmrw‖ ≤ T4 * vw * nh * nl * nm * nr)
    (htp_klmr : ‖qklmrv - qklmrw‖ ≤ T4 * vw * nk * nl * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d2v ph qklmrv - d2w ph' qklmrw) + (d2v pk qhlmrv - d2w pk' qhlmrw) + (d2v pl qhkmrv - d2w pl' qhkmrw) + (d2v pm qhklrv - d2w pm' qhklrw) + (d2v pr qhklmv - d2w pr' qhklmw)‖ ≤ c + (Kstar2 * (CPD * vw * nh) * (B4 * nk * nl * nm * nr) + Kstar2 * (E * nh) * (T4 * vw * nk * nl * nm * nr) + (Ld2f * (vw * eKf)) * (E * nh) * (B4 * nk * nl * nm * nr)) + (Kstar2 * (CPD * vw * nk) * (B4 * nh * nl * nm * nr) + Kstar2 * (E * nk) * (T4 * vw * nh * nl * nm * nr) + (Ld2f * (vw * eKf)) * (E * nk) * (B4 * nh * nl * nm * nr)) + (Kstar2 * (CPD * vw * nl) * (B4 * nh * nk * nm * nr) + Kstar2 * (E * nl) * (T4 * vw * nh * nk * nm * nr) + (Ld2f * (vw * eKf)) * (E * nl) * (B4 * nh * nk * nm * nr)) + (Kstar2 * (CPD * vw * nm) * (B4 * nh * nk * nl * nr) + Kstar2 * (E * nm) * (T4 * vw * nh * nk * nl * nr) + (Ld2f * (vw * eKf)) * (E * nm) * (B4 * nh * nk * nl * nr)) + (Kstar2 * (CPD * vw * nr) * (B4 * nh * nk * nl * nm) + Kstar2 * (E * nr) * (T4 * vw * nh * nk * nl * nm) + (Ld2f * (vw * eKf)) * (E * nr) * (B4 * nh * nk * nl * nm)) := by
  have hD47 := expJet5TelePeel2 d2v d2w ph qklmrv ph' qklmrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hpn_h hpn'_h hval_klmr hval'_klmr hpd_h htp_klmr
  have hD48 := expJet5TelePeel2 d2v d2w pk qhlmrv pk' qhlmrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hpn_k hpn'_k hval_hlmr hval'_hlmr hpd_k htp_hlmr
  have hD49 := expJet5TelePeel2 d2v d2w pl qhkmrv pl' qhkmrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hpn_l hpn'_l hval_hkmr hval'_hkmr hpd_l htp_hkmr
  have hD50 := expJet5TelePeel2 d2v d2w pm qhklrv pm' qhklrw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hpn_m hpn'_m hval_hklr hval'_hklr hpd_m htp_hklr
  have hD51 := expJet5TelePeel2 d2v d2w pr qhklmv pr' qhklmw
    hKstar20 (by positivity) (by positivity) (by positivity)
    hd2n hd2diff hpn_r hpn'_r hval_hklm hval'_hklm hpd_r htp_hklm
  refine (norm_add_le _ _).trans (add_le_add ?_ hD51)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD50)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD49)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD48)
  exact (norm_add_le _ _).trans (add_le_add hX hD47)

end QIQTH.ExpMap
