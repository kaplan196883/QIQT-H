/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5TeleA
import Mathlib
/-!
# JET-5 phase-5 split, family file B (J4-650): abstract per-arity peel telescope

Brick **J4-650** of the JET-5 campaign toward the truly-unconditional `a₁ = R/6`
(`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Split of the timed-out monolith: this file
holds ABSTRACT D³ partial telescopes of the 202-sub-term `ρ₅`-bound, over abstract
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
theorem expJet5TeleB0 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d3v d3w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhlv qhlw : V)
    (qhmv qhmw : V)
    (qklv qklw : V)
    (qkmv qkmw : V)
    (qkrv qkrw : V)
    (qlmv qlmw : V)
    (qlrv qlrw : V)
    (qmrv qmrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd3diff : ‖d3v - d3w‖ ≤ Ld3f * (vw * eKf))
    (hd3n : ‖d3v‖ ≤ Kstar3)
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
    (hval_hl : ‖qhlv‖ ≤ B2 * nh * nl) (hval'_hl : ‖qhlw‖ ≤ B2 * nh * nl)
    (hval_hm : ‖qhmv‖ ≤ B2 * nh * nm) (hval'_hm : ‖qhmw‖ ≤ B2 * nh * nm)
    (hval_kl : ‖qklv‖ ≤ B2 * nk * nl) (hval'_kl : ‖qklw‖ ≤ B2 * nk * nl)
    (hval_km : ‖qkmv‖ ≤ B2 * nk * nm) (hval'_km : ‖qkmw‖ ≤ B2 * nk * nm)
    (hval_kr : ‖qkrv‖ ≤ B2 * nk * nr) (hval'_kr : ‖qkrw‖ ≤ B2 * nk * nr)
    (hval_lm : ‖qlmv‖ ≤ B2 * nl * nm) (hval'_lm : ‖qlmw‖ ≤ B2 * nl * nm)
    (hval_lr : ‖qlrv‖ ≤ B2 * nl * nr) (hval'_lr : ‖qlrw‖ ≤ B2 * nl * nr)
    (hval_mr : ‖qmrv‖ ≤ B2 * nm * nr) (hval'_mr : ‖qmrw‖ ≤ B2 * nm * nr)
    (htp_hl : ‖qhlv - qhlw‖ ≤ T2 * vw * nh * nl)
    (htp_hm : ‖qhmv - qhmw‖ ≤ T2 * vw * nh * nm)
    (htp_kl : ‖qklv - qklw‖ ≤ T2 * vw * nk * nl)
    (htp_km : ‖qkmv - qkmw‖ ≤ T2 * vw * nk * nm)
    (htp_kr : ‖qkrv - qkrw‖ ≤ T2 * vw * nk * nr)
    (htp_lm : ‖qlmv - qlmw‖ ≤ T2 * vw * nl * nm)
    (htp_lr : ‖qlrv - qlrw‖ ≤ T2 * vw * nl * nr)
    (htp_mr : ‖qmrv - qmrw‖ ≤ T2 * vw * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d3v ph qklv qmrv - d3w ph' qklw qmrw) + (d3v ph qkmv qlrv - d3w ph' qkmw qlrw) + (d3v ph qkrv qlmv - d3w ph' qkrw qlmw) + (d3v pk qhlv qmrv - d3w pk' qhlw qmrw) + (d3v pk qhmv qlrv - d3w pk' qhmw qlrw)‖ ≤ c + (Kstar3 * (CPD * vw * nh) * (B2 * nk * nl) * (B2 * nm * nr) + Kstar3 * (E * nh) * (T2 * vw * nk * nl) * (B2 * nm * nr) + Kstar3 * (E * nh) * (B2 * nk * nl) * (T2 * vw * nm * nr) + (Ld3f * (vw * eKf)) * (E * nh) * (B2 * nk * nl) * (B2 * nm * nr)) + (Kstar3 * (CPD * vw * nh) * (B2 * nk * nm) * (B2 * nl * nr) + Kstar3 * (E * nh) * (T2 * vw * nk * nm) * (B2 * nl * nr) + Kstar3 * (E * nh) * (B2 * nk * nm) * (T2 * vw * nl * nr) + (Ld3f * (vw * eKf)) * (E * nh) * (B2 * nk * nm) * (B2 * nl * nr)) + (Kstar3 * (CPD * vw * nh) * (B2 * nk * nr) * (B2 * nl * nm) + Kstar3 * (E * nh) * (T2 * vw * nk * nr) * (B2 * nl * nm) + Kstar3 * (E * nh) * (B2 * nk * nr) * (T2 * vw * nl * nm) + (Ld3f * (vw * eKf)) * (E * nh) * (B2 * nk * nr) * (B2 * nl * nm)) + (Kstar3 * (CPD * vw * nk) * (B2 * nh * nl) * (B2 * nm * nr) + Kstar3 * (E * nk) * (T2 * vw * nh * nl) * (B2 * nm * nr) + Kstar3 * (E * nk) * (B2 * nh * nl) * (T2 * vw * nm * nr) + (Ld3f * (vw * eKf)) * (E * nk) * (B2 * nh * nl) * (B2 * nm * nr)) + (Kstar3 * (CPD * vw * nk) * (B2 * nh * nm) * (B2 * nl * nr) + Kstar3 * (E * nk) * (T2 * vw * nh * nm) * (B2 * nl * nr) + Kstar3 * (E * nk) * (B2 * nh * nm) * (T2 * vw * nl * nr) + (Ld3f * (vw * eKf)) * (E * nk) * (B2 * nh * nm) * (B2 * nl * nr)) := by
  have hD12 := expJet5TelePeel3 d3v d3w ph qklv qmrv ph' qklw qmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hval_kl hval'_kl hval_mr hval'_mr hpd_h htp_kl htp_mr
  have hD13 := expJet5TelePeel3 d3v d3w ph qkmv qlrv ph' qkmw qlrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hval_km hval'_km hval_lr hval'_lr hpd_h htp_km htp_lr
  have hD14 := expJet5TelePeel3 d3v d3w ph qkrv qlmv ph' qkrw qlmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hval_kr hval'_kr hval_lm hval'_lm hpd_h htp_kr htp_lm
  have hD15 := expJet5TelePeel3 d3v d3w pk qhlv qmrv pk' qhlw qmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hval_hl hval'_hl hval_mr hval'_mr hpd_k htp_hl htp_mr
  have hD16 := expJet5TelePeel3 d3v d3w pk qhmv qlrv pk' qhmw qlrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hval_hm hval'_hm hval_lr hval'_lr hpd_k htp_hm htp_lr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD16)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD15)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD14)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD13)
  exact (norm_add_le _ _).trans (add_le_add hX hD12)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleB1 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d3v d3w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhkv qhkw : V)
    (qhmv qhmw : V)
    (qhrv qhrw : V)
    (qkmv qkmw : V)
    (qkrv qkrw : V)
    (qlmv qlmw : V)
    (qlrv qlrw : V)
    (qmrv qmrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd3diff : ‖d3v - d3w‖ ≤ Ld3f * (vw * eKf))
    (hd3n : ‖d3v‖ ≤ Kstar3)
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
    (hval_hm : ‖qhmv‖ ≤ B2 * nh * nm) (hval'_hm : ‖qhmw‖ ≤ B2 * nh * nm)
    (hval_hr : ‖qhrv‖ ≤ B2 * nh * nr) (hval'_hr : ‖qhrw‖ ≤ B2 * nh * nr)
    (hval_km : ‖qkmv‖ ≤ B2 * nk * nm) (hval'_km : ‖qkmw‖ ≤ B2 * nk * nm)
    (hval_kr : ‖qkrv‖ ≤ B2 * nk * nr) (hval'_kr : ‖qkrw‖ ≤ B2 * nk * nr)
    (hval_lm : ‖qlmv‖ ≤ B2 * nl * nm) (hval'_lm : ‖qlmw‖ ≤ B2 * nl * nm)
    (hval_lr : ‖qlrv‖ ≤ B2 * nl * nr) (hval'_lr : ‖qlrw‖ ≤ B2 * nl * nr)
    (hval_mr : ‖qmrv‖ ≤ B2 * nm * nr) (hval'_mr : ‖qmrw‖ ≤ B2 * nm * nr)
    (htp_hk : ‖qhkv - qhkw‖ ≤ T2 * vw * nh * nk)
    (htp_hm : ‖qhmv - qhmw‖ ≤ T2 * vw * nh * nm)
    (htp_hr : ‖qhrv - qhrw‖ ≤ T2 * vw * nh * nr)
    (htp_km : ‖qkmv - qkmw‖ ≤ T2 * vw * nk * nm)
    (htp_kr : ‖qkrv - qkrw‖ ≤ T2 * vw * nk * nr)
    (htp_lm : ‖qlmv - qlmw‖ ≤ T2 * vw * nl * nm)
    (htp_lr : ‖qlrv - qlrw‖ ≤ T2 * vw * nl * nr)
    (htp_mr : ‖qmrv - qmrw‖ ≤ T2 * vw * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d3v pk qhrv qlmv - d3w pk' qhrw qlmw) + (d3v pl qhkv qmrv - d3w pl' qhkw qmrw) + (d3v pl qhmv qkrv - d3w pl' qhmw qkrw) + (d3v pl qhrv qkmv - d3w pl' qhrw qkmw) + (d3v pm qhkv qlrv - d3w pm' qhkw qlrw)‖ ≤ c + (Kstar3 * (CPD * vw * nk) * (B2 * nh * nr) * (B2 * nl * nm) + Kstar3 * (E * nk) * (T2 * vw * nh * nr) * (B2 * nl * nm) + Kstar3 * (E * nk) * (B2 * nh * nr) * (T2 * vw * nl * nm) + (Ld3f * (vw * eKf)) * (E * nk) * (B2 * nh * nr) * (B2 * nl * nm)) + (Kstar3 * (CPD * vw * nl) * (B2 * nh * nk) * (B2 * nm * nr) + Kstar3 * (E * nl) * (T2 * vw * nh * nk) * (B2 * nm * nr) + Kstar3 * (E * nl) * (B2 * nh * nk) * (T2 * vw * nm * nr) + (Ld3f * (vw * eKf)) * (E * nl) * (B2 * nh * nk) * (B2 * nm * nr)) + (Kstar3 * (CPD * vw * nl) * (B2 * nh * nm) * (B2 * nk * nr) + Kstar3 * (E * nl) * (T2 * vw * nh * nm) * (B2 * nk * nr) + Kstar3 * (E * nl) * (B2 * nh * nm) * (T2 * vw * nk * nr) + (Ld3f * (vw * eKf)) * (E * nl) * (B2 * nh * nm) * (B2 * nk * nr)) + (Kstar3 * (CPD * vw * nl) * (B2 * nh * nr) * (B2 * nk * nm) + Kstar3 * (E * nl) * (T2 * vw * nh * nr) * (B2 * nk * nm) + Kstar3 * (E * nl) * (B2 * nh * nr) * (T2 * vw * nk * nm) + (Ld3f * (vw * eKf)) * (E * nl) * (B2 * nh * nr) * (B2 * nk * nm)) + (Kstar3 * (CPD * vw * nm) * (B2 * nh * nk) * (B2 * nl * nr) + Kstar3 * (E * nm) * (T2 * vw * nh * nk) * (B2 * nl * nr) + Kstar3 * (E * nm) * (B2 * nh * nk) * (T2 * vw * nl * nr) + (Ld3f * (vw * eKf)) * (E * nm) * (B2 * nh * nk) * (B2 * nl * nr)) := by
  have hD17 := expJet5TelePeel3 d3v d3w pk qhrv qlmv pk' qhrw qlmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hval_hr hval'_hr hval_lm hval'_lm hpd_k htp_hr htp_lm
  have hD18 := expJet5TelePeel3 d3v d3w pl qhkv qmrv pl' qhkw qmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_l hpn'_l hval_hk hval'_hk hval_mr hval'_mr hpd_l htp_hk htp_mr
  have hD19 := expJet5TelePeel3 d3v d3w pl qhmv qkrv pl' qhmw qkrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_l hpn'_l hval_hm hval'_hm hval_kr hval'_kr hpd_l htp_hm htp_kr
  have hD20 := expJet5TelePeel3 d3v d3w pl qhrv qkmv pl' qhrw qkmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_l hpn'_l hval_hr hval'_hr hval_km hval'_km hpd_l htp_hr htp_km
  have hD21 := expJet5TelePeel3 d3v d3w pm qhkv qlrv pm' qhkw qlrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_m hpn'_m hval_hk hval'_hk hval_lr hval'_lr hpd_m htp_hk htp_lr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD21)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD20)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD19)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD18)
  exact (norm_add_le _ _).trans (add_le_add hX hD17)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleB2 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d3v d3w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
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
    (qkmv qkmw : V)
    (qkrv qkrw : V)
    (qlmv qlmw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd3diff : ‖d3v - d3w‖ ≤ Ld3f * (vw * eKf))
    (hd3n : ‖d3v‖ ≤ Kstar3)
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
    (hval_km : ‖qkmv‖ ≤ B2 * nk * nm) (hval'_km : ‖qkmw‖ ≤ B2 * nk * nm)
    (hval_kr : ‖qkrv‖ ≤ B2 * nk * nr) (hval'_kr : ‖qkrw‖ ≤ B2 * nk * nr)
    (hval_lm : ‖qlmv‖ ≤ B2 * nl * nm) (hval'_lm : ‖qlmw‖ ≤ B2 * nl * nm)
    (htp_hk : ‖qhkv - qhkw‖ ≤ T2 * vw * nh * nk)
    (htp_hl : ‖qhlv - qhlw‖ ≤ T2 * vw * nh * nl)
    (htp_hm : ‖qhmv - qhmw‖ ≤ T2 * vw * nh * nm)
    (htp_hr : ‖qhrv - qhrw‖ ≤ T2 * vw * nh * nr)
    (htp_kl : ‖qklv - qklw‖ ≤ T2 * vw * nk * nl)
    (htp_km : ‖qkmv - qkmw‖ ≤ T2 * vw * nk * nm)
    (htp_kr : ‖qkrv - qkrw‖ ≤ T2 * vw * nk * nr)
    (htp_lm : ‖qlmv - qlmw‖ ≤ T2 * vw * nl * nm)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d3v pm qhlv qkrv - d3w pm' qhlw qkrw) + (d3v pm qhrv qklv - d3w pm' qhrw qklw) + (d3v pr qhkv qlmv - d3w pr' qhkw qlmw) + (d3v pr qhlv qkmv - d3w pr' qhlw qkmw) + (d3v pr qhmv qklv - d3w pr' qhmw qklw)‖ ≤ c + (Kstar3 * (CPD * vw * nm) * (B2 * nh * nl) * (B2 * nk * nr) + Kstar3 * (E * nm) * (T2 * vw * nh * nl) * (B2 * nk * nr) + Kstar3 * (E * nm) * (B2 * nh * nl) * (T2 * vw * nk * nr) + (Ld3f * (vw * eKf)) * (E * nm) * (B2 * nh * nl) * (B2 * nk * nr)) + (Kstar3 * (CPD * vw * nm) * (B2 * nh * nr) * (B2 * nk * nl) + Kstar3 * (E * nm) * (T2 * vw * nh * nr) * (B2 * nk * nl) + Kstar3 * (E * nm) * (B2 * nh * nr) * (T2 * vw * nk * nl) + (Ld3f * (vw * eKf)) * (E * nm) * (B2 * nh * nr) * (B2 * nk * nl)) + (Kstar3 * (CPD * vw * nr) * (B2 * nh * nk) * (B2 * nl * nm) + Kstar3 * (E * nr) * (T2 * vw * nh * nk) * (B2 * nl * nm) + Kstar3 * (E * nr) * (B2 * nh * nk) * (T2 * vw * nl * nm) + (Ld3f * (vw * eKf)) * (E * nr) * (B2 * nh * nk) * (B2 * nl * nm)) + (Kstar3 * (CPD * vw * nr) * (B2 * nh * nl) * (B2 * nk * nm) + Kstar3 * (E * nr) * (T2 * vw * nh * nl) * (B2 * nk * nm) + Kstar3 * (E * nr) * (B2 * nh * nl) * (T2 * vw * nk * nm) + (Ld3f * (vw * eKf)) * (E * nr) * (B2 * nh * nl) * (B2 * nk * nm)) + (Kstar3 * (CPD * vw * nr) * (B2 * nh * nm) * (B2 * nk * nl) + Kstar3 * (E * nr) * (T2 * vw * nh * nm) * (B2 * nk * nl) + Kstar3 * (E * nr) * (B2 * nh * nm) * (T2 * vw * nk * nl) + (Ld3f * (vw * eKf)) * (E * nr) * (B2 * nh * nm) * (B2 * nk * nl)) := by
  have hD22 := expJet5TelePeel3 d3v d3w pm qhlv qkrv pm' qhlw qkrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_m hpn'_m hval_hl hval'_hl hval_kr hval'_kr hpd_m htp_hl htp_kr
  have hD23 := expJet5TelePeel3 d3v d3w pm qhrv qklv pm' qhrw qklw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_m hpn'_m hval_hr hval'_hr hval_kl hval'_kl hpd_m htp_hr htp_kl
  have hD24 := expJet5TelePeel3 d3v d3w pr qhkv qlmv pr' qhkw qlmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_r hpn'_r hval_hk hval'_hk hval_lm hval'_lm hpd_r htp_hk htp_lm
  have hD25 := expJet5TelePeel3 d3v d3w pr qhlv qkmv pr' qhlw qkmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_r hpn'_r hval_hl hval'_hl hval_km hval'_km hpd_r htp_hl htp_km
  have hD26 := expJet5TelePeel3 d3v d3w pr qhmv qklv pr' qhmw qklw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_r hpn'_r hval_hm hval'_hm hval_kl hval'_kl hpd_r htp_hm htp_kl
  refine (norm_add_le _ _).trans (add_le_add ?_ hD26)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD25)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD24)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD23)
  exact (norm_add_le _ _).trans (add_le_add hX hD22)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleB3 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d3v d3w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
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
    (hd3diff : ‖d3v - d3w‖ ≤ Ld3f * (vw * eKf))
    (hd3n : ‖d3v‖ ≤ Kstar3)
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
    (hval_hkl : ‖qhklv‖ ≤ B3 * nh * nk * nl) (hval'_hkl : ‖qhklw‖ ≤ B3 * nh * nk * nl)
    (hval_hkm : ‖qhkmv‖ ≤ B3 * nh * nk * nm) (hval'_hkm : ‖qhkmw‖ ≤ B3 * nh * nk * nm)
    (hval_hkr : ‖qhkrv‖ ≤ B3 * nh * nk * nr) (hval'_hkr : ‖qhkrw‖ ≤ B3 * nh * nk * nr)
    (hval_hlm : ‖qhlmv‖ ≤ B3 * nh * nl * nm) (hval'_hlm : ‖qhlmw‖ ≤ B3 * nh * nl * nm)
    (hval_hlr : ‖qhlrv‖ ≤ B3 * nh * nl * nr) (hval'_hlr : ‖qhlrw‖ ≤ B3 * nh * nl * nr)
    (htp_hkl : ‖qhklv - qhklw‖ ≤ T3 * vw * nh * nk * nl)
    (htp_hkm : ‖qhkmv - qhkmw‖ ≤ T3 * vw * nh * nk * nm)
    (htp_hkr : ‖qhkrv - qhkrw‖ ≤ T3 * vw * nh * nk * nr)
    (htp_hlm : ‖qhlmv - qhlmw‖ ≤ T3 * vw * nh * nl * nm)
    (htp_hlr : ‖qhlrv - qhlrw‖ ≤ T3 * vw * nh * nl * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d3v pm pr qhklv - d3w pm' pr' qhklw) + (d3v pl pr qhkmv - d3w pl' pr' qhkmw) + (d3v pl pm qhkrv - d3w pl' pm' qhkrw) + (d3v pk pr qhlmv - d3w pk' pr' qhlmw) + (d3v pk pm qhlrv - d3w pk' pm' qhlrw)‖ ≤ c + (Kstar3 * (CPD * vw * nm) * (E * nr) * (B3 * nh * nk * nl) + Kstar3 * (E * nm) * (CPD * vw * nr) * (B3 * nh * nk * nl) + Kstar3 * (E * nm) * (E * nr) * (T3 * vw * nh * nk * nl) + (Ld3f * (vw * eKf)) * (E * nm) * (E * nr) * (B3 * nh * nk * nl)) + (Kstar3 * (CPD * vw * nl) * (E * nr) * (B3 * nh * nk * nm) + Kstar3 * (E * nl) * (CPD * vw * nr) * (B3 * nh * nk * nm) + Kstar3 * (E * nl) * (E * nr) * (T3 * vw * nh * nk * nm) + (Ld3f * (vw * eKf)) * (E * nl) * (E * nr) * (B3 * nh * nk * nm)) + (Kstar3 * (CPD * vw * nl) * (E * nm) * (B3 * nh * nk * nr) + Kstar3 * (E * nl) * (CPD * vw * nm) * (B3 * nh * nk * nr) + Kstar3 * (E * nl) * (E * nm) * (T3 * vw * nh * nk * nr) + (Ld3f * (vw * eKf)) * (E * nl) * (E * nm) * (B3 * nh * nk * nr)) + (Kstar3 * (CPD * vw * nk) * (E * nr) * (B3 * nh * nl * nm) + Kstar3 * (E * nk) * (CPD * vw * nr) * (B3 * nh * nl * nm) + Kstar3 * (E * nk) * (E * nr) * (T3 * vw * nh * nl * nm) + (Ld3f * (vw * eKf)) * (E * nk) * (E * nr) * (B3 * nh * nl * nm)) + (Kstar3 * (CPD * vw * nk) * (E * nm) * (B3 * nh * nl * nr) + Kstar3 * (E * nk) * (CPD * vw * nm) * (B3 * nh * nl * nr) + Kstar3 * (E * nk) * (E * nm) * (T3 * vw * nh * nl * nr) + (Ld3f * (vw * eKf)) * (E * nk) * (E * nm) * (B3 * nh * nl * nr)) := by
  have hD27 := expJet5TelePeel3 d3v d3w pm pr qhklv pm' pr' qhklw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_m hpn'_m hpn_r hpn'_r hval_hkl hval'_hkl hpd_m hpd_r htp_hkl
  have hD28 := expJet5TelePeel3 d3v d3w pl pr qhkmv pl' pr' qhkmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_l hpn'_l hpn_r hpn'_r hval_hkm hval'_hkm hpd_l hpd_r htp_hkm
  have hD29 := expJet5TelePeel3 d3v d3w pl pm qhkrv pl' pm' qhkrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_l hpn'_l hpn_m hpn'_m hval_hkr hval'_hkr hpd_l hpd_m htp_hkr
  have hD30 := expJet5TelePeel3 d3v d3w pk pr qhlmv pk' pr' qhlmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hpn_r hpn'_r hval_hlm hval'_hlm hpd_k hpd_r htp_hlm
  have hD31 := expJet5TelePeel3 d3v d3w pk pm qhlrv pk' pm' qhlrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hpn_m hpn'_m hval_hlr hval'_hlr hpd_k hpd_m htp_hlr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD31)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD30)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD29)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD28)
  exact (norm_add_le _ _).trans (add_le_add hX hD27)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleB4 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d3v d3w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
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
    (hd3diff : ‖d3v - d3w‖ ≤ Ld3f * (vw * eKf))
    (hd3n : ‖d3v‖ ≤ Kstar3)
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
    (hval_hmr : ‖qhmrv‖ ≤ B3 * nh * nm * nr) (hval'_hmr : ‖qhmrw‖ ≤ B3 * nh * nm * nr)
    (hval_klm : ‖qklmv‖ ≤ B3 * nk * nl * nm) (hval'_klm : ‖qklmw‖ ≤ B3 * nk * nl * nm)
    (hval_klr : ‖qklrv‖ ≤ B3 * nk * nl * nr) (hval'_klr : ‖qklrw‖ ≤ B3 * nk * nl * nr)
    (hval_kmr : ‖qkmrv‖ ≤ B3 * nk * nm * nr) (hval'_kmr : ‖qkmrw‖ ≤ B3 * nk * nm * nr)
    (hval_lmr : ‖qlmrv‖ ≤ B3 * nl * nm * nr) (hval'_lmr : ‖qlmrw‖ ≤ B3 * nl * nm * nr)
    (htp_hmr : ‖qhmrv - qhmrw‖ ≤ T3 * vw * nh * nm * nr)
    (htp_klm : ‖qklmv - qklmw‖ ≤ T3 * vw * nk * nl * nm)
    (htp_klr : ‖qklrv - qklrw‖ ≤ T3 * vw * nk * nl * nr)
    (htp_kmr : ‖qkmrv - qkmrw‖ ≤ T3 * vw * nk * nm * nr)
    (htp_lmr : ‖qlmrv - qlmrw‖ ≤ T3 * vw * nl * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d3v pk pl qhmrv - d3w pk' pl' qhmrw) + (d3v ph pr qklmv - d3w ph' pr' qklmw) + (d3v ph pm qklrv - d3w ph' pm' qklrw) + (d3v ph pl qkmrv - d3w ph' pl' qkmrw) + (d3v ph pk qlmrv - d3w ph' pk' qlmrw)‖ ≤ c + (Kstar3 * (CPD * vw * nk) * (E * nl) * (B3 * nh * nm * nr) + Kstar3 * (E * nk) * (CPD * vw * nl) * (B3 * nh * nm * nr) + Kstar3 * (E * nk) * (E * nl) * (T3 * vw * nh * nm * nr) + (Ld3f * (vw * eKf)) * (E * nk) * (E * nl) * (B3 * nh * nm * nr)) + (Kstar3 * (CPD * vw * nh) * (E * nr) * (B3 * nk * nl * nm) + Kstar3 * (E * nh) * (CPD * vw * nr) * (B3 * nk * nl * nm) + Kstar3 * (E * nh) * (E * nr) * (T3 * vw * nk * nl * nm) + (Ld3f * (vw * eKf)) * (E * nh) * (E * nr) * (B3 * nk * nl * nm)) + (Kstar3 * (CPD * vw * nh) * (E * nm) * (B3 * nk * nl * nr) + Kstar3 * (E * nh) * (CPD * vw * nm) * (B3 * nk * nl * nr) + Kstar3 * (E * nh) * (E * nm) * (T3 * vw * nk * nl * nr) + (Ld3f * (vw * eKf)) * (E * nh) * (E * nm) * (B3 * nk * nl * nr)) + (Kstar3 * (CPD * vw * nh) * (E * nl) * (B3 * nk * nm * nr) + Kstar3 * (E * nh) * (CPD * vw * nl) * (B3 * nk * nm * nr) + Kstar3 * (E * nh) * (E * nl) * (T3 * vw * nk * nm * nr) + (Ld3f * (vw * eKf)) * (E * nh) * (E * nl) * (B3 * nk * nm * nr)) + (Kstar3 * (CPD * vw * nh) * (E * nk) * (B3 * nl * nm * nr) + Kstar3 * (E * nh) * (CPD * vw * nk) * (B3 * nl * nm * nr) + Kstar3 * (E * nh) * (E * nk) * (T3 * vw * nl * nm * nr) + (Ld3f * (vw * eKf)) * (E * nh) * (E * nk) * (B3 * nl * nm * nr)) := by
  have hD32 := expJet5TelePeel3 d3v d3w pk pl qhmrv pk' pl' qhmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_k hpn'_k hpn_l hpn'_l hval_hmr hval'_hmr hpd_k hpd_l htp_hmr
  have hD33 := expJet5TelePeel3 d3v d3w ph pr qklmv ph' pr' qklmw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hpn_r hpn'_r hval_klm hval'_klm hpd_h hpd_r htp_klm
  have hD34 := expJet5TelePeel3 d3v d3w ph pm qklrv ph' pm' qklrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hpn_m hpn'_m hval_klr hval'_klr hpd_h hpd_m htp_klr
  have hD35 := expJet5TelePeel3 d3v d3w ph pl qkmrv ph' pl' qkmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hpn_l hpn'_l hval_kmr hval'_kmr hpd_h hpd_l htp_kmr
  have hD36 := expJet5TelePeel3 d3v d3w ph pk qlmrv ph' pk' qlmrw
    hKstar30 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd3n hd3diff hpn_h hpn'_h hpn_k hpn'_k hval_lmr hval'_lmr hpd_h hpd_k htp_lmr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD36)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD35)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD34)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD33)
  exact (norm_add_le _ _).trans (add_le_add hX hD32)

end QIQTH.ExpMap
