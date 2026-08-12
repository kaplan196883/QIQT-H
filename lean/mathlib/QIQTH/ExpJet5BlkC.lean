/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5TeleA
import Mathlib
/-!
# JET-5 phase-5 split, family file C (J4-650): abstract per-arity peel telescope

Brick **J4-650** of the JET-5 campaign toward the truly-unconditional `a₁ = R/6`
(`docs/qg_roadmap/HEAT_KERNEL_GAP_PLAN.md`).  Split of the timed-out monolith: this file
holds ABSTRACT D⁵+D⁴ partial telescopes of the 202-sub-term `ρ₅`-bound, over abstract
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
theorem expJet5TeleC0 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d4v d4w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (d5v d5w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhkv qhkw : V)
    (qhlv qhlw : V)
    (qhmv qhmw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd4diff : ‖d4v - d4w‖ ≤ Ld4f * (vw * eKf))
    (hd5diff : ‖d5v - d5w‖ ≤ Ld5f * (vw * eKf))
    (hd4n : ‖d4v‖ ≤ Kstar4)
    (hd5n : ‖d5v‖ ≤ Kstar5)
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
    (htp_hk : ‖qhkv - qhkw‖ ≤ T2 * vw * nh * nk)
    (htp_hl : ‖qhlv - qhlw‖ ≤ T2 * vw * nh * nl)
    (htp_hm : ‖qhmv - qhmw‖ ≤ T2 * vw * nh * nm)
    : ‖(d5v ph pk pl pm pr - d5w ph' pk' pl' pm' pr') + (d4v pl pm pr qhkv - d4w pl' pm' pr' qhkw) + (d4v pk pm pr qhlv - d4w pk' pm' pr' qhlw) + (d4v pk pl pr qhmv - d4w pk' pl' pr' qhmw)‖ ≤ (Kstar5 * (CPD * vw * nh) * (E * nk) * (E * nl) * (E * nm) * (E * nr) + Kstar5 * (E * nh) * (CPD * vw * nk) * (E * nl) * (E * nm) * (E * nr) + Kstar5 * (E * nh) * (E * nk) * (CPD * vw * nl) * (E * nm) * (E * nr) + Kstar5 * (E * nh) * (E * nk) * (E * nl) * (CPD * vw * nm) * (E * nr) + Kstar5 * (E * nh) * (E * nk) * (E * nl) * (E * nm) * (CPD * vw * nr) + (Ld5f * (vw * eKf)) * (E * nh) * (E * nk) * (E * nl) * (E * nm) * (E * nr)) + (Kstar4 * (CPD * vw * nl) * (E * nm) * (E * nr) * (B2 * nh * nk) + Kstar4 * (E * nl) * (CPD * vw * nm) * (E * nr) * (B2 * nh * nk) + Kstar4 * (E * nl) * (E * nm) * (CPD * vw * nr) * (B2 * nh * nk) + Kstar4 * (E * nl) * (E * nm) * (E * nr) * (T2 * vw * nh * nk) + (Ld4f * (vw * eKf)) * (E * nl) * (E * nm) * (E * nr) * (B2 * nh * nk)) + (Kstar4 * (CPD * vw * nk) * (E * nm) * (E * nr) * (B2 * nh * nl) + Kstar4 * (E * nk) * (CPD * vw * nm) * (E * nr) * (B2 * nh * nl) + Kstar4 * (E * nk) * (E * nm) * (CPD * vw * nr) * (B2 * nh * nl) + Kstar4 * (E * nk) * (E * nm) * (E * nr) * (T2 * vw * nh * nl) + (Ld4f * (vw * eKf)) * (E * nk) * (E * nm) * (E * nr) * (B2 * nh * nl)) + (Kstar4 * (CPD * vw * nk) * (E * nl) * (E * nr) * (B2 * nh * nm) + Kstar4 * (E * nk) * (CPD * vw * nl) * (E * nr) * (B2 * nh * nm) + Kstar4 * (E * nk) * (E * nl) * (CPD * vw * nr) * (B2 * nh * nm) + Kstar4 * (E * nk) * (E * nl) * (E * nr) * (T2 * vw * nh * nm) + (Ld4f * (vw * eKf)) * (E * nk) * (E * nl) * (E * nr) * (B2 * nh * nm)) := by
  have hD1 := expJet5TelePeel5 d5v d5w ph pk pl pm pr ph' pk' pl' pm' pr'
    hKstar50 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd5n hd5diff hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hpd_h hpd_k hpd_l hpd_m hpd_r
  have hD2 := expJet5TelePeel4 d4v d4w pl pm pr qhkv pl' pm' pr' qhkw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_l hpn'_l hpn_m hpn'_m hpn_r hpn'_r hval_hk hval'_hk hpd_l hpd_m hpd_r htp_hk
  have hD3 := expJet5TelePeel4 d4v d4w pk pm pr qhlv pk' pm' pr' qhlw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_k hpn'_k hpn_m hpn'_m hpn_r hpn'_r hval_hl hval'_hl hpd_k hpd_m hpd_r htp_hl
  have hD4 := expJet5TelePeel4 d4v d4w pk pl pr qhmv pk' pl' pr' qhmw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_k hpn'_k hpn_l hpn'_l hpn_r hpn'_r hval_hm hval'_hm hpd_k hpd_l hpd_r htp_hm
  refine (norm_add_le _ _).trans (add_le_add ?_ hD4)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD3)
  exact (norm_add_le _ _).trans (add_le_add hD1 hD2)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleC1 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d4v d4w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
    (qhrv qhrw : V)
    (qklv qklw : V)
    (qkmv qkmw : V)
    (qkrv qkrw : V)
    (E eKf CPD B2 B3 B4 B5 T2 T3 T4 : ℝ)
    (Kstar2 Kstar3 Kstar4 Kstar5 Ldf Ld2f Ld3f Ld4f Ld5f vw nh nk nl nm nr : ℝ)
    (hE0 : 0 ≤ E) (heKf0 : 0 ≤ eKf) (hCPD0 : 0 ≤ CPD)
    (hB20 : 0 ≤ B2) (hB30 : 0 ≤ B3) (hB40 : 0 ≤ B4) (hB50 : 0 ≤ B5)
    (hT20 : 0 ≤ T2) (hT30 : 0 ≤ T3) (hT40 : 0 ≤ T4)
    (hKstar20 : 0 ≤ Kstar2) (hKstar30 : 0 ≤ Kstar3) (hKstar40 : 0 ≤ Kstar4) (hKstar50 : 0 ≤ Kstar5)
    (hLdf0 : 0 ≤ Ldf) (hLd2f0 : 0 ≤ Ld2f) (hLd3f0 : 0 ≤ Ld3f) (hLd4f0 : 0 ≤ Ld4f) (hLd5f0 : 0 ≤ Ld5f)
    (hvw0 : 0 ≤ vw) (hnh0 : 0 ≤ nh) (hnk0 : 0 ≤ nk) (hnl0 : 0 ≤ nl) (hnm0 : 0 ≤ nm) (hnr0 : 0 ≤ nr)
    (hd4diff : ‖d4v - d4w‖ ≤ Ld4f * (vw * eKf))
    (hd4n : ‖d4v‖ ≤ Kstar4)
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
    (hval_hr : ‖qhrv‖ ≤ B2 * nh * nr) (hval'_hr : ‖qhrw‖ ≤ B2 * nh * nr)
    (hval_kl : ‖qklv‖ ≤ B2 * nk * nl) (hval'_kl : ‖qklw‖ ≤ B2 * nk * nl)
    (hval_km : ‖qkmv‖ ≤ B2 * nk * nm) (hval'_km : ‖qkmw‖ ≤ B2 * nk * nm)
    (hval_kr : ‖qkrv‖ ≤ B2 * nk * nr) (hval'_kr : ‖qkrw‖ ≤ B2 * nk * nr)
    (htp_hr : ‖qhrv - qhrw‖ ≤ T2 * vw * nh * nr)
    (htp_kl : ‖qklv - qklw‖ ≤ T2 * vw * nk * nl)
    (htp_km : ‖qkmv - qkmw‖ ≤ T2 * vw * nk * nm)
    (htp_kr : ‖qkrv - qkrw‖ ≤ T2 * vw * nk * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d4v pk pl pm qhrv - d4w pk' pl' pm' qhrw) + (d4v ph pm pr qklv - d4w ph' pm' pr' qklw) + (d4v ph pl pr qkmv - d4w ph' pl' pr' qkmw) + (d4v ph pl pm qkrv - d4w ph' pl' pm' qkrw)‖ ≤ c + (Kstar4 * (CPD * vw * nk) * (E * nl) * (E * nm) * (B2 * nh * nr) + Kstar4 * (E * nk) * (CPD * vw * nl) * (E * nm) * (B2 * nh * nr) + Kstar4 * (E * nk) * (E * nl) * (CPD * vw * nm) * (B2 * nh * nr) + Kstar4 * (E * nk) * (E * nl) * (E * nm) * (T2 * vw * nh * nr) + (Ld4f * (vw * eKf)) * (E * nk) * (E * nl) * (E * nm) * (B2 * nh * nr)) + (Kstar4 * (CPD * vw * nh) * (E * nm) * (E * nr) * (B2 * nk * nl) + Kstar4 * (E * nh) * (CPD * vw * nm) * (E * nr) * (B2 * nk * nl) + Kstar4 * (E * nh) * (E * nm) * (CPD * vw * nr) * (B2 * nk * nl) + Kstar4 * (E * nh) * (E * nm) * (E * nr) * (T2 * vw * nk * nl) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nm) * (E * nr) * (B2 * nk * nl)) + (Kstar4 * (CPD * vw * nh) * (E * nl) * (E * nr) * (B2 * nk * nm) + Kstar4 * (E * nh) * (CPD * vw * nl) * (E * nr) * (B2 * nk * nm) + Kstar4 * (E * nh) * (E * nl) * (CPD * vw * nr) * (B2 * nk * nm) + Kstar4 * (E * nh) * (E * nl) * (E * nr) * (T2 * vw * nk * nm) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nl) * (E * nr) * (B2 * nk * nm)) + (Kstar4 * (CPD * vw * nh) * (E * nl) * (E * nm) * (B2 * nk * nr) + Kstar4 * (E * nh) * (CPD * vw * nl) * (E * nm) * (B2 * nk * nr) + Kstar4 * (E * nh) * (E * nl) * (CPD * vw * nm) * (B2 * nk * nr) + Kstar4 * (E * nh) * (E * nl) * (E * nm) * (T2 * vw * nk * nr) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nl) * (E * nm) * (B2 * nk * nr)) := by
  have hD5 := expJet5TelePeel4 d4v d4w pk pl pm qhrv pk' pl' pm' qhrw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_k hpn'_k hpn_l hpn'_l hpn_m hpn'_m hval_hr hval'_hr hpd_k hpd_l hpd_m htp_hr
  have hD6 := expJet5TelePeel4 d4v d4w ph pm pr qklv ph' pm' pr' qklw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_m hpn'_m hpn_r hpn'_r hval_kl hval'_kl hpd_h hpd_m hpd_r htp_kl
  have hD7 := expJet5TelePeel4 d4v d4w ph pl pr qkmv ph' pl' pr' qkmw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_l hpn'_l hpn_r hpn'_r hval_km hval'_km hpd_h hpd_l hpd_r htp_km
  have hD8 := expJet5TelePeel4 d4v d4w ph pl pm qkrv ph' pl' pm' qkrw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_l hpn'_l hpn_m hpn'_m hval_kr hval'_kr hpd_h hpd_l hpd_m htp_kr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD8)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD7)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD6)
  exact (norm_add_le _ _).trans (add_le_add hX hD5)

set_option maxHeartbeats 1600000 in
theorem expJet5TeleC2 
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : V} {c : ℝ}
    (d4v d4w : V →L[ℝ] V →L[ℝ] V →L[ℝ] V →L[ℝ] V)
    (ph ph' : V)
    (pk pk' : V)
    (pl pl' : V)
    (pm pm' : V)
    (pr pr' : V)
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
    (hd4diff : ‖d4v - d4w‖ ≤ Ld4f * (vw * eKf))
    (hd4n : ‖d4v‖ ≤ Kstar4)
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
    (hval_lm : ‖qlmv‖ ≤ B2 * nl * nm) (hval'_lm : ‖qlmw‖ ≤ B2 * nl * nm)
    (hval_lr : ‖qlrv‖ ≤ B2 * nl * nr) (hval'_lr : ‖qlrw‖ ≤ B2 * nl * nr)
    (hval_mr : ‖qmrv‖ ≤ B2 * nm * nr) (hval'_mr : ‖qmrw‖ ≤ B2 * nm * nr)
    (htp_lm : ‖qlmv - qlmw‖ ≤ T2 * vw * nl * nm)
    (htp_lr : ‖qlrv - qlrw‖ ≤ T2 * vw * nl * nr)
    (htp_mr : ‖qmrv - qmrw‖ ≤ T2 * vw * nm * nr)
    (hX : ‖X‖ ≤ c)
    : ‖X + (d4v ph pk pr qlmv - d4w ph' pk' pr' qlmw) + (d4v ph pk pm qlrv - d4w ph' pk' pm' qlrw) + (d4v ph pk pl qmrv - d4w ph' pk' pl' qmrw)‖ ≤ c + (Kstar4 * (CPD * vw * nh) * (E * nk) * (E * nr) * (B2 * nl * nm) + Kstar4 * (E * nh) * (CPD * vw * nk) * (E * nr) * (B2 * nl * nm) + Kstar4 * (E * nh) * (E * nk) * (CPD * vw * nr) * (B2 * nl * nm) + Kstar4 * (E * nh) * (E * nk) * (E * nr) * (T2 * vw * nl * nm) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nk) * (E * nr) * (B2 * nl * nm)) + (Kstar4 * (CPD * vw * nh) * (E * nk) * (E * nm) * (B2 * nl * nr) + Kstar4 * (E * nh) * (CPD * vw * nk) * (E * nm) * (B2 * nl * nr) + Kstar4 * (E * nh) * (E * nk) * (CPD * vw * nm) * (B2 * nl * nr) + Kstar4 * (E * nh) * (E * nk) * (E * nm) * (T2 * vw * nl * nr) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nk) * (E * nm) * (B2 * nl * nr)) + (Kstar4 * (CPD * vw * nh) * (E * nk) * (E * nl) * (B2 * nm * nr) + Kstar4 * (E * nh) * (CPD * vw * nk) * (E * nl) * (B2 * nm * nr) + Kstar4 * (E * nh) * (E * nk) * (CPD * vw * nl) * (B2 * nm * nr) + Kstar4 * (E * nh) * (E * nk) * (E * nl) * (T2 * vw * nm * nr) + (Ld4f * (vw * eKf)) * (E * nh) * (E * nk) * (E * nl) * (B2 * nm * nr)) := by
  have hD9 := expJet5TelePeel4 d4v d4w ph pk pr qlmv ph' pk' pr' qlmw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_k hpn'_k hpn_r hpn'_r hval_lm hval'_lm hpd_h hpd_k hpd_r htp_lm
  have hD10 := expJet5TelePeel4 d4v d4w ph pk pm qlrv ph' pk' pm' qlrw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_k hpn'_k hpn_m hpn'_m hval_lr hval'_lr hpd_h hpd_k hpd_m htp_lr
  have hD11 := expJet5TelePeel4 d4v d4w ph pk pl qmrv ph' pk' pl' qmrw
    hKstar40 (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hd4n hd4diff hpn_h hpn'_h hpn_k hpn'_k hpn_l hpn'_l hval_mr hval'_mr hpd_h hpd_k hpd_l htp_mr
  refine (norm_add_le _ _).trans (add_le_add ?_ hD11)
  refine (norm_add_le _ _).trans (add_le_add ?_ hD10)
  exact (norm_add_le _ _).trans (add_le_add hX hD9)

end QIQTH.ExpMap
