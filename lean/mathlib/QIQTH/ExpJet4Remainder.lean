/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Prereq
import QIQTH.ExpJet4Residual
import QIQTH.ExpJet4Val
import QIQTH.ExpJet4DFull

/-!
# Jet₄ quadratic remainder bound — rung J4-5b

FAITHFUL one-Fréchet-order-up mirror of `expJet3_remainder_quadratic_bound`
(`ExpMapContDiff3.lean:1605`).  It derives the `O(‖m‖²)` bound on the exact remainder `ρ(t)` fed to
`expJet4_residual_bound`'s `hr` obligation, discharging the Fréchet little-o for the fourth variation.

The `[0,1]`-uniform obligation `‖ρ(t)‖ ≤ C·‖m‖²` is the CONCLUSION; it is DERIVED by the
cancellation argument (a five-block telescope + `abel` + per-term `O(‖m‖²)` estimates).  Only the
same kind of INPUTS the order-3 original carries are carried as explicit numbered hypotheses:
first→second and second→third variation residuals (`hFP*`/`hFQ*`), lower-order solution Lipschitz
bounds (`hQlip*`), value bounds on the abstract second-variation curves, and definitional curve
identities.  The conclusion is never carried.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 6

variable {n : ℕ}

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

/-- **Generic bilinear CLM-application norm bound.** -/
private theorem clmApply2_norm_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) {KB Ka Kb : ℝ}
    (hKB : 0 ≤ KB) (hKa : 0 ≤ Ka)
    (hB : ‖B‖ ≤ KB) (ha : ‖a‖ ≤ Ka) (hb : ‖b‖ ≤ Kb) : ‖B a b‖ ≤ KB * Ka * Kb :=
  (B.le_opNorm₂ a b).trans
    (mul_le_mul (mul_le_mul hB ha (norm_nonneg _) hKB) hb (norm_nonneg _) (mul_nonneg hKB hKa))

/-- **CLM-application norm bound with an explicit factored constant.** -/
private theorem clmApply_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : E →L[ℝ] F) (a : E) {KC Ka : ℝ} (hKC : 0 ≤ KC)
    (hC : ‖C‖ ≤ KC) (ha : ‖a‖ ≤ Ka) : ‖C a‖ ≤ KC * Ka :=
  (C.le_opNorm a).trans (mul_le_mul hC ha (norm_nonneg _) hKC)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **Jet₄ quadratic remainder bound** (mirror of `expJet3_remainder_quadratic_bound`, one Fréchet
    order up).  DERIVES the `O(‖m‖²)` bound on the exact `ρ(t)` fed to `expJet4_residual_bound`.
    Carried INPUTS (all strictly-lower-order than the conclusion, never the conclusion itself):
    definitional curve identities (`hQvkl`/`hQvhl`/`hQvhk`/`hQhklv`), first→second variation residuals
    (`hFPh`/`hFPk`/`hFPl`), second→third variation residuals (`hFQkl`/`hFQhl`/`hFQhk`), the top and
    lower-order solution Lipschitz bounds (`hQlip`/`hQlip{kl,hl,hk}`), and value bounds on the abstract
    second-variation curves (`hV*`).  The `Θ₃`/`Θ₄` ODE data (`hΦ*`,`hQwd`) supply the derived
    `Φ`-norm/two-point and third-variation value bounds. -/
theorem expJet4_remainder_quadratic_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w m : Point n) (hwm : w = v + m)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw : ℝ → (Point n × Point n))
    (Qvkl Qvhl Qvhk Qwkl Qwhl Qwhk : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm : ℝ → (Point n × Point n)) (h k l : Point n)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ' (expJetPsi g gi hC p w t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
    (hQw0 : Qw 0 = 0)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    -- definitional curve identities
    (hQvkl : Qvkl = Qkl) (hQvhl : Qvhl = Qhl) (hQvhk : Qvhk = Qhk) (hQhklv : Qhkl = Qv)
    (Cd Ce Cq2 : ℝ) (hCd0 : 0 ≤ Cd) (hCe0 : 0 ≤ Ce) (hCq20 : 0 ≤ Cq2)
    -- first→second variation residuals (direction m)
    (hFPh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhm t‖ ≤ Cd * ‖m‖ ^ 2)
    (hFPk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkm t‖ ≤ Cd * ‖m‖ ^ 2)
    (hFPl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota l) - Φ t (expJetIota l) - Qlm t‖ ≤ Cd * ‖m‖ ^ 2)
    -- second→third variation residuals
    (hFQkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t - Qvkl t - Qklm t‖ ≤ Cd * ‖m‖ ^ 2)
    (hFQhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t - Qvhl t - Qhlm t‖ ≤ Cd * ‖m‖ ^ 2)
    (hFQhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t - Qvhk t - Qhkm t‖ ≤ Cd * ‖m‖ ^ 2)
    -- solution Lipschitz bounds
    (hQlip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qw t - Qv t‖ ≤ Ce * ‖m‖)
    (hQlipkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t - Qvkl t‖ ≤ Ce * ‖m‖)
    (hQliphl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t - Qvhl t‖ ≤ Ce * ‖m‖)
    (hQliphk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t - Qvhk t‖ ≤ Ce * ‖m‖)
    -- value bounds on the abstract second-variation curves
    (hVkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq2)
    (hVhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq2)
    (hVhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq2)
    (hVwkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t‖ ≤ Cq2)
    (hVwhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t‖ ≤ Cq2)
    (hVwhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t‖ ≤ Cq2)
    -- (all four higher blocks are now DERIVED below; nothing carried)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
         + (expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t
            - expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t
            - expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)‖
        ≤ C * ‖m‖ ^ 2 := by
  subst hwm
  subst Qvkl; subst Qvhl; subst Qvhk; subst Qv
  have hC₀ := expConst_nonneg g gi hC p
  -- ── Lipschitz constants on the confined tube ball ──
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Ld4f, hLipD4⟩ := expJet_fderiv4_lipschitzOnWith g gi hC p
  -- ── tube bounds ──
  obtain ⟨Kvb, hKvb0, hKvbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  obtain ⟨Kwb, _hKwb0, hKwbd⟩ := expJet_fderiv_tube_bddAbove g gi hC p (v + m) hw
  obtain ⟨Kstar2, hKstar20, hD2bd⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hD3bd⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hD4bd⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  -- ── real constants ──
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set Kstar : ℝ := max Kvb Kwb with hKstardef
  have hKstar0 : 0 ≤ Kstar := le_max_of_le_left hKvb0
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
  -- Lipschitz constants in `.toNNReal` shape.
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
  -- ── uniform `[0,1]` DF/D²F/D³F/D⁴F bounds ──
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar :=
    fun t ht => (hKvbd t ht).trans (le_max_left Kvb Kwb)
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + m) t)‖ ≤ Kstar :=
    fun t ht => (hKwbd t ht).trans (le_max_right Kvb Kwb)
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd v hv t ht
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd v hv t ht
  have hK3w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + m) t)‖ ≤ Kstar3 :=
    fun t ht => hD3bd (v + m) hw t ht
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + m) t)‖ ≤ Kstar2 :=
    fun t ht => hD2bd (v + m) hw t ht
  have hK4v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4 := fun t ht => hD4bd v hv t ht
  -- ── `Φ`, `Φ'` op-norm bounds on `[0,1]` ──
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + m) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  -- ── tube-ball memberships and separation ──
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + m) hw
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hC₀)
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + m) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hw hC₀)
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
  -- ── Taylor / accuracy / value / two-point ingredients ──
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
    fun t ht => expTube_second_order_accuracy g gi hC p v m hw hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have hqwval : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qw t‖ ≤ (Kstar3 * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖)
        + Kstar2 * (eKs * ‖h‖) * Cq2 + Kstar2 * (eKs * ‖k‖) * Cq2
        + Kstar2 * (eKs * ‖l‖) * Cq2) * Real.exp Kstar :=
    expJet3Fund_value_bound_Icc g gi hC p (v + m) Φ' Qwkl Qwhl Qwhk h k l
      Kstar Kstar3 Kstar2 eKs Cq2 Cq2 Cq2 hKstar0 hKstar30 hKstar20 heKs0
      hKstarw hK3w hK2w hΦ'norm hVwkl hVwhl hVwhk Qw hQw0 hQwd
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * ‖m‖ := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + m) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hw Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + m) = -m by abel, norm_neg] at hb
    exact hb
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
  -- ── set the Block-0 constant and finish ──
  set M3 : ℝ := (Kstar3 * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖)
      + Kstar2 * (eKs * ‖h‖) * Cq2 + Kstar2 * (eKs * ‖k‖) * Cq2
      + Kstar2 * (eKs * ‖l‖) * Cq2) * Real.exp Kstar with hM3def
  have hM30 : 0 ≤ M3 := by
    rw [hM3def]; positivity
  set CB0 : ℝ := L2 * eKf ^ 2 * M3 + Kstar2 * C2 * M3 + Kstar2 * eKs * Ce with hCB0def
  have hCB00 : 0 ≤ CB0 := by rw [hCB0def]; positivity
  set CB2 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 * ‖h‖ + Kstar3 * C2 * eKs * Cq2 * ‖h‖
      + Kstar3 * eKs * C3 * Cq2 * ‖h‖ + Kstar3 * eKs ^ 2 * Ce * ‖h‖ + Kstar2 * C3 * Ce * ‖h‖
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖h‖ with hCB2def
  have hCB20 : 0 ≤ CB2 := by rw [hCB2def]; positivity
  set CB3 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 * ‖k‖ + Kstar3 * C2 * eKs * Cq2 * ‖k‖
      + Kstar3 * eKs * C3 * Cq2 * ‖k‖ + Kstar3 * eKs ^ 2 * Ce * ‖k‖ + Kstar2 * C3 * Ce * ‖k‖
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖k‖ with hCB3def
  have hCB30 : 0 ≤ CB3 := by rw [hCB3def]; positivity
  set CB4 : ℝ := L3 * eKf ^ 2 * eKs * Cq2 * ‖l‖ + Kstar3 * C2 * eKs * Cq2 * ‖l‖
      + Kstar3 * eKs * C3 * Cq2 * ‖l‖ + Kstar3 * eKs ^ 2 * Ce * ‖l‖ + Kstar2 * C3 * Ce * ‖l‖
      + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖l‖ with hCB4def
  have hCB40 : 0 ≤ CB4 := by rw [hCB4def]; positivity
  set CB1 : ℝ := L4 * eKf ^ 2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar4 * C2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖ + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar3 * Cd * eKs ^ 2 * ‖k‖ * ‖l‖
      + Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)
      + Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)
      + Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖l‖
      + Kstar3 * eKs * C3 ^ 2 * ‖h‖ * ‖k‖ * ‖l‖
      + Kstar3 * (eKs * ‖h‖) * Cd * (eKs * ‖l‖ + eKs * ‖l‖)
      + Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖k‖ with hCB1def
  have hCB10 : 0 ≤ CB1 := by rw [hCB1def]; positivity
  refine ⟨CB0 + CB1 + CB2 + CB3 + CB4, by positivity, ?_⟩
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
  -- (after the substs, `Qhkl` is the surviving name of the third-variation solution `Qv`)
  -- master assembly: LHS = Block0 + Block1 + Block2 + Block3 + Block4.
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
  -- Block 0 bound.
  have hbB0 : ‖(dw - dv) qw - d2v Pm qv‖ ≤ CB0 * ‖m‖ ^ 2 := by
    have heq0 : (dw - dv) qw - d2v Pm qv
        = (dw - dv - d2v (yw - yv)) qw + d2v (yw - yv - Pm) qw + d2v Pm (qw - qv) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    rw [heq0]
    have hqwn : ‖qw‖ ≤ M3 := hqwval t ht
    have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
    have hPmn : ‖Pm‖ ≤ eKs * ‖m‖ := by
      rw [hPmE]; exact clmApply_norm_le (Φ t) (expJetIota m) heKs0 (hΦnorm t ht) hιm
    have hA0 : ‖(dw - dv - d2v (yw - yv)) qw‖ ≤ (L2 * eKf ^ 2 * M3) * ‖m‖ ^ 2 := by
      calc ‖(dw - dv - d2v (yw - yv)) qw‖
          ≤ ‖dw - dv - d2v (yw - yv)‖ * ‖qw‖ := (dw - dv - d2v (yw - yv)).le_opNorm _
        _ ≤ (L2 * ‖yw - yv‖ ^ 2) * M3 :=
            mul_le_mul (htay t ht) hqwn (norm_nonneg _) (by positivity)
        _ ≤ (L2 * (‖m‖ * eKf) ^ 2) * M3 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hsep t ht) 2) hL2_0)
              hM30
        _ = (L2 * eKf ^ 2 * M3) * ‖m‖ ^ 2 := by ring
    have hB0 : ‖d2v (yw - yv - Pm) qw‖ ≤ (Kstar2 * C2 * M3) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (yw - yv - Pm) qw hKstar20 (by positivity) hd2n
        (hacc t ht) hqwn).trans (le_of_eq (by ring))
    have hC0 : ‖d2v Pm (qw - qv)‖ ≤ (Kstar2 * eKs * Ce) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pm (qw - qv) hKstar20 (by positivity) hd2n hPmn
        (hQlip t ht)).trans (le_of_eq (by ring))
    rw [hCB0def, show (L2 * eKf ^ 2 * M3 + Kstar2 * C2 * M3 + Kstar2 * eKs * Ce) * ‖m‖ ^ 2
      = (L2 * eKf ^ 2 * M3) * ‖m‖ ^ 2 + (Kstar2 * C2 * M3) * ‖m‖ ^ 2
        + (Kstar2 * eKs * Ce) * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hA0 hB0)) hC0)
  -- ── shared per-`t` vector bounds (Block 2) ──
  have hd2n : ‖d2v‖ ≤ Kstar2 := hK2v t ht
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
  have hQwklV : ‖Qwkl t - Qkl t‖ ≤ Cq2 + Cq2 :=
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
  have hQwhlV : ‖Qwhl t - Qhl t‖ ≤ Cq2 + Cq2 :=
    (norm_sub_le _ _).trans (add_le_add (hVwhl t ht) (hVhl t ht))
  have hQwhkV : ‖Qwhk t - Qhk t‖ ≤ Cq2 + Cq2 :=
    (norm_sub_le _ _).trans (add_le_add (hVwhk t ht) (hVhk t ht))
  -- ── Block 2 (kl-cross): abstract-variation cancellation matching T5, T10, T11 ──
  have hbB2 : ‖d2w Ph' (Qwkl t) - d2v Ph (Qkl t) - d3v Ph Pm (Qkl t)
      - d2v (Qhm t) (Qkl t) - d2v Ph (Qklm t)‖ ≤ CB2 * ‖m‖ ^ 2 := by
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
        ≤ (L3 * eKf ^ 2 * eKs * Cq2 * ‖h‖) * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Ph' (Qwkl t) (by positivity)
        (by positivity) (hD2tay t ht) hPh'n (hVwkl t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * Cq2
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖h‖) * Cq2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2 * ‖h‖) * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Ph' (Qwkl t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2 * ‖h‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Ph' (Qwkl t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPh'n (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Ph' - Ph) (Qwkl t)‖ ≤ (Kstar3 * eKs * C3 * Cq2 * ‖h‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Ph' - Ph) (Qwkl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδh (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Ph (Qwkl t - Qkl t)‖ ≤ (Kstar3 * eKs ^ 2 * Ce * ‖h‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Ph (Qwkl t - Qkl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPhn (hQlipkl t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Ph' - Ph) (Qwkl t - Qkl t)‖ ≤ (Kstar2 * C3 * Ce * ‖h‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Ph' - Ph) (Qwkl t - Qkl t) hKstar20 (by positivity)
        hd2n hδh (hQlipkl t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Ph' - Ph - Qhm t) (Qkl t - Qwkl t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2 := by
      have hb : ‖Qkl t - Qwkl t‖ ≤ Cq2 + Cq2 := by rw [norm_sub_rev]; exact hQwklV
      exact (clmApply2_norm_le d2v (Ph' - Ph - Qhm t) (Qkl t - Qwkl t) hKstar20 (by positivity)
        hd2n (hFPh t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Ph' - Ph - Qhm t) (Qwkl t)‖ ≤ (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Ph' - Ph - Qhm t) (Qwkl t) hKstar20 (by positivity)
        hd2n (hFPh t ht) (hVwkl t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Ph (Qwkl t - Qkl t - Qklm t)‖ ≤ (Kstar2 * eKs * Cd * ‖h‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Ph (Qwkl t - Qkl t - Qklm t) hKstar20 (by positivity)
        hd2n hPhn (hFQkl t ht)).trans (le_of_eq (by ring))
    rw [hCB2def, show (L3 * eKf ^ 2 * eKs * Cq2 * ‖h‖ + Kstar3 * C2 * eKs * Cq2 * ‖h‖
          + Kstar3 * eKs * C3 * Cq2 * ‖h‖ + Kstar3 * eKs ^ 2 * Ce * ‖h‖ + Kstar2 * C3 * Ce * ‖h‖
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖h‖) * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2 * ‖h‖) * ‖m‖ ^ 2 + (Kstar3 * C2 * eKs * Cq2 * ‖h‖) * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2 * ‖h‖) * ‖m‖ ^ 2 + (Kstar3 * eKs ^ 2 * Ce * ‖h‖) * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce * ‖h‖) * ‖m‖ ^ 2 + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 + (Kstar2 * eKs * Cd * ‖h‖) * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 3 (hl-cross): abstract-variation cancellation matching T3, T9, T12 ──
  have hbB3 : ‖d2w Pk' (Qwhl t) - d2v Pk (Qhl t) - d3v Pk Pm (Qhl t)
      - d2v (Qhl t) (Qkm t) - d2v Pk (Qhlm t)‖ ≤ CB3 * ‖m‖ ^ 2 := by
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
        ≤ (L3 * eKf ^ 2 * eKs * Cq2 * ‖k‖) * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Pk' (Qwhl t) (by positivity)
        (by positivity) (hD2tay t ht) hPk'n (hVwhl t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖k‖) * Cq2
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖k‖) * Cq2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2 * ‖k‖) * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Pk' (Qwhl t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2 * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Pk' (Qwhl t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPk'n (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Pk' - Pk) (Qwhl t)‖ ≤ (Kstar3 * eKs * C3 * Cq2 * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Pk' - Pk) (Qwhl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδk (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Pk (Qwhl t - Qhl t)‖ ≤ (Kstar3 * eKs ^ 2 * Ce * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Pk (Qwhl t - Qhl t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPkn (hQliphl t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Pk' - Pk) (Qwhl t - Qhl t)‖ ≤ (Kstar2 * C3 * Ce * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pk' - Pk) (Qwhl t - Qhl t) hKstar20 (by positivity)
        hd2n hδk (hQliphl t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Pk' - Pk - Qkm t) (Qhl t - Qwhl t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2 := by
      have hb : ‖Qhl t - Qwhl t‖ ≤ Cq2 + Cq2 := by rw [norm_sub_rev]; exact hQwhlV
      exact (clmApply2_norm_le d2v (Pk' - Pk - Qkm t) (Qhl t - Qwhl t) hKstar20 (by positivity)
        hd2n (hFPk t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Pk' - Pk - Qkm t) (Qwhl t)‖ ≤ (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pk' - Pk - Qkm t) (Qwhl t) hKstar20 (by positivity)
        hd2n (hFPk t ht) (hVwhl t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Pk (Qwhl t - Qhl t - Qhlm t)‖ ≤ (Kstar2 * eKs * Cd * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pk (Qwhl t - Qhl t - Qhlm t) hKstar20 (by positivity)
        hd2n hPkn (hFQhl t ht)).trans (le_of_eq (by ring))
    rw [hCB3def, show (L3 * eKf ^ 2 * eKs * Cq2 * ‖k‖ + Kstar3 * C2 * eKs * Cq2 * ‖k‖
          + Kstar3 * eKs * C3 * Cq2 * ‖k‖ + Kstar3 * eKs ^ 2 * Ce * ‖k‖ + Kstar2 * C3 * Ce * ‖k‖
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖k‖) * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2 * ‖k‖) * ‖m‖ ^ 2 + (Kstar3 * C2 * eKs * Cq2 * ‖k‖) * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2 * ‖k‖) * ‖m‖ ^ 2 + (Kstar3 * eKs ^ 2 * Ce * ‖k‖) * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce * ‖k‖) * ‖m‖ ^ 2 + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 + (Kstar2 * eKs * Cd * ‖k‖) * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 4 (hk-cross): abstract-variation cancellation matching T2, T8, T13 ──
  have hbB4 : ‖d2w Pl' (Qwhk t) - d2v Pl (Qhk t) - d3v Pl Pm (Qhk t)
      - d2v (Qhk t) (Qlm t) - d2v Pl (Qhkm t)‖ ≤ CB4 * ‖m‖ ^ 2 := by
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
        ≤ (L3 * eKf ^ 2 * eKs * Cq2 * ‖l‖) * ‖m‖ ^ 2 := by
      refine (clmApply2_norm_le (d2w - d2v - d3v (yw - yv)) Pl' (Qwhk t) (by positivity)
        (by positivity) (hD2tay t ht) hPl'n (hVwhk t ht)).trans ?_
      calc (L3 * ‖yw - yv‖ ^ 2) * (eKs * ‖l‖) * Cq2
          ≤ (L3 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖l‖) * Cq2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL3_0) (by positivity)) (by positivity)
        _ = (L3 * eKf ^ 2 * eKs * Cq2 * ‖l‖) * ‖m‖ ^ 2 := by ring
    have hR22 : ‖d3v (yw - yv - Pm) Pl' (Qwhk t)‖
        ≤ (Kstar3 * C2 * eKs * Cq2 * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (yw - yv - Pm) Pl' (Qwhk t) hKstar30 (by positivity) (by positivity)
        hd3n (hacc t ht) hPl'n (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR23 : ‖d3v Pm (Pl' - Pl) (Qwhk t)‖ ≤ (Kstar3 * eKs * C3 * Cq2 * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm (Pl' - Pl) (Qwhk t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hδl (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR24 : ‖d3v Pm Pl (Qwhk t - Qhk t)‖ ≤ (Kstar3 * eKs ^ 2 * Ce * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Pm Pl (Qwhk t - Qhk t) hKstar30 (by positivity) (by positivity)
        hd3n hPmn hPln (hQliphk t ht)).trans (le_of_eq (by ring))
    have hR25a : ‖d2v (Pl' - Pl) (Qwhk t - Qhk t)‖ ≤ (Kstar2 * C3 * Ce * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pl' - Pl) (Qwhk t - Qhk t) hKstar20 (by positivity)
        hd2n hδl (hQliphk t ht)).trans (le_of_eq (by ring))
    have hR25b : ‖d2v (Pl' - Pl - Qlm t) (Qhk t - Qwhk t)‖
        ≤ (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2 := by
      have hb : ‖Qhk t - Qwhk t‖ ≤ Cq2 + Cq2 := by rw [norm_sub_rev]; exact hQwhkV
      exact (clmApply2_norm_le d2v (Pl' - Pl - Qlm t) (Qhk t - Qwhk t) hKstar20 (by positivity)
        hd2n (hFPl t ht) hb).trans (le_of_eq (by ring))
    have hR26 : ‖d2v (Pl' - Pl - Qlm t) (Qwhk t)‖ ≤ (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v (Pl' - Pl - Qlm t) (Qwhk t) hKstar20 (by positivity)
        hd2n (hFPl t ht) (hVwhk t ht)).trans (le_of_eq (by ring))
    have hR31 : ‖d2v Pl (Qwhk t - Qhk t - Qhkm t)‖ ≤ (Kstar2 * eKs * Cd * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply2_norm_le d2v Pl (Qwhk t - Qhk t - Qhkm t) hKstar20 (by positivity)
        hd2n hPln (hFQhk t ht)).trans (le_of_eq (by ring))
    rw [hCB4def, show (L3 * eKf ^ 2 * eKs * Cq2 * ‖l‖ + Kstar3 * C2 * eKs * Cq2 * ‖l‖
          + Kstar3 * eKs * C3 * Cq2 * ‖l‖ + Kstar3 * eKs ^ 2 * Ce * ‖l‖ + Kstar2 * C3 * Ce * ‖l‖
          + Kstar2 * Cd * (Cq2 + Cq2) + Kstar2 * Cd * Cq2 + Kstar2 * eKs * Cd * ‖l‖) * ‖m‖ ^ 2
        = (L3 * eKf ^ 2 * eKs * Cq2 * ‖l‖) * ‖m‖ ^ 2 + (Kstar3 * C2 * eKs * Cq2 * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 * Cq2 * ‖l‖) * ‖m‖ ^ 2 + (Kstar3 * eKs ^ 2 * Ce * ‖l‖) * ‖m‖ ^ 2
          + (Kstar2 * C3 * Ce * ‖l‖) * ‖m‖ ^ 2 + (Kstar2 * Cd * (Cq2 + Cq2)) * ‖m‖ ^ 2
          + (Kstar2 * Cd * Cq2) * ‖m‖ ^ 2 + (Kstar2 * eKs * Cd * ‖l‖) * ‖m‖ ^ 2 from by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ hR31)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR26)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25b)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR25a)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR24)
    refine (norm_add_le _ _).trans (add_le_add ?_ hR23)
    exact (norm_add_le _ _).trans (add_le_add hR21 hR22)
  -- ── Block 1 (pure D³F/D⁴F): Taylor/Faà cancellation matching T1, T4, T6, T7 ──
  have hd4n : ‖d4v‖ ≤ Kstar4 := hK4v t ht
  have hPkPk'V : ‖Pk - Pk'‖ ≤ eKs * ‖k‖ + eKs * ‖k‖ :=
    (norm_sub_le _ _).trans (add_le_add hPkn hPk'n)
  have hPlPl'V : ‖Pl - Pl'‖ ≤ eKs * ‖l‖ + eKs * ‖l‖ :=
    (norm_sub_le _ _).trans (add_le_add hPln hPl'n)
  have hbB1 : ‖d3w Ph' Pk' Pl' - d3v Ph Pk Pl - d4v Ph Pk Pl Pm
      - d3v Pk Pl (Qhm t) - d3v Ph Pl (Qkm t) - d3v Ph Pk (Qlm t)‖ ≤ CB1 * ‖m‖ ^ 2 := by
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
        ≤ (L4 * eKf ^ 2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 := by
      refine (clmApply3_norm_le (d3w - d3v - d4v (yw - yv)) Ph' Pk' Pl' (by positivity)
        (by positivity) (by positivity) (hD3tay t ht) hPh'n hPk'n hPl'n).trans ?_
      calc (L4 * ‖yw - yv‖ ^ 2) * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖)
          ≤ (L4 * (eKf ^ 2 * ‖m‖ ^ 2)) * (eKs * ‖h‖) * (eKs * ‖k‖) * (eKs * ‖l‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsep2 hL4_0) (by positivity)) (by positivity))
              (by positivity)
        _ = (L4 * eKf ^ 2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 := by ring
    have hRb : ‖d4v (yw - yv - Pm) Ph' Pk' Pl'‖
        ≤ (Kstar4 * C2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v (yw - yv - Pm) Ph' Pk' Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n (hacc t ht) hPh'n hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRc : ‖d4v Pm (Ph' - Ph) Pk' Pl'‖
        ≤ (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm (Ph' - Ph) Pk' Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hδh hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRd : ‖d4v Pm Ph (Pk' - Pk) Pl'‖
        ≤ (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm Ph (Pk' - Pk) Pl' hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hPhn hδk hPl'n).trans (le_of_eq (by ring))
    have hRe : ‖d4v Pm Ph Pk (Pl' - Pl)‖
        ≤ (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply4_norm_le d4v Pm Ph Pk (Pl' - Pl) hKstar40 (by positivity) (by positivity)
        (by positivity) hd4n hPmn hPhn hPkn hδl).trans (le_of_eq (by ring))
    have hRf : ‖d3v (Ph' - Ph - Qhm t) Pk' Pl'‖
        ≤ (Kstar3 * Cd * eKs ^ 2 * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) Pk' Pl' hKstar30 (by positivity) (by positivity)
        hd3n (hFPh t ht) hPk'n hPl'n).trans (le_of_eq (by ring))
    have hRg1 : ‖d3v (Ph' - Ph) (Pk' - Pk) Pl'‖
        ≤ (Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph) (Pk' - Pk) Pl' hKstar30 (by positivity) (by positivity)
        hd3n hδh hδk hPl'n).trans (le_of_eq (by ring))
    have hRg2 : ‖d3v (Ph' - Ph - Qhm t) (Pk - Pk') Pl'‖
        ≤ (Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) (Pk - Pk') Pl' hKstar30 (by positivity)
        (by positivity) hd3n (hFPh t ht) hPkPk'V hPl'n).trans (le_of_eq (by ring))
    have hRh1 : ‖d3v (Ph' - Ph) Pk (Pl' - Pl)‖
        ≤ (Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v (Ph' - Ph) Pk (Pl' - Pl) hKstar30 (by positivity) (by positivity)
        hd3n hδh hPkn hδl).trans (le_of_eq (by ring))
    have hRh2 : ‖d3v (Ph' - Ph - Qhm t) Pk (Pl - Pl')‖
        ≤ (Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)) * ‖m‖ ^ 2 := by
      refine (clmApply3_norm_le d3v (Ph' - Ph - Qhm t) Pk (Pl - Pl') hKstar30 (by positivity)
        (by positivity) hd3n (hFPh t ht) hPkn hPlPl'V).trans (le_of_eq ?_)
      ring
    have hRj : ‖d3v Ph (Pk' - Pk - Qkm t) Pl'‖
        ≤ (Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk - Qkm t) Pl' hKstar30 (by positivity) (by positivity)
        hd3n hPhn (hFPk t ht) hPl'n).trans (le_of_eq (by ring))
    have hRk1 : ‖d3v Ph (Pk' - Pk) (Pl' - Pl)‖
        ≤ (Kstar3 * eKs * C3 ^ 2 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk) (Pl' - Pl) hKstar30 (by positivity) (by positivity)
        hd3n hPhn hδk hδl).trans (le_of_eq (by ring))
    have hRk2 : ‖d3v Ph (Pk' - Pk - Qkm t) (Pl - Pl')‖
        ≤ (Kstar3 * (eKs * ‖h‖) * Cd * (eKs * ‖l‖ + eKs * ‖l‖)) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph (Pk' - Pk - Qkm t) (Pl - Pl') hKstar30 (by positivity)
        (by positivity) hd3n hPhn (hFPk t ht) hPlPl'V).trans (le_of_eq (by ring))
    have hRl : ‖d3v Ph Pk (Pl' - Pl - Qlm t)‖
        ≤ (Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖k‖) * ‖m‖ ^ 2 :=
      (clmApply3_norm_le d3v Ph Pk (Pl' - Pl - Qlm t) hKstar30 (by positivity) (by positivity)
        hd3n hPhn hPkn (hFPl t ht)).trans (le_of_eq (by ring))
    rw [hCB1def, show (L4 * eKf ^ 2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar4 * C2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖ + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖ + Kstar3 * Cd * eKs ^ 2 * ‖k‖ * ‖l‖
          + Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)
          + Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)
          + Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖l‖ + Kstar3 * eKs * C3 ^ 2 * ‖h‖ * ‖k‖ * ‖l‖
          + Kstar3 * (eKs * ‖h‖) * Cd * (eKs * ‖l‖ + eKs * ‖l‖)
          + Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖k‖) * ‖m‖ ^ 2
        = (L4 * eKf ^ 2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar4 * C2 * eKs ^ 3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar4 * eKs ^ 3 * C3 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * Cd * eKs ^ 2 * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)) * ‖m‖ ^ 2
          + (Kstar3 * C3 ^ 2 * eKs * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * Cd * (eKs * ‖k‖ + eKs * ‖k‖) * (eKs * ‖l‖)) * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * eKs * C3 ^ 2 * ‖h‖ * ‖k‖ * ‖l‖) * ‖m‖ ^ 2
          + (Kstar3 * (eKs * ‖h‖) * Cd * (eKs * ‖l‖ + eKs * ‖l‖)) * ‖m‖ ^ 2
          + (Kstar3 * eKs ^ 2 * Cd * ‖h‖ * ‖k‖) * ‖m‖ ^ 2 from by ring]
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
  -- ── final assembly (all five blocks derived) ──
  rw [show (CB0 + CB1 + CB2 + CB3 + CB4) * ‖m‖ ^ 2
    = CB0 * ‖m‖ ^ 2 + CB1 * ‖m‖ ^ 2 + CB2 * ‖m‖ ^ 2 + CB3 * ‖m‖ ^ 2 + CB4 * ‖m‖ ^ 2 from by ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB4)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB3)
  refine (norm_add_le _ _).trans (add_le_add ?_ hbB2)
  exact (norm_add_le _ _).trans (add_le_add hbB0 hbB1)

end QIQTH.ExpMap
