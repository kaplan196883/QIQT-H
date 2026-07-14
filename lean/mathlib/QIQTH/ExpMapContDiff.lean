/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpMap

/-!
# `ContDiff¹ exp_p` — the geodesic exponential map is continuously differentiable near `0`

`ContDiff¹ exp_p` (the exp map is continuously differentiable on a neighbourhood of `0`), via
**continuous dependence of the operator fundamental solution `Φ_v` on the initial velocity `v`**
(the Jet₁ augmented ODE, equilibrium-Grönwall — NOT the general C¹-flow theorem Mathlib lacks).

The route (`THE_EXP_JETS_PLAN.md`, Rung 1):
* By `hasFDerivAt_expMap`, `fderiv exp_p v = π ∘ (Φ_v 1) ∘ ι` where `Φ_v` is the `[0,1]`
  operator-valued fundamental solution of the Jacobi ODE along the confined tube `Y_v`.
* The crux `expFund_two_pt_diff` is the **Lipschitz-in-`v` bound**
  `‖Φ_v 1 − Φ_w 1‖ ≤ C · ‖v − w‖`, from an operator two-point Grönwall on `t ↦ ‖Φ_v t − Φ_w t‖`:
  the field difference `‖Ψ_v(t)M − Ψ_w(t)M‖ ≤ ‖DF(Y_v t) − DF(Y_w t)‖·‖M‖`, with
  `‖DF(Y_v t) − DF(Y_w t)‖ ≤ L_{DF}·‖Y_v t − Y_w t‖ ≤ L_{DF}·e^{K_F}·‖v−w‖`
  (`geodesic_twopoint_gronwall`), `‖Φ_w t‖ ≤ e^{K*}` (single-solution Grönwall), and
  `‖DF(Y_v t)‖ ≤ K*` uniform (`expJet_fderiv_tube_bddAbove_unif`).
* Composing with the fixed norm-`≤ 1` maps `π`, `ι` gives `v ↦ fderiv exp_p v` Lipschitz, hence
  continuous, on the ball `‖v‖ < expRho` (`fderivExpMap_continuousOn`); together with pointwise
  differentiability (`hasFDerivAt_expMap`) this yields `ContDiffOn ℝ 1 exp_p (ball 0 expRho)`
  (`contDiffAt_one_iff`).

The heavy CLM-Grönwall / operator-norm steps are offloaded to the small-context abstract helpers
`gronwall_Icc01_all` and `opFieldDiff_bound`.

## Honest firewall (binding)
This is **Rung 1 of the `ContDiff³ exp_p` tower** — it strengthens the Jacobian 1-jet from pointwise
to continuous.  ⚠ It does **NOT** by itself unlock `κ = 1/6` for the pullback metric (that needs the
full `ContDiff³ exp_p`, Rungs 2–3, because of the derivative-loss in `g̃`), does **NOT** build the
heat-kernel parametrix, does **NOT** discharge general `a₁ = R/6`, is **NOT** numerical-`G`, and is
**NOT** the conjecture / QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-! ### Small-context abstract helpers (kept whnf-light, away from the capstone context) -/

/-- **Generic Grönwall on `[0,1]`, pointwise form.**  If `f : ℝ → E` has right derivative `f' t`
    within `[0,1]` at each `t ∈ [0,1]`, `‖f 0‖ ≤ δ`, and `‖f' t‖ ≤ K·‖f t‖ + ε` on `[0,1]`, then
    `‖f x‖ ≤ gronwallBound δ K ε x` on `[0,1]`.  Wraps Mathlib's
    `norm_le_gronwallBound_of_norm_deriv_right_le`, converting the `[0,1]`-derivative into an
    `Ici x`-right-derivative via `Set.OrdConnected.mem_nhdsGE`.  Abstract in `E` (tiny context). -/
theorem gronwall_Icc01_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f f' : ℝ → E) (δ K ε : ℝ)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t)
    (h0 : ‖f 0‖ ≤ δ)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ gronwallBound δ K ε x := by
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hderiv t ht).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := f) (f' := f') (δ := δ) (K := K) (ε := ε) (a := 0) (b := 1)
    hcont
    (fun x hx => (hderiv x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Set.ordConnected_Icc.mem_nhdsGE ⟨hx.1, hx.2.le⟩ ⟨zero_le_one, le_refl 1⟩ hx.2))
    h0 (fun x hx => hbound x (Set.Ico_subset_Icc_self hx))
  intro x hx
  simpa using hmain x hx

/-- **Operator field-difference bound.**  For continuous linear operators `Av Aw Φv Φw` on a normed
    space, `‖Av∘Φv − Aw∘Φw‖ ≤ Ks·‖Φv − Φw‖ + b` given `‖Av‖ ≤ Ks` and `‖Av − Aw‖·‖Φw‖ ≤ b`.
    Splits `Av∘Φv − Aw∘Φw = Av∘(Φv−Φw) + (Av−Aw)∘Φw` and bounds each summand by operator-norm
    submultiplicativity.  Abstract (tiny context) — the CLM whnf/instance search runs bare here. -/
theorem opFieldDiff_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Av Aw Φv Φw : G →L[ℝ] G) {Ks b : ℝ}
    (hAv : ‖Av‖ ≤ Ks) (hAw : ‖Av - Aw‖ * ‖Φw‖ ≤ b) :
    ‖Av.comp Φv - Aw.comp Φw‖ ≤ Ks * ‖Φv - Φw‖ + b := by
  have hrw : Av.comp Φv - Aw.comp Φw = Av.comp (Φv - Φw) + (Av - Aw).comp Φw := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
  rw [hrw]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hAv (norm_nonneg _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans hAw

/-- **Projected difference identity.**  `π∘(X∘ι) − π∘(Y∘ι) = π∘((X−Y)∘ι)` for the fixed
    inclusion/projection `ι = expJetIota`, `π = expJetPi`. -/
theorem expJet_pi_comp_iota_sub (X Y : (Point n × Point n) →L[ℝ] (Point n × Point n)) :
    (expJetPi (n := n)).comp (X.comp (expJetIota (n := n)))
        - (expJetPi (n := n)).comp (Y.comp (expJetIota (n := n)))
      = (expJetPi (n := n)).comp ((X - Y).comp (expJetIota (n := n))) := by
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]

/-! ### The crux — parameter-continuity of the operator fundamental solution -/

set_option maxHeartbeats 2000000 in
/-- **CRUX (Rung 1) — Lipschitz dependence of `Φ_v(1)` on the initial velocity `v`.**
    For two fundamental solutions `Φ_v`, `Φ_w` of the Jacobi operator ODE along the confined tubes
    `Y_v`, `Y_w` (each `Φ 0 = 1`, `Φ' = Ψ(Φ)`), with the uniform constants:
    `Kf` = a Lipschitz constant of `geodesicField` on the tube ball `S`, `Ldf` = a Lipschitz constant
    of `DF = fderiv geodesicField` on `S`, and `Kstar` = the uniform bound `‖DF(Y_· t)‖ ≤ Kstar`, one
    has `‖Φ_v 1 − Φ_w 1‖ ≤ (Ldf·e^{Kf}·e^{Kstar}·e^{Kstar})·‖v − w‖`.

    Proof: the single-solution Grönwall gives `‖Φ_w t‖ ≤ e^{Kstar}`; the two-point tube Grönwall gives
    `‖Y_v t − Y_w t‖ ≤ ‖v−w‖·e^{Kf}`, hence `‖DF(Y_v t) − DF(Y_w t)‖ ≤ Ldf·‖v−w‖·e^{Kf}`; and the
    difference operator ODE `E' = Ψ_v(Φ_v) − Ψ_w(Φ_w)`, `E 0 = 0` obeys
    `‖E' t‖ ≤ Kstar·‖E t‖ + b` with `b = Ldf·‖v−w‖·e^{Kf}·e^{Kstar}` (`opFieldDiff_bound`), so the
    inhomogeneous Grönwall (`gronwall_Icc01_all`) gives `‖E 1‖ ≤ gronwallBound 0 Kstar b 1 ≤ b·e^{Kstar}`.

    HONEST: the equilibrium-Grönwall continuous dependence of the Jet₁ fundamental solution — Rung 1
    of the `ContDiff³` tower.  NOT `κ=1/6`, NOT a heat kernel, NOT numerical-`G`. -/
theorem expFund_two_pt_diff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n) (Kf Ldf : NNReal) (Kstar : ℝ) (hKstar0 : 0 ≤ Kstar)
    (hLipF : LipschitzOnWith Kf (geodesicField g gi)
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hLipDF : LipschitzOnWith Ldf (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)))
    (hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖ ≤ Kstar)
    (hv : ‖v‖ ≤ expRho g gi hC p) (hw : ‖w‖ ≤ expRho g gi hC p)
    (Φv Φw : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hΦv0 : Φv 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦw0 : Φw 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φv (expJetPsi g gi hC p v t (Φv t)) (Set.Icc (0 : ℝ) 1) t)
    (hΦwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φw (expJetPsi g gi hC p w t (Φw t)) (Set.Icc (0 : ℝ) 1) t) :
    ‖Φv 1 - Φw 1‖
      ≤ ((Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar) * ‖v - w‖ := by
  have hC₀ := expConst_nonneg g gi hC p
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  set S : Set (Point n × Point n) := Metric.closedBall ((p, 0) : Point n × Point n) Rb with hSdef
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p w hw
  have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- both tubes lie in the ball `S` on `[0,1]`.
  have hSv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p v t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖v‖ := hconfv t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hv hC₀
  have hSw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p w t ∈ S := by
    intro t ht; rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖expTube g gi hC p w t - ((p, 0) : Point n × Point n)‖
        ≤ expConst g gi hC p * ‖w‖ := hconfw t ht
      _ ≤ Rb := by rw [hRbdef]; exact mul_le_mul_of_nonneg_left hw hC₀
  -- single-solution norm bound `‖Φw t‖ ≤ e^{Kstar}`.
  have hΦwbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φw t‖ ≤ Real.exp Kstar := by
    have hall := gronwall_Icc01_all Φw (fun t => expJetPsi g gi hC p w t (Φw t)) 1 Kstar 0
      hΦwd (by rw [hΦw0]; exact ContinuousLinearMap.norm_id_le)
      (fun t ht => by
        rw [add_zero]
        exact (expJetPsi_norm_le g gi hC p w t (Φw t)).trans
          (mul_le_mul_of_nonneg_right (hKstarw t ht) (norm_nonneg _)))
    intro t ht
    have h := hall t ht
    rw [gronwallBound_ε0, one_mul] at h
    refine h.trans (Real.exp_le_exp.mpr ?_)
    calc Kstar * t ≤ Kstar * 1 := mul_le_mul_of_nonneg_left ht.2 hKstar0
      _ = Kstar := mul_one _
  -- two-point tube separation `‖Y_v t − Y_w t‖ ≤ ‖v−w‖·e^{Kf}`.
  have hdist0 : dist (expTube g gi hC p v 0) (expTube g gi hC p w 0) = ‖v - w‖ := by
    rw [hY0v, hY0w, dist_eq_norm, Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _)]
  have htwopoint := geodesic_twopoint_gronwall g gi (S := S) (K := Kf) hLipF
    (fun t ht => hYdv t (hIcc_Ioo t ht)) (fun t ht => hYdw t (hIcc_Ioo t ht)) hSv hSw
  have hYvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p v t - expTube g gi hC p w t‖ ≤ ‖v - w‖ * Real.exp (Kf : ℝ) := by
    intro t ht
    have h := htwopoint t ht
    rw [hdist0, dist_eq_norm] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  -- Lipschitz of `DF` in the space variable ⟹ two-point `DF`-difference bound.
  have hDFvw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)‖
        ≤ (Ldf : ℝ) * (‖v - w‖ * Real.exp (Kf : ℝ)) := by
    intro t ht
    have hd := hLipDF.dist_le_mul (expTube g gi hC p v t) (hSv t ht)
      (expTube g gi hC p w t) (hSw t ht)
    rw [dist_eq_norm, dist_eq_norm] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (hYvw t ht) (by positivity))
  -- the inhomogeneous constant `b` and the difference Grönwall.
  set b : ℝ := (Ldf : ℝ) * ‖v - w‖ * Real.exp (Kf : ℝ) * Real.exp Kstar with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hEall := gronwall_Icc01_all (fun t => Φv t - Φw t)
    (fun t => expJetPsi g gi hC p v t (Φv t) - expJetPsi g gi hC p w t (Φw t))
    0 Kstar b
    (fun t ht => (hΦvd t ht).sub (hΦwd t ht))
    (by simp [hΦv0, hΦw0])
    (fun t ht => by
      show ‖expJetPsi g gi hC p v t (Φv t) - expJetPsi g gi hC p w t (Φw t)‖
          ≤ Kstar * ‖Φv t - Φw t‖ + b
      rw [expJetPsi_apply, expJetPsi_apply]
      refine opFieldDiff_bound (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))
        (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) _ _ (hKstarv t ht) ?_
      rw [hbdef]
      refine (mul_le_mul (hDFvw t ht) (hΦwbound t ht) (norm_nonneg _) (by positivity)).trans ?_
      exact le_of_eq (by ring))
  have h1 : ‖Φv 1 - Φw 1‖ ≤ gronwallBound 0 Kstar b 1 :=
    hEall 1 (by norm_num [Set.mem_Icc])
  refine (h1.trans (gronwallBound_zero_le_exp Kstar b 1 hKstar0 hb0 (by norm_num) le_rfl)).trans ?_
  rw [hbdef]; exact le_of_eq (by ring)

/-! ### `fderiv exp_p` is continuous on the ball, and `ContDiff¹` -/

set_option maxHeartbeats 1600000 in
/-- **`v ↦ fderiv exp_p v` is continuous on `ball 0 expRho`.**  It is in fact Lipschitz there: the
    fixed norm-`≤ 1` maps `π`, `ι` and the crux `expFund_two_pt_diff` give
    `‖fderiv exp_p v − fderiv exp_p w‖ ≤ ‖Φ_v 1 − Φ_w 1‖ ≤ C·‖v − w‖`. -/
theorem fderivExpMap_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContinuousOn (fun v => fderiv ℝ (expMap g gi hC p) v)
      (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  set Rb : ℝ := expConst g gi hC p * expRho g gi hC p with hRbdef
  obtain ⟨Kf, hLipF⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn
        (s := Metric.closedBall ((p, 0) : Point n × Point n) Rb)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hDFcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    (contDiff_geodesicField g gi hC).fderiv_right le_top
  obtain ⟨Ldf, hLipDF⟩ :=
    (hDFcd.contDiffOn
        (s := Metric.closedBall ((p, 0) : Point n × Point n) Rb)).exists_lipschitzOnWith
      (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  set Cfinal : ℝ := (Ldf : ℝ) * Real.exp (Kf : ℝ) * Real.exp Kstar * Real.exp Kstar with hCfdef
  have hCf0 : 0 ≤ Cfinal := by rw [hCfdef]; positivity
  -- the uniform Lipschitz bound on the derivative field.
  have hkey : ∀ v ∈ Metric.ball (0 : Point n) (expRho g gi hC p),
      ∀ w ∈ Metric.ball (0 : Point n) (expRho g gi hC p),
        ‖fderiv ℝ (expMap g gi hC p) v - fderiv ℝ (expMap g gi hC p) w‖ ≤ Cfinal * ‖v - w‖ := by
    intro v hv w hw
    rw [Metric.mem_ball, dist_zero_right] at hv hw
    obtain ⟨Φv, hΦv0, hΦvd, hFDv⟩ := hasFDerivAt_expMap g gi hC p v hv
    obtain ⟨Φw, hΦw0, hΦwd, hFDw⟩ := hasFDerivAt_expMap g gi hC p w hw
    rw [hFDv.fderiv, hFDw.fderiv, expJet_pi_comp_iota_sub]
    refine (expJet_pi_comp_iota_norm_le _).trans ?_
    rw [hCfdef]
    exact expFund_two_pt_diff g gi hC p v w Kf Ldf Kstar hKstar0 hLipF hLipDF
      (fun t ht => hKstar v hv.le t ht) (fun t ht => hKstar w hw.le t ht) hv.le hw.le
      Φv Φw hΦv0 hΦw0 hΦvd hΦwd
  -- Lipschitz ⟹ continuous on the ball.
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε / (Cfinal + 1), by positivity, ?_⟩
  intro a ha hab
  calc dist (fderiv ℝ (expMap g gi hC p) a) (fderiv ℝ (expMap g gi hC p) b)
      = ‖fderiv ℝ (expMap g gi hC p) a - fderiv ℝ (expMap g gi hC p) b‖ := dist_eq_norm _ _
    _ ≤ Cfinal * ‖a - b‖ := hkey a ha b hb
    _ = Cfinal * dist a b := by rw [dist_eq_norm]
    _ < ε := by
        have h1 : Cfinal * dist a b ≤ Cfinal * (ε / (Cfinal + 1)) :=
          mul_le_mul_of_nonneg_left hab.le hCf0
        have h2 : Cfinal * (ε / (Cfinal + 1)) < ε := by
          rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith [hε, hCf0]
        exact lt_of_le_of_lt h1 h2

/-- **`ContDiff¹ exp_p` on the ball `‖v‖ < expRho`.**  `exp_p` is differentiable there
    (`hasFDerivAt_expMap`) with continuous derivative (`fderivExpMap_continuousOn`); by
    `contDiffAt_one_iff` this is `ContDiffAt ℝ 1 exp_p v` at each such `v`, hence
    `ContDiffOn ℝ 1 exp_p (ball 0 expRho)`.

    HONEST: Rung 1 of the `ContDiff³ exp_p` tower — the 1-jet made continuous.  NOT `κ=1/6`, NOT a
    heat kernel, NOT numerical-`G`, NOT the conjecture / QG. -/
theorem expMap_contDiffOn_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) (p : Point n) :
    ContDiffOn ℝ 1 (expMap g gi hC p) (Metric.ball (0 : Point n) (expRho g gi hC p)) := by
  intro v hv
  refine (?_ : ContDiffAt ℝ 1 (expMap g gi hC p) v).contDiffWithinAt
  rw [contDiffAt_one_iff]
  refine ⟨fun w => fderiv ℝ (expMap g gi hC p) w, Metric.ball (0 : Point n) (expRho g gi hC p),
    Metric.isOpen_ball.mem_nhds hv, fderivExpMap_continuousOn g gi hC p, ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_zero_right] at hw
  obtain ⟨Φ, _, _, hFD⟩ := hasFDerivAt_expMap g gi hC p w hw
  exact hFD.differentiableAt.hasFDerivAt

end QIQTH.ExpMap
