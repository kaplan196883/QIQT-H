/-
  BaseFlowHderFamilyFixedRadius — J4-735 (B): THE FIXED-RADIUS (v-INDEPENDENT) re-derivation of the
  base-slot `hder` family, EXPOSING `Dc = M₂·C₀·‖v‖` as manifestly linear in `‖v‖`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` (`R/6` stays a labelled carrier, untouched).
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ── THE SMALLNESS GAP (the pivot of J4-735 (B)).
    `BaseFlowHderFamily.baseFlow_hder_family` proves, for a FIXED `v`, the per-base near-identity
    derivative package with constant `Dc = M₂·C₀·‖v‖` — but it hides `M₂` behind a phase ball
    `S := closedBall (c₀,0) (C₀·‖v‖ + Rwin + σ)` whose radius DEPENDS ON `‖v‖`.  So `M₂` (a second-jet
    field bound over `S`) itself varies with `v`, and the `‖v‖→0` vanishing of `Dc` is never exposed at
    the type level: `Dc` is an opaque existential per-`v` call, with no visible linear-in-`‖v‖` shape.

    This file MIRRORS the banked fixed-radius phase-ball technique of
    `UniformFlowJacobianBound.uniformFlowExp_fderiv_uniform_bound` (a SINGLE compact `S = closedBall …
    RG` sized from `K`/`ρ_K`/`C₀` alone, BEFORE picking `v`): using `‖v‖ ≤ ρ_K = uniformFlowRadius`, the
    tube confinement `≤ C₀·‖v‖ ≤ C₀·ρ_K`, so the phase ball
    `S := closedBall (c₀,0) (C₀·ρ_K + Rwin + σ)` is **v-INDEPENDENT**, its second-jet field bound `M₂`
    and Lipschitz/field constant `Kc = Kf` are **single v-independent constants**, and the near-identity
    bound is `‖L − id‖ ≤ (M₂·C₀·‖v‖)·e^{Kc}` with `M₂, Kc` quantified OUTSIDE the `∀ v`.  The
    `Dc = M₂·C₀·‖v‖` linear-in-`‖v‖` shape is now MANIFEST.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).
    * `baseFlow_hder_family_fixedRadius` — ★★★ the v-INDEPENDENT `hder` family.  A single pair of
      constants `M₂fix, Kc` (from the FIXED phase ball) such that for EVERY `v` with `‖v‖ ≤ ρ_K` and every
      base `u` in the σ-interior window, `q ↦ φ_q v` has a Fréchet derivative with
      `‖L − id‖ ≤ (M₂fix · C₀ · ‖v‖) · e^{Kc}`.  ⚠ NOT `a₁ = R/6`.
    * `baseDisplacement_windowed_lipschitz_fixedRadius` — ★ the exposed-smallness Lipschitz corollary.
      For every `v` with `‖v‖ ≤ ρ_K`, `u ↦ φ_u v − u` is `LipschitzOnWith ((M₂fix·C₀·‖v‖)·e^{Kc}).toNNReal`
      on the window, with `M₂fix, Kc` the SAME v-independent constants.  The contraction magnitude is now
      manifestly `O(‖v‖)`.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseFlowHderFamily

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

variable {n : ℕ}

set_option maxHeartbeats 2000000

/-! ### The fixed-radius (v-independent) base-slot `hder` family. -/

/-- **★★★ J4-735 (B) — the FIXED-RADIUS (v-independent) per-base near-identity `hder` family.**

    Mirror of `baseFlow_hder_family`, but with the phase ball sized from `K`/`ρ_K`/`C₀` alone (radius
    `C₀·ρ_K + Rwin + σ`, INDEPENDENT of the differentiation velocity `v`).  Consequently the second-jet
    field bound `M₂fix` and the field/Lipschitz constant `Kc = Kf` are SINGLE constants, quantified
    OUTSIDE the `∀ v`, and the near-identity bound has the MANIFESTLY linear-in-`‖v‖` shape
    `‖L − id‖ ≤ (M₂fix · C₀ · ‖v‖) · e^{Kc}` with `C₀ = uniformFlowConst`.  The hidden smallness is thus
    EXPOSED at the type level: as `‖v‖ → 0` the near-identity defect `→ 0` linearly, with a fixed rate. -/
theorem baseFlow_hder_family_fixedRadius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (c₀ : Point n) (Rwin σ : ℝ) (hRwin : 0 ≤ Rwin) (hσ : 0 < σ)
    (hKσ : ∀ u ∈ Metric.closedBall c₀ Rwin, ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K) :
    ∃ M₂fix Kc : ℝ, 0 ≤ M₂fix ∧ 0 ≤ Kc ∧
      ∀ v : Point n, ‖v‖ ≤ uniformFlowRadius g gi hC hK →
        ∀ u ∈ Metric.closedBall c₀ Rwin, ∃ L : Point n →L[ℝ] Point n,
          HasFDerivAt (fun q => uniformFlowExp g gi hC hK q v) L u ∧
          ‖L - ContinuousLinearMap.id ℝ (Point n)‖
            ≤ (M₂fix * uniformFlowConst g gi hC hK * ‖v‖) * Real.exp Kc := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- FIXED (v-independent) phase-ball radius: `C₀·ρ_K + Rwin + σ`.
  set Rphase : ℝ := C₀ * ρ + Rwin + σ with hRphasedef
  have hRphase0 : 0 ≤ Rphase := by
    rw [hRphasedef]; have := mul_nonneg hC₀nn hρ0.le; linarith [hσ.le, hRwin]
  set S : Set (Point n × Point n) := Metric.closedBall ((c₀, 0) : Point n × Point n) Rphase with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hSne : S.Nonempty := ⟨(c₀, 0), by rw [hSdef]; exact Metric.mem_closedBall_self hRphase0⟩
  -- window-uniform, v-INDEPENDENT field constants on the single FIXED convex phase ball `S`.
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  -- `M₂fix := M₂`, `Kc := Kf`, both v-INDEPENDENT.
  refine ⟨M₂, Kf, hM₂0, hKf0, ?_⟩
  intro v hv u huS
  have hu_c : ‖u - c₀‖ ≤ Rwin := by rw [← dist_eq_norm]; rwa [Metric.mem_closedBall] at huS
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK (u + δ) v with hWfdef
  have hqK : ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K := fun δ hδ => hKσ u huS δ hδ
  -- windowed perturbed-tube ODE / confinement / IC (v-INDEPENDENT phase ball).
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK (u + δ) (hqK δ hδ) v hv τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    have hconf : ‖Wf δ τ - ((u + δ, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK (u + δ) (hqK δ hδ) v hv τ hτ
    have hb1 : ‖((u + δ, 0) : Point n × Point n) - (c₀, 0)‖ ≤ Rwin + σ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]
      simp only [norm_zero]
      rw [max_eq_left (norm_nonneg _), show u + δ - c₀ = (u - c₀) + δ from by abel]
      exact le_trans (norm_add_le _ _) (add_le_add hu_c hδ)
    have hvρ : C₀ * ‖v‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hv hC₀nn
    calc ‖Wf δ τ - ((c₀, 0) : Point n × Point n)‖
        = ‖(Wf δ τ - (u + δ, 0)) + ((u + δ, 0) - (c₀, 0))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Wf δ τ - ((u + δ, 0) : Point n × Point n)‖
            + ‖((u + δ, 0) : Point n × Point n) - (c₀, 0)‖ := norm_add_le _ _
      _ ≤ C₀ * ‖v‖ + (Rwin + σ) := add_le_add hconf hb1
      _ ≤ C₀ * ρ + (Rwin + σ) := by linarith
      _ = Rphase := by rw [hRphasedef]; ring
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((δ, 0) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = ((u + δ, v) : Point n × Point n) :=
      uniformFlowTube_spec_ic g gi hC hK (u + δ) (hqK δ hδ) v hv
    have h2 : Wf 0 0 = ((u + 0, v) : Point n × Point n) :=
      uniformFlowTube_spec_ic g gi hC hK (u + 0) (hqK 0 h0σ) v hv
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  -- base-tube continuity and Jacobi solutions (position seed).
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK (u + 0) (hqK 0 h0σ) v hv τ hτoo).continuousAt).continuousWithinAt
  set V : Point n → ℝ → Point n × Point n :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose with hVdef
  have hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n) :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose_spec.1
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (Wf 0 τ) (V δ τ)) τ :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((δ, 0) : Point n × Point n)).choose_spec.2
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  -- confinement-driven coefficient deviation, centre `q := u + 0` (the base tube's own centre).
  have hcenterS : ((u + 0, 0) : Point n × Point n) ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_self, add_zero,
      Prod.norm_def]
    simp only [norm_zero]
    rw [max_eq_left (norm_nonneg _)]
    exact le_trans hu_c (by rw [hRphasedef]; linarith [mul_nonneg hC₀nn hρ0.le, hσ.le])
  have hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)
        - fderiv ℝ (geodesicField g gi) ((u + 0, 0) : Point n × Point n)‖ ≤ M₂ * (C₀ * ‖v‖) := by
    intro τ hτ
    have hmvt := hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hM₂ hcenterS (hmem 0 h0σ τ hτ)
    refine le_trans hmvt ?_
    have hconf0 : ‖Wf 0 τ - ((u + 0, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK (u + 0) (hqK 0 h0σ) v hv τ hτ
    exact mul_le_mul_of_nonneg_left hconf0 hM₂0
  -- windowed base-slot near-identity Fréchet derivative at `δ = 0`, with `Dc = M₂·(C₀·‖v‖)`.
  obtain ⟨L, hFDpos, hbound⟩ := baseFlow_endpoint_fderiv_near_id_window g gi hC hKf0
    (mul_nonneg hM₂0 (mul_nonneg hC₀nn (norm_nonneg _))) hσ hSconv hM₂ hLip hWode hVode hV0 hIC hKb
    hmem hAd
  -- `(Wf δ 1).1 = uniformFlowExp g gi hC hK (u+δ) v`, then recentre by the base translation.
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK (u + δ) v) := by
    funext δ
    show (Wf δ 1).1 = uniformFlowExp g gi hC hK (u + δ) v
    rw [uniformFlowExp_eq]
  rw [hfun] at hFDpos
  have hshift : HasFDerivAt (fun q : Point n => q - u) (ContinuousLinearMap.id ℝ (Point n)) u :=
    (hasFDerivAt_id u).sub_const u
  have hFD0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK (u + δ) v) L (u - u) := by
    rw [sub_self]; exact hFDpos
  have hcomp : HasFDerivAt (fun q => uniformFlowExp g gi hC hK (u + (q - u)) v)
      (L.comp (ContinuousLinearMap.id ℝ (Point n))) u :=
    hFD0.comp (f := fun q : Point n => q - u) u hshift
  have hfun2 : (fun q => uniformFlowExp g gi hC hK (u + (q - u)) v)
      = (fun q => uniformFlowExp g gi hC hK q v) := by
    funext q; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  refine ⟨L, hcomp, ?_⟩
  -- rearrange `M₂·(C₀·‖v‖)·e^{Kf}` into `(M₂·C₀·‖v‖)·e^{Kf}`.
  have hrw : M₂ * (C₀ * ‖v‖) * Real.exp Kf = M₂ * C₀ * ‖v‖ * Real.exp Kf := by ring
  rw [hrw] at hbound
  exact hbound

/-- **★ J4-735 (B) STEP (2) — the EXPOSED-SMALLNESS windowed base-displacement Lipschitz bound.**
    Feeding `baseFlow_hder_family_fixedRadius` (per fixed `v`) into
    `BaseFlowLipTrunc.baseDisplacement_lipschitzOnWith_window_nearId`, the base-displacement map
    `u ↦ φ_u v − u` is `LipschitzOnWith ((M₂fix·C₀·‖v‖)·e^{Kc}).toNNReal` on the convex base window, with
    `M₂fix, Kc` the SAME v-independent constants for EVERY `v` with `‖v‖ ≤ ρ_K`.  The contraction
    magnitude is now MANIFESTLY `O(‖v‖)` — as `‖v‖ → 0` the Lipschitz constant `→ 0` linearly. -/
theorem baseDisplacement_windowed_lipschitz_fixedRadius (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (c₀ : Point n) (Rwin σ : ℝ) (hRwin : 0 ≤ Rwin) (hσ : 0 < σ)
    (hKσ : ∀ u ∈ Metric.closedBall c₀ Rwin, ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K) :
    ∃ M₂fix Kc : ℝ, 0 ≤ M₂fix ∧ 0 ≤ Kc ∧
      ∀ v : Point n, ‖v‖ ≤ uniformFlowRadius g gi hC hK →
        LipschitzOnWith ((M₂fix * uniformFlowConst g gi hC hK * ‖v‖) * Real.exp Kc).toNNReal
          (fun u => uniformFlowExp g gi hC hK u v - u) (Metric.closedBall c₀ Rwin) := by
  obtain ⟨M₂fix, Kc, hM₂0, hKc0, hfam⟩ :=
    baseFlow_hder_family_fixedRadius g gi hC hK c₀ Rwin σ hRwin hσ hKσ
  refine ⟨M₂fix, Kc, hM₂0, hKc0, fun v hv => ?_⟩
  exact QIQTH.BaseFlowLipTrunc.baseDisplacement_lipschitzOnWith_window_nearId
    (fun q => uniformFlowExp g gi hC hK q v) (Metric.closedBall c₀ Rwin)
    (M₂fix * uniformFlowConst g gi hC hK * ‖v‖) Kc
    (mul_nonneg (mul_nonneg hM₂0 (uniformFlowConst_nonneg g gi hC hK)) (norm_nonneg v))
    hKc0 (convex_closedBall _ _) (hfam v hv)

end QIQTH.ExpMap

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#check @baseFlow_hder_family_fixedRadius
#check @baseDisplacement_windowed_lipschitz_fixedRadius
#print axioms baseFlow_hder_family_fixedRadius
#print axioms baseDisplacement_windowed_lipschitz_fixedRadius
end AxiomChecks
