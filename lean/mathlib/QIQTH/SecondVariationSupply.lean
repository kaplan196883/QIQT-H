/-
  SecondVariationSupply — J4-49: the INHOMOGENEOUS linear-ODE existence engine and the generic
  SECOND-VARIATION field over an arbitrary base geodesic — the analytic core of the doubled-family
  second-variation SUPPLY block consumed by
  `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## Context

  The CLOSE bridge `expMap_common_nondeg_radius_of_doubled_supply` proves the compact-uniform local
  exp-nondegeneracy gate `(J)` from a doubled-family supply.  The base supply
  (`σ/hYode/hIC/hScompact/hSconvex/hmem/Vf/hVode/hV0`, packaged in
  `confined_doubled_family_with_variation_exists`) and the first-jet link `hlink` are already
  discharged.  The SOLE carried block is the SECOND-VARIATION block: the fields `Ybase, Zf, Src` and
  the binders `hZf, h0d, hKbd, hZ, h0cap, hKbcap, hAd, hXb, hSd`.

  `hZf` / `hZ` require `Zf` to solve the INHOMOGENEOUS linearized-geodesic ODE
      `Zf' τ = fderiv(geodesicField)(Ybase τ)·Zf τ + Src τ`,
  whose source is the second-order coupling `Src τ = fderiv²(geodesicField)(Ybase τ)(p τ)(w τ)`.  The
  repo's `linODE_exists_on_Icc` (`GenericJacobiExists.lean`) solves only the HOMOGENEOUS system
  `X' = A(τ)X`.  This file ADDS the inhomogeneous solver and the generic second-variation field.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled supply)

  * `linODE_inhomog_exists_on_Icc` — **(F1 engine)** the inhomogeneous linear-ODE existence.  For a
    continuous time-dependent bounded operator `A` and a continuous source `src` on the padded `[-1,2]`
    and a seed `w₀`, there is `J` with `J 0 = w₀` and a genuine two-sided
    `HasDerivAt J (A τ (J τ) + src τ) τ` on `[0,1]`.  DERIVED by the state-augmentation reduction to the
    HOMOGENEOUS `linODE_exists_hasDerivAt_Icc` on `E × ℝ`: the augmented operator
    `Ã τ (X,u) = (A τ X + u·src τ, 0)` is continuous linear, the constancy of the `ℝ`-tracker
    (`u ≡ 1` via `constant_of_has_deriv_right_zero`) recovers the affine source.

  * `secondVariation_field_exists` — **(F1+F2)** the generic second-variation field over an arbitrary
    continuous phase base curve `Ybase` with continuous coupling input `pfield`.  Produces `Zf` solving
    the inhomogeneous 2nd-var ODE with `Src τ = fderiv²(geodesicField)(Ybase τ)(pfield τ)(Ybase τ).2`,
    seed `Zf 0 = seed`, together with the Grönwall norm bound
    `‖Zf τ‖ ≤ gronwallBound ‖seed‖ K' (sup‖Src‖) 0 τ` under an operator bound `‖A τ‖ ≤ K'`.  Source
    continuity is DERIVED from `geodesicField ∈ C^∞` (`contDiff_geodesicField` ⇒ `fderiv²` continuous).

  ## HONEST CHECKPOINT (binding)

  This lands the inhomogeneous linear-ODE existence engine (F1 core) and the generic second-variation
  field with its ODE / seed / Grönwall-bound data (F1 + the `hXb`-shaped bound of F2), all DERIVED,
  self-contained (hypotheses only: continuity of `A`/`src`/`Ybase`/`pfield`, an operator bound, `hC`).
  It does NOT thread these to the specific `(Y…0)`/`Vf` of the package (the final `Ybase q v` /
  `Src q v a b` identification), does NOT build the Lipschitz-in-`q` binders `hAd`/`hSd` (F3 — needs the
  base-geodesic two-point Grönwall `geodesic_twopoint_gronwall` composed with the specific package
  curves), and does NOT assemble the final `(J)` (F4).  Those remain carried.  It does NOT touch
  Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.DoubledFamilyLink
import QIQTH.DoubledVariationField
import QIQTH.JacobiDoubledFamily
import QIQTH.GenericJacobiExists
import QIQTH.BoundedGeometry
import QIQTH.BoundedGeometryConfine
import QIQTH.VelocitySecondJetId
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

section InhomogLinODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **(F1 engine) — inhomogeneous linear-ODE existence on `[0,1]`.**  For a continuous time-dependent
    bounded operator `A` and a continuous source `src` on the padded interval `[-1,2]`, and a seed `w₀`,
    there is `J : ℝ → E` with `J 0 = w₀` solving the INHOMOGENEOUS linear ODE
    `J' τ = A τ (J τ) + src τ` on `[0,1]` (two-sided `HasDerivAt`).

    DERIVED by the classical state-augmentation trick: solve the HOMOGENEOUS system on `E × ℝ` with
    augmented operator `Ã τ (X,u) = (A τ X + u • src τ, 0)` (continuous linear) and seed `(w₀, 1)` via
    the repo's homogeneous solver `linODE_exists_hasDerivAt_Icc`; the `ℝ`-tracker `u` has zero
    derivative on `[0,1]`, hence `u ≡ 1` (`constant_of_has_deriv_right_zero`), turning the first
    component's ODE into `X' = A τ X + src τ`. -/
theorem linODE_inhomog_exists_on_Icc (A : ℝ → (E →L[ℝ] E)) (src : ℝ → E)
    (hA : ContinuousOn A (Set.Icc (-1 : ℝ) 2))
    (hsrc : ContinuousOn src (Set.Icc (-1 : ℝ) 2)) (w₀ : E) :
    ∃ J : ℝ → E, J 0 = w₀ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J (A τ (J τ) + src τ) τ := by
  classical
  -- Augmented operator on `E × ℝ`: `Ã τ (X,u) = (A τ X + u • src τ, 0)`.
  set Ã : ℝ → ((E × ℝ) →L[ℝ] (E × ℝ)) := fun τ =>
    (ContinuousLinearMap.inl ℝ E ℝ).comp
      ((A τ).comp (ContinuousLinearMap.fst ℝ E ℝ)
        + (ContinuousLinearMap.snd ℝ E ℝ).smulRight (src τ)) with hÃdef
  -- Pointwise action.
  have hApp : ∀ (τ : ℝ) (z : E × ℝ), Ã τ z = (A τ z.1 + z.2 • src τ, (0 : ℝ)) := by
    intro τ z
    simp [hÃdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply]
  -- Continuity of the augmented operator on the padded interval.
  have hÃcont : ContinuousOn Ã (Set.Icc (-1 : ℝ) 2) := by
    have h1 : ContinuousOn (fun τ => (A τ).comp (ContinuousLinearMap.fst ℝ E ℝ))
        (Set.Icc (-1 : ℝ) 2) := hA.clm_comp continuousOn_const
    have h2 : ContinuousOn
        (fun τ => (ContinuousLinearMap.snd ℝ E ℝ).smulRight (src τ)) (Set.Icc (-1 : ℝ) 2) := by
      have := (continuousOn_const (c :=
        ContinuousLinearMap.smulRightL ℝ (E × ℝ) E (ContinuousLinearMap.snd ℝ E ℝ))).clm_apply hsrc
      simpa [ContinuousLinearMap.smulRightL_apply_apply] using this
    exact continuousOn_const.clm_comp (h1.add h2)
  -- Solve the augmented homogeneous system.
  obtain ⟨J, hJ0, hJd⟩ := linODE_exists_hasDerivAt_Icc Ã hÃcont (w₀, (1 : ℝ))
  -- The `ℝ`-tracker `u := (J ·).2` has zero derivative on `[0,1]`.
  have hu0 : (fun t => (J t).2) 0 = 1 := by show (J 0).2 = 1; rw [hJ0]
  have hud : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t => (J t).2) 0 τ := by
    intro τ hτ
    have h := (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt τ (hJd τ hτ)
    have hz : (Ã τ (J τ)).2 = (0 : ℝ) := by rw [hApp]
    simpa [ContinuousLinearMap.coe_snd', hz] using h
  -- Constancy `u ≡ 1` on `[0,1]`.
  have hucont : ContinuousOn (fun t => (J t).2) (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hud τ hτ).continuousAt.continuousWithinAt
  have huconst : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (J τ).2 = 1 := by
    intro τ hτ
    have := constant_of_has_deriv_right_zero hucont
      (fun x hx => ((hud x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)) τ hτ
    rw [this]; exact hu0
  -- First component solves the inhomogeneous ODE.
  refine ⟨fun t => (J t).1, by show (J 0).1 = w₀; rw [hJ0], fun τ hτ => ?_⟩
  have h := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt τ (hJd τ hτ)
  have hval : (Ã τ (J τ)).1 = A τ (J τ).1 + src τ := by
    rw [hApp, huconst τ hτ, one_smul]
  simpa [ContinuousLinearMap.coe_fst', hval] using h

end InhomogLinODE

section SecondVariationField

variable {n : ℕ}

/-- **(F1 + F2) — generic second-variation field over an arbitrary base geodesic phase curve.**
    For continuous phase curves `bcurve` (the base geodesic state), `pfield` (the first-order variation
    field's first factor), `wfield` (the base's second doubled factor) on the padded `[-1,2]`, a seed,
    and an operator bound `‖fderiv(geodesicField)(bcurve τ)‖ ≤ K'` and a source bound
    `‖Src τ‖ ≤ Smax` on `[0,1]`, there is `Zf` solving the INHOMOGENEOUS second-variation ODE
      `Zf' τ = fderiv(geodesicField)(bcurve τ)·Zf τ + fderiv²(geodesicField)(bcurve τ)(pfield τ)(wfield τ)`
    with `Zf 0 = seed` (two-sided `HasDerivAt` on `[0,1]`) together with the Grönwall norm bound
      `‖Zf τ‖ ≤ gronwallBound ‖seed‖ K' Smax (τ - 0)`.

    This is exactly the ODE-shape of the bridge binders `hZf` / `hZ` (with `bcurve = (Y…0).1`,
    `pfield = (Vf …).1`, `wfield = (Y…0).2`) and the `hXb`-shaped norm control (F2).  The A-operator and
    source continuity are DERIVED from `geodesicField ∈ C^∞` (`contDiff_geodesicField` ⇒ `fderiv` and
    `fderiv²` continuous), composed with the continuous input curves. -/
theorem secondVariation_field_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (bcurve pfield wfield : ℝ → Point n × Point n)
    (hbcurve : ContinuousOn bcurve (Set.Icc (-1 : ℝ) 2))
    (hpfield : ContinuousOn pfield (Set.Icc (-1 : ℝ) 2))
    (hwfield : ContinuousOn wfield (Set.Icc (-1 : ℝ) 2))
    (seed : Point n × Point n) {K' Smax : ℝ} (hK'0 : 0 ≤ K')
    (hKbd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (bcurve τ)‖ ≤ K')
    (hSmax : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (bcurve τ) (pfield τ) (wfield τ)‖ ≤ Smax) :
    ∃ Zf : ℝ → Point n × Point n, Zf 0 = seed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt Zf
          (fderiv ℝ (geodesicField g gi) (bcurve τ) (Zf τ)
            + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (bcurve τ) (pfield τ) (wfield τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖Zf τ‖ ≤ gronwallBound ‖seed‖ K' Smax (τ - 0)) := by
  -- Smoothness of the geodesic field and its first/second Fréchet derivatives.
  have hgf : ContDiff ℝ (⊤ : WithTop ℕ∞) (geodesicField g gi) := contDiff_geodesicField g gi hC
  have hDf : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (geodesicField g gi)) :=
    hgf.fderiv_right le_top
  have hD2f : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    hDf.fderiv_right le_top
  -- Time-dependent operator and source.
  set A : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)) :=
    fun τ => fderiv ℝ (geodesicField g gi) (bcurve τ) with hAdef
  set Src : ℝ → Point n × Point n :=
    fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (bcurve τ) (pfield τ) (wfield τ) with hSrcdef
  -- Continuity of `A` and `Src` on the padded interval.
  have hAcont : ContinuousOn A (Set.Icc (-1 : ℝ) 2) :=
    hDf.continuous.comp_continuousOn hbcurve
  have hSrccont : ContinuousOn Src (Set.Icc (-1 : ℝ) 2) := by
    have h0 : ContinuousOn (fun τ => fderiv ℝ (fderiv ℝ (geodesicField g gi)) (bcurve τ))
        (Set.Icc (-1 : ℝ) 2) := hD2f.continuous.comp_continuousOn hbcurve
    exact (h0.clm_apply hpfield).clm_apply hwfield
  -- Solve the inhomogeneous second-variation ODE.
  obtain ⟨Zf, hZ0, hZd⟩ := linODE_inhomog_exists_on_Icc A Src hAcont hSrccont seed
  refine ⟨Zf, hZ0, hZd, ?_⟩
  -- Grönwall bound on `‖Zf‖`.
  have hZcont : ContinuousOn Zf (Set.Icc (0 : ℝ) 1) :=
    fun τ hτ => (hZd τ hτ).continuousAt.continuousWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖A x (Zf x) + Src x‖ ≤ K' * ‖Zf x‖ + Smax := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
    calc ‖A x (Zf x) + Src x‖ ≤ ‖A x (Zf x)‖ + ‖Src x‖ := norm_add_le _ _
      _ ≤ ‖A x‖ * ‖Zf x‖ + ‖Src x‖ := by
          gcongr; exact (A x).le_opNorm (Zf x)
      _ ≤ K' * ‖Zf x‖ + Smax := by
          gcongr
          · exact hKbd x hxIcc
          · exact hSmax x hxIcc
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := Zf)
    (f' := fun x => A x (Zf x) + Src x) (δ := ‖seed‖) (K := K') (ε := Smax) (a := 0) (b := 1)
    hZcont (fun x hx => (hZd x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (le_of_eq (by rw [hZ0])) hbound
  exact this

end SecondVariationField

end QIQTH.ExpMap
