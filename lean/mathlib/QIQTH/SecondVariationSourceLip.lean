/-
  SecondVariationSourceLip — J4-51: the (F3b) three-fold Lipschitz-in-basepoint bound `hSd` for the
  second-order coupling SOURCE of the doubled-family second-variation block consumed by
  `expMap_common_nondeg_radius_of_doubled_supply` (`JacobiDoubledFamily.lean`).

  ## Context

  The CLOSE bridge produces the compact-uniform local exp-nondegeneracy gate `(J)` from a doubled-family
  supply.  Its SECOND-VARIATION block carries the `Src`-Lipschitz binder

    `hSd : ‖Src q v a b τ − Src q' v a b τ‖ ≤ Sr₀ · dist q q' · ‖a‖ · ‖b‖`,

  where the concrete source built by `secondVariation_field_exists` is the second-order coupling
    `Src q v a b τ = fderiv²(geodesicField)(Ybase q v τ)(pfield q v a b τ)(wfield q v a b τ)`,
  with `Ybase q v` the base geodesic phase curve, `pfield = (Vf …).1` the linearized field (a Jacobi
  field seeded by `(0,a)`), and `wfield = (Y…0).2` the base's second doubled factor (a Jacobi field
  seeded by `(0,b)`).  Both `pfield` and `wfield` solve the SAME homogeneous Jacobi linODE
  `X' = fderiv(geodesicField)(bcurve)(X)` along the base geodesic (the first factor of `doubledField`),
  differing only in their seeds.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `fderiv2_geodesicField_lipschitzOnWith_of_isCompact_convex` — **(G0)** the exact analogue of J4-50's
    `fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex` ONE derivative higher: `fderiv²
    (geodesicField)` is Lipschitz on any compact convex phase set (its own Fréchet derivative `fderiv³`
    is continuous, hence bounded on the compact set; the mean-value theorem on the convex set gives the
    modulus).

  * `fderiv2_geodesicField_twopoint_dist_bound` — **(G-A)** the two-point Lipschitz-in-basepoint bound
    for `fderiv²(geodesicField)` along two geodesic phase flows, mirroring J4-50's
    `fderiv_geodesicField_twopoint_dist_bound` with the second Fréchet derivative:
    `‖fderiv²(gf)(Y₁ τ) − fderiv²(gf)(Y₂ τ)‖ ≤ Lg₂·e^{Kg}·dist (Y₁ 0)(Y₂ 0)`.

  * `secondVariation_source_twopoint_dist_bound` — **(G-Σ, the `hSd`-shaped capstone).**  The TRILINEAR
    split `Src_q − Src_q' = (F₁−F₂)(p₁)(w₁) + F₂(p₁−p₂)(w₁) + F₂(p₂)(w₁−w₂)` (`Fᵢ = fderiv²(gf)(Yᵢ)`),
    bounded term-by-term:
      * term A (base-point `q`-dep) via G-A on `‖F₁−F₂‖` and the `‖p₁‖,‖w₁‖` bounds;
      * term B (`pfield` `q`-dep) via the two-point Jacobi Grönwall `jacobi_twopoint_diff_bound`
        (`BasepointJetModulus.lean`) on `‖p₁−p₂‖`, the `‖F₂‖ ≤ M₂` bound, and the `‖w₁‖` bound;
      * term C (`wfield` `q`-dep) via the SAME two-point Jacobi Grönwall on `‖w₁−w₂‖`, the `‖F₂‖ ≤ M₂`
        bound, and the `‖p₂‖` bound.
    Each is `≲ dist (Y₁ 0)(Y₂ 0)·‖a‖·‖b‖`, delivering exactly the `hSd` shape with an EXPLICIT,
    `a,b`-independent `Sr₀` built from the Lipschitz moduli / operator bounds / field-norm coefficients.

  The two-point-linODE engine for terms B/C is the repo's geometry-free
  `jacobi_twopoint_diff_bound`/`linODE_twopoint_diff_bound` (`BasepointJetModulus.lean`): a two-point
  Grönwall for two Jacobi fields with the SAME seed along two base geodesics whose coefficient fields
  differ by `‖DF(Y₁)−DF(Y₂)‖ ≤ Dcoef` — supplied here by J4-50's
  `fderiv_geodesicField_twopoint_dist_bound`.

  ## HONEST CHECKPOINT (binding)

  This DISCHARGES the `hSd` binder of the bridge for the concrete coupling source, given genuine data:
  the two geodesic base flows (integral curves of `geodesicField`, confined in a common compact
  `S`), the two `pfield`/`wfield` Jacobi linODE families (same seeds), the field-norm coefficient bounds
  (`‖p‖ ≤ Cp·‖a‖`, `‖w‖ ≤ Cw·‖b‖` — the genuine Grönwall control the supply provides, NOT the
  conclusion), the Lipschitz moduli of `gf`/`fderiv gf`/`fderiv² gf` on `S` (produced by G0 + J4-50),
  and the operator bounds `‖fderiv gf‖ ≤ Kb`, `‖fderiv² gf‖ ≤ M₂` on `S`.  `Sr₀` is DERIVED explicitly,
  uniform in `a,b`.

  This does NOT thread `hSd` to the specific `(Ybase q v)`/`(pfield q v a b)`/`(wfield q v a b)` of the
  package (the `dist (Y₁ 0)(Y₂ 0) = dist q q'` identification and the final `(J)` assembly are F4), does
  NOT build the covariant `D²/dτ²`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.SecondVariationLipschitz
import QIQTH.SecondVariationSupply
import QIQTH.DoubledVariationField
import QIQTH.JacobiDoubledFamily
import QIQTH.BasepointJetModulus
import QIQTH.BoundedGeometry
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **(G0) — `fderiv² (geodesicField)` is Lipschitz on any compact convex phase set.**  Exact analogue
    of J4-50's `fderiv_geodesicField_lipschitzOnWith_of_isCompact_convex`, one derivative higher:
    `geodesicField` is `C^∞`, so `fderiv² (geodesicField)` is `C^∞` too, hence `fderiv³ (geodesicField)`
    is continuous and bounded on the compact `S`; the mean-value theorem on the convex `S`
    (`Convex.lipschitzOnWith_of_nnnorm_fderiv_le`) converts that into a Lipschitz modulus. -/
theorem fderiv2_geodesicField_lipschitzOnWith_of_isCompact_convex
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {S : Set (Point n × Point n)} (hS : IsCompact S) (hSc : Convex ℝ S) :
    ∃ Lg2 : ℝ≥0, LipschitzOnWith Lg2 (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S := by
  have hD2f : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ (geodesicField g gi))) :=
    ((contDiff_geodesicField g gi hC).fderiv_right le_top).fderiv_right le_top
  -- Bound the (real-valued, continuous) operator norm of `fderiv³(geodesicField)` on the compact `S`.
  have hcont : Continuous
      (fun x => ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖) :=
    (hD2f.continuous_fderiv (by simp)).norm
  obtain ⟨C, hCb⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (hD2f.differentiable (by simp)).differentiableAt) (fun x hx => ?_) hSc
  have h : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) x‖ ≤ max C 0 :=
    ((Real.le_norm_self _).trans (hCb x hx)).trans (le_max_left _ _)
  exact_mod_cast h

/-- **(G-A) — the two-point Lipschitz-in-basepoint bound for `fderiv²(geodesicField)`.**

    If `Y₁, Y₂` are two integral curves of the autonomous geodesic field on `[0,1]` that both stay in a
    set `S` on which `geodesicField` is `Kg`-Lipschitz and `fderiv²(geodesicField)` is `Lg₂`-Lipschitz,
    then along the whole interval
    `‖fderiv²(gf)(Y₁ τ) − fderiv²(gf)(Y₂ τ)‖ ≤ Lg₂·e^{Kg}·dist (Y₁ 0)(Y₂ 0)`.

    Mirror of J4-50's `fderiv_geodesicField_twopoint_dist_bound` with the second Fréchet derivative:
    the two-point geodesic Grönwall (`geodesic_twopoint_gronwall`) bounds the phase distance, and the
    `Lg₂`-Lipschitz control of `fderiv²(geodesicField)` on `S` (`LipschitzOnWith.dist_le_mul`) converts
    that into the operator-norm bound. -/
theorem fderiv2_geodesicField_twopoint_dist_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set (Point n × Point n)} {Kg Lg2 : ℝ≥0}
    (hLip : LipschitzOnWith Kg (geodesicField g gi) S)
    (hLip2 : LipschitzOnWith Lg2 (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    {Y₁ Y₂ : ℝ → Point n × Point n}
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖
        ≤ (Lg2 : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by
  intro τ hτ
  have hg : dist (Y₁ τ) (Y₂ τ) ≤ dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ) :=
    geodesic_twopoint_gronwall g gi hLip h1 h2 hS1 hS2 τ hτ
  have hlip2τ :
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)‖
        ≤ (Lg2 : ℝ) * dist (Y₁ τ) (Y₂ τ) := by
    have h := hLip2.dist_le_mul (Y₁ τ) (hS1 τ hτ) (Y₂ τ) (hS2 τ hτ)
    rwa [dist_eq_norm] at h
  refine hlip2τ.trans ?_
  have hexp : Real.exp ((Kg : ℝ) * τ) ≤ Real.exp Kg := by
    apply Real.exp_le_exp.mpr
    have : (Kg : ℝ) * τ ≤ (Kg : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg Kg)
    simpa using this
  calc (Lg2 : ℝ) * dist (Y₁ τ) (Y₂ τ)
      ≤ (Lg2 : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp ((Kg : ℝ) * τ)) :=
        mul_le_mul_of_nonneg_left hg (NNReal.coe_nonneg Lg2)
    _ ≤ (Lg2 : ℝ) * (dist (Y₁ 0) (Y₂ 0) * Real.exp Kg) := by
        apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg Lg2)
        exact mul_le_mul_of_nonneg_left hexp dist_nonneg
    _ = (Lg2 : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) := by ring

/-- **(G-Σ) — the `hSd`-shaped three-fold Lipschitz-in-basepoint bound for the second-order coupling
    source.**

    For two geodesic base phase flows `Y₁, Y₂` (integral curves of `geodesicField` on `[0,1]`, confined
    in a common `S`), and two `pfield`/`wfield` Jacobi families `p₁,p₂`/`w₁,w₂` solving the homogeneous
    Jacobi linODE `X' = fderiv(gf)(Yᵢ)(X)` along `Y₁`/`Y₂` respectively with the SAME seeds
    (`p₁ 0 = p₂ 0`, `w₁ 0 = w₂ 0`), under
      * the Lipschitz moduli `Kg` (`gf`), `Lg` (`fderiv gf`), `Lg₂` (`fderiv² gf`) on `S`,
      * the operator bounds `‖fderiv gf‖ ≤ Kb`, `‖fderiv² gf‖ ≤ M₂` on `S`,
      * the field-norm coefficient bounds `‖p₁‖,‖p₂‖ ≤ Cp·‖a‖`, `‖w₁‖,‖w₂‖ ≤ Cw·‖b‖`,
    the concrete source `Srcᵢ τ = fderiv²(gf)(Yᵢ τ)(pᵢ τ)(wᵢ τ)` obeys
      `‖Src₁ τ − Src₂ τ‖ ≤ Sr₀ · dist (Y₁ 0)(Y₂ 0) · ‖a‖ · ‖b‖`,
    with the EXPLICIT, `a,b`-independent
      `Sr₀ = Lg₂·e^{Kg}·Cp·Cw + 2·M₂·Lg·e^{Kg}·e^{Kb}·Cp·Cw`.

    This is exactly the `hSd` binder of `expMap_common_nondeg_radius_of_doubled_supply` for the concrete
    coupling source, with `dist (Y₁ 0)(Y₂ 0)` in place of `dist q q'` (the identification is F4). -/
theorem secondVariation_source_twopoint_dist_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    {S : Set (Point n × Point n)} {Kg Lg Lg2 : ℝ≥0} {Kb M2 Cp Cw : ℝ}
    (hKb0 : 0 ≤ Kb) (hM2_0 : 0 ≤ M2) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw)
    (hLipK : LipschitzOnWith Kg (geodesicField g gi) S)
    (hLipL : LipschitzOnWith Lg (fderiv ℝ (geodesicField g gi)) S)
    (hLipL2 : LipschitzOnWith Lg2 (fderiv ℝ (fderiv ℝ (geodesicField g gi))) S)
    (hMK : ∀ z ∈ S, ‖fderiv ℝ (geodesicField g gi) z‖ ≤ Kb)
    (hM2 : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ M2)
    {Y₁ Y₂ p1 p2 w1 w2 : ℝ → Point n × Point n} (a b : Point n)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₁ (geodesicField g gi (Y₁ t)) t)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y₂ (geodesicField g gi (Y₂ t)) t)
    (hS1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t ∈ S)
    (hS2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y₂ t ∈ S)
    (hp1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt p1 (fderiv ℝ (geodesicField g gi) (Y₁ τ) (p1 τ)) τ)
    (hp2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt p2 (fderiv ℝ (geodesicField g gi) (Y₂ τ) (p2 τ)) τ)
    (hp0 : p1 0 = p2 0)
    (hw1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt w1 (fderiv ℝ (geodesicField g gi) (Y₁ τ) (w1 τ)) τ)
    (hw2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt w2 (fderiv ℝ (geodesicField g gi) (Y₂ τ) (w2 τ)) τ)
    (hw0 : w1 0 = w2 0)
    (hPb1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p1 τ‖ ≤ Cp * ‖a‖)
    (hPb2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p2 τ‖ ≤ Cp * ‖a‖)
    (hWb1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖w1 τ‖ ≤ Cw * ‖b‖)
    (hWb2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖w2 τ‖ ≤ Cw * ‖b‖) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ) (p1 τ) (w1 τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p2 τ) (w2 τ)‖
        ≤ ((Lg2 : ℝ) * Real.exp Kg * Cp * Cw
            + M2 * ((Lg : ℝ) * Real.exp Kg * Real.exp Kb) * Cp * Cw
            + M2 * ((Lg : ℝ) * Real.exp Kg * Real.exp Kb) * Cp * Cw)
          * dist (Y₁ 0) (Y₂ 0) * ‖a‖ * ‖b‖ := by
  -- The first- and second-order two-point operator bounds along the two base geodesics.
  have hAop := fderiv_geodesicField_twopoint_dist_bound g gi hLipK hLipL h1 h2 hS1 hS2
  have hA2op := fderiv2_geodesicField_twopoint_dist_bound g gi hLipK hLipL2 h1 h2 hS1 hS2
  -- Two-point Jacobi Grönwall for the `pfield` difference (seed-shared, `q`-dependent coefficient).
  have hpdiff := jacobi_twopoint_diff_bound g gi (K := Kb)
    (Dcoef := (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0)) (Jb := Cp * ‖a‖)
    hKb0 hp1 hp2 hp0 (fun τ hτ => hMK (Y₁ τ) (hS1 τ hτ)) hAop hPb2
  -- Two-point Jacobi Grönwall for the `wfield` difference (seed-shared, `q`-dependent coefficient).
  have hwdiff := jacobi_twopoint_diff_bound g gi (K := Kb)
    (Dcoef := (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0)) (Jb := Cw * ‖b‖)
    hKb0 hw1 hw2 hw0 (fun τ hτ => hMK (Y₁ τ) (hS1 τ hτ)) hAop hWb2
  -- Nonnegativity helpers.
  have he : (0 : ℝ) ≤ Real.exp (Kg : ℝ) := (Real.exp_pos _).le
  have hek : (0 : ℝ) ≤ Real.exp Kb := (Real.exp_pos _).le
  have hlg : (0 : ℝ) ≤ (Lg : ℝ) := NNReal.coe_nonneg _
  have hlg2 : (0 : ℝ) ≤ (Lg2 : ℝ) := NNReal.coe_nonneg _
  have hdist : (0 : ℝ) ≤ dist (Y₁ 0) (Y₂ 0) := dist_nonneg
  have hCpa : (0 : ℝ) ≤ Cp * ‖a‖ := mul_nonneg hCp (norm_nonneg _)
  have hcoefA : (0 : ℝ) ≤ (Lg2 : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) :=
    mul_nonneg (mul_nonneg hlg2 he) hdist
  intro τ hτ
  -- The trilinear split of the source difference.
  have hsplit :
      fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ) (p1 τ) (w1 τ)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p2 τ) (w2 τ)
        = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
              - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)) (p1 τ) (w1 τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p1 τ - p2 τ) (w1 τ)
          + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p2 τ) (w1 τ - w2 τ) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  -- Term A: base-point `q`-dependence of `fderiv²(gf)`.
  have htA :
      ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
              - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)) (p1 τ) (w1 τ)‖
        ≤ ((Lg2 : ℝ) * Real.exp Kg * Cp * Cw) * (dist (Y₁ 0) (Y₂ 0) * ‖a‖ * ‖b‖) := by
    refine ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₁ τ)
        - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)).le_opNorm₂ (p1 τ) (w1 τ)).trans ?_
    refine (mul_le_mul
      (mul_le_mul (hA2op τ hτ) (hPb1 τ hτ) (norm_nonneg _) hcoefA)
      (hWb1 τ hτ) (norm_nonneg _) (mul_nonneg hcoefA hCpa)).trans ?_
    apply le_of_eq; ring
  -- Term B: `pfield` `q`-dependence.
  have htB :
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p1 τ - p2 τ) (w1 τ)‖
        ≤ (M2 * ((Lg : ℝ) * Real.exp Kg * Real.exp Kb) * Cp * Cw)
            * (dist (Y₁ 0) (Y₂ 0) * ‖a‖ * ‖b‖) := by
    refine ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)).le_opNorm₂
        (p1 τ - p2 τ) (w1 τ)).trans ?_
    have hpb : (0 : ℝ) ≤
        (Lg : ℝ) * Real.exp Kg * dist (Y₁ 0) (Y₂ 0) * (Cp * ‖a‖) * Real.exp Kb :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hlg he) hdist) hCpa) hek
    refine (mul_le_mul
      (mul_le_mul (hM2 (Y₂ τ) (hS2 τ hτ)) (hpdiff τ hτ) (norm_nonneg _) hM2_0)
      (hWb1 τ hτ) (norm_nonneg _) (mul_nonneg hM2_0 hpb)).trans ?_
    apply le_of_eq; ring
  -- Term C: `wfield` `q`-dependence.
  have htC :
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ) (p2 τ) (w1 τ - w2 τ)‖
        ≤ (M2 * ((Lg : ℝ) * Real.exp Kg * Real.exp Kb) * Cp * Cw)
            * (dist (Y₁ 0) (Y₂ 0) * ‖a‖ * ‖b‖) := by
    refine ((fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Y₂ τ)).le_opNorm₂
        (p2 τ) (w1 τ - w2 τ)).trans ?_
    refine (mul_le_mul
      (mul_le_mul (hM2 (Y₂ τ) (hS2 τ hτ)) (hPb2 τ hτ) (norm_nonneg _) hM2_0)
      (hwdiff τ hτ) (norm_nonneg _) (mul_nonneg hM2_0 hCpa)).trans ?_
    apply le_of_eq; ring
  -- Assemble the trilinear split.
  rw [hsplit]
  refine norm_add₃_le.trans ?_
  refine (add_le_add (add_le_add htA htB) htC).trans (le_of_eq ?_)
  ring

end QIQTH.ExpMap
