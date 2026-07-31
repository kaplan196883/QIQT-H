/-
  BasepointFDeriv — assembling the base-point (starting-point) DIRECTIONAL smooth-dependence
  derivatives of the geodesic flow into a FULL Fréchet derivative in the base point.

  ODE_VARIATIONAL_PLAN.md, Phase J-c.  `BasepointSmoothDep` (J-b) proved, for each fixed perturbation
  direction `δq`, that the flow `s ↦ Y s t` of a one-parameter family whose STARTING POINT is perturbed
  linearly has an IC-derivative equal to the Jacobi field (`geodesicBasepoint_flow_hasDerivAt`).  This
  file assembles those per-direction derivatives into a genuine multivariable
  `HasFDerivAt (fun δ => W δ t) L 0`, where `L` is the CONTINUOUS-LINEAR endpoint Jacobi map
  `δ ↦ V δ t` (linear because the Jacobi equation is a linear ODE).

  WHAT LANDS HERE (all axiom-clean, no `sorry`; DERIVED, carrying only the SAME genuine geometric
  regularity inputs `GeodesicSmoothDep`/`BasepointSmoothDep` carry — `S` convex, the field's C² bound
  `‖∂²F‖ ≤ M₂` on `S`, the field Lipschitz on `S`, the Jacobi-coefficient bound `‖DF(W 0 τ)‖ ≤ K`, tube
  containment `W δ τ ∈ S`, and the supplied Jacobi solutions `V δ`):

  * `jacobiSol_unique` — uniqueness for the linear Jacobi ODE along the base geodesic: two Jacobi
    solutions with the same initial value agree on `[0,1]`.  DERIVED from `geodesicVariation_residual_bound`
    applied to the base curve as BOTH endpoints (so the field remainder `C = 0`), i.e. the homogeneous
    Grönwall `‖J₁ − J₂‖ ≤ 0`.  This is the linearity engine.

  * `geodesicBasepoint_endpoint_hasFDerivAt` — **J-c (core assembly).**  Given a continuous-linear
    `L` representing the endpoint Jacobi map (`∀ δ, L δ = V δ t`), the endpoint `fun δ => W δ t` has
    Fréchet derivative `L` at the base point (`δ = 0`).  The per-direction quadratic remainder
    `‖W δ t − W 0 t − V δ t‖ ≤ C·‖δ‖²` (two-point Grönwall + uniform C² field remainder + residual
    Grönwall, exactly as J-b, now applied with the increment `δ` itself rather than a scalar `s`) is
    `o(‖δ‖)`, which is the little-o characterisation of `HasFDerivAt`.

  * `geodesicBasepoint_endpoint_hasFDerivAt_exists` — **J-c (capstone).**  CONSTRUCTS the continuous-
    linear `L`: `δ ↦ V δ t` is additive and homogeneous (`jacobiSol_unique` applied to the sum /
    scalar multiple of Jacobi solutions, which are again Jacobi solutions with the matching seed), hence
    a `LinearMap`, promoted to `L : Point n →L[ℝ] Point n × Point n` by finite-dimensionality of the
    domain.  Delivers `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0` — fully DERIVED.

  * `geodesicBasepoint_endpoint_position_hasFDerivAt_exists` — the position-component projection:
    `∃ L, (∀ δ, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0`, the exp-map-shaped
    base-point endpoint-position Fréchet derivative.

  HONEST CHECKPOINT (binding): this is the base-point FIRST-order FULL Fréchet derivative (J-c),
  DERIVED (linearity + the uniform-in-direction little-o) carrying only the genuine geometric
  regularity already carried by J-b.  It does NOT build the base-point SECOND-order jet (J-d), NOT the
  joint (base,velocity) 2-jet continuity input (J), NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep
import QIQTH.BasepointSmoothDep

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **J-c #0 (linear-Jacobi-ODE uniqueness) — the linearity engine.**  Let `Y0` be an integral curve of
    the geodesic field on `[0,1]` with the Jacobi coefficient bounded `‖DF(Y0 τ)‖ ≤ K`.  Any two
    solutions `J₁, J₂` of the linear Jacobi equation `J' = DF(Y0)·J` along `Y0` that agree at `0` agree
    on all of `[0,1]`.

    Proof: the difference `J₁ − J₂` is again a Jacobi solution (the equation is linear) with zero initial
    value, so `geodesicVariation_residual_bound` — applied with `Y0` as BOTH endpoint curves, forcing the
    first-order field remainder `C = 0` — gives `‖J₁ t − J₂ t‖ ≤ 0·exp K = 0`. -/
theorem jacobiSol_unique (g gi : Point n → Fin n → Fin n → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    {Y0 J₁ J₂ : ℝ → Point n × Point n}
    (hY0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y0 (geodesicField g gi (Y0 τ)) τ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y0 τ)‖ ≤ K)
    (hJ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J₁ (fderiv ℝ (geodesicField g gi) (Y0 τ) (J₁ τ)) τ)
    (hJ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J₂ (fderiv ℝ (geodesicField g gi) (Y0 τ) (J₂ τ)) τ)
    (h0 : J₁ 0 = J₂ 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    J₁ t = J₂ t := by
  -- the difference is a Jacobi solution with zero initial value.
  have hD : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun σ => J₁ σ - J₂ σ)
        (fderiv ℝ (geodesicField g gi) (Y0 τ) ((fun σ => J₁ σ - J₂ σ) τ)) τ := by
    intro τ hτ
    simpa [map_sub] using (hJ1 τ hτ).sub (hJ2 τ hτ)
  have hD0 : Y0 0 - Y0 0 - (fun σ => J₁ σ - J₂ σ) 0 = 0 := by
    simp [h0]
  have hNb0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖geodesicField g gi (Y0 τ) - geodesicField g gi (Y0 τ)
          - fderiv ℝ (geodesicField g gi) (Y0 τ) (Y0 τ - Y0 τ)‖ ≤ 0 := by
    intro τ _; simp
  have hbnd := geodesicVariation_residual_bound g gi hK0 (le_refl (0 : ℝ))
    hY0 hY0 hD hD0 hKb hNb0 t ht
  simp only [sub_self, zero_sub, norm_neg, zero_mul] at hbnd
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbnd)

/-- **J-c (core assembly) — base-point first-order FULL Fréchet derivative of the geodesic flow.**
    For a base-point-perturbation-indexed family `W : Point n → ℝ → State` of geodesics
    (`W δ 0 − W 0 0 = (δ, 0)`, fixed velocity) and Jacobi solutions `V δ` along the base geodesic `W 0`
    with `V δ 0 = (δ, 0)`, given a CONTINUOUS-LINEAR `L` representing the endpoint Jacobi map
    (`∀ δ, L δ = V δ t`), the endpoint `fun δ => W δ t` has Fréchet derivative `L` at the base point
    (`δ = 0`):  `HasFDerivAt (fun δ => W δ t) L 0`.

    DERIVED: the per-direction quadratic remainder `‖W δ t − W 0 t − V δ t‖ ≤ C·‖δ‖²`
    (`C = M₂·(e^{K₀})²·e^K`), obtained from the two-point Grönwall (`geodesic_twopoint_gronwall`), the
    uniform C² field remainder (`geodesicField_uniform_C2_remainder`), and the residual Grönwall
    (`geodesicVariation_residual_bound`) exactly as in J-b but with the increment `δ` itself, is `o(‖δ‖)`
    uniformly in the direction — the little-o characterisation of `HasFDerivAt`.  Carries only the
    genuine geometric regularity (`S` convex, C² field bound, field Lipschitz, Jacobi-coefficient bound,
    tube containment, supplied Jacobi solutions) plus the continuous-linear representation of the
    endpoint Jacobi map (constructed unconditionally in `..._exists`). -/
theorem geodesicBasepoint_endpoint_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {L : Point n →L[ℝ] Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hLeq : ∀ δ : Point n, L δ = V δ t) :
    HasFDerivAt (fun δ => W δ t) L 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (W 0 0)))
      (hbound2 (W 0 0) (hmem 0 0 (Set.left_mem_Icc.mpr zero_le_one)))
  set Ctot : ℝ := M₂ * (Real.exp K₀) ^ 2 * Real.exp K with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  -- per-direction quadratic remainder.
  have hquad : ∀ δ : Point n, ‖W δ t - W 0 t - V δ t‖ ≤ Ctot * ‖δ‖ ^ 2 := by
    intro δ
    have hnorm : ‖((δ, 0) : Point n × Point n)‖ = ‖δ‖ := by
      rw [Prod.norm_def]; simp
    -- uniform quadratic field remainder along the pair (W δ, W 0).
    have hNb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖geodesicField g gi (W δ τ) - geodesicField g gi (W 0 τ)
            - fderiv ℝ (geodesicField g gi) (W 0 τ) (W δ τ - W 0 τ)‖
          ≤ M₂ * (‖δ‖ * Real.exp K₀) ^ 2 := by
      intro τ hτ
      have htp := geodesic_twopoint_gronwall g gi hLip (hWode δ) (hWode 0)
        (hmem δ) (hmem 0) τ hτ
      have hd0 : dist (W δ 0) (W 0 0) = ‖δ‖ := by
        rw [dist_eq_norm, hIC δ, hnorm]
      have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
        apply Real.exp_le_exp.mpr
        calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
          _ = (K₀ : ℝ) := mul_one _
      have hLb : ‖W δ τ - W 0 τ‖ ≤ ‖δ‖ * Real.exp K₀ := by
        rw [← dist_eq_norm]
        calc dist (W δ τ) (W 0 τ)
            ≤ dist (W δ 0) (W 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
          _ = ‖δ‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
          _ ≤ ‖δ‖ * Real.exp K₀ := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2
        (hmem δ τ hτ) (hmem 0 τ hτ)
      refine hrem.trans ?_
      have hsq : ‖W δ τ - W 0 τ‖ ^ 2 ≤ (‖δ‖ * Real.exp K₀) ^ 2 := by
        have := mul_le_mul hLb hLb (norm_nonneg _) (by positivity)
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left hsq hnn
    have h0 : W δ 0 - W 0 0 - V δ 0 = 0 := by rw [hIC δ, hV0 δ]; abel
    have hbnd := geodesicVariation_residual_bound g gi hK0
      (mul_nonneg hnn (sq_nonneg _)) (hWode 0) (hWode δ) (hVode δ) h0 hKb hNb t ht
    refine hbnd.trans_eq ?_
    rw [hCtotdef, mul_pow]; ring
  -- assemble the little-o characterisation of the Fréchet derivative at `0`.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (Ctot + 1), div_pos hc (by linarith [hCtot0]), fun δ hδ => ?_⟩
  rw [dist_eq_norm, sub_zero] at hδ
  rw [hLeq δ]
  have hlt : ‖δ‖ * (Ctot + 1) < c := (lt_div_iff₀ (by linarith [hCtot0])).mp hδ
  have hCtotδ : Ctot * ‖δ‖ ≤ c := by nlinarith [norm_nonneg δ, hCtot0]
  calc ‖W δ t - W 0 t - V δ t‖
      ≤ Ctot * ‖δ‖ ^ 2 := hquad δ
    _ = (Ctot * ‖δ‖) * ‖δ‖ := by ring
    _ ≤ c * ‖δ‖ := mul_le_mul_of_nonneg_right hCtotδ (norm_nonneg _)

/-- **J-c (capstone) — the base-point Fréchet derivative EXISTS, with its continuous-linear map
    CONSTRUCTED.**  Same hypotheses as the core assembly minus the supplied `L`.  The endpoint Jacobi map
    `δ ↦ V δ t` is additive and homogeneous — `jacobiSol_unique` applied to the sum / scalar multiple of
    Jacobi solutions (each again a Jacobi solution with the matching seed `(δ₁+δ₂,0)` resp. `(c·δ,0)`) —
    hence a `LinearMap`, promoted to a `ContinuousLinearMap` by finite-dimensionality of `Point n`.  The
    result: `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`, fully DERIVED. -/
theorem geodesicBasepoint_endpoint_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n × Point n,
      (∀ δ : Point n, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0 := by
  -- additivity of `δ ↦ V δ t` from Jacobi-ODE uniqueness.
  have hadd : ∀ a b : Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hK0 (hWode 0) hKb (J₁ := fun σ => V a σ + V b σ)
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b), Prod.mk_add_mk]
  -- homogeneity of `δ ↦ V δ t` from Jacobi-ODE uniqueness.
  have hsmul : ∀ (c : ℝ) (a : Point n), c • V a t = V (c • a) t := by
    intro c a
    refine jacobiSol_unique g gi hK0 (hWode 0) hKb (J₁ := fun σ => c • V a σ)
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a), Prod.smul_mk]
  -- package the endpoint Jacobi map as a continuous-linear map.
  let Lₗ : Point n →ₗ[ℝ] Point n × Point n :=
    { toFun := fun δ => V δ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun δ => rfl, ?_⟩
  exact geodesicBasepoint_endpoint_hasFDerivAt g gi hC hK0 ht hconv hbound2 hLip hWode hVode
    hV0 hIC hKb hmem (fun δ => rfl)

/-- **J-c (endpoint position) — the exp-map-shaped base-point endpoint-position Fréchet derivative.**
    Projecting the base-point endpoint Fréchet derivative onto the position component:
    `∃ L, (∀ δ, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0`.  At `t = 1` this is the
    base-point (`q`) Fréchet derivative of the exp-map-shaped geodesic-endpoint position for a confined
    tube family. -/
theorem geodesicBasepoint_endpoint_position_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n,
      (∀ δ : Point n, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0 := by
  obtain ⟨L, hLeq, hFD⟩ := geodesicBasepoint_endpoint_hasFDerivAt_exists g gi hC hK0 ht hconv
    hbound2 hLip hWode hVode hV0 hIC hKb hmem
  refine ⟨(ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L, fun δ => ?_, ?_⟩
  · simp [hLeq δ]
  · have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [Function.comp] using this

end QIQTH.ExpMap
