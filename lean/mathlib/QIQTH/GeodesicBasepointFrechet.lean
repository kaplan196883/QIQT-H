/-
  GeodesicBasepointFrechet — the JOINT (base + velocity) FULL-PHASE-SPACE Fréchet derivative of the
  geodesic flow, the Fréchet-level upgrade of `GeodesicSmoothDepDir`'s DIRECTION-GENERAL (arbitrary
  perturbation `ξ : Point n × Point n`) Gâteaux derivative (J4-825).

  MOTIVATION (plan `tranquil-stargazing-fox.md`, Brick 1 — corrected for repo credit).
  The plan framed Brick 1 as "upgrade `GeodesicSmoothDepDir.geodesicVariation_basepoint_endpoint_exists_uncond`
  from a per-direction Gâteaux derivative to a genuine Fréchet derivative (CLM + `HasFDerivAt`)".  A
  repo audit shows the *base-slot* Fréchet derivative ALREADY EXISTS and is banked:

    * `BasepointFDeriv.geodesicBasepoint_endpoint_hasFDerivAt(_exists)` — the base-slot (seed `(δ,0)`)
      full Fréchet derivative with its CLM constructed from Jacobi-ODE uniqueness;
    * `BaseFlowHderFamily.baseFlow_hder_family` / `..._position_hasFDerivAt_window_exists` — the same,
      σ-windowed and WIRED to the concrete `uniformFlowExp` (the plan's "Brick 2");
    * `UniformFlowFDeriv.flowVelocity_endpoint_hasFDerivAt_window` — the mirror VELOCITY-slot core.

  So the base-only and velocity-only first Fréchet derivatives are done.  What the repo LACKS — and what
  the DIRECTION-GENERAL J4-825 lineage (`GeodesicSmoothDepDir`, whose `geodesicVariation_exists_dir*`
  theorems take an ARBITRARY `ξ`, not just `(u,0)`) uniquely enables — is the JOINT derivative: the flow
  endpoint's Fréchet derivative with respect to the FULL phase-space initial condition
  `ξ = (δq, δv) : Point n × Point n` (base AND velocity perturbed simultaneously).  Both banked cores
  restrict the perturbed-tube data to a coordinate subspace (`(δ,0)` resp. `(0,δ)`); neither delivers the
  full State-slot CLM `ξ ↦ V ξ t`.  This file builds it.

  WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `geodesicFlow_joint_hasFDerivAt` — **the joint Fréchet-derivative core.**  For a family
    `W : State → ℝ → State` of geodesics whose FULL initial condition is perturbed linearly
    (`W ξ 0 − W 0 0 = ξ`, arbitrary `ξ ∈ Point n × Point n`) and Jacobi solutions `V ξ` along the base
    geodesic `W 0` with `V ξ 0 = ξ`, given a continuous-linear `L` representing the endpoint Jacobi map
    (`∀ ξ, L ξ = V ξ t`), the endpoint `fun ξ => W ξ t` has Fréchet derivative `L` at `ξ = 0`.  Proof is
    the direction-general residual-Grönwall quadratic remainder `‖W ξ t − W 0 t − V ξ t‖ ≤ Ctot·‖ξ‖²`
    (two-point Grönwall + uniform C² field remainder + residual Grönwall), which is `o(‖ξ‖)` uniformly in
    the direction — the little-o characterisation of `HasFDerivAt`.  It is the Fréchet analogue of
    `GeodesicSmoothDepDir.geodesicVariation_exists_dir_uncond`.

  * `geodesicFlow_joint_hasFDerivAt_exists` — **the joint Fréchet derivative, CLM CONSTRUCTED.**  The
    endpoint Jacobi map `ξ ↦ V ξ t` is additive and homogeneous (`jacobiSol_unique` — the banked linearity
    engine — applied to sums / scalar multiples of Jacobi solutions, again Jacobi solutions with the
    matching seed), hence a `LinearMap`, promoted to a `ContinuousLinearMap` by finite-dimensionality of the
    phase space `Point n × Point n`.  Delivers
    `∃ L, (∀ ξ, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L 0`.

  * `geodesicFlow_joint_endpoint_position_hasFDerivAt_exists` — the position-component projection:
    `∃ L, (∀ ξ, L ξ = (V ξ t).1) ∧ HasFDerivAt (fun ξ => (W ξ t).1) L 0` — the joint (base,velocity)
    Fréchet derivative of the exp-map-shaped endpoint POSITION.

  * `geodesicFlow_basepoint_hasFDerivAt_ofJoint` — the base-slot Fréchet derivative recovered as the
    RESTRICTION of the joint one to the base subspace `δ ↦ (δ,0)` (bridging back to the plan's stated
    base-point goal): `HasFDerivAt (fun δ => W (δ,0) t) (L.comp (inl ..)) 0`.

  HONEST CHECKPOINT (binding): this is the JOINT first-order Fréchet derivative of the geodesic flow on
  the FULL phase space — the direction-general (`ξ` arbitrary) Fréchet upgrade of J4-825's Gâteaux
  derivative, carrying only the SAME genuine geometric regularity the base/velocity cores carry (`S`
  convex, the field's C² bound `‖∂²F‖ ≤ M₂` on `S`, field Lipschitz on `S`, the Jacobi-coefficient bound
  `‖DF(W 0 τ)‖ ≤ K`, tube containment, supplied Jacobi solutions).  It does NOT wire to the concrete
  `uniformFlowExp` (Brick 2, already banked for the base slot), NOT build the base-point SECOND-order jet,
  NOT Raychaudhuri, NOT `a₁ = R/6`, and does NOT by itself discharge `hCConv`.
-/
import Mathlib
import QIQTH.GeodesicSmoothDep
import QIQTH.GeodesicSmoothDepDir
import QIQTH.BasepointFDeriv

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **Joint (base + velocity) Fréchet-derivative core.**  For a FULL-phase-space-perturbation-indexed
    family `W : State → ℝ → State` of geodesics (`W ξ 0 − W 0 0 = ξ`, arbitrary `ξ`) and Jacobi solutions
    `V ξ` along the base geodesic `W 0` with `V ξ 0 = ξ`, given a continuous-linear `L` representing the
    endpoint Jacobi map (`∀ ξ, L ξ = V ξ t`), the endpoint `fun ξ => W ξ t` has Fréchet derivative `L` at
    `ξ = 0`:  `HasFDerivAt (fun ξ => W ξ t) L 0`.

    DERIVED: the direction-general quadratic remainder `‖W ξ t − W 0 t − V ξ t‖ ≤ Ctot·‖ξ‖²`
    (`Ctot = M₂·(e^{K₀})²·e^K`), obtained from the two-point Grönwall (`geodesic_twopoint_gronwall`), the
    uniform C² field remainder (`geodesicField_uniform_C2_remainder`) and the residual Grönwall
    (`geodesicVariation_residual_bound`), is `o(‖ξ‖)` uniformly in the direction — the little-o
    characterisation of `HasFDerivAt`.  This is the Fréchet analogue of
    `GeodesicSmoothDepDir.geodesicVariation_exists_dir_uncond`. -/
theorem geodesicFlow_joint_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    {L : (Point n × Point n) →L[ℝ] Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ : Point n × Point n, W ξ 0 - W 0 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S)
    (hLeq : ∀ ξ : Point n × Point n, L ξ = V ξ t) :
    HasFDerivAt (fun ξ => W ξ t) L 0 := by
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (W 0 0)))
      (hbound2 (W 0 0) (hmem 0 0 (Set.left_mem_Icc.mpr zero_le_one)))
  set Ctot : ℝ := M₂ * (Real.exp K₀) ^ 2 * Real.exp K with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  -- per-direction quadratic remainder, uniform over the direction `ξ`.
  have hquad : ∀ ξ : Point n × Point n, ‖W ξ t - W 0 t - V ξ t‖ ≤ Ctot * ‖ξ‖ ^ 2 := by
    intro ξ
    -- uniform quadratic field remainder along the pair `(W ξ, W 0)`.
    have hNb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖geodesicField g gi (W ξ τ) - geodesicField g gi (W 0 τ)
            - fderiv ℝ (geodesicField g gi) (W 0 τ) (W ξ τ - W 0 τ)‖
          ≤ M₂ * (‖ξ‖ * Real.exp K₀) ^ 2 := by
      intro τ hτ
      have htp := geodesic_twopoint_gronwall g gi hLip (hWode ξ) (hWode 0)
        (hmem ξ) (hmem 0) τ hτ
      have hd0 : dist (W ξ 0) (W 0 0) = ‖ξ‖ := by
        rw [dist_eq_norm, hIC ξ]
      have hexp : Real.exp ((K₀ : ℝ) * τ) ≤ Real.exp K₀ := by
        apply Real.exp_le_exp.mpr
        calc (K₀ : ℝ) * τ ≤ (K₀ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτ.2 (NNReal.coe_nonneg K₀)
          _ = (K₀ : ℝ) := mul_one _
      have hLb : ‖W ξ τ - W 0 τ‖ ≤ ‖ξ‖ * Real.exp K₀ := by
        rw [← dist_eq_norm]
        calc dist (W ξ τ) (W 0 τ)
            ≤ dist (W ξ 0) (W 0 0) * Real.exp ((K₀ : ℝ) * τ) := htp
          _ = ‖ξ‖ * Real.exp ((K₀ : ℝ) * τ) := by rw [hd0]
          _ ≤ ‖ξ‖ * Real.exp K₀ := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      have hrem := geodesicField_uniform_C2_remainder g gi hC hconv hbound2
        (hmem ξ τ hτ) (hmem 0 τ hτ)
      refine hrem.trans ?_
      have hsq : ‖W ξ τ - W 0 τ‖ ^ 2 ≤ (‖ξ‖ * Real.exp K₀) ^ 2 := by
        have := mul_le_mul hLb hLb (norm_nonneg _) (by positivity)
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left hsq hnn
    have h0 : W ξ 0 - W 0 0 - V ξ 0 = 0 := by rw [hIC ξ, hV0 ξ]; abel
    have hbnd := geodesicVariation_residual_bound g gi hK0
      (mul_nonneg hnn (sq_nonneg _)) (hWode 0) (hWode ξ) (hVode ξ) h0 hKb hNb t ht
    refine hbnd.trans_eq ?_
    rw [hCtotdef, mul_pow]; ring
  -- assemble the little-o characterisation of the Fréchet derivative at `0`.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (Ctot + 1), div_pos hc (by linarith [hCtot0]), fun ξ hξ => ?_⟩
  rw [dist_eq_norm, sub_zero] at hξ
  rw [hLeq ξ]
  have hlt : ‖ξ‖ * (Ctot + 1) < c := (lt_div_iff₀ (by linarith [hCtot0])).mp hξ
  have hCtotξ : Ctot * ‖ξ‖ ≤ c := by nlinarith [norm_nonneg ξ, hCtot0]
  calc ‖W ξ t - W 0 t - V ξ t‖
      ≤ Ctot * ‖ξ‖ ^ 2 := hquad ξ
    _ = (Ctot * ‖ξ‖) * ‖ξ‖ := by ring
    _ ≤ c * ‖ξ‖ := mul_le_mul_of_nonneg_right hCtotξ (norm_nonneg _)

/-- **Joint Fréchet derivative, its CLM CONSTRUCTED.**  Same hypotheses as the core minus the supplied
    `L`.  The endpoint Jacobi map `ξ ↦ V ξ t` is additive and homogeneous — `jacobiSol_unique` (the
    banked linearity engine) applied to the sum / scalar multiple of Jacobi solutions (each again a Jacobi
    solution with the matching seed `a+b` resp. `c•a`) — hence a `LinearMap`, promoted to a
    `ContinuousLinearMap` by finite-dimensionality of the phase space `Point n × Point n`.  Delivers
    `∃ L, (∀ ξ, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L 0`, fully DERIVED. -/
theorem geodesicFlow_joint_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ : Point n × Point n, W ξ 0 - W 0 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n × Point n,
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L 0 := by
  -- additivity of `ξ ↦ V ξ t` from Jacobi-ODE uniqueness.
  have hadd : ∀ a b : Point n × Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hK0 (hWode 0) hKb (J₁ := fun σ => V a σ + V b σ)
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b)]
  -- homogeneity of `ξ ↦ V ξ t` from Jacobi-ODE uniqueness.
  have hsmul : ∀ (c : ℝ) (a : Point n × Point n), c • V a t = V (c • a) t := by
    intro c a
    refine jacobiSol_unique g gi hK0 (hWode 0) hKb (J₁ := fun σ => c • V a σ)
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a)]
  -- package the endpoint Jacobi map as a continuous-linear map (finite-dim phase space).
  let Lₗ : (Point n × Point n) →ₗ[ℝ] Point n × Point n :=
    { toFun := fun ξ => V ξ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun ξ => rfl, ?_⟩
  exact geodesicFlow_joint_hasFDerivAt g gi hC hK0 ht hconv hbound2 hLip hWode hVode
    hV0 hIC hKb hmem (fun ξ => rfl)

/-- **Joint Fréchet derivative of the endpoint POSITION.**  Projecting the joint (base,velocity) endpoint
    Fréchet derivative onto the position component:
    `∃ L, (∀ ξ, L ξ = (V ξ t).1) ∧ HasFDerivAt (fun ξ => (W ξ t).1) L 0` — the full-phase-space Fréchet
    derivative of the exp-map-shaped geodesic-endpoint position. -/
theorem geodesicFlow_joint_endpoint_position_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ : Point n × Point n, W ξ 0 - W 0 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n,
      (∀ ξ : Point n × Point n, L ξ = (V ξ t).1) ∧ HasFDerivAt (fun ξ => (W ξ t).1) L 0 := by
  obtain ⟨L, hLeq, hFD⟩ := geodesicFlow_joint_hasFDerivAt_exists g gi hC hK0 ht hconv
    hbound2 hLip hWode hVode hV0 hIC hKb hmem
  refine ⟨(ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L, fun ξ => ?_, ?_⟩
  · simp [hLeq ξ]
  · have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp
      (0 : Point n × Point n) hFD
    simpa [Function.comp] using this

/-- **Base-slot Fréchet derivative as a RESTRICTION of the joint one.**  Bridging back to the plan's
    stated base-point goal: the base-slot endpoint derivative is the joint derivative `L` precomposed with
    the base-subspace inclusion `δ ↦ (δ, 0)` (`ContinuousLinearMap.inl`).  For the joint family `W`, the
    base-slice map `δ ↦ W (δ,0) t` has Fréchet derivative `L.comp (inl ℝ (Point n) (Point n))` at `0`. -/
theorem geodesicFlow_basepoint_hasFDerivAt_ofJoint (g gi : Point n → Fin n → Fin n → ℝ)
    {W : Point n × Point n → ℝ → Point n × Point n}
    {L : (Point n × Point n) →L[ℝ] Point n × Point n} {t : ℝ}
    (hFD : HasFDerivAt (fun ξ => W ξ t) L 0) :
    HasFDerivAt (fun δ : Point n => W ((δ, 0) : Point n × Point n) t)
      (L.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n))) 0 := by
  have hinl : HasFDerivAt (fun δ : Point n => ((δ, 0) : Point n × Point n))
      (ContinuousLinearMap.inl ℝ (Point n) (Point n)) 0 :=
    (ContinuousLinearMap.inl ℝ (Point n) (Point n)).hasFDerivAt
  have hFD0 : HasFDerivAt (fun ξ => W ξ t) L ((ContinuousLinearMap.inl ℝ (Point n) (Point n)) 0) := by
    simpa using hFD
  simpa [Function.comp] using hFD0.comp (0 : Point n) hinl

end QIQTH.ExpMap
