/-
  UniformFlowFDeriv — J4-55 (K2 of the (J) re-architecture): the FIRST-JET Fréchet derivative of the
  UNIFORM-flow exp endpoint `uniformFlowExp` in the initial condition `w`, over the compact base set
  `K`, carried with the GENUINE uniform radius `ρ_K` (`uniformFlowRadius`) — NO opaque per-`q` `expRho`.

  ## Context

  `UniformFlowNondeg` (K1) built `uniformFlowExp g gi hC hK q : Point n → Point n`,
  `w ↦ (uniformFlowTube … q w 1).1`, the position endpoint of the compact-uniform confined geodesic
  tube through `(q, w)`, with a single uniform confinement radius `ρ_K`.  K1 delivered ONLY the tube's
  IC / geodesic-ODE / confinement spec — NOT differentiability of the endpoint in `w`.  Mathlib's
  Picard–Lindelöf gives only Lipschitz-in-IC; the endpoint derivative must be produced by a
  VARIATIONAL (Jacobi-field) argument.

  ## Why a WINDOWED core (and why `expRho` cannot be borrowed)

  The velocity-slot first-jet tower `flowVelocity_endpoint_hasFDerivAt(_exists)` (`VelocitySecondJetId`)
  proves the endpoint Fréchet derivative for an ABSTRACT velocity-seeded geodesic family `W`, but its
  hypotheses (`hWode / hIC / hmem`) are quantified over ALL seed increments `δ` — a GLOBAL family of
  confined geodesics, which real geodesic tubes cannot supply (an unbounded seed escapes any fixed
  confinement ball).  The from-scratch `hasFDerivAt_expMap` avoids this by working locally, but requires
  `‖v‖ < expRho`; and the compact-uniform confinement radius `ρ_K` is a Picard–Lindelöf EXISTENCE radius
  that is NOT `≤ expRho` in general (`CommonNondegRadius` firewall item (a): discharging `ρ_K < expRho`
  needs lower semicontinuity of `expRho` over `K`, absent from the substrate).  So the K2 derivative
  cannot be transported from `expMap` without reintroducing `expRho`.

  The resolution (this file): a σ-WINDOWED velocity-slot core `flowVelocity_endpoint_hasFDerivAt_window`
  whose PERTURBED-tube hypotheses (`hWode / hIC / hmem`) hold only for `‖δ‖ ≤ σ` — which real uniform
  tubes DO supply (`‖w + δ‖ ≤ ρ_K` for `‖δ‖ ≤ ρ_K − ‖w‖`) — while the Jacobi solutions `V δ`, built
  along the FIXED base tube, stay globally defined and linear in the seed (so the endpoint Jacobi map is
  still a genuine `ContinuousLinearMap`).  The `HasFDerivAt` little-o characterisation only ever
  probes `δ` near `0`, so windowing is sound: the proof is the verbatim `flowVelocity_endpoint_hasFDerivAt`
  with the little-o neighbourhood shrunk into the window.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion, no smuggled `HasFDerivAt`, no `expRho`)

  * `flowVelocity_endpoint_hasFDerivAt_window` / `flowVelocity_endpoint_hasFDerivAt_window_exists`
    — the σ-windowed velocity-slot first Fréchet derivative core / capstone (perturbed-tube data only on
    `‖δ‖ ≤ σ`; Jacobi data global).

  * `uniformFlowExp_hasFDerivAt` — **K2.**  For `q ∈ K` and `‖w‖ < ρ_K`, the uniform-flow exp endpoint
    `uniformFlowExp g gi hC hK q` has a Fréchet derivative at `w`:
        `∃ L : Point n →L[ℝ] Point n, HasFDerivAt (uniformFlowExp g gi hC hK q) L w`,
    with `L` the velocity Jacobi endpoint operator along the base tube.  Hypotheses ONLY `hC`
    (Christoffel `C^∞`) + `IsCompact K` (+ the unconditional uniform-tube data).  NO `expRho`.

  This REDUCES the compact-uniform (J) gate for `F = uniformFlowExp` to K3 (Neumann / `IsUnit`): a
  uniform lower bound on `‖L − id‖` making `L` a unit for `w` small.
-/
import QIQTH.UniformFlowNondeg
import QIQTH.VelocitySecondJetId
import QIQTH.GenericJacobiExists
import QIQTH.DoubledFamilyFullSupply
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 2000000

variable {n : ℕ}

/-- **σ-windowed velocity-slot first Fréchet derivative of the geodesic-flow endpoint (core).**

    Verbatim `flowVelocity_endpoint_hasFDerivAt`, but the perturbed-tube hypotheses `hWode / hIC / hmem`
    are restricted to the window `‖δ‖ ≤ σ` (`σ > 0`), while the Jacobi data `hVode / hV0` and the CLM
    representation `hLeq` stay global.  Since the `HasFDerivAt` little-o only probes `δ` near `0`, the
    proof is unchanged apart from shrinking the little-o neighbourhood into `min σ (c / (Ctot+1))`. -/
theorem flowVelocity_endpoint_hasFDerivAt_window (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {L : Point n →L[ℝ] Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K σ : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hLeq : ∀ δ : Point n, L δ = V δ t) :
    HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (W 0 0)))
      (hbound2 (W 0 0) (hmem 0 h0σ 0 (Set.left_mem_Icc.mpr zero_le_one)))
  set Ctot : ℝ := M₂ * (Real.exp K₀) ^ 2 * Real.exp K with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  -- per-direction quadratic remainder, on the window.
  have hquad : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖W δ t - W 0 t - V δ t‖ ≤ Ctot * ‖δ‖ ^ 2 := by
    intro δ hδσ
    have hnorm : ‖((0, δ) : Point n × Point n)‖ = ‖δ‖ := by
      rw [Prod.norm_def]; simp
    have hNb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖geodesicField g gi (W δ τ) - geodesicField g gi (W 0 τ)
            - fderiv ℝ (geodesicField g gi) (W 0 τ) (W δ τ - W 0 τ)‖
          ≤ M₂ * (‖δ‖ * Real.exp K₀) ^ 2 := by
      intro τ hτ
      have htp := geodesic_twopoint_gronwall g gi hLip (hWode δ hδσ) (hWode 0 h0σ)
        (hmem δ hδσ) (hmem 0 h0σ) τ hτ
      have hd0 : dist (W δ 0) (W 0 0) = ‖δ‖ := by
        rw [dist_eq_norm, hIC δ hδσ, hnorm]
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
        (hmem δ hδσ τ hτ) (hmem 0 h0σ τ hτ)
      refine hrem.trans ?_
      have hsq : ‖W δ τ - W 0 τ‖ ^ 2 ≤ (‖δ‖ * Real.exp K₀) ^ 2 := by
        have := mul_le_mul hLb hLb (norm_nonneg _) (by positivity)
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left hsq hnn
    have h0 : W δ 0 - W 0 0 - V δ 0 = 0 := by rw [hIC δ hδσ, hV0 δ]; abel
    have hbnd := geodesicVariation_residual_bound g gi hK0
      (mul_nonneg hnn (sq_nonneg _)) (hWode 0 h0σ) (hWode δ hδσ) (hVode δ) h0 hKb hNb t ht
    refine hbnd.trans_eq ?_
    rw [hCtotdef, mul_pow]; ring
  -- little-o characterisation of the Fréchet derivative at `0`, on the window.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min σ (c / (Ctot + 1)), lt_min hσ (div_pos hc (by linarith [hCtot0])), fun δ hδ => ?_⟩
  rw [dist_eq_norm, sub_zero] at hδ
  have hδσ : ‖δ‖ ≤ σ := (lt_of_lt_of_le hδ (min_le_left _ _)).le
  have hδc : ‖δ‖ < c / (Ctot + 1) := lt_of_lt_of_le hδ (min_le_right _ _)
  rw [hLeq δ]
  have hlt : ‖δ‖ * (Ctot + 1) < c := (lt_div_iff₀ (by linarith [hCtot0])).mp hδc
  have hCtotδ : Ctot * ‖δ‖ ≤ c := by nlinarith [norm_nonneg δ, hCtot0]
  calc ‖W δ t - W 0 t - V δ t‖
      ≤ Ctot * ‖δ‖ ^ 2 := hquad δ hδσ
    _ = (Ctot * ‖δ‖) * ‖δ‖ := by ring
    _ ≤ c * ‖δ‖ := mul_le_mul_of_nonneg_right hCtotδ (norm_nonneg _)

/-- **σ-windowed velocity-slot first Fréchet derivative, its CLM CONSTRUCTED.**  Same window as the
    core minus the supplied `L`.  The endpoint velocity Jacobi map `δ ↦ V δ t` is additive and
    homogeneous (`jacobiSol_unique` on sums / scalar multiples of the GLOBALLY defined Jacobi solutions
    along the fixed base `W 0`), hence a `LinearMap`, promoted to a `ContinuousLinearMap` by finite-
    dimensionality of `Point n`.  Delivers `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`. -/
theorem flowVelocity_endpoint_hasFDerivAt_window_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K σ : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n × Point n,
      (∀ δ : Point n, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  -- additivity of `δ ↦ V δ t` from Jacobi-ODE uniqueness (Jacobi data global in the seed).
  have hadd : ∀ a b : Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hK0 (hWode 0 h0σ) hKb (J₁ := fun σ' => V a σ' + V b σ')
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b), Prod.mk_add_mk]
  -- homogeneity of `δ ↦ V δ t` from Jacobi-ODE uniqueness.
  have hsmul : ∀ (c : ℝ) (a : Point n), c • V a t = V (c • a) t := by
    intro c a
    refine jacobiSol_unique g gi hK0 (hWode 0 h0σ) hKb (J₁ := fun σ' => c • V a σ')
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a), Prod.smul_mk]
  let Lₗ : Point n →ₗ[ℝ] Point n × Point n :=
    { toFun := fun δ => V δ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun δ => rfl, ?_⟩
  exact flowVelocity_endpoint_hasFDerivAt_window g gi hC hK0 hσ ht hconv hbound2 hLip hWode hVode
    hV0 hIC hKb hmem (fun δ => rfl)

/-- **K2 — the uniform-flow exp endpoint `uniformFlowExp` is Fréchet-differentiable in the IC `w`.**

    For `q ∈ K` and `‖w‖ < ρ_K` (`ρ_K = uniformFlowRadius`), the uniform-flow exp endpoint map
    `uniformFlowExp g gi hC hK q` has a Fréchet derivative at `w`.  The derivative operator `L` is the
    velocity Jacobi endpoint operator (position projection) of the confined base tube through `(q, w)`.

    DERIVED, carrying ONLY `hC` (Christoffel `C^∞`) and `IsCompact K` (plus the unconditional
    compact-uniform tube data of K1); NO `expRho`, NO carried `HasFDerivAt`.  Assembled from the
    σ-windowed velocity-slot first-jet capstone `flowVelocity_endpoint_hasFDerivAt_window_exists`, fed
    with the perturbed tubes `δ ↦ uniformFlowTube g gi hC hK q (w + δ)` on the window
    `‖δ‖ ≤ ρ_K − ‖w‖` and the base-tube velocity Jacobi solutions (`geodesicJacobi_exists_hasDerivAt_Icc`),
    then recentred at `w` by the translation `δ ↦ w + δ`. -/
theorem uniformFlowExp_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (w : Point n)
    (hw : ‖w‖ < uniformFlowRadius g gi hC hK) :
    ∃ L : Point n →L[ℝ] Point n, HasFDerivAt (uniformFlowExp g gi hC hK q) L w := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set σ : ℝ := ρ - ‖w‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  -- the perturbed uniform tubes and the confinement ball `S`.
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK q (w + δ) with hWfdef
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖w + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le w δ).trans ?_
    rw [hσdef] at hδ; linarith
  set S : Set (Point n × Point n) := Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hC₀ρ0 : 0 ≤ C₀ * ρ := mul_nonneg hC₀nn hρ0.le
  have hqmem : ((q, 0) : Point n × Point n) ∈ S := by
    rw [hSdef]; exact Metric.mem_closedBall_self hC₀ρ0
  -- field-regularity constants over the compact convex `S`.
  obtain ⟨M₂, _hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
      (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
        (by simp)).norm
    obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn ⟨(q, 0), hqmem⟩ hcontr.continuousOn
    exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
      norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
      fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  obtain ⟨K₀, hLip⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := S)).exists_lipschitzOnWith
      (by simp) hSconv hScompact
  -- windowed perturbed-tube data.
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q hq (w + δ) (hle δ hδ) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖Wf δ τ - ((q, 0) : Point n × Point n)‖
        ≤ C₀ * ‖w + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (w + δ) (hle δ hδ) τ hτ
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hle δ hδ) hC₀nn
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((0, δ) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = (q, w + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (w + δ) (hle δ hδ)
    have h2 : Wf 0 0 = (q, w + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (w + 0) (hle 0 h0σ)
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  -- base-tube continuity on the NARROW padded interval `[-1/2,3/2] ⊂ (-2,2)`, for Jacobi existence.
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (w + 0) (hle 0 h0σ) τ hτoo).continuousAt).continuousWithinAt
  -- the base-tube velocity Jacobi solutions (globally defined in the seed).
  set V : Point n → ℝ → Point n × Point n :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont ((0, δ) : Point n × Point n)).choose
    with hVdef
  have hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n) :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((0, δ) : Point n × Point n)).choose_spec.1
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (Wf 0 τ) (V δ τ)) τ :=
    fun δ => (geodesicJacobi_narrowpad_hasDerivAt_Icc g gi hC (Wf 0) hbasecont
      ((0, δ) : Point n × Point n)).choose_spec.2
  -- windowed first-jet capstone gives the endpoint Fréchet derivative at `δ = 0`.
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂ := hM₂
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  obtain ⟨L, hLeq, hFD⟩ :=
    flowVelocity_endpoint_hasFDerivAt_window_exists g gi hC hKf0 hσ ht1 hSconv hbound2 hLip
      hWode hVode hV0 hIC hKb hmem
  -- project onto the position component and recentre by the translation `δ ↦ w + δ`.
  set Lpos : Point n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L with hLposdef
  have hFDpos : HasFDerivAt (fun δ => (Wf δ 1).1) Lpos 0 := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [hLposdef, Function.comp] using this
  -- `(Wf δ 1).1 = uniformFlowExp g gi hC hK q (w + δ)`.
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK q (w + δ)) := by
    funext δ; rw [hWfdef]; rw [uniformFlowExp_eq]
  rw [hfun] at hFDpos
  -- recentre: `HasFDerivAt (fun δ => f (w+δ)) Lpos 0 ⟹ HasFDerivAt f Lpos w`.
  have hshift : HasFDerivAt (fun u : Point n => u - w) (ContinuousLinearMap.id ℝ (Point n)) w :=
    (hasFDerivAt_id w).sub_const w
  have hFDpos0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK q (w + δ)) Lpos (w - w) := by
    rw [sub_self]; exact hFDpos
  have hcomp : HasFDerivAt (fun u => uniformFlowExp g gi hC hK q (w + (u - w)))
      (Lpos.comp (ContinuousLinearMap.id ℝ (Point n))) w :=
    hFDpos0.comp (f := fun u : Point n => u - w) w hshift
  have hfun2 : (fun u => uniformFlowExp g gi hC hK q (w + (u - w)))
      = uniformFlowExp g gi hC hK q := by
    funext u; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  exact ⟨Lpos, hcomp⟩

end QIQTH.ExpMap
