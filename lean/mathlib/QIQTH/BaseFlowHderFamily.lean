/-
  BaseFlowHderFamily — J4-731, J3 (the ∀-BASE `hder` family plumbing): THE σ-WINDOWED BASE-SLOT
  FRÉCHET-DERIVATIVE ADAPTERS + the concrete per-base near-identity `hder` family.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md.  The `hflowData (i)` contraction leg of
  `WhiteHsolveFlowContraction.white_hInnerCont_closed_final8` demands, through
  `BaseFlowLipschitzTruncation.baseDisplacement_lipschitzOnWith_window_nearId`, the per-base
  near-identity DERIVATIVE package

      `∀ u ∈ S, ∃ L, HasFDerivAt (fun q => φ_q v) L u ∧ ‖L − id‖ ≤ Dc·e^K`   (★ the `hder` clause)

  for the base-slot endpoint map `F q := uniformFlowExp g gi hC hK q v` on a convex window `S`.

  ── THE INTERFACE VERDICT (why a WINDOWED base core is needed — J4-731).
    The banked base-slot Fréchet cores `BasepointFDeriv.geodesicBasepoint_endpoint_hasFDerivAt(_exists)`
    and the near-identity `BaseFlowNearId.baseFlow_endpoint_fderiv_near_id` demand their perturbed-tube
    hypotheses `hWode / hIC / hmem` for ALL seeds `δ : Point n` (a GLOBAL family of confined geodesics).
    Real uniform geodesic tubes CANNOT supply that — a base `u + δ` with `δ` large escapes the compact
    base set `K`, where no confined tube exists.  This is EXACTLY the mismatch the velocity-slot
    `UniformFlowFDeriv` resolved by a σ-WINDOWED core `flowVelocity_endpoint_hasFDerivAt_window`
    (perturbed-tube data only on `‖δ‖ ≤ σ`, Jacobi data global).  The base slot lacked the mirror.  This
    file BUILDS it — the σ-windowed base-slot core / capstone / position / near-identity — then feeds it
    from the banked `uniformFlowTube` data to deliver the concrete per-base `hder` family and its
    `LipschitzOnWith` upgrade.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited).

    * `geodesicBasepoint_endpoint_hasFDerivAt_window` — ★ the σ-windowed base-slot first Fréchet
      derivative core (position seed `(δ,0)`); verbatim `flowVelocity_endpoint_hasFDerivAt_window`
      with the base seed, perturbed-tube data restricted to `‖δ‖ ≤ σ`.
    * `geodesicBasepoint_endpoint_hasFDerivAt_window_exists` — the CLM CONSTRUCTED (Jacobi-ODE
      uniqueness ⟹ additive+homogeneous endpoint Jacobi map ⟹ `ContinuousLinearMap`).
    * `geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists` — the position projection.
    * `baseFlow_endpoint_fderiv_near_id_window` — ★ the σ-windowed base-slot Fréchet near-identity
      bound `‖L − id‖ ≤ Dc·e^K`, mirror of `BaseFlowNearId.baseFlow_endpoint_fderiv_near_id`.
    * `uniformFlowExp_baseHasFDerivAt_nearId` — ★ THE CONCRETE per-base derivative.  For `u` with a
      σ-ball `‖δ‖ ≤ σ ⟹ u+δ ∈ K` and `‖v‖ < ρ_K`, the base-slot endpoint `q ↦ φ_q v` has a Fréchet
      derivative `L` at `u` with `‖L − id‖ ≤ (M₂·C₀‖v‖)·e^K` — fed entirely from banked uniform-tube data
      (`uniformFlowTube_spec_ode/ic/conf`, `geodesicJacobi_narrowpad_hasDerivAt_Icc`), recentred by the
      translation `δ ↦ u + δ`.
    * `baseFlow_hder_family` — ★ THE `hder` FAMILY.  For a convex window `S` sitting in the σ-interior of
      `K` (each `u ∈ S` has its σ-ball inside `K`), the per-base near-identity derivative package holds at
      every `u ∈ S` with the SAME window-uniform constant `Dc·e^K`.
    * `baseDisplacement_windowed_lipschitz_concrete` — ★ STEP (2).  Feeds `baseFlow_hder_family` into
      `baseDisplacement_lipschitzOnWith_window_nearId` to get `LipschitzOnWith (Dc·e^K).toNNReal` for
      `u ↦ φ_u v − u` on `S` — the contraction's magnitude input, fully supplied.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — the σ-windowed base-slot derivative adapter
  and the concrete per-base near-identity family feeding the `hflowData (i)` contraction.  It is NOT
  `a₁ = R/6` (still a labelled carrier).  It does NOT build the full `hflowData` record, the second-order
  jet, Raychaudhuri, or numerical `G`.  The σ-interior-of-`K` window hypothesis is an honest geometric
  input (the base window must not touch `∂K`).
-/
import Mathlib
import QIQTH.BaseFlowNearId
import QIQTH.BasepointFDeriv
import QIQTH.UniformFlowFDeriv
import QIQTH.BaseFlowLipschitzTruncation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Set Filter
open scoped Topology NNReal

variable {n : ℕ}

set_option maxHeartbeats 2000000

/-! ### The σ-windowed base-slot first Fréchet derivative (core). -/

/-- **σ-windowed base-slot first Fréchet derivative of the geodesic-flow endpoint (core).**

    Verbatim `flowVelocity_endpoint_hasFDerivAt_window`, but with the BASE (position) seed `(δ,0)`: the
    perturbed-tube hypotheses `hWode / hIC / hmem` hold only on the window `‖δ‖ ≤ σ` (`σ > 0`), while the
    Jacobi data `hVode / hV0` and the CLM representation `hLeq` stay global.  Since the `HasFDerivAt`
    little-o only probes `δ` near `0`, the proof shrinks the little-o neighbourhood into
    `min σ (c / (Ctot+1))`. -/
theorem geodesicBasepoint_endpoint_hasFDerivAt_window (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
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
    have hnorm : ‖((δ, 0) : Point n × Point n)‖ = ‖δ‖ := by
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

/-- **σ-windowed base-slot first Fréchet derivative, its CLM CONSTRUCTED.**  Same window as the core
    minus the supplied `L`.  The endpoint Jacobi map `δ ↦ V δ t` is additive and homogeneous
    (`jacobiSol_unique` on sums / scalar multiples of the GLOBALLY defined Jacobi solutions along the
    fixed base `W 0`), hence a `LinearMap`, promoted to a `ContinuousLinearMap` by finite-dimensionality
    of `Point n`.  Delivers `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`. -/
theorem geodesicBasepoint_endpoint_hasFDerivAt_window_exists (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n × Point n,
      (∀ δ : Point n, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hadd : ∀ a b : Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hK0 (hWode 0 h0σ) hKb (J₁ := fun σ' => V a σ' + V b σ')
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b), Prod.mk_add_mk]
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
  exact geodesicBasepoint_endpoint_hasFDerivAt_window g gi hC hK0 hσ ht hconv hbound2 hLip hWode
    hVode hV0 hIC hKb hmem (fun δ => rfl)

/-- **σ-windowed base-slot endpoint-POSITION Fréchet derivative (constructed).**  Projecting the
    windowed base-slot endpoint Fréchet derivative onto the position component:
    `∃ L, (∀ δ, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0`. -/
theorem geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists
    (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n,
      (∀ δ : Point n, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0 := by
  obtain ⟨L, hLeq, hFD⟩ := geodesicBasepoint_endpoint_hasFDerivAt_window_exists g gi hC hK0 hσ ht
    hconv hbound2 hLip hWode hVode hV0 hIC hKb hmem
  refine ⟨(ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L, fun δ => ?_, ?_⟩
  · simp [hLeq δ]
  · have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [Function.comp] using this

/-! ### The σ-windowed base-slot Fréchet near-identity bound. -/

/-- **σ-windowed base-slot Fréchet near-identity bound.**  Mirror of
    `BaseFlowNearId.baseFlow_endpoint_fderiv_near_id`, but with the perturbed-tube data restricted to the
    window `‖δ‖ ≤ σ`.  The base-point endpoint-position derivative
    `L = fderiv (fun δ => (W δ 1).1) 0` (constructed by the windowed capstone above) satisfies, under the
    uniform coefficient deviation `‖DF(W 0 τ) − DF((q,0))‖ ≤ Dc`, the near-identity bound
    `‖L − id‖ ≤ Dc·e^K`. -/
theorem baseFlow_endpoint_fderiv_near_id_window (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n} {q : Point n}
    {S : Set (Point n × Point n)} {M₂ K Dc σ : ℝ} {K₀ : NNReal}
    (hK0 : 0 ≤ K) (hDc0 : 0 ≤ Dc) (hσ : 0 < σ)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((δ, 0) : Point n × Point n))
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (W 0 τ)
        - fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)‖ ≤ Dc) :
    ∃ L : Point n →L[ℝ] Point n,
      HasFDerivAt (fun δ => (W δ 1).1) L 0 ∧
      ‖L - ContinuousLinearMap.id ℝ (Point n)‖ ≤ Dc * Real.exp K := by
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  obtain ⟨L, hLeq, hFD⟩ := geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists g gi hC hK0
    hσ ht1 hconv hbound2 hLip hWode hVode hV0 hIC hKb hmem
  refine ⟨L, hFD, ?_⟩
  have hnearId : ∀ δ : Point n, ‖L δ - δ‖ ≤ (Dc * Real.exp K) * ‖δ‖ := by
    intro δ
    have hbnd := jacobiEndpoint_base_near_id_bound g gi hC hK0 (hVode δ) (hV0 δ) hKb hAd
    calc ‖L δ - δ‖ = ‖(V δ 1).1 - δ‖ := by rw [hLeq δ]
      _ ≤ Dc * ‖δ‖ * Real.exp K := hbnd
      _ = (Dc * Real.exp K) * ‖δ‖ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hDc0 (Real.exp_pos K).le) (fun δ => ?_)
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  exact hnearId δ

/-! ### The concrete per-base `hder` family from banked uniform-tube data. -/

/-- **★ J4-731 (the `hder` family) — the per-base near-identity derivative package at every window base.**
    Fix a velocity `v` with `‖v‖ ≤ ρ_K`.  For a convex base window `closedBall c₀ Rwin` sitting in the
    σ-interior of the compact base set `K` (each `u` in the window has its σ-ball inside `K`,
    `hKσ`), there are WINDOW-UNIFORM constants `Dc = M₂·C₀‖v‖` and `Kc = Kf` such that at EVERY base `u`
    in the window the base-slot endpoint map `q ↦ uniformFlowExp g gi hC hK q v` has a Fréchet
    derivative `L` at `u` with `‖L − id‖ ≤ Dc·e^{Kc}`.

    Constructed entirely from banked uniform-tube data: the perturbed base tubes
    `Wf δ := uniformFlowTube g gi hC hK (u+δ) v` (ODE / IC / confinement from `uniformFlowTube_spec_*`),
    the base-tube Jacobi solutions (`geodesicJacobi_narrowpad_hasDerivAt_Icc`), the window-uniform field
    constants (`M₂`, `Kf`, `K₀` on the single convex phase ball `S` containing every perturbed tube),
    the confinement-driven coefficient deviation `‖DF(Wf 0 τ) − DF((u,0))‖ ≤ M₂·C₀‖v‖`, fed through the
    σ-windowed base-slot near-identity `baseFlow_endpoint_fderiv_near_id_window`, and recentred by the
    base translation `δ ↦ u + δ`.  This is the `hder` clause feeding the `hflowData (i)` contraction. -/
theorem baseFlow_hder_family (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (c₀ : Point n) (Rwin σ : ℝ) (hRwin : 0 ≤ Rwin) (hσ : 0 < σ)
    (hKσ : ∀ u ∈ Metric.closedBall c₀ Rwin, ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K) :
    ∃ Dc Kc : ℝ, 0 ≤ Dc ∧ 0 ≤ Kc ∧
      ∀ u ∈ Metric.closedBall c₀ Rwin, ∃ L : Point n →L[ℝ] Point n,
        HasFDerivAt (fun q => uniformFlowExp g gi hC hK q v) L u ∧
        ‖L - ContinuousLinearMap.id ℝ (Point n)‖ ≤ Dc * Real.exp Kc := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set Rphase : ℝ := C₀ * ‖v‖ + Rwin + σ with hRphasedef
  have hRphase0 : 0 ≤ Rphase := by
    rw [hRphasedef]; have := mul_nonneg hC₀nn (norm_nonneg v); linarith [hσ.le, hRwin]
  set S : Set (Point n × Point n) := Metric.closedBall ((c₀, 0) : Point n × Point n) Rphase with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hSne : S.Nonempty := ⟨(c₀, 0), by rw [hSdef]; exact Metric.mem_closedBall_self hRphase0⟩
  -- window-uniform field constants on the single convex phase ball `S`.
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
  refine ⟨M₂ * (C₀ * ‖v‖), Kf,
    mul_nonneg hM₂0 (mul_nonneg hC₀nn (norm_nonneg _)), hKf0, ?_⟩
  intro u huS
  have hu_c : ‖u - c₀‖ ≤ Rwin := by rw [← dist_eq_norm]; rwa [Metric.mem_closedBall] at huS
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK (u + δ) v with hWfdef
  have hqK : ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K := fun δ hδ => hKσ u huS δ hδ
  -- windowed perturbed-tube ODE / confinement / IC.
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
    calc ‖Wf δ τ - ((c₀, 0) : Point n × Point n)‖
        = ‖(Wf δ τ - (u + δ, 0)) + ((u + δ, 0) - (c₀, 0))‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Wf δ τ - ((u + δ, 0) : Point n × Point n)‖
            + ‖((u + δ, 0) : Point n × Point n) - (c₀, 0)‖ := norm_add_le _ _
      _ ≤ C₀ * ‖v‖ + (Rwin + σ) := add_le_add hconf hb1
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
    exact le_trans hu_c (by rw [hRphasedef]; linarith [mul_nonneg hC₀nn (norm_nonneg v), hσ.le])
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
  -- windowed base-slot near-identity Fréchet derivative at `δ = 0`.
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
  exact ⟨L, hcomp, hbound⟩

/-- **★ J4-731 STEP (2) — the windowed base-displacement Lipschitz bound (concrete).**  Feeding the
    per-base near-identity `hder` family (`baseFlow_hder_family`) into
    `BaseFlowLipTrunc.baseDisplacement_lipschitzOnWith_window_nearId`, the base-displacement map
    `u ↦ uniformFlowExp g gi hC hK u v − u` is `LipschitzOnWith (Dc·e^{Kc}).toNNReal` on the convex base
    window `closedBall c₀ Rwin`, with the SAME window-uniform `Dc = M₂·C₀‖v‖`, `Kc = Kf`.  This is the
    contraction's magnitude input, fully supplied from banked uniform-tube data. -/
theorem baseDisplacement_windowed_lipschitz_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (v : Point n) (hv : ‖v‖ ≤ uniformFlowRadius g gi hC hK)
    (c₀ : Point n) (Rwin σ : ℝ) (hRwin : 0 ≤ Rwin) (hσ : 0 < σ)
    (hKσ : ∀ u ∈ Metric.closedBall c₀ Rwin, ∀ δ : Point n, ‖δ‖ ≤ σ → u + δ ∈ K) :
    ∃ Dc Kc : ℝ, 0 ≤ Dc ∧ 0 ≤ Kc ∧
      LipschitzOnWith (Dc * Real.exp Kc).toNNReal
        (fun u => uniformFlowExp g gi hC hK u v - u) (Metric.closedBall c₀ Rwin) := by
  obtain ⟨Dc, Kc, hDc0, hKc0, hfam⟩ :=
    baseFlow_hder_family g gi hC hK v hv c₀ Rwin σ hRwin hσ hKσ
  exact ⟨Dc, Kc, hDc0, hKc0,
    QIQTH.BaseFlowLipTrunc.baseDisplacement_lipschitzOnWith_window_nearId
      (fun q => uniformFlowExp g gi hC hK q v) (Metric.closedBall c₀ Rwin) Dc Kc hDc0 hKc0
      (convex_closedBall _ _) hfam⟩

end QIQTH.ExpMap

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ExpMap
#check @geodesicBasepoint_endpoint_hasFDerivAt_window
#check @geodesicBasepoint_endpoint_hasFDerivAt_window_exists
#check @geodesicBasepoint_endpoint_position_hasFDerivAt_window_exists
#check @baseFlow_endpoint_fderiv_near_id_window
#check @baseFlow_hder_family
#check @baseDisplacement_windowed_lipschitz_concrete
end AxiomChecks
