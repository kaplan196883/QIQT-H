/-
  BaseFlowNearId — J4-727, J3 BRICK 5: THE BASE-SLOT NEAR-IDENTITY CONTRACTION CORE.

  ODE_VARIATIONAL_PLAN.md / WHITENED_CAMPAIGN_TERMINAL.md.  The w-slot (base-point) analogue of the
  velocity-slot near-identity Jacobian bound `uniformFlowExp_fderiv_near_id_quant`
  (`NearIsometryBudget.lean`), targeting the `hflowData (i)` contraction leg of
  `WhiteHsolveFlowContraction.white_hInnerCont_closed_final8`:

      the base-displacement map `w ↦ φ_w v − w` has a SMALL derivative — its base-point (`w`) Fréchet
      derivative deviates from the identity by `≤ C·‖v‖`, hence is `O(c)`-small on the sphere `‖v‖ = c`.

  ── THE STRUCTURE (mirrors the v-slot `hnearId` block of `NearIsometryBudget.lean`, but perturbing the
     STARTING POINT `q ↦ q+δ` rather than the velocity `v ↦ v+δ`).
     The base-point endpoint Jacobi field `V δ` has flat initial condition `V δ 0 = (δ, 0)` (a pure
     position displacement, zero velocity displacement).  In FLAT space a pure position displacement
     PARALLEL-TRANSPORTS unchanged: the constant field `Jf τ = (δ, 0)` solves the flat Jacobi equation
     `J' = DF((q,0))·J` (because `DF((q,0))·(δ,0) = 0` — the geodesic-field derivative at zero velocity
     kills a pure-position seed).  The DEVIATION `‖(V δ 1).1 − δ‖` of the TRUE endpoint from the flat
     `δ` is then bounded by the two-point Jacobi comparison `jacobi_twopoint_diff_bound`
     (`BasepointJetModulus.lean`) against the constant curve `Y₂ ≡ (q,0)`:
         `‖(V δ 1).1 − δ‖ ≤ Dc · ‖δ‖ · e^K`,
     where `Dc` bounds the Jacobi-coefficient deviation `‖DF(W0 τ) − DF((q,0))‖` along the base geodesic.
     The Christoffel symbols of the geodesic field vanish at the RNC centre `(q,0)`, so `Dc = M₂·β` is
     LINEAR in the confinement radius `β = ‖W0 τ − (q,0)‖` of the base geodesic — which is `O(‖v‖)`.  On
     the sphere `‖v‖ = c` this makes `Dc·e^K = O(c)` small: the base-displacement derivative is a
     contraction for small `c`.

  ── WHAT LANDS HERE (all axiom-clean, std-3, no `sorry`, no new axioms; metric-agnostic `g gi`).

    * `geodesicField_fderiv_center_pos_zero` — the flat-propagation identity `DF((q,0))·(δ,0) = 0`
      (a pure-position seed at zero velocity is annihilated by the geodesic-field derivative).

    * `jacobiEndpoint_base_near_id_bound` — ★ THE CORE DEVIATION BOUND (BRICK 2, `jacobiPropagator_near_id`).
      For a Jacobi field `V` along a base geodesic `W0` with position-seed `V 0 = (δ,0)`, coefficient
      bound `‖DF(W0)‖ ≤ K` and coefficient deviation `‖DF(W0 τ) − DF((q,0))‖ ≤ Dc`,
          `‖(V 1).1 − δ‖ ≤ Dc·‖δ‖·e^K`.
      Metric-agnostic; `Dc` carried as input.

    * `jacobiEndpoint_base_near_id_confined` — ★ BRICK 1 wired in: `Dc = M₂·β` from a supplied
      confinement `‖W0 τ − (q,0)‖ ≤ β` and a C²-field sup bound `M₂` on a convex set, via the
      mean-value inequality on `fderiv (geodesicField)`.  Delivers `‖(V 1).1 − δ‖ ≤ M₂·β·‖δ‖·e^K`.

    * `baseFlow_endpoint_fderiv_near_id` — ★ THE FRÉCHET NEAR-IDENTITY BOUND (BRICK 3, partial).  With
      the full base-point Fréchet-derivative package (`geodesicBasepoint_endpoint_position_hasFDerivAt_exists`,
      `BasepointFDeriv.lean`) plus the uniform coefficient deviation `Dc`, the base-point endpoint-position
      derivative `L = fderiv (fun δ => (W δ 1).1) 0` satisfies `‖L − id‖ ≤ Dc·e^K`.  This is the exact
      base-slot analogue of `uniformFlowExp_fderiv_near_id_quant`, AT the base point.

  HONEST FIREWALL: this is J3 REGULARITY infrastructure — the base-slot near-identity core of the
  `hflowData (i)` contraction.  It is NOT `a₁ = R/6` (still a labelled carrier).  It delivers the
  derivative-AT-THE-CENTRE smallness; it does NOT deliver the GLOBAL Lipschitz-over-`w` bound that
  `ContractingWith` needs (the geodesic flow is near-identity only on the compact window — the global
  contraction requires a base-truncation of `Ψ` off the window, a separate structural step not built
  here; see the file-end note).  It does not build the second-order jet, Raychaudhuri, or numerical `G`.
-/
import Mathlib
import QIQTH.JacobiEquation
import QIQTH.BasepointJetModulus

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-! ### The flat-propagation identity: a pure-position seed at zero velocity is annihilated. -/

/-- **Flat propagation.**  `DF((q,0))·(δ,0) = 0`.  The geodesic-field Fréchet derivative at zero
    velocity, applied to a pure-position seed `(δ,0)`, vanishes: `DF(x,v)(ξ,η) = (η, −jacobiOperator …)`
    with `η = 0`, and `jacobiOperator g gi q 0 δ 0 = 0` because every summand of the Jacobi operator
    carries a velocity factor `v = 0`.  This makes the constant field `τ ↦ (δ,0)` a solution of the flat
    Jacobi equation along the constant curve `τ ↦ (q,0)`. -/
theorem geodesicField_fderiv_center_pos_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (q δ : Point n) :
    fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n) ((δ, 0) : Point n × Point n)
      = (0 : Point n × Point n) := by
  have hjac : jacobiOperator g gi q 0 δ 0 = 0 := by
    funext i; simp [jacobiOperator]
  rw [geodesicField_fderiv_eq_jacobiOperator g gi hC q 0 δ 0, hjac]
  simp

/-! ### BRICK 2 — the core base-slot endpoint deviation bound. -/

/-- **★ J3 brick 5 (core) — the base-slot Jacobi endpoint near-identity deviation.**
    Let `V` be a Jacobi field along the base geodesic `W0` (`V' = DF(W0)·V`) with the pure-position seed
    `V 0 = (δ, 0)`.  If the Jacobi coefficient is bounded `‖DF(W0 τ)‖ ≤ K` and deviates from its centre
    value by `‖DF(W0 τ) − DF((q,0))‖ ≤ Dc`, then the endpoint position component deviates from the flat
    parallel transport `δ` by
        `‖(V 1).1 − δ‖ ≤ Dc·‖δ‖·e^K`.

    Proof: the constant field `Jf τ = (δ,0)` is the FLAT Jacobi field along the constant curve
    `Y₂ ≡ (q,0)` (`geodesicField_fderiv_center_pos_zero`), with the same seed `(δ,0)`.  The two-point
    Jacobi comparison `jacobi_twopoint_diff_bound` (with coefficient deviation `Dc`, seed-field bound
    `‖(δ,0)‖ = ‖δ‖`) gives `‖V 1 − (δ,0)‖ ≤ Dc·‖δ‖·e^K`; the position projection only shrinks the norm.
    Metric-agnostic; `Dc` carried as input (produced by compactness in `..._confined`). -/
theorem jacobiEndpoint_base_near_id_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W0 V : ℝ → Point n × Point n} {q δ : Point n} {K Dc : ℝ} (hK0 : 0 ≤ K)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (W0 τ) (V τ)) τ)
    (hV0 : V 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W0 τ)‖ ≤ K)
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (W0 τ)
        - fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)‖ ≤ Dc) :
    ‖(V 1).1 - δ‖ ≤ Dc * ‖δ‖ * Real.exp K := by
  -- the constant flat comparison field along the constant curve `(q,0)`.
  set Y₂ : ℝ → Point n × Point n := fun _ => ((q, 0) : Point n × Point n) with hY₂
  set Jf : ℝ → Point n × Point n := fun _ => ((δ, 0) : Point n × Point n) with hJf
  have hJ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Jf (fderiv ℝ (geodesicField g gi) (Y₂ τ) (Jf τ)) τ := by
    intro τ _
    have hz : fderiv ℝ (geodesicField g gi) (Y₂ τ) (Jf τ) = 0 := by
      simp only [hY₂, hJf]; exact geodesicField_fderiv_center_pos_zero g gi hC q δ
    rw [hz]; exact hasDerivAt_const τ _
  have h0 : V 0 = Jf 0 := hV0
  have hAd' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (W0 τ) - fderiv ℝ (geodesicField g gi) (Y₂ τ)‖ ≤ Dc := by
    intro τ hτ; simpa only [hY₂] using hAd τ hτ
  have hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf τ‖ ≤ ‖δ‖ := by
    intro τ _; simp only [hJf]; rw [Prod.norm_def]; simp
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hbnd := jacobi_twopoint_diff_bound g gi hK0 hVode hJ2 h0 hKb hAd' hJb 1 ht1
  -- project onto the position component; `Jf 1 = (δ,0)`.
  have hJf1 : (Jf 1).1 = δ := by simp only [hJf]
  have hproj : ‖(V 1).1 - δ‖ ≤ ‖V 1 - Jf 1‖ := by
    have heq : (V 1).1 - δ = (V 1 - Jf 1).1 := by rw [Prod.fst_sub, hJf1]
    rw [heq, Prod.norm_def]; exact le_max_left _ _
  exact le_trans hproj hbnd

/-! ### BRICK 1 wired — the coefficient deviation `Dc = M₂·β` from confinement. -/

/-- **★ J3 brick 5 (confined) — coefficient deviation produced from confinement + C² bound.**  Same as
    the core bound but with `Dc = M₂·β` supplied by geometry: on a convex set `S` on which the second
    derivative of the geodesic field is bounded (`‖∂²F‖ ≤ M₂`), if the base geodesic and the centre both
    lie in `S` and the base geodesic is confined `‖W0 τ − (q,0)‖ ≤ β`, then the coefficient deviation
    `‖DF(W0 τ) − DF((q,0))‖ ≤ M₂·β` by the mean-value inequality on `fderiv (geodesicField)`, giving
        `‖(V 1).1 − δ‖ ≤ M₂·β·‖δ‖·e^K`.
    On the sphere `‖v‖ = c`, `β = O(‖v‖) = O(c)`, so `M₂·β·e^K = O(c)`: the base-displacement derivative
    is a contraction for small `c`. -/
theorem jacobiEndpoint_base_near_id_confined (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W0 V : ℝ → Point n × Point n} {q δ : Point n}
    {S : Set (Point n × Point n)} {M₂ K β : ℝ} (hK0 : 0 ≤ K)
    (hconv : Convex ℝ S)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hcenterS : ((q, 0) : Point n × Point n) ∈ S)
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W0 τ ∈ S)
    (hconf : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖W0 τ - ((q, 0) : Point n × Point n)‖ ≤ β)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt V (fderiv ℝ (geodesicField g gi) (W0 τ) (V τ)) τ)
    (hV0 : V 0 = ((δ, 0) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W0 τ)‖ ≤ K) :
    ‖(V 1).1 - δ‖ ≤ M₂ * β * ‖δ‖ * Real.exp K := by
  have hM₂0 : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) ((q, 0) : Point n × Point n)))
      (hbound2 ((q, 0) : Point n × Point n) hcenterS)
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  have hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (W0 τ)
        - fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)‖ ≤ M₂ * β := by
    intro τ hτ
    have hmvt := hconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hbound2
      hcenterS (hmem τ hτ)
    refine le_trans hmvt ?_
    exact mul_le_mul_of_nonneg_left (hconf τ hτ) hM₂0
  have hbnd := jacobiEndpoint_base_near_id_bound g gi hC hK0 hVode hV0 hKb hAd
  calc ‖(V 1).1 - δ‖ ≤ (M₂ * β) * ‖δ‖ * Real.exp K := hbnd
    _ = M₂ * β * ‖δ‖ * Real.exp K := by ring

/-! ### BRICK 3 (partial) — the base-point Fréchet near-identity operator bound. -/

/-- **★ J3 brick 5 (Fréchet near-identity) — the base-point endpoint derivative is near the identity.**
    The exact base-slot analogue of `uniformFlowExp_fderiv_near_id_quant` (AT the base point).  With the
    full base-point Fréchet-derivative package — a base-perturbation family `W δ` of geodesics
    (`W δ 0 − W 0 0 = (δ,0)`, fixed velocity) and its endpoint Jacobi fields `V δ` (seed `V δ 0 = (δ,0)`)
    on a convex `S` with C² field bound `M₂`, field Lipschitz `K₀`, coefficient bound `K`, tube
    containment — the base-point endpoint-position derivative `L = fderiv (fun δ => (W δ 1).1) 0`
    (constructed by `geodesicBasepoint_endpoint_position_hasFDerivAt_exists`, linear in the seed by
    Jacobi-ODE uniqueness) satisfies, under the uniform coefficient deviation `‖DF(W 0 τ) − DF((q,0))‖ ≤ Dc`,
        `‖L − id‖ ≤ Dc·e^K`.

    Proof: each seed `δ` gives `‖L δ − δ‖ = ‖(V δ 1).1 − δ‖ ≤ (Dc·e^K)·‖δ‖` by the core deviation bound
    (`jacobiEndpoint_base_near_id_bound`); `opNorm_le_bound` assembles the operator inequality.  This is
    the derivative-AT-THE-CENTRE smallness feeding the `hflowData (i)` contraction. -/
theorem baseFlow_endpoint_fderiv_near_id (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n} {q : Point n}
    {S : Set (Point n × Point n)} {M₂ K Dc : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K) (hDc0 : 0 ≤ Dc)
    (hconv : Convex ℝ S)
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
    (hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (W 0 τ)
        - fderiv ℝ (geodesicField g gi) ((q, 0) : Point n × Point n)‖ ≤ Dc) :
    ∃ L : Point n →L[ℝ] Point n,
      HasFDerivAt (fun δ => (W δ 1).1) L 0 ∧
      ‖L - ContinuousLinearMap.id ℝ (Point n)‖ ≤ Dc * Real.exp K := by
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  obtain ⟨L, hLeq, hFD⟩ := geodesicBasepoint_endpoint_position_hasFDerivAt_exists g gi hC hK0 ht1
    hconv hbound2 hLip hWode hVode hV0 hIC hKb hmem
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

end QIQTH.ExpMap
