/-
  VelocitySecondJetId — J4-33: the VELOCITY-slot first- and second-order jets of the geodesic-flow
  ENDPOINT map, at an arbitrary base velocity, mirroring the fully-built BASE-POINT jet tower one
  direction-slot over (velocity seed `(0,δ)` instead of the position seed `(δ,0)`).

  ## Context

  `FlowVelocityJacobiField` (J4-32) reduced `(J)` / the unconditional common exp-nondeg radius over a
  compact `K` (via `expMap_common_nondeg_radius_of_velocity_ode_data`) to the SINGLE residual input
  `hid` — the second-order velocity jet IDENTIFICATION

    `hid : (fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = (Zf q v a b 1).1`,

  i.e. the flow-endpoint velocity 2-jet `fderiv²(Fam q)(v)` applied to a direction pair `(a,b)` equals
  the POSITION endpoint of the second-order velocity variation field `Zf`.  `Fam q = F_q` is the
  uniform-confinement flow endpoint (`= expMap g gi hC q` on the overlap, via `UniformFlowBridge`),
  which is `C⁴` (`ExpMapContDiffFour`).

  The BASE-POINT jet tower (`BasepointFDeriv`, `BasepointSecondJetFDeriv`, `BasepointJacobi2`) built
  the analogue in the POSITION slot: for a family `W : Point n → ℝ → State` perturbed in the POSITION
  slot (`W δ 0 − W 0 0 = (δ,0)`), the endpoint `δ ↦ W δ t` has a first Fréchet derivative equal to the
  endpoint Jacobi field `V δ t` (J-c) and a second-order Taylor expansion with a cubic remainder whose
  bilinear coefficient is `fderiv²(δ↦W δ t)|₀` (J-d, brick 1).  That tower STOPPED SHORT of linking the
  bilinear coefficient to an ODE endpoint object.

  This file carries the SAME arc one direction-slot over — the VELOCITY slot — where the perturbation
  seed is `(0,δ)` (perturbing the initial VELOCITY) instead of `(δ,0)`.  The first-order variation
  machinery is already direction-agnostic (`geodesicVariation_exists_dir`, `jacobiSol_unique`), so this
  is a re-derivation with the seed swapped, NOT new analysis.

  ## What lands here (DERIVED; no `sorry`, no hyp = conclusion)

  * `flowVelocity_endpoint_hasFDerivAt` / `flowVelocity_endpoint_hasFDerivAt_exists`
    — **(h1) the VELOCITY-slot first Fréchet derivative of the flow endpoint.**  For a velocity-seeded
    family (`W δ 0 − W 0 0 = (0,δ)`) with velocity Jacobi fields `V δ` (`V δ 0 = (0,δ)`) along the base
    geodesic `W 0`, the endpoint `δ ↦ W δ t` has Fréchet derivative the endpoint velocity Jacobi map
    `δ ↦ V δ t` at the base increment `0`.  The verbatim velocity-slot analogue of
    `geodesicBasepoint_endpoint_hasFDerivAt_exists` (`jacobiSol_unique` linearity + the uniform-in-
    direction little-o), with `(δ,0)` replaced by `(0,δ)`.

  * `flowVelocity_endpoint_position_hasFDerivAt_exists` — the position-component projection of (h1).

  * `flowVelocity_endpoint_secondOrder_taylor` / `flowVelocity_endpoint_position_secondOrder_taylor`
    — **(h2) the VELOCITY-slot SECOND-order Taylor expansion of the flow endpoint, with cubic
    remainder**, the linear term identified as the first-order velocity Jacobi endpoint field `V δ t`:
        `‖W δ t − W 0 t − V δ t − ½·(fderiv²(δ'↦W δ' t)|₀ δ) δ‖ ≤ M·‖δ‖³`.
    DERIVED by welding `DecayOrderThree.decay_order_three_remainder_convex` with (h1), the velocity-slot
    mirror of `geodesicBasepoint_endpoint_secondOrder_taylor`.

  ## The residual `(h3)` — the ODE identification (FIREWALLED, NOT built here)

  What (h2) delivers is the velocity 2-jet's bilinear coefficient `fderiv²(δ'↦W δ' t)|₀` with its LINEAR
  term pinned to the first Jacobi field.  It does NOT identify that bilinear coefficient's value on
  `(a,b)` with the endpoint `(Zf … 1).1` of a second-order variation FIELD solving the inhomogeneous
  linearized geodesic ODE (`jacobiVariation_secondOrder`'s ODE).  That link — `(h3)` —

    `(fderiv ℝ (fun w => fderiv ℝ (Fam q) w) v) a b = (Zf q v a b 1).1`  (= `hid`),

  is the genuinely-new content the whole base-point/velocity jet tower stops short of: it requires
  either (i) a genuine SECOND-variation argument producing a Taylor expansion whose QUADRATIC term is an
  ODE endpoint (not merely an abstract bilinear form), or (ii) smooth dependence of the first velocity
  Jacobi field `V_{q,w,a}` on the base velocity `w`, differentiating the FIRST-order identification
  `fderiv(Fam q)(w)(a) = (V_{q,w,a} 1).1` once more and matching `∂_w V` to the second-order variation
  field.  Neither is present in the codebase.

  HONEST CHECKPOINT (binding).  This lands the VELOCITY-slot first jet (h1) and second-order Taylor jet
  (h2), DERIVED, carrying only the SAME genuine geometric-regularity / supplied-Jacobi-field data the
  base-point tower carries — one direction-slot over.  It REDUCES `hid`/`(J)` to the single genuine ODE-
  identification input `(h3)` above (the value-of-the-bilinear-coefficient = variation-field-endpoint
  link) and does NOT smuggle `hid`/`hbnd`/`hFoplip`/`hunif`.  It does NOT build `(h3)`, NOT the covariant
  `D²/dτ²`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.FlowVelocityJacobiField
import QIQTH.BasepointSecondJetFDeriv
import QIQTH.BasepointFDeriv
import QIQTH.BasepointJacobi2
import QIQTH.DecayOrderThree
import QIQTH.UniformFlowBridge
import QIQTH.ExpMapContDiffFour
import QIQTH.JacobiEquation
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **(h1, core) — VELOCITY-slot first Fréchet derivative of the geodesic-flow endpoint.**
    For a velocity-perturbation-indexed family `W : Point n → ℝ → State` of geodesics
    (`W δ 0 − W 0 0 = (0, δ)`, i.e. the INITIAL VELOCITY is perturbed linearly, the base point fixed)
    and velocity Jacobi solutions `V δ` along the base geodesic `W 0` with `V δ 0 = (0, δ)`, given a
    CONTINUOUS-LINEAR `L` representing the endpoint velocity Jacobi map (`∀ δ, L δ = V δ t`), the
    endpoint `fun δ => W δ t` has Fréchet derivative `L` at the base increment (`δ = 0`).

    The verbatim velocity-slot analogue of `geodesicBasepoint_endpoint_hasFDerivAt` with the position
    seed `(δ, 0)` replaced by the velocity seed `(0, δ)` (`‖(0,δ)‖ = ‖δ‖` too, so the quantitative
    little-o is unchanged). -/
theorem flowVelocity_endpoint_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
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
    have hnorm : ‖((0, δ) : Point n × Point n)‖ = ‖δ‖ := by
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

/-- **(h1, capstone) — the VELOCITY-slot first Fréchet derivative EXISTS, its continuous-linear map
    CONSTRUCTED.**  Same hypotheses as the core minus the supplied `L`.  The endpoint velocity Jacobi
    map `δ ↦ V δ t` is additive and homogeneous (`jacobiSol_unique` applied to the sum / scalar multiple
    of velocity Jacobi solutions, each again a Jacobi solution with the matching velocity seed
    `(0, δ₁+δ₂)` resp. `(0, c·δ)`), hence a `LinearMap`, promoted to a `ContinuousLinearMap` by finite-
    dimensionality of `Point n`.  Delivers `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`,
    fully DERIVED — the verbatim velocity-slot analogue of
    `geodesicBasepoint_endpoint_hasFDerivAt_exists`. -/
theorem flowVelocity_endpoint_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
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
  -- package the endpoint velocity Jacobi map as a continuous-linear map.
  let Lₗ : Point n →ₗ[ℝ] Point n × Point n :=
    { toFun := fun δ => V δ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun δ => rfl, ?_⟩
  exact flowVelocity_endpoint_hasFDerivAt g gi hC hK0 ht hconv hbound2 hLip hWode hVode
    hV0 hIC hKb hmem (fun δ => rfl)

/-- **(h1, position) — the VELOCITY-slot endpoint-position first Fréchet derivative.**  Projecting the
    velocity-slot base-increment endpoint Fréchet derivative onto the position component:
    `∃ L, (∀ δ, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0`.  At `t = 1` this is the
    velocity-slot Fréchet derivative of the exp-map-shaped geodesic-endpoint position `Fam q`
    (`w ↦ (Y_{q,w} 1).1`) at the base velocity, once the family is centred at that velocity. -/
theorem flowVelocity_endpoint_position_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] Point n,
      (∀ δ : Point n, L δ = (V δ t).1) ∧ HasFDerivAt (fun δ => (W δ t).1) L 0 := by
  obtain ⟨L, hLeq, hFD⟩ := flowVelocity_endpoint_hasFDerivAt_exists g gi hC hK0 ht hconv
    hbound2 hLip hWode hVode hV0 hIC hKb hmem
  refine ⟨(ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L, fun δ => ?_, ?_⟩
  · simp [hLeq δ]
  · have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [Function.comp] using this

/-- **(h2) — VELOCITY-slot SECOND-ORDER Taylor expansion of the geodesic-flow endpoint, with the linear
    term identified as the first-order velocity Jacobi endpoint field.**

    For a velocity-seeded family `W` (`W δ 0 − W 0 0 = (0,δ)`) with velocity Jacobi solutions `V δ`
    (`V δ 0 = (0,δ)`) along the base geodesic `W 0`, and given the base-increment (`δ`-side) C²
    regularity of the endpoint map `δ' ↦ W δ' t` on a convex neighbourhood `Sδ ∋ 0`
    (`hEdiff`, `hEdiff2`, base-increment symmetry `hEsymm`, second-derivative Lipschitz constant `M`
    `hElip2`), the endpoint map obeys the second-order Taylor expansion with cubic remainder:
        `‖W δ t − W 0 t − V δ t − ½·(fderiv²(δ'↦W δ' t)|₀ δ) δ‖ ≤ M·‖δ‖³`.

    DERIVED by welding `DecayOrderThree.decay_order_three_remainder_convex` (at `a = δ`, `b = 0`) with
    (h1) `flowVelocity_endpoint_hasFDerivAt_exists`: the latter's `HasFDerivAt (δ'↦W δ' t) L 0` gives
    `fderiv(δ'↦W δ' t)|₀ = L` (`HasFDerivAt.fderiv`), and `L δ = V δ t` identifies the analytic linear
    term with the first-order velocity Jacobi endpoint field.  The verbatim velocity-slot analogue of
    `geodesicBasepoint_endpoint_secondOrder_taylor`. -/
theorem flowVelocity_endpoint_secondOrder_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {Sδ : Set (Point n)} {M₂ K M : ℝ} {K₀ : NNReal}
    (hK0 : 0 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hconv : Convex ℝ S) (hconvδ : Convex ℝ Sδ)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hEdiff : ∀ x ∈ Sδ, DifferentiableAt ℝ (fun d => W d t) x)
    (hEdiff2 : ∀ x ∈ Sδ, DifferentiableAt ℝ (fderiv ℝ (fun d => W d t)) x)
    (hElip2 : ∀ z ∈ Sδ,
      ‖fderiv ℝ (fderiv ℝ (fun d => W d t)) z - fderiv ℝ (fderiv ℝ (fun d => W d t)) 0‖
        ≤ M * ‖z - 0‖)
    (hEsymm : IsSymmSndFDerivAt ℝ (fun d => W d t) 0)
    {δ : Point n} (hδmem : δ ∈ Sδ) (h0mem : (0 : Point n) ∈ Sδ) :
    ‖W δ t - W 0 t - V δ t
        - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ‖ ≤ M * ‖δ‖ ^ 3 := by
  -- (i) cubic Taylor remainder of the endpoint map at `a = δ`, `b = 0`.
  have hlem := decay_order_three_remainder_convex (fun d => W d t) M hconvδ
    hEdiff hEdiff2 hElip2 hδmem h0mem hEsymm
  simp only [sub_zero] at hlem
  -- (ii) (h1): the analytic linear term equals the first-order velocity Jacobi endpoint field `V δ t`.
  obtain ⟨L, hLeq, hFD⟩ := flowVelocity_endpoint_hasFDerivAt_exists g gi hC hK0 ht hconv
    hbound2 hLip hWode hVode hV0 hIC hKb hmem
  have hfd0 : fderiv ℝ (fun d => W d t) 0 = L := hFD.fderiv
  rw [hfd0, hLeq δ] at hlem
  exact hlem

/-- **(h2, position) — the exp-map-shaped VELOCITY-slot second-order Taylor expansion of the geodesic-
    endpoint POSITION.**  Projecting (h2) onto the position component: linear term the velocity Jacobi
    position field `(V δ t).1`, quadratic coefficient the position part of the base-increment second-
    order bilinear jet,
        `‖(W δ t).1 − (W 0 t).1 − (V δ t).1 − ½·((fderiv²(δ'↦W δ' t)|₀ δ) δ).1‖ ≤ M·‖δ‖³`.
    At `t = 1` this is the velocity-slot second-order Taylor expansion of the exp-map-shaped geodesic-
    endpoint position `Fam q` — the shape whose bilinear coefficient's endpoint the residual `(h3)`
    identifies with the ODE object `Zf`. -/
theorem flowVelocity_endpoint_position_secondOrder_taylor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {Sδ : Set (Point n)} {M₂ K M : ℝ} {K₀ : NNReal}
    (hK0 : 0 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hconv : Convex ℝ S) (hconvδ : Convex ℝ Sδ)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (geodesicField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n))
    (hIC : ∀ δ : Point n, W δ 0 - W 0 0 = ((0, δ) : Point n × Point n))
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hEdiff : ∀ x ∈ Sδ, DifferentiableAt ℝ (fun d => W d t) x)
    (hEdiff2 : ∀ x ∈ Sδ, DifferentiableAt ℝ (fderiv ℝ (fun d => W d t)) x)
    (hElip2 : ∀ z ∈ Sδ,
      ‖fderiv ℝ (fderiv ℝ (fun d => W d t)) z - fderiv ℝ (fderiv ℝ (fun d => W d t)) 0‖
        ≤ M * ‖z - 0‖)
    (hEsymm : IsSymmSndFDerivAt ℝ (fun d => W d t) 0)
    {δ : Point n} (hδmem : δ ∈ Sδ) (h0mem : (0 : Point n) ∈ Sδ) :
    ‖(W δ t).1 - (W 0 t).1 - (V δ t).1
        - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ).1‖ ≤ M * ‖δ‖ ^ 3 := by
  have hfull := flowVelocity_endpoint_secondOrder_taylor g gi hC hK0 ht hconv hconvδ
    hbound2 hLip hWode hVode hV0 hIC hKb hmem hEdiff hEdiff2 hElip2 hEsymm hδmem h0mem
  set Z : Point n × Point n := W δ t - W 0 t - V δ t
      - (1/2 : ℝ) • (fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ with hZ
  have hproj : (W δ t).1 - (W 0 t).1 - (V δ t).1
      - (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ (fun d => W d t)) 0 δ) δ).1 = Z.1 := by
    rw [hZ]; simp [Prod.fst_sub, Prod.smul_fst]
  rw [hproj]
  calc ‖Z.1‖ ≤ ‖Z‖ := by
        rw [Prod.norm_def]; exact le_max_left _ _
    _ ≤ M * ‖δ‖ ^ 3 := hfull

end QIQTH.ExpMap
