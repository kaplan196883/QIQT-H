/-
  UniformFlowSecondFDeriv — J4-66 (Brick-A β, R2 climb): the ABSTRACT σ-windowed Fréchet FIRST-JET
  theorem for a general autonomous C²-field, the reusable ENABLER of the second-order Fréchet
  regularity of `uniformFlowExp` (R2).

  ## Context

  * K2 (`UniformFlowFDeriv`, `uniformFlowExp_hasFDerivAt`, J4-55) proved the FIRST-order Fréchet
    derivative of `uniformFlowExp` via the geodesicField-SPECIFIC σ-windowed first-jet little-o
    `flowVelocity_endpoint_hasFDerivAt_window(_exists)`.
  * R1 (`UniformFlowSecondJet`, `uniformFlowTube_secondVariation_uniform_bound`, J4-65) built the
    intrinsic SECOND-variation field `Zf` along the uniform tube with a uniform quadratic Grönwall bound.
  * `hid_of_doubled_data` (`JacobiOperatorFDeriv`) identifies the VALUE of the jet map's Fréchet
    derivative `(fderiv ℝ (fun w => fderiv ℝ Fam w) v) a b = (Zf a b 1).1` but PRESUPPOSES the jet-map
    differentiability `hdiff : DifferentiableAt ℝ (fun w => fderiv ℝ Fam w) v` — the exact object R2
    needs and which the FIRST-jet machinery does NOT supply.

  ## Why this file (route to R2, per GPT-5.5 consult)

  The clean route to `hdiff` at the FULL uniform radius `ρ_K/2` (NO `expRho`) is to establish Fréchet
  (not merely directional) differentiability of the DOUBLED-flow endpoint in the base velocity, i.e. to
  run the K2 σ-windowed first-jet argument ONE ORDER UP on the doubled field
  `G = doubledField g gi`, `G(P,W) = (F P, DF(P)·W)`.  The abstract autonomous engine
  (`QIQTH.AutonomousDep.autonomousField_variation_exists_uncond`) delivers only the DIRECTIONAL
  (scalar `s`) `HasDerivAt`; the Fréchet/operator-valued upgrade — the exact analogue of K2's
  `flowVelocity_endpoint_hasFDerivAt_window(_exists)` but field-AGNOSTIC — does not exist in the
  codebase.  This file builds it.

  ## What lands here (S1/S2 enabler; DERIVED; no `sorry`, no hyp = conclusion, no `expRho`)

  * `autonomousLinODE_unique` — **abstract linear-ODE (Jacobi) uniqueness.**  Two solutions of the
    linearized ODE `J' = DΦ(Y0)·J` along a `Φ`-integral curve `Y0` that agree at `0` agree on `[0,1]`.
    Abstract mirror of `jacobiSol_unique`, via `autonomousField_variation_residual_bound` with the
    first-order remainder forced to `0`.

  * `autonomousFlow_endpoint_hasFDerivAt_window` — **the abstract σ-windowed Fréchet first-jet CORE.**
    For a perturbation `δ ∈ P` injected into the phase space `E` by a norm-preserving `seed`, a family
    `W δ` of `Φ`-integral curves on the window `‖δ‖ ≤ σ` with `W δ 0 − W 0 0 = seed δ`, and GLOBALLY
    defined linearized solutions `V δ` (`V δ 0 = seed δ`), given a continuous-linear `L` representing
    the endpoint linearized map (`∀ δ, L δ = V δ t`), the endpoint `δ ↦ W δ t` has Fréchet derivative
    `L` at `0`.  DERIVED via the per-direction quadratic remainder
    `‖W δ t − W 0 t − V δ t‖ ≤ Ctot·‖δ‖²` (`autonomous_twopoint_gronwall` +
    `decay_order_two_remainder_convex` + `autonomousField_variation_residual_bound`) — the field-
    agnostic mirror of K2's window core.

  * `autonomousFlow_endpoint_hasFDerivAt_window_exists` — **the abstract capstone, its CLM CONSTRUCTED.**
    The endpoint linearized map `δ ↦ V δ t` is additive and homogeneous (`autonomousLinODE_unique` on
    sums / scalar multiples of linearized solutions), hence a `LinearMap`, promoted to a
    `ContinuousLinearMap` by finite-dimensionality of `P`.  Delivers
    `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`.

  ## HONEST CHECKPOINT (binding) — what R2 still needs on top of this

  This lands the ABSTRACT Fréchet first-jet enabler (the field-agnostic K2, one order up).  It does NOT
  yet land R2 (`∃ B₂, HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w) B₂ v`).  Applying
  the capstone with `Φ := doubledField g gi` to obtain `hdiff` requires, still firewalled:
    * (R2-a) the base-velocity-perturbed CONFINED doubled uniform-tube supply — the family
      `Wf δ = (uniformFlowTube q (v+δ), G-Jacobi seeded (0,b))` as genuine `G`-integral curves on the
      window, confined in a compact convex product ball (base ball via K1; Jacobi ball via Grönwall),
      with the base-velocity linear IC `Wf δ 0 − Wf 0 0 = ((0,δ),(0,0))` and the base-doubled-curve
      linearized field `Vf δ` (padded-continuous base ⟹ `doubledVariation_narrowpad_hasDerivAt_Icc`);
    * (R2-b) the identification `fderiv ℝ (uniformFlowExp g gi hC hK q) w = ` the velocity-Jacobi
      endpoint operator, so that the doubled-flow endpoint `.2.1` component IS `fderiv (uniformFlowExp
      q) w b`, feeding `hdiff` for the jet map `w ↦ fderiv (uniformFlowExp q) w`;
    * (R2-c) the curried bilinear CLM assembly of `B₂ : Point n →L (Point n →L Point n)` from the mixed
      endpoint map `(δ,b) ↦ (Zf 1).1` (R1's `Zf`), and the transfer to R2/R3.
  It does NOT touch Raychaudhuri (L3) or `a₁ = R/6`.
-/
import QIQTH.UniformFlowSecondJet
import QIQTH.UniformFlowFDeriv
import QIQTH.JacobiOperatorFDeriv
import QIQTH.JacobiOperatorBaseDeriv
import QIQTH.GenericJacobiExists
import QIQTH.UniformFlowNondeg
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 4000000

/-! ### Abstract linear-ODE (Jacobi) uniqueness -/

section AbstractUnique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abstract linear-ODE (Jacobi) uniqueness.**  Let `Y0` be an integral curve of `Φ : E → E` on
    `[0,1]` with the linearized coefficient bounded `‖DΦ(Y0 τ)‖ ≤ K`.  Any two solutions `J₁, J₂` of the
    linearized ODE `J' = DΦ(Y0)·J` along `Y0` agreeing at `0` agree on `[0,1]`.  Abstract mirror of
    `jacobiSol_unique`: the difference is a linearized solution with zero initial value, so
    `autonomousField_variation_residual_bound` (both endpoint curves `= Y0`, forcing the first-order
    remainder `C = 0`) gives `‖J₁ t − J₂ t‖ ≤ 0`. -/
theorem autonomousLinODE_unique (Φ : E → E) {K : ℝ} (hK0 : 0 ≤ K)
    {Y0 J₁ J₂ : ℝ → E}
    (hY0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Y0 (Φ (Y0 τ)) τ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (Y0 τ)‖ ≤ K)
    (hJ1 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J₁ (fderiv ℝ Φ (Y0 τ) (J₁ τ)) τ)
    (hJ2 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt J₂ (fderiv ℝ Φ (Y0 τ) (J₂ τ)) τ)
    (h0 : J₁ 0 = J₂ 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    J₁ t = J₂ t := by
  have hD : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun σ => J₁ σ - J₂ σ)
        (fderiv ℝ Φ (Y0 τ) ((fun σ => J₁ σ - J₂ σ) τ)) τ := by
    intro τ hτ
    simpa [map_sub] using (hJ1 τ hτ).sub (hJ2 τ hτ)
  have hD0 : Y0 0 - Y0 0 - (fun σ => J₁ σ - J₂ σ) 0 = 0 := by simp [h0]
  have hNb0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ (Y0 τ) - Φ (Y0 τ) - fderiv ℝ Φ (Y0 τ) (Y0 τ - Y0 τ)‖ ≤ 0 := by
    intro τ _; simp
  have hbnd := autonomousField_variation_residual_bound Φ hK0 (le_refl (0 : ℝ))
    hY0 hY0 hD hD0 hKb hNb0 t ht
  simp only [sub_self, zero_sub, norm_neg, zero_mul] at hbnd
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hbnd)

end AbstractUnique

/-! ### The abstract σ-windowed Fréchet first-jet -/

section AbstractFirstJet

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Abstract σ-windowed Fréchet first-jet of the autonomous-flow endpoint (CORE).**

    The field-agnostic mirror of K2's `flowVelocity_endpoint_hasFDerivAt_window`.  Perturbations
    `δ : P` are injected into the phase space `E` by a norm-preserving `seed` (`‖seed δ‖ = ‖δ‖`); the
    perturbed integral curves `W δ` of `Φ` satisfy `W δ 0 − W 0 0 = seed δ` on the window `‖δ‖ ≤ σ`,
    while the linearized solutions `V δ` (`V δ 0 = seed δ`) along the fixed base curve `W 0` are
    GLOBALLY defined; given a continuous-linear `L` with `∀ δ, L δ = V δ t`, the endpoint
    `δ ↦ W δ t` has Fréchet derivative `L` at `0`.  DERIVED via the per-direction quadratic remainder
    `‖W δ t − W 0 t − V δ t‖ ≤ Ctot·‖δ‖²` (`Ctot = M₂·(e^{K₀})²·e^K`) from the two-point Grönwall, the
    convex-set C² Taylor remainder, and the residual Grönwall — the `HasFDerivAt` little-o at `0`. -/
theorem autonomousFlow_endpoint_hasFDerivAt_window (Φ : E → E)
    {W V : P → ℝ → E} {L : P →L[ℝ] E} {seed : P → E}
    {S : Set E} {M₂ K σ : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ Φ) x)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ Φ S)
    (hseednorm : ∀ δ : P, ‖seed δ‖ = ‖δ‖)
    (hWode : ∀ δ : P, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (Φ (W δ τ)) τ)
    (hVode : ∀ δ : P, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ Φ (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : P, V δ 0 = seed δ)
    (hIC : ∀ δ : P, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = seed δ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : P, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S)
    (hLeq : ∀ δ : P, L δ = V δ t) :
    HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : P)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ Φ) (W 0 0)))
      (hbound2 (W 0 0) (hmem 0 h0σ 0 (Set.left_mem_Icc.mpr zero_le_one)))
  set Ctot : ℝ := M₂ * (Real.exp K₀) ^ 2 * Real.exp K with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  -- per-direction quadratic remainder, on the window.
  have hquad : ∀ δ : P, ‖δ‖ ≤ σ → ‖W δ t - W 0 t - V δ t‖ ≤ Ctot * ‖δ‖ ^ 2 := by
    intro δ hδσ
    have hNb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖Φ (W δ τ) - Φ (W 0 τ) - fderiv ℝ Φ (W 0 τ) (W δ τ - W 0 τ)‖
          ≤ M₂ * (‖δ‖ * Real.exp K₀) ^ 2 := by
      intro τ hτ
      have htp := autonomous_twopoint_gronwall Φ hLip (hWode δ hδσ) (hWode 0 h0σ)
        (hmem δ hδσ) (hmem 0 h0σ) τ hτ
      have hd0 : dist (W δ 0) (W 0 0) = ‖δ‖ := by
        rw [dist_eq_norm, hIC δ hδσ, hseednorm]
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
      have hrem := decay_order_two_remainder_convex Φ M₂ hconv hdiff hdiff2 hbound2
        (hmem δ hδσ τ hτ) (hmem 0 h0σ τ hτ)
      refine hrem.trans ?_
      have hsq : ‖W δ τ - W 0 τ‖ ^ 2 ≤ (‖δ‖ * Real.exp K₀) ^ 2 := by
        have := mul_le_mul hLb hLb (norm_nonneg _) (by positivity)
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left hsq hnn
    have h0 : W δ 0 - W 0 0 - V δ 0 = 0 := by rw [hIC δ hδσ, hV0 δ]; abel
    have hbnd := autonomousField_variation_residual_bound Φ hK0
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

variable [FiniteDimensional ℝ P]

/-- **Abstract σ-windowed Fréchet first-jet, its CLM CONSTRUCTED (capstone).**  Same window as the core
    minus the supplied `L`, with `seed` a `ContinuousLinearMap`.  The endpoint linearized map
    `δ ↦ V δ t` is additive and homogeneous (`autonomousLinODE_unique` on sums / scalar multiples of the
    globally defined linearized solutions along the fixed base `W 0`), hence a `LinearMap`, promoted to a
    `ContinuousLinearMap` by finite-dimensionality of `P`.  Delivers
    `∃ L, (∀ δ, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0`. -/
theorem autonomousFlow_endpoint_hasFDerivAt_window_exists (Φ : E → E)
    {W V : P → ℝ → E} {seed : P →L[ℝ] E}
    {S : Set E} {M₂ K σ : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ Φ x)
    (hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ Φ) x)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ Φ S)
    (hseednorm : ∀ δ : P, ‖seed δ‖ = ‖δ‖)
    (hWode : ∀ δ : P, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (Φ (W δ τ)) τ)
    (hVode : ∀ δ : P, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ Φ (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : P, V δ 0 = seed δ)
    (hIC : ∀ δ : P, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = seed δ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ Φ (W 0 τ)‖ ≤ K)
    (hmem : ∀ δ : P, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : P →L[ℝ] E, (∀ δ : P, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : P)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  -- additivity of `δ ↦ V δ t` from linearized-ODE uniqueness.
  have hadd : ∀ a b : P, V a t + V b t = V (a + b) t := by
    intro a b
    refine autonomousLinODE_unique Φ hK0 (hWode 0 h0σ) hKb (J₁ := fun σ' => V a σ' + V b σ')
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b), map_add]
  -- homogeneity of `δ ↦ V δ t` from linearized-ODE uniqueness.
  have hsmul : ∀ (c : ℝ) (a : P), c • V a t = V (c • a) t := by
    intro c a
    refine autonomousLinODE_unique Φ hK0 (hWode 0 h0σ) hKb (J₁ := fun σ' => c • V a σ')
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a), map_smul]
  let Lₗ : P →ₗ[ℝ] E :=
    { toFun := fun δ => V δ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun δ => rfl, ?_⟩
  exact autonomousFlow_endpoint_hasFDerivAt_window Φ hK0 hσ ht hconv hdiff hdiff2 hbound2 hLip
    hseednorm hWode hVode hV0 hIC hKb hmem (fun δ => rfl)

end AbstractFirstJet

/-! ### Specialization to the doubled field — the base-velocity Fréchet first-jet of the doubled flow -/

section DoubledFlow

variable {n : ℕ}

/-- **Base-velocity Fréchet first-jet of the DOUBLED flow endpoint (the R2 consumer).**  Specializes the
    abstract capstone `autonomousFlow_endpoint_hasFDerivAt_window_exists` to `Φ := doubledField g gi`
    over a compact convex phase set `S`, DISCHARGING all of `G`'s field-regularity inputs
    (`hdiff`/`hdiff2` from `contDiff_doubledField`; `hbound2` from `doubledField_fderiv2_bddOn_compact`;
    `hLip` from `doubledField_fderiv_bddOn_compact` + `Convex.lipschitzOnWith_of_nnnorm_fderiv_le`;
    `hKb` from the `DG` sup along the base curve).  Given a family `W δ` of doubled integral curves on
    the window `‖δ‖ ≤ σ` whose base IC is perturbed linearly `W δ 0 − W 0 0 = seed δ` (norm-preserving
    injection `seed`), and GLOBALLY defined doubled-linearized solutions `V δ` (`V δ 0 = seed δ`) along
    the fixed base doubled curve `W 0`, the doubled-flow endpoint `δ ↦ W δ t` is Fréchet-differentiable
    at `0`, its derivative the continuous-linear endpoint linearized map `δ ↦ V δ t`.

    This is EXACTLY the engine the R2 climb consumes when fed the base-velocity-perturbed confined
    doubled uniform-tube supply (R2-a, still firewalled — see module checkpoint): its `.2.1` component,
    once identified with `fderiv (uniformFlowExp q) (v+δ) b` (R2-b), yields the jet-map differentiability
    `hdiff` at the FULL uniform radius, NO `expRho`.  Carries only `hC` + the genuine tube ODE/IC/
    confinement data + the supplied doubled-linearized field. -/
theorem doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → (Point n × Point n) × (Point n × Point n)}
    {seed : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n)}
    {S : Set ((Point n × Point n) × (Point n × Point n))} {σ : ℝ}
    (hScompact : IsCompact S) (hSconvex : Convex ℝ S) (hσ : 0 < σ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hseednorm : ∀ δ : Point n, ‖seed δ‖ = ‖δ‖)
    (hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ) (doubledField g gi (W δ τ)) τ)
    (hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (doubledField g gi) (W 0 τ) (V δ τ)) τ)
    (hV0 : ∀ δ : Point n, V δ 0 = seed δ)
    (hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = seed δ)
    (hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S) :
    ∃ L : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n),
      (∀ δ : Point n, L δ = V δ t) ∧ HasFDerivAt (fun δ => W δ t) L 0 := by
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  -- (a) `G = doubledField` is `C^∞`; discharge the engine's regularity inputs.
  have hGcd : ContDiff ℝ (⊤ : WithTop ℕ∞) (doubledField g gi) := contDiff_doubledField g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ (doubledField g gi) x :=
    fun x _ => (hGcd.differentiable (by simp)).differentiableAt
  have hGcd' : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (doubledField g gi)) :=
    hGcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ (fderiv ℝ (doubledField g gi)) x :=
    fun x _ => (hGcd'.differentiable (by simp)).differentiableAt
  obtain ⟨M₂, _hM₂0, hbound2⟩ := doubledField_fderiv2_bddOn_compact g gi hC hScompact
  obtain ⟨Kf, hKf0, hKfbd⟩ := doubledField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀ (doubledField g gi) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (doubledField g gi) (W 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKfbd (W 0 τ) (hmem 0 h0σ τ hτ)
  -- (b) apply the abstract Fréchet first-jet capstone to `Φ := doubledField g gi`.
  exact autonomousFlow_endpoint_hasFDerivAt_window_exists (doubledField g gi) hKf0 hσ ht hSconvex
    hdiff hdiff2 hbound2 hLip hseednorm hWode hVode hV0 hIC hKb hmem

end DoubledFlow

end QIQTH.ExpMap
