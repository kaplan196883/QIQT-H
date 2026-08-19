/-
  GeodesicJointFDerivAtPointLocal — the JOINT (base + velocity) FULL-PHASE-SPACE Fréchet derivative of
  the geodesic flow at an ARBITRARY base point `ξ₀`, with the perturbation family quantified only over a
  BOUNDED BALL `Metric.ball ξ₀ r` around the base point (NOT the whole phase space).

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  WHY THIS FILE EXISTS — the vacuity of the GLOBAL Task A (J4-847), and its fix.

  `GeodesicJointFDerivAtPoint.geodesicFlow_joint_hasFDerivAt_exists_atPoint` (Task A, global) — and its
  origin core `GeodesicBasepointFrechet.geodesicFlow_joint_hasFDerivAt(_exists)` — quantify the perturbed
  geodesic family over the WHOLE phase space:
      `hmem : ∀ ξ : Point n × Point n, ∀ τ ∈ [0,1], W ξ τ ∈ S`
      `hIC  : ∀ ξ, W ξ 0 − W ξ₀ 0 = ξ − ξ₀`
      `hLip : LipschitzOnWith K₀ (geodesicField g gi) S`.
  `hIC` makes `ξ ↦ W ξ 0` an AFFINE BIJECTION of the whole phase space, so `hmem` at `τ = 0` forces
  `S ⊇ {W ξ 0 : ξ} = univ`.  But
      `geodesicField g gi (x,v) = (v, −Γ(x)(v,v))`
  is QUADRATIC in `v`, hence NOT globally Lipschitz for genuinely curved `Γ`; so `hLip` on `S = univ`
  fails.  The global Task A is therefore VACUOUS at any curved geodesic field (satisfiable only in the
  flat / globally-Lipschitz case).  This was the J4-847 decisive finding.

  THE FIX (this file, plan v8-redirect).  Restrict the family hypotheses `hWode`, `hIC`, `hmem` to
  `ξ ∈ Metric.ball ξ₀ r` for a fixed `r > 0`.  Then `hIC` only forces `{W ξ 0 : ξ ∈ ball ξ₀ r}` — a
  BOUNDED ball `ball (W ξ₀ 0) r` — into `S`, so `S` may be a genuine COMPACT ball around the base point,
  on which `geodesicField` genuinely IS Lipschitz for curved fields (via `hC`'s smoothness).  The
  Jacobi-field data `hVode`, `hV0` stay GLOBAL (the linearized ODE along the reference geodesic references
  no `S`, so the Jacobi families and their additivity/homogeneity are unaffected — no vacuity there).

  WHY THE PROOF STILL GOES THROUGH.  The global core proves the quadratic remainder
  `hquad : ‖W ξ t − W 0 t − V ξ t‖ ≤ Ctot·‖ξ‖²` for all `ξ`, but the little-o assembly of `HasFDerivAt`
  only ever invokes `hquad` for `ξ` in a small ball around `0` (radius `c/(Ctot+1)`).  Restricting `hquad`
  to `ξ ∈ ball 0 r` and choosing the eventual neighborhood radius `min r (c/(Ctot+1))` recovers the exact
  same conclusion.  The base point `ξ₀` case follows by the same coordinate translation Task A already used,
  with the ball `ball 0 r ↔ ball ξ₀ r` moved along.

  WHAT LANDS HERE (axiom-clean, std-3, no `sorry`, no new axioms, no existing file edited):

  * `geodesicFlow_joint_hasFDerivAt_local` — the local (ball-`0`) core.
  * `geodesicFlow_joint_hasFDerivAt_exists_local` — the local core with the CLM `L` constructed.
  * `geodesicFlow_joint_hasFDerivAt_exists_atPoint_local` — ★ the base-point-`ξ₀` local Task A:
      `∃ L, (∀ ξ, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L ξ₀`,
    with `hWode`/`hIC`/`hmem` quantified over `ξ ∈ Metric.ball ξ₀ r` — NON-VACUOUS for curved fields.

  HONEST CHECKPOINT (binding): this is the base-point generalization of the JOINT first-order Fréchet
  derivative with a BOUNDED-BALL perturbation scope — the vacuity-free replacement for the global Task A.
  It is still a POINTWISE `HasFDerivAt` (at `ξ₀`), not `ContDiffAt`/`ContDiffOn`.  The concrete
  non-vacuity witness (a genuinely curved `uniformFlowTube` instantiation) lives in the companion concrete
  file; this abstract file merely makes such an instantiation POSSIBLE (which the global Task A did not).
-/
import Mathlib
import QIQTH.GeodesicBasepointFrechet

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- **Joint Fréchet-derivative core, LOCAL perturbation scope (base point `0`).**  Same as
    `geodesicFlow_joint_hasFDerivAt`, but `hWode`, `hIC`, `hmem` are quantified only over
    `ξ ∈ Metric.ball 0 r` (`r > 0`).  The Jacobi data `hVode`, `hV0` stay global.  The endpoint
    `fun ξ => W ξ t` has Fréchet derivative `L` at `ξ = 0`.  Non-vacuous for curved fields: `hmem`+`hIC`
    now only force `S ⊇ ball (W 0 0) r`, a bounded ball, on which `geodesicField` is Lipschitz. -/
theorem geodesicFlow_joint_hasFDerivAt_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    {L : (Point n × Point n) →L[ℝ] Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    {r : ℝ} (hr : 0 < r)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, W ξ 0 - W 0 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S)
    (hLeq : ∀ ξ : Point n × Point n, L ξ = V ξ t) :
    HasFDerivAt (fun ξ => W ξ t) L 0 := by
  have h0ball : (0 : Point n × Point n) ∈ Metric.ball (0 : Point n × Point n) r :=
    Metric.mem_ball_self hr
  have hnn : 0 ≤ M₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (W 0 0)))
      (hbound2 (W 0 0) (hmem 0 h0ball 0 (Set.left_mem_Icc.mpr zero_le_one)))
  set Ctot : ℝ := M₂ * (Real.exp K₀) ^ 2 * Real.exp K with hCtotdef
  have hCtot0 : 0 ≤ Ctot := by rw [hCtotdef]; positivity
  -- per-direction quadratic remainder, uniform over directions `ξ ∈ ball 0 r`.
  have hquad : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r,
      ‖W ξ t - W 0 t - V ξ t‖ ≤ Ctot * ‖ξ‖ ^ 2 := by
    intro ξ hξ
    have hNb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ‖geodesicField g gi (W ξ τ) - geodesicField g gi (W 0 τ)
            - fderiv ℝ (geodesicField g gi) (W 0 τ) (W ξ τ - W 0 τ)‖
          ≤ M₂ * (‖ξ‖ * Real.exp K₀) ^ 2 := by
      intro τ hτ
      have htp := geodesic_twopoint_gronwall g gi hLip (hWode ξ hξ) (hWode 0 h0ball)
        (hmem ξ hξ) (hmem 0 h0ball) τ hτ
      have hd0 : dist (W ξ 0) (W 0 0) = ‖ξ‖ := by
        rw [dist_eq_norm, hIC ξ hξ]
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
        (hmem ξ hξ τ hτ) (hmem 0 h0ball τ hτ)
      refine hrem.trans ?_
      have hsq : ‖W ξ τ - W 0 τ‖ ^ 2 ≤ (‖ξ‖ * Real.exp K₀) ^ 2 := by
        have := mul_le_mul hLb hLb (norm_nonneg _) (by positivity)
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left hsq hnn
    have h0 : W ξ 0 - W 0 0 - V ξ 0 = 0 := by rw [hIC ξ hξ, hV0 ξ]; abel
    have hbnd := geodesicVariation_residual_bound g gi hK0
      (mul_nonneg hnn (sq_nonneg _)) (hWode 0 h0ball) (hWode ξ hξ) (hVode ξ) h0 hKb hNb t ht
    refine hbnd.trans_eq ?_
    rw [hCtotdef, mul_pow]; ring
  -- assemble the little-o characterisation of the Fréchet derivative at `0`.
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min r (c / (Ctot + 1)), lt_min hr (div_pos hc (by linarith [hCtot0])), fun ξ hξ => ?_⟩
  rw [dist_eq_norm, sub_zero] at hξ
  have hξr : ξ ∈ Metric.ball (0 : Point n × Point n) r := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_lt_of_le hξ (min_le_left _ _)
  have hξc : ‖ξ‖ < c / (Ctot + 1) := lt_of_lt_of_le hξ (min_le_right _ _)
  rw [hLeq ξ]
  have hlt : ‖ξ‖ * (Ctot + 1) < c := (lt_div_iff₀ (by linarith [hCtot0])).mp hξc
  have hCtotξ : Ctot * ‖ξ‖ ≤ c := by nlinarith [norm_nonneg ξ, hCtot0]
  calc ‖W ξ t - W 0 t - V ξ t‖
      ≤ Ctot * ‖ξ‖ ^ 2 := hquad ξ hξr
    _ = (Ctot * ‖ξ‖) * ‖ξ‖ := by ring
    _ ≤ c * ‖ξ‖ := mul_le_mul_of_nonneg_right hCtotξ (norm_nonneg _)

/-- **Joint Fréchet derivative, CLM CONSTRUCTED, LOCAL perturbation scope (base point `0`).**  Same as
    `geodesicFlow_joint_hasFDerivAt_exists` but with `hWode`/`hIC`/`hmem` on `ξ ∈ Metric.ball 0 r`.  The
    endpoint Jacobi map `ξ ↦ V ξ t` is additive/homogeneous by `jacobiSol_unique` (using only the GLOBAL
    `hVode`/`hV0` and the reference-curve data at `ξ = 0`), hence a CLM.  Delivers
    `∃ L, (∀ ξ, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L 0`. -/
theorem geodesicFlow_joint_hasFDerivAt_exists_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    {r : ℝ} (hr : 0 < r)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, W ξ 0 - W 0 0 = ξ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W 0 τ)‖ ≤ K)
    (hmem : ∀ ξ ∈ Metric.ball (0 : Point n × Point n) r, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n × Point n,
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L 0 := by
  have h0ball : (0 : Point n × Point n) ∈ Metric.ball (0 : Point n × Point n) r :=
    Metric.mem_ball_self hr
  -- additivity of `ξ ↦ V ξ t` from Jacobi-ODE uniqueness (global Jacobi data, reference curve at 0).
  have hadd : ∀ a b : Point n × Point n, V a t + V b t = V (a + b) t := by
    intro a b
    refine jacobiSol_unique g gi hK0 (hWode 0 h0ball) hKb (J₁ := fun σ => V a σ + V b σ)
      ?_ (hVode (a + b)) ?_ ht
    · intro τ hτ
      simpa [map_add] using (hVode a τ hτ).add (hVode b τ hτ)
    · simp [hV0 a, hV0 b, hV0 (a + b)]
  have hsmul : ∀ (c : ℝ) (a : Point n × Point n), c • V a t = V (c • a) t := by
    intro c a
    refine jacobiSol_unique g gi hK0 (hWode 0 h0ball) hKb (J₁ := fun σ => c • V a σ)
      ?_ (hVode (c • a)) ?_ ht
    · intro τ hτ
      simpa [map_smul] using (hVode a τ hτ).const_smul c
    · simp [hV0 a, hV0 (c • a)]
  let Lₗ : (Point n × Point n) →ₗ[ℝ] Point n × Point n :=
    { toFun := fun ξ => V ξ t
      map_add' := fun a b => (hadd a b).symm
      map_smul' := fun c a => by simpa using (hsmul c a).symm }
  refine ⟨Lₗ.toContinuousLinearMap, fun ξ => rfl, ?_⟩
  exact geodesicFlow_joint_hasFDerivAt_local g gi hC hK0 ht hconv hr hbound2 hLip hWode hVode
    hV0 hIC hKb hmem (fun ξ => rfl)

/-- **★ Joint Fréchet derivative of the geodesic flow at an ARBITRARY base point `ξ₀`, LOCAL scope.**
    The vacuity-free replacement for `GeodesicJointFDerivAtPoint.geodesicFlow_joint_hasFDerivAt_exists_atPoint`.
    `hWode`/`hIC`/`hmem` are quantified over `ξ ∈ Metric.ball ξ₀ r` (`r > 0`), so `S` need only contain the
    bounded ball `ball (W ξ₀ 0) r` — genuinely satisfiable for a curved `geodesicField` on a compact `S`.
    The endpoint `fun ξ => W ξ t` has joint Fréchet derivative `L` (`L ξ = V ξ t`) at `ξ₀`.

    PROOF: re-instantiate `geodesicFlow_joint_hasFDerivAt_exists_local` on the shifted family
    `W̃ η := W (η + ξ₀)` (reference `W̃ 0 = W ξ₀`), translating `ball 0 r ↔ ball ξ₀ r`, then compose with
    the translation `ξ ↦ ξ − ξ₀` (Fréchet derivative `id`, sending `ξ₀ ↦ 0`). -/
theorem geodesicFlow_joint_hasFDerivAt_exists_atPoint_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n × Point n → ℝ → Point n × Point n}
    (ξ₀ : Point n × Point n)
    {S : Set (Point n × Point n)} {M₂ K : ℝ} {K₀ : NNReal} (hK0 : 0 ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hconv : Convex ℝ S)
    {r : ℝ} (hr : 0 < r)
    (hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂)
    (hLip : LipschitzOnWith K₀ (geodesicField g gi) S)
    (hWode : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W ξ) (geodesicField g gi (W ξ τ)) τ)
    (hVode : ∀ ξ : Point n × Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V ξ) (fderiv ℝ (geodesicField g gi) (W ξ₀ τ) (V ξ τ)) τ)
    (hV0 : ∀ ξ : Point n × Point n, V ξ 0 = ξ)
    (hIC : ∀ ξ ∈ Metric.ball ξ₀ r, W ξ 0 - W ξ₀ 0 = ξ - ξ₀)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (W ξ₀ τ)‖ ≤ K)
    (hmem : ∀ ξ ∈ Metric.ball ξ₀ r, ∀ τ ∈ Set.Icc (0 : ℝ) 1, W ξ τ ∈ S) :
    ∃ L : (Point n × Point n) →L[ℝ] Point n × Point n,
      (∀ ξ : Point n × Point n, L ξ = V ξ t) ∧ HasFDerivAt (fun ξ => W ξ t) L ξ₀ := by
  -- translation of the ball: `η ∈ ball 0 r → η + ξ₀ ∈ ball ξ₀ r`.
  have hshift : ∀ η : Point n × Point n, η ∈ Metric.ball (0 : Point n × Point n) r →
      η + ξ₀ ∈ Metric.ball ξ₀ r := by
    intro η hη
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hη
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
    exact hη
  -- Re-instantiate the local `ξ = 0` theorem on the shifted family `W̃ η := W (η + ξ₀)`.
  obtain ⟨L, hLeq, hFD⟩ :=
    geodesicFlow_joint_hasFDerivAt_exists_local (W := fun η => W (η + ξ₀)) (V := V)
      g gi hC hK0 ht hconv hr hbound2 hLip
      (fun η hη τ hτ => hWode (η + ξ₀) (hshift η hη) τ hτ)
      (fun η τ hτ => by simpa only [zero_add] using hVode η τ hτ)
      hV0
      (fun η hη => by
        simp only [zero_add]
        rw [hIC (η + ξ₀) (hshift η hη)]; abel)
      (fun τ hτ => by simpa only [zero_add] using hKb τ hτ)
      (fun η hη τ hτ => hmem (η + ξ₀) (hshift η hη) τ hτ)
  -- Compose with the translation `ξ ↦ ξ - ξ₀` (derivative `id`, `ξ₀ ↦ 0`).
  refine ⟨L, hLeq, ?_⟩
  have hsh : HasFDerivAt (fun ξ : Point n × Point n => ξ - ξ₀)
      (ContinuousLinearMap.id ℝ (Point n × Point n)) ξ₀ := by
    simpa using (hasFDerivAt_id ξ₀).sub_const ξ₀
  have hg : HasFDerivAt (fun η => W (η + ξ₀) t) L (ξ₀ - ξ₀) := by
    rw [sub_self]; exact hFD
  have hcomp : HasFDerivAt (fun ξ : Point n × Point n => W (ξ - ξ₀ + ξ₀) t)
      (L.comp (ContinuousLinearMap.id ℝ (Point n × Point n))) ξ₀ :=
    HasFDerivAt.comp ξ₀ (g := fun η => W (η + ξ₀) t)
      (f := fun ξ : Point n × Point n => ξ - ξ₀) hg hsh
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hfun : (fun ξ : Point n × Point n => W (ξ - ξ₀ + ξ₀) t) = fun ξ => W ξ t := by
    funext ξ
    have : ξ - ξ₀ + ξ₀ = ξ := by abel
    rw [this]
  rw [hfun] at hcomp
  exact hcomp

end QIQTH.ExpMap
