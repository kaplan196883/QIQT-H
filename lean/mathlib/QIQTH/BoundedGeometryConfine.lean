/-
  BoundedGeometryConfine — the UNIFORM-over-compact a-priori geodesic confinement.

  J4-17 (Brick A2).  This is the compact-uniform strengthening of
  `geodesic_apriori_confinement` (`ExpMap.lean`): a SINGLE radius `ρ > 0` and a SINGLE constant
  `C₀ ≥ 0` such that for EVERY base point `q` in a fixed compact `K` and every velocity `v` with
  `‖v‖ ≤ ρ`, the geodesic tube through `(q, v)` exists on `(-2,2) ⊇ [0,1]` and stays `C₀‖v‖`-close to
  the equilibrium `(q,0)` on `[0,1]`.

  The one non-mechanical step over the point-local version is a COMPACT-UNIFORM Picard–Lindelöf
  existence: instead of routing through the opaque point-local constructor
  `IsPicardLindelof.of_contDiffAt_one` (whose radius/time shrink with the base point), we build a
  SINGLE `IsPicardLindelof` datum on a fixed compact convex phase-space ball
  `S = closedBall (p₀,0) (R+2)` (with `K ⊆ closedBall p₀ R`) from the J4-16 uniform bounds
  (`geodesicField_bddOn_compact` = field bound `M`, `geodesicField_fderiv_bddOn_compact` +
  `Convex.lipschitzOnWith_of_nnnorm_fderiv_le` = uniform Lipschitz modulus `Klip`).  Its flow
  `α : (phase) → ℝ → (phase)` and the flow's uniform Lipschitz-in-initial-condition constant `L'`
  are therefore valid for ALL initial conditions in `closedBall (p₀,0) (R+1) ⊇ {(q, w) : q∈K}` at
  once — giving `q`-INDEPENDENT `ρ = T/2`, `C₀ = (1+s)L's⁻¹`.

  The equilibrium constancy `α (q,0) ≡ (q,0)` (per `q`, by ODE uniqueness on the compact range of
  that trajectory) and the rescaling to `[0,1]` (`geodesic_rescale`, `s = T/2`) mirror the
  point-local proof exactly; only the uniform provenance of `α, L'` is new.

  DERIVED (no firewall): the uniform `ρ, C₀` are genuine single values working across all `q ∈ K`.
-/
import Mathlib
import QIQTH.BoundedGeometry
import QIQTH.ExpMap

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open scoped NNReal

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-- **Compact-uniform a-priori geodesic confinement.**  For a compact set `K` of base points there
    is ONE radius `ρ > 0` and ONE constant `C₀ ≥ 0` such that for every `q ∈ K` and every velocity
    `v` with `‖v‖ ≤ ρ`, the geodesic tube `Y` through `(q, v)` exists on `(-2,2) ⊇ [0,1]` and stays
    `C₀‖v‖`-close to the equilibrium `(q, 0)` on `[0,1]`.

    This is the uniform-over-`K` strengthening of `geodesic_apriori_confinement`.  The uniform
    constants are DERIVED from a single compact-uniform Picard–Lindelöf datum on a fixed compact
    convex phase-space ball (built from the J4-16 uniform Christoffel/geodesic-field bounds), whose
    flow is Lipschitz-in-initial-condition with a single constant `L'` valid for all initial
    conditions `(q, w)` with `q ∈ K`. -/
theorem geodesic_apriori_confinement_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ →
      ∃ Y : ℝ → Point n × Point n, Y 0 = (q, v) ∧
        (∀ t ∈ Set.Ioo (-2 : ℝ) 2, HasDerivAt Y (geodesicField g gi (Y t)) t) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖Y t - ((q, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · -- Vacuous over an empty base set.
    refine ⟨1, one_pos, 0, le_rfl, ?_⟩
    intro q hq
    rw [hKe] at hq
    simp only [Set.mem_empty_iff_false] at hq
  -- Nonempty compact base set: enclose it in a ball `closedBall p₀ R`.
  obtain ⟨p₀, hp₀⟩ := hKne
  obtain ⟨R, hRsub⟩ := hK.isBounded.subset_closedBall p₀
  have hR0 : 0 ≤ R := by
    have h := hRsub hp₀; rw [Metric.mem_closedBall, dist_self] at h; exact h
  set x₀ : Point n × Point n := (p₀, 0) with hx₀
  -- The fixed compact convex phase-space ball `S = closedBall x₀ (R+2)`.
  have haR : (0 : ℝ) ≤ R + 2 := by linarith
  have hrR : (0 : ℝ) ≤ R + 1 := by linarith
  set ann : ℝ≥0 := ⟨R + 2, haR⟩ with hanndef
  set rplnn : ℝ≥0 := ⟨R + 1, hrR⟩ with hrpldef
  have ha_coe : (ann : ℝ) = R + 2 := rfl
  have hr_coe : (rplnn : ℝ) = R + 1 := rfl
  set S : Set (Point n × Point n) := Metric.closedBall x₀ (ann : ℝ) with hSdef
  have hScompact : IsCompact S := by rw [hSdef]; exact isCompact_closedBall _ _
  have hSconvex : Convex ℝ S := by rw [hSdef]; exact convex_closedBall _ _
  -- Uniform field bound `M` and uniform Lipschitz modulus `Klip` on `S`.
  obtain ⟨M, hM0, hMbd⟩ := geodesicField_bddOn_compact g gi hC hScompact
  obtain ⟨Lf, hLf0, hLfbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  set Lnn : ℝ≥0 := ⟨M, hM0⟩ with hLnndef
  have hL_coe : (Lnn : ℝ) = M := rfl
  set Klip : ℝ≥0 := ⟨Lf, hLf0⟩ with hKlipdef
  have hLip : LipschitzOnWith Klip (geodesicField g gi) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => ((contDiff_geodesicField g gi hC).differentiable (by simp)).differentiableAt)
      (fun x hx => by
        rw [← NNReal.coe_le_coe]; simpa [hKlipdef] using hLfbd x hx)
      hSconvex
  -- Uniform existence time `T` (Picard–Lindelöf CFL condition `M·T ≤ (R+2)-(R+1) = 1`).
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  set T : ℝ := 1 / (M + 1) with hTdef
  have hT0 : 0 < T := by rw [hTdef]; positivity
  have ht0mem : (0 : ℝ) ∈ Set.Icc (-T) T := ⟨by linarith, le_of_lt hT0⟩
  -- The single compact-uniform Picard–Lindelöf datum.
  have hpl : IsPicardLindelof (fun _ : ℝ => geodesicField g gi)
      (tmin := -T) (tmax := T) ⟨0, ht0mem⟩ x₀ ann rplnn Lnn Klip := by
    apply IsPicardLindelof.of_time_independent
    · intro x hx; exact hMbd x hx
    · exact hLip
    · show (Lnn : ℝ) * max (T - (0 : ℝ)) ((0 : ℝ) - (-T)) ≤ (ann : ℝ) - (rplnn : ℝ)
      rw [hL_coe, ha_coe, hr_coe, sub_zero, sub_neg_eq_add, zero_add, max_self,
        show (R + 2) - (R + 1) = (1 : ℝ) by ring, hTdef]
      rw [mul_one_div, div_le_one hM1]; linarith
  -- The uniform flow and its uniform Lipschitz-in-initial-condition constant `L'`.
  obtain ⟨α, hflow, L', hlip⟩ :=
    hpl.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  -- Uniform confinement radius and constant.
  set s : ℝ := T / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hs2T : 2 * s = T := by rw [hsdef]; ring
  have hC0 : (0 : ℝ) ≤ (1 + s) * (L' : ℝ) * s⁻¹ :=
    mul_nonneg (mul_nonneg (by linarith) (NNReal.coe_nonneg L')) (le_of_lt (inv_pos.mpr hs0))
  refine ⟨s, hs0, (1 + s) * (L' : ℝ) * s⁻¹, hC0, ?_⟩
  intro q hq v hv
  -- The equilibrium `e = (q,0)` lies in the initial-condition ball.
  set e : Point n × Point n := (q, 0) with he
  have hdist_q : dist q p₀ ≤ R := by
    have h := hRsub hq; rwa [Metric.mem_closedBall] at h
  have hmem_e : e ∈ Metric.closedBall x₀ (rplnn : ℝ) := by
    rw [he, hx₀, Metric.mem_closedBall, dist_eq_norm,
      show (q, 0) - ((p₀, 0) : Point n × Point n) = ((q - p₀, 0) : Point n × Point n) by simp,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), hr_coe]
    calc ‖q - p₀‖ = dist q p₀ := (dist_eq_norm q p₀).symm
      _ ≤ R := hdist_q
      _ ≤ R + 1 := by linarith
  -- The equilibrium trajectory `α e` is the constant curve `e` (ODE uniqueness, compact range).
  have hα0e : α e 0 = e := (hflow e hmem_e).1
  have hαe_deriv : ∀ t ∈ Set.Icc (-T) T,
      HasDerivWithinAt (α e) (geodesicField g gi (α e t)) (Set.Icc (-T) T) t :=
    (hflow e hmem_e).2
  have hcont : ContinuousOn (α e) (Set.Icc (-T) T) := HasDerivWithinAt.continuousOn hαe_deriv
  obtain ⟨Rq, hRq⟩ :=
    (((isCompact_Icc).image_of_continuousOn hcont).isBounded).subset_closedBall e
  have h0memoo : (0 : ℝ) ∈ Set.Ioo (-T) T := ⟨by linarith, hT0⟩
  have hRq0 : (0 : ℝ) ≤ Rq := by
    have : e ∈ Metric.closedBall e Rq := hRq ⟨0, ht0mem, hα0e⟩
    simpa using this
  obtain ⟨Kq, hKq⟩ :=
    ((contDiff_geodesicField g gi hC).contDiffOn (s := Metric.closedBall e Rq)).exists_lipschitzOnWith
      (by simp) (convex_closedBall e Rq) (isCompact_closedBall e Rq)
  have hEq : Set.EqOn (α e) (fun _ => e) (Set.Icc (-T) T) := by
    refine ODE_solution_unique_of_mem_Icc (v := fun _ => geodesicField g gi)
      (s := fun _ => Metric.closedBall e Rq) (K := Kq) (t₀ := 0)
      (fun t _ => hKq) h0memoo hcont
      (fun t ht => (hαe_deriv t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
      (fun t ht => hRq ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩)
      continuousOn_const
      (fun t _ => ?_) (fun _ _ => Metric.mem_closedBall_self hRq0) hα0e
    show HasDerivAt (fun _ : ℝ => e) (geodesicField g gi e) t
    rw [show geodesicField g gi e = 0 from by rw [he]; exact geodesicField_equilibrium g gi q]
    exact hasDerivAt_const t e
  -- The rescaled initial point `(q, s⁻¹•v)` lies in the initial-condition ball.
  have hmemball : (q, s⁻¹ • v) ∈ Metric.closedBall x₀ (rplnn : ℝ) := by
    rw [hx₀, Metric.mem_closedBall, dist_eq_norm,
      show (q, s⁻¹ • v) - ((p₀, 0) : Point n × Point n) = ((q - p₀, s⁻¹ • v) : Point n × Point n) by
        simp,
      Prod.norm_def, hr_coe]
    refine max_le ?_ ?_
    · calc ‖q - p₀‖ = dist q p₀ := (dist_eq_norm q p₀).symm
        _ ≤ R := hdist_q
        _ ≤ R + 1 := by linarith
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0]
      calc s⁻¹ * ‖v‖ ≤ s⁻¹ * s :=
            mul_le_mul_of_nonneg_left hv (le_of_lt (inv_pos.mpr hs0))
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hs0)
        _ ≤ R + 1 := by linarith
  have hw_deriv : ∀ t ∈ Set.Icc (-T) T,
      HasDerivWithinAt (α (q, s⁻¹ • v)) (geodesicField g gi (α (q, s⁻¹ • v) t)) (Set.Icc (-T) T) t :=
    (hflow (q, s⁻¹ • v) hmemball).2
  have hw0 : α (q, s⁻¹ • v) 0 = (q, s⁻¹ • v) := (hflow (q, s⁻¹ • v) hmemball).1
  -- Assemble the confined tube `Y τ = L_s (α (q, s⁻¹•v) (s τ))`.
  refine ⟨fun τ => rescaleCLM s (α (q, s⁻¹ • v) (s * τ)), ?_, ?_, ?_⟩
  · show rescaleCLM s (α (q, s⁻¹ • v) (s * 0)) = (q, v)
    rw [mul_zero, hw0, rescaleCLM_apply, smul_smul, mul_inv_cancel₀ (ne_of_gt hs0), one_smul]
  · intro t ht
    have hmem : s * t ∈ Set.Ioo (-T) T := by
      refine ⟨?_, ?_⟩
      · calc -T = s * (-2) := by rw [← hs2T]; ring
          _ < s * t := mul_lt_mul_of_pos_left ht.1 hs0
      · calc s * t < s * 2 := mul_lt_mul_of_pos_left ht.2 hs0
          _ = T := by rw [← hs2T]; ring
    refine geodesic_rescale g gi (a := -T) (b := T) ?_ s t hmem
    intro u hu
    exact (hw_deriv u (Set.Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  · intro t ht
    have hst : s * t ∈ Set.Icc (-T) T := by
      constructor
      · have : (0 : ℝ) ≤ s * t := mul_nonneg (le_of_lt hs0) ht.1
        linarith
      · calc s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hs0)
          _ = s := mul_one s
          _ ≤ T := by rw [hsdef]; linarith
    show ‖rescaleCLM s (α (q, s⁻¹ • v) (s * t)) - e‖ ≤ (1 + s) * (L' : ℝ) * s⁻¹ * ‖v‖
    set D : Point n × Point n := α (q, s⁻¹ • v) (s * t) - α e (s * t) with hD
    have hYt : rescaleCLM s (α (q, s⁻¹ • v) (s * t)) - e = rescaleCLM s D := by
      rw [hD, map_sub, hEq hst]
      congr 1
      rw [he]; simp [rescaleCLM_apply]
    have hdist : ‖D‖ ≤ (L' : ℝ) * ‖s⁻¹ • v‖ := by
      have hl := (hlip (s * t) hst).dist_le_mul (q, s⁻¹ • v) hmemball e hmem_e
      rw [dist_eq_norm, dist_eq_norm] at hl
      rw [hD]
      refine hl.trans (le_of_eq ?_)
      rw [he,
        show (q, s⁻¹ • v) - ((q, 0) : Point n × Point n) = ((0, s⁻¹ • v) : Point n × Point n) by simp,
        Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    have hcomp1 : ‖D.1‖ ≤ ‖D‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hcomp2 : ‖D.2‖ ≤ ‖D‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hrs : ‖rescaleCLM s D‖ ≤ (1 + s) * ‖D‖ := by
      rw [rescaleCLM_apply, Prod.norm_def, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      refine max_le ?_ ?_
      · exact hcomp1.trans (le_mul_of_one_le_left (norm_nonneg _) (by linarith))
      · calc s * ‖D.2‖ ≤ s * ‖D‖ := mul_le_mul_of_nonneg_left hcomp2 (le_of_lt hs0)
          _ ≤ (1 + s) * ‖D‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    rw [hYt]
    calc ‖rescaleCLM s D‖
        ≤ (1 + s) * ‖D‖ := hrs
      _ ≤ (1 + s) * ((L' : ℝ) * ‖s⁻¹ • v‖) := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = (1 + s) * (L' : ℝ) * s⁻¹ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs0]; ring

end QIQTH.ExpMap
