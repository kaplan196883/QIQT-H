/-
  JacobiCLMExposure — J4-435: re-expose the ENDPOINT velocity-Jacobi operator of the forward
  geodesic-flow first jet, and discharge the first-jet base modulus `hbaseJ` — closing the `hFwd`
  atom (`ForwardFlowJet`) of the a₁ = R/6 sup family.  ONE brick of the a₁ = R/6 campaign;
  **NOT a₁ = R/6** and proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable
  hypotheses, no result that is a conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-434).  `ForwardFlowJet` built the `hFwd` atom by a `q₀`-anchored triangle
  one derivative up, modulo ONE carried input `hbaseJ` — the first-jet base modulus
        `‖fderiv (uniformFlowExp q) w − fderiv (uniformFlowExp q') w‖ ≤ exp L·‖q − q'‖`  (‖w‖ < ρ).
  The diagnosis: the flow's Jacobian is the velocity-Jacobi endpoint operator `δ ↦ (V_{q,v} δ 1).1`
  built INTERNALLY inside `uniformFlowExp_hasFDerivAt` (a local `set V := …choose`); the tower's public
  spec exposed only `∃ L, HasFDerivAt` with `L` identified with nothing accessible.  The discharge
  engine (`jacobi_twopoint_diff_bound` + the base-tube separation `uniformTube_twopoint_diff_bound` +
  the C² field bound) was ALREADY BANKED; the residue was spec-exposure.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `uniformFlowExp_jacobi_spec` — **★ THE EXPOSURE.**  For `q ∈ K`, `‖v‖ < ρ_K`, re-derives (by
      re-running the compiled `uniformFlowExp_hasFDerivAt` construction and concluding the full triple)
      the base geodesic `Y` through `(q,v)`, the endpoint velocity-Jacobi family `V` along `Y`
      (seed `V δ 0 = (0,δ)`, Jacobi ODE `V δ' = DF(Y)·V δ` on `[0,1]`), and the CLM identity
        `fderiv ℝ (uniformFlowExp … q) v = L`,  `L δ = (V δ 1).1`.
      This is the missing spec lemma naming the endpoint Jacobi CLM (Sol #21's precise ingredient).

    * `jacobiEndpoint_op_diff_bound` — **★ per-`δ` operator seed bound.**  For two bases `q, q' ∈ K`
      with `‖v‖ < ρ_K`, the two endpoint Jacobi families differ (position slot) by
        `‖(fderiv (uniformFlowExp q) v − fderiv (uniformFlowExp q') v) δ‖ ≤ Λ·‖q − q'‖·‖δ‖`,
      assembled from the exposure + `jacobi_twopoint_diff_bound` (base-tube separation
      `uniformTube_twopoint_diff_bound` × the uniform C² field bound), + the homogeneous Jacobi growth
      bound `jacobiEndpoint_growth_bound`.

    * `uniformFlowExp_fderiv_base_modulus` — **★★ hbaseJ (strict interior), DISCHARGED.**  The operator
      first-jet base modulus `‖fderiv (uniformFlowExp q) v − fderiv (uniformFlowExp q') v‖ ≤ exp L·‖q−q'‖`
      for `‖v‖ < ρ_K`, `q, q' ∈ K` — via the bilinear opNorm bound over the per-`δ` seed bound.

    * `forwardFlowJet_continuousOn` — **★★★ THE hFwd ATOM, UNCONDITIONAL.**  Joint-in-`(z,v)` continuity
      of the forward-flow first jet on `K ×ˢ ball 0 ρ_K`, no carried `hbaseJ`.

    * `chartFieldJacobian_continuousOn` — **the J3 wiring, UNCONDITIONAL** (modulo the banked
      origin-section / nondeg / IFT inputs, exactly as `chartFieldJacobian_continuousOn_of_baseMod`).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL — the SECOND-order carry `hcont2`/`C₂` of the sup
  family is untouched here.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.UniformFlowFDeriv
import QIQTH.NearIsometryBudget
import QIQTH.GeodesicGronwall
import QIQTH.BasepointJetModulus
import QIQTH.ForwardFlowJet

open Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.GeodesicGronwall QIQTH.ForwardFlowJet
open scoped Topology NNReal

namespace QIQTH.JacobiCLMExposure

variable {n : ℕ}

set_option maxHeartbeats 2000000

/-! ###############################################################################
    ### ★ THE EXPOSURE — re-derive the endpoint velocity-Jacobi CLM as a public spec.
    ############################################################################### -/

/-- **★ `uniformFlowExp_jacobi_spec` — THE EXPOSURE.**  For `q ∈ K` and `‖v‖ < ρ_K`, the forward-flow
    first jet is the endpoint velocity-Jacobi operator along the base geodesic through `(q,v)`.  Re-runs
    the compiled `uniformFlowExp_hasFDerivAt` construction, but CONCLUDES the full triple instead of just
    `∃ L, HasFDerivAt`:
      * a base geodesic `Y` with `Y 0 = (q,v)` solving the geodesic phase-ODE on `[0,1]`;
      * an endpoint velocity-Jacobi family `V` along `Y` with seed `V δ 0 = (0,δ)` solving the
        first-variation (Jacobi) ODE `V δ' = DF(Y)·V δ` on `[0,1]`;
      * the CLM identity `fderiv ℝ (uniformFlowExp … q) v = L` with `L δ = (V δ 1).1`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_jacobi_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) :
    ∃ (V : Point n → ℝ → Point n × Point n) (L : Point n →L[ℝ] Point n),
      (∀ δ : Point n, V δ 0 = ((0, δ) : Point n × Point n)) ∧
      (∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (V δ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (V δ τ)) τ) ∧
      (∀ δ : Point n, L δ = (V δ 1).1) ∧
      fderiv ℝ (uniformFlowExp g gi hC hK q) v = L := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  set Wf : Point n → ℝ → Point n × Point n :=
    fun δ => uniformFlowTube g gi hC hK q (v + δ) with hWfdef
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖v + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le v δ).trans ?_
    rw [hσdef] at hδ; linarith
  set S : Set (Point n × Point n) := Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  have hC₀ρ0 : 0 ≤ C₀ * ρ := mul_nonneg hC₀nn hρ0.le
  have hqmem : ((q, 0) : Point n × Point n) ∈ S := by
    rw [hSdef]; exact Metric.mem_closedBall_self hC₀ρ0
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
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Wf δ) (geodesicField g gi (Wf δ τ)) τ := by
    intro δ hδ τ hτ
    exact uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) (hle δ hδ) τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, Wf δ τ ∈ S := by
    intro δ hδ τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_eq_norm]
    calc ‖Wf δ τ - ((q, 0) : Point n × Point n)‖
        ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) (hle δ hδ) τ hτ
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left (hle δ hδ) hC₀nn
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → Wf δ 0 - Wf 0 0 = ((0, δ) : Point n × Point n) := by
    intro δ hδ
    have h1 : Wf δ 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) (hle δ hδ)
    have h2 : Wf 0 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) (hle 0 h0σ)
    rw [h1, h2, Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left]
  have hbasecont : ContinuousOn (Wf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) (hle 0 h0σ) τ hτoo).continuousAt).continuousWithinAt
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
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hbound2 : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖ ≤ M₂ := hM₂
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Wf 0 τ)‖ ≤ Kf :=
    fun τ hτ => hKf (Wf 0 τ) (hmem 0 h0σ τ hτ)
  obtain ⟨L, hLeq, hFD⟩ :=
    flowVelocity_endpoint_hasFDerivAt_window_exists g gi hC hKf0 hσ ht1 hSconv hbound2 hLip
      hWode hVode hV0 hIC hKb hmem
  set Lpos : Point n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp L with hLposdef
  have hLpos_apply : ∀ δ : Point n, Lpos δ = (V δ 1).1 := fun δ => by
    show (L δ).1 = (V δ 1).1
    rw [hLeq δ]
  have hFDpos : HasFDerivAt (fun δ => (Wf δ 1).1) Lpos 0 := by
    have := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp (0 : Point n) hFD
    simpa [hLposdef, Function.comp] using this
  have hfun : (fun δ => (Wf δ 1).1) = (fun δ => uniformFlowExp g gi hC hK q (v + δ)) := by
    funext δ; rw [hWfdef]; rw [uniformFlowExp_eq]
  rw [hfun] at hFDpos
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFDpos0 : HasFDerivAt (fun δ => uniformFlowExp g gi hC hK q (v + δ)) Lpos (v - v) := by
    rw [sub_self]; exact hFDpos
  have hcomp : HasFDerivAt (fun u => uniformFlowExp g gi hC hK q (v + (u - v)))
      (Lpos.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFDpos0.comp (f := fun u : Point n => u - v) v hshift
  have hfun2 : (fun u => uniformFlowExp g gi hC hK q (v + (u - v)))
      = uniformFlowExp g gi hC hK q := by
    funext u; congr 1; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  have hFDexp : HasFDerivAt (uniformFlowExp g gi hC hK q) Lpos v := hcomp
  have hfd : fderiv ℝ (uniformFlowExp g gi hC hK q) v = Lpos := hFDexp.fderiv
  -- the base curve `Wf 0` IS the concrete tube through `(q, v)` (`v + 0 = v`).
  have hWf0 : Wf 0 = uniformFlowTube g gi hC hK q v := by
    simp only [hWfdef, add_zero]
  -- rewrite the Jacobi ODE along the concrete tube.
  have hVode' : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (V δ τ)) τ := by
    rw [← hWf0]; exact hVode
  exact ⟨V, Lpos, hV0, hVode', hLpos_apply, hfd⟩

/-! ###############################################################################
    ### ★ THE DISCHARGE — homogeneous Jacobi growth + the operator base modulus.
    ############################################################################### -/

/-- **Homogeneous Jacobi growth bound.**  A Jacobi field `J` along a base curve `Y` (`J' = DF(Y)·J`)
    with `‖DF(Y τ)‖ ≤ K` on `[0,1]` grows at most exponentially: `‖J t‖ ≤ ‖J 0‖·exp K`.  Mathlib's
    homogeneous Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`, `ε = 0`, `gronwallBound_ε0`).
    Supplies the `hJb` (second-field bound) hypothesis of `jacobi_twopoint_diff_bound`. -/
theorem jacobi_growth_bound (g gi : Point n → Fin n → Fin n → ℝ)
    {Y J : ℝ → Point n × Point n} {K : ℝ} (hK0 : 0 ≤ K)
    (hJ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (Y τ) (J τ)) τ)
    (hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (geodesicField g gi) (Y τ)‖ ≤ K) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖J t‖ ≤ ‖J 0‖ * Real.exp K := by
  have hcont : ContinuousOn J (Set.Icc 0 1) :=
    fun t ht => ((hJ t ht).continuousAt).continuousWithinAt
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le (f := J)
    (f' := fun t => fderiv ℝ (geodesicField g gi) (Y t) (J t))
    (δ := ‖J 0‖) (K := K) (ε := 0) (a := 0) (b := 1)
    hcont
    (fun x hx => (hJ x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (le_refl _)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      show ‖fderiv ℝ (geodesicField g gi) (Y x) (J x)‖ ≤ K * ‖J x‖ + 0
      rw [add_zero]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hKb x hx') (norm_nonneg _)))
  intro t ht
  refine (hmain t ht).trans ?_
  rw [gronwallBound_ε0, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  calc K * t ≤ K * 1 := mul_le_mul_of_nonneg_left ht.2 hK0
    _ = K := mul_one _

/-- **★★ `uniformFlowExp_fderiv_base_modulus` — hbaseJ (strict interior), DISCHARGED.**  The operator
    first-jet base modulus of the forward flow: there is a single uniform `Λ ≥ 0` over `K` with
      `‖fderiv (uniformFlowExp … q) v − fderiv (uniformFlowExp … q') v‖ ≤ Λ·‖q − q'‖`
    for all `q, q' ∈ K` and `‖v‖ < ρ_K`.  Assembled from the exposure `uniformFlowExp_jacobi_spec`
    (fderiv = endpoint Jacobi CLM) + `jacobi_twopoint_diff_bound` (two Jacobi fields, same seed `(0,δ)`,
    along the two base tubes) with `Dcoef = M₂·exp L_sep·‖q−q'‖` (the C² field bound `M₂` × the base-tube
    separation `uniformTube_twopoint_diff_bound`) and `Jb = ‖δ‖·exp K_f` (`jacobi_growth_bound`), then
    the bilinear opNorm bound `‖(L−L')δ‖ ≤ Λ·‖q−q'‖·‖δ‖ ⟹ ‖L−L'‖ ≤ Λ·‖q−q'‖`.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_fderiv_base_modulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ q ∈ K, ∀ q' ∈ K, ∀ v : Point n,
      ‖v‖ < uniformFlowRadius g gi hC hK →
        ‖fderiv ℝ (uniformFlowExp g gi hC hK q) v
            - fderiv ℝ (uniformFlowExp g gi hC hK q') v‖
          ≤ Λ * ‖q - q'‖ := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  -- `K ⊆ closedBall 0 M`; the common confinement ball `S`.
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : Point n)
  set S : Set (Point n × Point n) := Metric.closedBall (0 : Point n × Point n) (M + C₀ * ρ) with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconv : Convex ℝ S := convex_closedBall _ _
  -- second-fderiv (C²) bound `M₂` and field bound `Kf` on `S`.
  have hdiffglob : Differentiable ℝ (fderiv ℝ (geodesicField g gi)) :=
    ((contDiff_geodesicField g gi hC).fderiv_right (m := ⊤) le_top).differentiable (by simp)
  obtain ⟨M₂, hM₂0, hM₂⟩ :
      ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖ ≤ Kb := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · refine ⟨0, le_refl _, fun z hz => ?_⟩
      rw [hSe] at hz; exact absurd hz (by simp)
    · have hcontr : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) z‖) :=
        (((contDiff_geodesicField g gi hC).fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top).continuous_fderiv
          (by simp)).norm
      obtain ⟨x, hxS, hx⟩ := hScompact.exists_isMaxOn hSne hcontr.continuousOn
      exact ⟨‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) x‖,
        norm_nonneg (fderiv ℝ (fderiv ℝ (geodesicField g gi)) x),
        fun z hz => (isMaxOn_iff.mp hx) z hz⟩
  obtain ⟨Kf, hKf0, hKf⟩ := geodesicField_fderiv_bddOn_compact g gi hC hScompact
  -- base-tube separation `L_sep` (W2, uniform over `K`).
  obtain ⟨Lsep, hLsep0, hsep⟩ := uniformTube_twopoint_diff_bound g gi hC hK
  set Λ : ℝ := M₂ * Real.exp Lsep * Real.exp Kf * Real.exp Kf with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  refine ⟨Λ, hΛ0, ?_⟩
  intro q hq q' hq' v hv
  have hvρ : ‖v‖ ≤ ρ := hv.le
  -- both tubes live in `S`.
  have hmemtube : ∀ z ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      uniformFlowTube g gi hC hK z v τ ∈ S := by
    intro z hz τ hτ
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]
    have hconf : ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ ≤ C₀ * ‖v‖ :=
      uniformFlowTube_spec_conf g gi hC hK z hz v hvρ τ hτ
    have hzn : ‖((z, 0) : Point n × Point n)‖ ≤ M := by
      rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
      have := hM hz; rwa [Metric.mem_closedBall, dist_zero_right] at this
    calc ‖uniformFlowTube g gi hC hK z v τ‖
        ≤ ‖((z, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((z, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK z v τ - ((z, 0) : Point n × Point n))
          simpa using this
      _ ≤ M + C₀ * ‖v‖ := add_le_add hzn hconf
      _ ≤ M + C₀ * ρ := by
          have : C₀ * ‖v‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ hC₀nn
          linarith
  -- field bounds along both tubes.
  have hKbq : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q hq τ hτ)
  have hKbq' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Kf :=
    fun τ hτ => hKf _ (hmemtube q' hq' τ hτ)
  -- coefficient separation `Dcoef = M₂·exp L_sep·‖q−q'‖` (MVT × W2).
  set Dc : ℝ := M₂ * (‖q - q'‖ * Real.exp Lsep) with hDcdef
  have hAd : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)
          - fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q' v τ)‖ ≤ Dc := by
    intro τ hτ
    have hmvt := hSconv.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fderiv ℝ (geodesicField g gi)) (fun x _ => hdiffglob x) hM₂
      (hmemtube q' hq' τ hτ) (hmemtube q hq τ hτ)
    refine hmvt.trans ?_
    have hd := hsep q hq q' hq' v hvρ τ hτ
    simp only [dist_eq_norm] at hd
    have hexpτ : Real.exp (Lsep * τ) ≤ Real.exp Lsep := by
      apply Real.exp_le_exp.mpr
      calc Lsep * τ ≤ Lsep * 1 := mul_le_mul_of_nonneg_left hτ.2 hLsep0
        _ = Lsep := mul_one _
    rw [hDcdef]
    calc M₂ * ‖uniformFlowTube g gi hC hK q v τ - uniformFlowTube g gi hC hK q' v τ‖
        ≤ M₂ * (‖q - q'‖ * Real.exp (Lsep * τ)) := mul_le_mul_of_nonneg_left hd hM₂0
      _ ≤ M₂ * (‖q - q'‖ * Real.exp Lsep) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpτ (norm_nonneg _)) hM₂0
  -- the two exposures.
  obtain ⟨Vq, Lq, hVq0, hVqode, hLq, hfdq⟩ :=
    uniformFlowExp_jacobi_spec g gi hC hK q hq v hv
  obtain ⟨Vq', Lq', hVq'0, hVq'ode, hLq', hfdq'⟩ :=
    uniformFlowExp_jacobi_spec g gi hC hK q' hq' v hv
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- per-`δ` seed bound via `jacobi_twopoint_diff_bound` + growth.
  have hper : ∀ δ : Point n,
      ‖(fderiv ℝ (uniformFlowExp g gi hC hK q) v
          - fderiv ℝ (uniformFlowExp g gi hC hK q') v) δ‖ ≤ Λ * ‖q - q'‖ * ‖δ‖ := by
    intro δ
    -- growth bound on the second Jacobi field.
    have hgrow := jacobi_growth_bound g gi hKf0 (hVq'ode δ) hKbq' 1 ht1
    rw [hVq'0 δ] at hgrow
    have hseed : ‖((0, δ) : Point n × Point n)‖ = ‖δ‖ := by rw [Prod.norm_mk]; simp
    rw [hseed] at hgrow
    -- two-point Jacobi difference at `t = 1`.
    have h0eq : Vq δ 0 = Vq' δ 0 := by rw [hVq0 δ, hVq'0 δ]
    have hJb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Vq' δ τ‖ ≤ ‖δ‖ * Real.exp Kf :=
      fun τ hτ => by
        have := jacobi_growth_bound g gi hKf0 (hVq'ode δ) hKbq' τ hτ
        rw [hVq'0 δ, hseed] at this; exact this
    have htp := jacobi_twopoint_diff_bound g gi (Y₁ := uniformFlowTube g gi hC hK q v)
      (Y₂ := uniformFlowTube g gi hC hK q' v) (J₁ := Vq δ) (J₂ := Vq' δ)
      (K := Kf) (Dcoef := Dc) (Jb := ‖δ‖ * Real.exp Kf) hKf0
      (hVqode δ) (hVq'ode δ) h0eq hKbq hAd hJb 1 ht1
    -- turn the phase-space endpoint bound into the position-slot operator bound.
    have hpos : ‖(fderiv ℝ (uniformFlowExp g gi hC hK q) v
          - fderiv ℝ (uniformFlowExp g gi hC hK q') v) δ‖ ≤ ‖Vq δ 1 - Vq' δ 1‖ := by
      rw [ContinuousLinearMap.sub_apply, hfdq, hfdq', hLq δ, hLq' δ, ← Prod.fst_sub, Prod.norm_def]
      exact le_max_left _ _
    refine hpos.trans (htp.trans ?_)
    rw [hΛdef, hDcdef]; ring_nf
    rfl
  -- opNorm bound over the per-`δ` seed bound.
  have hbnd := ContinuousLinearMap.opNorm_le_bound
    (fderiv ℝ (uniformFlowExp g gi hC hK q) v - fderiv ℝ (uniformFlowExp g gi hC hK q') v)
    (mul_nonneg hΛ0 (norm_nonneg _)) hper
  exact hbnd

/-! ###############################################################################
    ### ★★★ THE COLLAPSE — hFwd and the J3 chart Jacobian, UNCONDITIONAL.
    ############################################################################### -/

/-- **★★★ `forwardFlowJet_continuousOn` — THE hFwd ATOM, UNCONDITIONAL.**  Joint-in-`(z,v)` continuity
    of the forward-flow first jet `(z,v) ↦ fderiv ℝ (uniformFlowExp … z) v` on `K ×ˢ ball 0 ρ_K`, with
    NO carried first-jet base modulus.  The `q₀`-anchored triangle of `ForwardFlowJet` one derivative
    up, now with the base-slot modulus DISCHARGED by `uniformFlowExp_fderiv_base_modulus` (used only at
    strict-interior velocities, all the weld ever probes).  NOT `a₁ = R/6`. -/
theorem forwardFlowJet_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ContinuousOn
      (fun p : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  classical
  obtain ⟨Λ, hΛ0, hmod⟩ := uniformFlowExp_fderiv_base_modulus g gi hC hK
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hw₀ : ‖p.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hp2
  have hvel : ContinuousAt (fun w : Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) w) p.2 :=
    forwardFlowJet_velocityContinuousAt g gi hC hK p.1 hp1 p.2 hw₀
  have hfst : Tendsto (fun x : Point n × Point n => x.1)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.1) :=
    (continuous_fst.tendsto p).mono_left nhdsWithin_le_nhds
  have hsndp : Tendsto (fun x : Point n × Point n => x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 p.2) :=
    (continuous_snd.tendsto p).mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun x : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p)
      (𝓝 (fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2)) :=
    hvel.tendsto.comp hsndp
  have htend : Tendsto (fun x : Point n × Point n => Λ * ‖x.1 - p.1‖)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    have hc : Continuous (fun z : Point n => Λ * ‖z - p.1‖) := by fun_prop
    have h := (hc.tendsto p.1).comp hfst
    simpa using h
  have hdiff : Tendsto (fun x : Point n × Point n =>
        fderiv ℝ (uniformFlowExp g gi hC hK x.1) x.2
          - fderiv ℝ (uniformFlowExp g gi hC hK p.1) x.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] p) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ htend
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx2' : ‖x.2‖ < uniformFlowRadius g gi hC hK := by rwa [mem_ball_zero_iff] at hx2
    exact hmod x.1 hx1 p.1 hp1 x.2 hx2'
  have hcomb := hdiff.add hsnd
  simp only [zero_add] at hcomb
  exact Filter.Tendsto.congr (fun x => by abel) hcomb

/-- **`chartFieldJacobian_continuousOn` — the J3 wiring, UNCONDITIONAL.**  Feeds the now-unconditional
    hFwd atom into the J4-433 IFT reduction: for `U ⊆ K` with the banked origin-section continuity `hW0`,
    the origin smallness `horigin`, the nondegeneracy `hunit` and the IFT identity `hIFT` (all supplied
    by `ChartFieldJacobian`), the chart field-slot Jacobian `z ↦ fderiv ℝ (uniformInverseChart … z) 0`
    is base-continuous on `U` — with NO carried first-jet base modulus.  NOT `a₁ = R/6`. -/
theorem chartFieldJacobian_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hIFT : ∀ z ∈ U, fderiv ℝ (uniformInverseChart g gi hC hK z) 0
      = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0))) :
    ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U := by
  have hFwd := forwardFlowJet_continuousOn g gi hC hK
  have hpair : ContinuousOn
      (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U :=
    continuousOn_id.prodMk hW0
  have hmaps : Set.MapsTo (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
    fun z hz => ⟨hUK hz, by rw [mem_ball_zero_iff]; exact horigin z hz⟩
  have hinner : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0)) U :=
    hFwd.comp hpair hmaps
  have hRinv : ContinuousOn
      (fun z : Point n => Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0))) U := by
    intro z₀ hz₀
    obtain ⟨u₀, hu₀⟩ := hunit z₀ hz₀
    have hca : ContinuousAt Ring.inverse
        (fderiv ℝ (uniformFlowExp g gi hC hK z₀) (uniformInverseChart g gi hC hK z₀ 0)) := by
      rw [← hu₀]; exact (contDiffAt_ringInverse (n := 1) ℝ u₀).continuousAt
    exact hca.tendsto.comp (hinner z₀ hz₀)
  exact hRinv.congr hIFT

end QIQTH.JacobiCLMExposure

section AxiomChecks
open QIQTH.JacobiCLMExposure
#print axioms uniformFlowExp_jacobi_spec
#print axioms jacobi_growth_bound
#print axioms uniformFlowExp_fderiv_base_modulus
#print axioms forwardFlowJet_continuousOn
#print axioms chartFieldJacobian_continuousOn
end AxiomChecks
