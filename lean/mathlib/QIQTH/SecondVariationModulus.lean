/-
  SecondVariationModulus — J4-481: the base-slot SECOND-jet exposure `hbaseJ2` groundwork — the
  second-variation solution operator of the forward geodesic flow, EXPOSED as a public spec, toward
  felling THE CONVERGENT WALL of the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.
  std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-479/480).  `ChartSecondJet` (J4-479) reduced the chart Hessian (the WALL both
  the a₁=R/6 htermBox chain and the C₂ derivative-sup chain converge on) to the atom `hFwd2` — the joint
  continuity of the forward SECOND jet `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v`.  `Flow3Regularity`
  (J4-480) discharged the VELOCITY slot of `hFwd2` (C³ via the banked C⁴ + `forward2_velocitySlot`).
  REMAINING for the full `hFwd2`: the BASE slot — the second-jet base modulus `hbaseJ2`
        `‖fderiv² (uniformFlowExp q) w − fderiv² (uniformFlowExp q') w‖ ≤ modulus(‖q − q'‖)`,
  then the `z₀`-anchored triangle weld (the J4-434/435 pattern one order up) gives
  `hFwd2 ⟹ chartSecondJet_continuousOn UNCONDITIONAL ⟹ THE WALL FALLS`.

  ── THE DIAGNOSIS (spec-exposure, exactly as J4-435).  The flow's SECOND jet is the DOUBLED
  second-variation endpoint operator `δ ↦ (Vf δ 1).2.1`, where `Vf` is the doubled-linearized field
  along the base DOUBLED curve `(uniformFlowTube q v, Jf0)` (`Jf0` = the base velocity Jacobi field
  through `(q,v)` with seed `(0,b)`).  This `Vf` is built INTERNALLY inside R2-a
  (`uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt`) as a local `Classical.choose`, and its
  defining endpoint identification `L δ = Vf δ 1` is DISCARDED (`_hLeq`) by both R2-a and R2-b
  (`uniformFlowExp_fderiv_apply_hasFDerivAt`).  The tower's public spec exposed only
  `∃ L₂, HasFDerivAt (fun w => fderiv (uniformFlowExp q) w b) L₂ v` with `L₂` identified with nothing
  accessible.  The residue is spec-exposure, exactly the J4-435 residue one order up.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `uniformFlowExp_secondVar_spec` — **★ THE EXPOSURE.**  For `q ∈ K`, `‖v‖ < ρ_K`, and each seed
      `b`, re-derives (by re-running the compiled R2-a/R2-b construction and CONCLUDING the full triple
      instead of just `∃ L₂, HasFDerivAt`):
        * the base velocity Jacobi field `Jf0` through `(q,v)` (seed `Jf0 0 = (0,b)`, Jacobi ODE
          `Jf0' = DF(geodesicField)(tube)·Jf0` on `[0,1]`);
        * the DOUBLED second-variation field `Vf` along the base doubled curve `(tube q v, Jf0)`
          (seed `Vf δ 0 = ((0,δ),(0,0))`, doubled ODE `Vf δ' = DF(doubledField)(tube,Jf0)·Vf δ` on `[0,1]`);
        * the endpoint identification `L₂ δ = (Vf δ 1).2.1` and the per-seed second-jet Fréchet identity
          `HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp … q) w b) L₂ v`.
      This is the missing spec lemma naming the endpoint second-variation operator — the ingredient the
      base-slot second-jet modulus `hbaseJ2` (the SECOND-variation two-point Grönwall) will consume,
      exactly as `JacobiCLMExposure.uniformFlowExp_jacobi_spec` fed the first-jet base modulus `hbaseJ`.
      NOT `a₁ = R/6`.

  ⚠ WHAT REMAINS for the full `hbaseJ2` / `hFwd2` / the wall (future J4-482+; NOT here):
    * THE GRÖNWALL: the two-point second-variation bound assembling `‖(Vf_q δ 1).2.1 − (Vf_{q'} δ 1).2.1‖`
      over the two base doubled curves, via `BasepointJetModulus.linODE_twopoint_diff_bound` applied to
      the DOUBLED field (the base-curve separation = tube separation `uniformTube_twopoint_diff_bound`
      ⊕ the base-Jacobi separation `jacobi_twopoint_diff_bound`), then the double opNorm bound over the
      per-`(δ,b)` seed bound;
    * THE WELD: the `z₀`-anchored triangle (the `ForwardFlowJet` pattern one order up) + the K-uniform
      reachability guard, welding VELOCITY (`Flow3Regularity.forward2_velocitySlot`) + BASE (`hbaseJ2`)
      into the joint `hFwd2` on `K ×ˢ ball`, whence `ChartSecondJet.chartSecondJet_continuousOn_of_forward2`
      becomes UNCONDITIONAL — THE CONVERGENT WALL FALLS.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.UniformFlowSecondSupply
import QIQTH.UniformFlowHessian
import QIQTH.JacobiOperatorFDeriv
import QIQTH.BasepointJetModulus
import QIQTH.JacobiCLMExposure
import QIQTH.Flow3Regularity
import QIQTH.ChartSecondJet

open Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap
open scoped Topology NNReal

namespace QIQTH.SecondVariationModulus

variable {n : ℕ}

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 6

/-! ###############################################################################
    ### ★ THE EXPOSURE — re-derive the endpoint SECOND-variation operator as a public spec.
    ############################################################################### -/

/-- **★ `uniformFlowExp_secondVar_spec` — THE EXPOSURE.**  For `q ∈ K`, `‖v‖ < ρ_K`, and each variation
    seed `b`, the forward-flow SECOND jet (applied to `b`) is the endpoint DOUBLED second-variation
    operator along the base doubled curve through `(q,v)`.  Re-runs the compiled R2-a/R2-b construction
    (`uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt` ⊕ `uniformFlowExp_fderiv_apply_hasFDerivAt`)
    but CONCLUDES the full triple instead of just `∃ L₂, HasFDerivAt`:
      * a base velocity Jacobi field `Jf0` with `Jf0 0 = (0,b)` solving the Jacobi ODE on `[0,1]`
        along `uniformFlowTube g gi hC hK q v`;
      * a DOUBLED second-variation family `Vf` along the base doubled curve `(uniformFlowTube … q v, Jf0)`
        with seed `Vf δ 0 = ((0,δ),(0,0))` solving the doubled-linearized ODE
        `Vf δ' = DF(doubledField)(tube,Jf0)·Vf δ` on `[0,1]`;
      * the endpoint identification `L₂ δ = (Vf δ 1).2.1` and the per-seed second-jet Fréchet identity
        `HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp … q) w b) L₂ v`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_secondVar_spec (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (b : Point n) :
    ∃ (Jf0 : ℝ → Point n × Point n)
      (Vf : Point n → ℝ → (Point n × Point n) × (Point n × Point n))
      (L₂ : Point n →L[ℝ] Point n),
      Jf0 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt Jf0
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Jf0 τ)) τ) ∧
      (∀ δ : Point n, Vf δ 0 = (((0 : Point n), δ), ((0 : Point n), (0 : Point n)))) ∧
      (∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Vf δ)
          (fderiv ℝ (doubledField g gi)
            ((uniformFlowTube g gi hC hK q v τ, Jf0 τ) :
              (Point n × Point n) × (Point n × Point n)) (Vf δ τ)) τ) ∧
      (∀ δ : Point n, L₂ δ = (Vf δ 1).2.1) ∧
      HasFDerivAt (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) L₂ v := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  set σ : ℝ := ρ - ‖v‖ with hσdef
  have hσ : 0 < σ := by rw [hσdef]; linarith
  have h0σ : ‖(0 : Point n)‖ ≤ σ := by rw [norm_zero]; exact hσ.le
  have hle : ∀ δ : Point n, ‖δ‖ ≤ σ → ‖v + δ‖ ≤ ρ := by
    intro δ hδ
    refine (norm_add_le v δ).trans ?_
    rw [hσdef] at hδ; linarith
  have hadm0 : ‖v + (0 : Point n)‖ ≤ ρ := by rw [add_zero]; exact hv.le
  -- Uniform `fderiv (geodesicField)` bound over the geodesic-tube confinement ball.
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  have hJbound0 : 0 ≤ Jbound := by rw [hJbounddef]; positivity
  -- The confinement product set.
  set S : Set ((Point n × Point n) × (Point n × Point n)) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdef
  have hScompact : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hSconvex : Convex ℝ S := (convex_closedBall _ _).prod (convex_closedBall _ _)
  -- Per-δ velocity Jacobi field along the perturbed tube (genuine when `‖v+δ‖ ≤ ρ`).
  have key : ∀ δ : Point n, ∃ Jc : ℝ → Point n × Point n,
      (‖v + δ‖ ≤ ρ →
        Jc 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt Jc
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jc τ)) τ) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
        ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro δ
    by_cases h : ‖v + δ‖ ≤ ρ
    · set P : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q (v + δ) with hPdef
      have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) h τ hτoo).continuousAt).continuousWithinAt
      obtain ⟨Jc, hJc0, hJcode, hJcpad⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC P hPcont ((0 : Point n), b)
      have hfderivbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kb := by
        intro x hx
        refine hKbbd (P x) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖P x - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
      have hJcont : ContinuousOn Jc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hJcode τ hτ).continuousAt).continuousWithinAt
      have hJgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Jc x‖ ≤ gronwallBound ‖((0 : Point n), b)‖ Kb 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖((0 : Point n), b)‖)
          (K := Kb) (ε := 0) (a := 0) (b := 1) hJcont
          (fun x hx => (hJcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hJc0]))
          (fun x hx => by
            have hle' := (fderiv ℝ (geodesicField g gi) (P x)).le_opNorm (Jc x)
            calc ‖fderiv ℝ (geodesicField g gi) (P x) (Jc x)‖
                ≤ ‖fderiv ℝ (geodesicField g gi) (P x)‖ * ‖Jc x‖ := hle'
              _ ≤ Kb * ‖Jc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderivbd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb * ‖Jc x‖ + 0 := by ring)
      have hJcbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound := by
        intro τ hτ
        have h1 := hJgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hJbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb * τ ≤ Kb * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb0
          _ = Kb := mul_one _
      exact ⟨Jc, fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  set Jf : Point n → ℝ → Point n × Point n := fun δ => Classical.choose (key δ) with hJfdef
  -- The base doubled curve `W0 = (uniformFlowTube q v, Jf 0)`, padded continuous.
  set W0 : ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun τ => (uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ) with hW0def
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + 0) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) hadm0 τ hτoo).continuousAt).continuousWithinAt
  have hJf0pad : ContinuousOn (Jf 0) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    (Classical.choose_spec (key 0) hadm0).2.2.2
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) := hP0cont.prodMk hJf0pad
  -- The doubled-linearized field `V δ` along the fixed base doubled curve `W0`.
  have varkey : ∀ δ : Point n, ∃ Vc : ℝ → (Point n × Point n) × (Point n × Point n),
      Vc 0 = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt Vc (fderiv ℝ (doubledField g gi) (W0 τ) (Vc τ)) τ) := by
    intro δ
    exact doubledVariation_narrowpad_hasDerivAt_Icc g gi hC W0 hW0pad
      (((0 : Point n), δ), ((0 : Point n), (0 : Point n)))
  set Vf : Point n → ℝ → (Point n × Point n) × (Point n × Point n) :=
    fun δ => Classical.choose (varkey δ) with hVfdef
  -- The base-velocity seed CLM `δ ↦ ((0,δ),(0,0))`.
  set seedCLM : Point n →L[ℝ] (Point n × Point n) × (Point n × Point n) :=
    (ContinuousLinearMap.inl ℝ (Point n × Point n) (Point n × Point n)).comp
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) with hseedCLMdef
  have hseed_eq : ∀ δ : Point n,
      seedCLM δ = (((0 : Point n), δ), ((0 : Point n), (0 : Point n))) := by
    intro δ
    simp [hseedCLMdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, Prod.ext_iff]
  have hseednorm : ∀ δ : Point n, ‖seedCLM δ‖ = ‖δ‖ := by
    intro δ
    rw [hseed_eq δ]
    simp [Prod.norm_def, norm_nonneg]
  -- Discharge the J4-66 hypotheses.
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
        (doubledField g gi (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ)) τ := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, hJcode, _, _⟩ := Classical.choose_spec (key δ) hadm
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) hadm τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact doubledField_prod_hasDerivAt g gi hP (hJcode τ hτ)
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf δ) (fderiv ℝ (doubledField g gi) (W0 τ) (Vf δ τ)) τ :=
    fun δ => (Classical.choose_spec (varkey δ)).2
  have hV0 : ∀ δ : Point n, Vf δ 0 = seedCLM δ := by
    intro δ
    rw [hseed_eq δ]
    exact (Classical.choose_spec (varkey δ)).1
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ →
      ((uniformFlowTube g gi hC hK q (v + δ) 0, Jf δ 0) :
          (Point n × Point n) × (Point n × Point n))
        - (uniformFlowTube g gi hC hK q (v + 0) 0, Jf 0 0) = seedCLM δ := by
    intro δ hδ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    have hJfδ0 : Jf δ 0 = ((0 : Point n), b) := (Classical.choose_spec (key δ) hadm).1
    have hJf00 : Jf 0 0 = ((0 : Point n), b) := (Classical.choose_spec (key 0) hadm0).1
    have h1 : uniformFlowTube g gi hC hK q (v + δ) 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) hadm
    have h2 : uniformFlowTube g gi hC hK q (v + 0) 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) hadm0
    rw [h1, h2, hJfδ0, hJf00, hseed_eq δ]
    simp only [add_zero, Prod.mk_sub_mk, sub_self, add_sub_cancel_left]
    rfl
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) :
        (Point n × Point n) × (Point n × Point n)) ∈ S := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, _, hJcbnd, _⟩ := Classical.choose_spec (key δ) hadm
    rw [hSdef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖uniformFlowTube g gi hC hK q (v + δ) τ - ((q, 0) : Point n × Point n)‖
          ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) hadm τ hτ
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm hC₀nn
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hJcbnd τ hτ
  -- Feed J4-66 (KEEP the endpoint identification `hLeq : L δ = Vf δ 1`).
  obtain ⟨L, hLeq, hFD⟩ :=
    doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists g gi hC
      (W := fun δ t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
      (V := Vf) (seed := seedCLM) (S := S) (σ := σ)
      hScompact hSconvex hσ ht1 hseednorm hWode hVode hV0 hIC hmem
  -- The `hJf` first conjunct (R2-a assembly), for the R2-b window rewrite.
  have hJf : ∀ δ : Point n, ‖δ‖ ≤ σ →
      Jf δ 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jf δ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) := by
    intro δ hδ
    obtain ⟨hJc0, hJcode, _, _⟩ := Classical.choose_spec (key δ) (hle δ hδ)
    exact ⟨hJc0, hJcode⟩
  -- ── R2-b — project the `.2.1` component and recentre `δ ↦ v + δ`.
  set proj21 : ((Point n × Point n) × (Point n × Point n)) →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      (ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)) with hproj21def
  set L₂ : Point n →L[ℝ] Point n := proj21.comp L with hL₂def
  have hFDproj : HasFDerivAt (fun δ => (Jf δ 1).1) L₂ 0 := by
    have hc := proj21.hasFDerivAt.comp (0 : Point n) hFD
    have hfe : (⇑proj21 ∘ fun δ => ((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1) :
        (Point n × Point n) × (Point n × Point n))) = (fun δ => (Jf δ 1).1) := by
      funext δ
      show proj21 (uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1) = (Jf δ 1).1
      simp [hproj21def, ContinuousLinearMap.comp_apply]
    rw [hfe] at hc
    exact hc
  -- On the open velocity window, `(Jf δ 1).1 = fderiv (uniformFlowExp q) (v+δ) b`.
  have hEq : (fun δ => (Jf δ 1).1)
      =ᶠ[𝓝 (0 : Point n)]
      (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) := by
    have hball : Metric.ball (0 : Point n) σ ∈ 𝓝 (0 : Point n) :=
      Metric.ball_mem_nhds _ hσ
    refine Filter.eventuallyEq_of_mem hball (fun δ hδ => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hδ
    have hδσ : ‖δ‖ ≤ σ := hδ.le
    have hvδ : ‖v + δ‖ < ρ := by
      refine lt_of_le_of_lt (norm_add_le v δ) ?_
      rw [hσdef] at hδ; linarith
    obtain ⟨hJc0, hJcode⟩ := hJf δ hδσ
    exact (uniformFlowExp_fderiv_apply_eq g gi hC hK q hq (v + δ) hvδ b (Jf δ) hJc0 hJcode).symm
  have hFDproj2 : HasFDerivAt (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) L₂ 0 :=
    hFDproj.congr_of_eventuallyEq hEq.symm
  have hshift : HasFDerivAt (fun u : Point n => u - v) (ContinuousLinearMap.id ℝ (Point n)) v :=
    (hasFDerivAt_id v).sub_const v
  have hFD0 : HasFDerivAt (fun δ => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + δ) b) L₂ (v - v) := by
    rw [sub_self]; exact hFDproj2
  have hcomp : HasFDerivAt (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + (u - v)) b)
      (L₂.comp (ContinuousLinearMap.id ℝ (Point n))) v :=
    hFD0.comp (f := fun u : Point n => u - v) v hshift
  have hfun2 : (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) (v + (u - v)) b)
      = (fun w => fderiv ℝ (uniformFlowExp g gi hC hK q) w b) := by
    funext u; congr 2; abel
  rw [hfun2, ContinuousLinearMap.comp_id] at hcomp
  -- ── Assemble the exposure.
  refine ⟨Jf 0, Vf, L₂, ?_, ?_, ?_, ?_, ?_, hcomp⟩
  · exact (hJf 0 h0σ).1
  · have hbase := (hJf 0 h0σ).2
    simpa only [add_zero] using hbase
  · intro δ; rw [hV0 δ, hseed_eq δ]
  · intro δ τ hτ
    have h := hVode δ τ hτ
    rw [hW0def] at h
    simpa only [add_zero] using h
  · intro δ
    rw [hL₂def]
    show proj21 (L δ) = (Vf δ 1).2.1
    rw [hLeq δ]
    simp [hproj21def, ContinuousLinearMap.comp_apply]

/-! ###############################################################################
    ### ★★ THE COMPONENT ODE — the `.2`-slot inhomogeneous Jacobi ODE of the 2nd-variation.
    ############################################################################### -/

/-- **★★ `secondVar_snd_hasDerivAt` — the `.2`-component inhomogeneous Jacobi ODE.**  If a doubled
    second-variation field `V` solves the doubled-linearized ODE `V' = DF(doubledField)(Ybase,Jbase)·V`
    along a base doubled curve `(Ybase, Jbase)` (`Ybase` = the base geodesic, `Jbase` = the base Jacobi
    field `Jf0`), then its Jacobi-slot component `t ↦ (V t).2` solves the INHOMOGENEOUS scalar-Jacobi ODE
        `(V·).2' = DF(geodesicField)(Ybase)·(V·).2  +  D²F(geodesicField)(Ybase)·(V·).1·Jbase`,
    the second summand a genuine curvature SOURCE driven by the base-velocity slot `(V·).1` (∝ the
    velocity perturbation `δ`) and the base Jacobi field `Jbase` (∝ the seed `b`).  This is the correct
    equation for the base-slot modulus `hbaseJ2`: the SOURCE (not the full doubled norm) carries the
    joint `δ·b` bilinearity that a naive full-doubled-norm Grönwall would lose.  DERIVED by projecting
    the doubled ODE (`HasFDerivAt.comp_hasDerivAt` with `ContinuousLinearMap.snd`) and rewriting via
    `doubledField_fderiv_snd_apply`.  NOT `a₁ = R/6`. -/
theorem secondVar_snd_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {V : ℝ → (Point n × Point n) × (Point n × Point n)} {Ybase Jbase : ℝ → Point n × Point n} {τ : ℝ}
    (hV : HasDerivAt V
      (fderiv ℝ (doubledField g gi)
        ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)) τ) :
    HasDerivAt (fun t => (V t).2)
      (fderiv ℝ (geodesicField g gi) (Ybase τ) ((V τ).2)
        + fderiv ℝ (fderiv ℝ (geodesicField g gi)) (Ybase τ) ((V τ).1) (Jbase τ)) τ := by
  have hsnd : HasDerivAt (fun t => (V t).2)
      ((fderiv ℝ (doubledField g gi)
        ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)).2) τ := by
    have h := (ContinuousLinearMap.snd ℝ (Point n × Point n)
      (Point n × Point n)).hasFDerivAt.comp_hasDerivAt τ hV
    simpa using h
  rwa [doubledField_fderiv_snd_apply g gi hC
    ((Ybase τ, Jbase τ) : (Point n × Point n) × (Point n × Point n)) (V τ)] at hsnd

end QIQTH.SecondVariationModulus

/-! ## THE MODULUS LEDGER (post J4-481).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE CONVERGENT WALL.  Both a₁=R/6 consumer chains bottom out on the chart SECOND field-jet at the │
  │  field centre `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0`; J4-479 reduced it  │
  │  to the atom `hFwd2` (joint continuity of the forward SECOND jet); J4-480 discharged the VELOCITY  │
  │  slot (`Flow3Regularity.forward2_velocitySlot`).  REMAINING: the BASE slot `hbaseJ2`.              │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (i) THE EXPOSURE — `uniformFlowExp_secondVar_spec` (DERIVED, the star).  Re-runs the compiled     │
  │  R2-a/R2-b construction KEEPING the discarded endpoint identification `_hLeq : L δ = Vf δ 1`, and  │
  │  concludes the full second-variation triple: the base velocity Jacobi field `Jf0` (seed `(0,b)`,   │
  │  Jacobi ODE along `uniformFlowTube q v`); the DOUBLED second-variation field `Vf` along the base    │
  │  doubled curve `(tube q v, Jf0)` (seed `((0,δ),(0,0))`, doubled ODE `Vf δ' = DF(doubledField)·Vf δ`);│
  │  the endpoint identification `L₂ δ = (Vf δ 1).2.1`; and the per-seed second-jet Fréchet identity    │
  │  `HasFDerivAt (fun w => fderiv (uniformFlowExp q) w b) L₂ v`.  This is the J4-435                   │
  │  `uniformFlowExp_jacobi_spec` one order up — the missing spec naming the endpoint operator.        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (ii) THE COMPONENT ODE — `secondVar_snd_hasDerivAt` (DERIVED).  The `.2`-slot of the doubled       │
  │  second-variation field solves the INHOMOGENEOUS scalar-Jacobi ODE                                  │
  │      `(V·).2' = DF(geo)(Ybase)·(V·).2 + D²F(geo)(Ybase)·(V·).1·Jbase`,                              │
  │  the curvature SOURCE `D²F·(V·).1·Jbase` carrying the joint `δ·b` bilinearity.  This is the correct │
  │  equation for `hbaseJ2` — the exact input `linODE_twopoint_diff_bound` (inhomogeneous variant)      │
  │  consumes at the next brick.                                                                        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  WHAT REMAINS for full `hbaseJ2` / `hFwd2` / the wall (future J4-482+):                            │
  │    • THE GRÖNWALL: `‖(Vf_q δ 1).2 − (Vf_{q'} δ 1).2‖ ≤ Λ·‖q−q'‖·‖δ‖·‖b‖` via                        │
  │      `linODE_twopoint_diff_bound` on the `.2`-COMPONENT ODE (`secondVar_snd_hasDerivAt`, same       │
  │      zero seed) — NOT the full doubled field: the SOURCE difference `Dsrc` (∝ `δ·b·‖q−q'‖`) and the │
  │      coefficient separation `Dcoef` (∝ `‖q−q'‖` via `uniformTube_twopoint_diff_bound`) carry the    │
  │      `‖b‖` factor a full-doubled-norm bound would lose.  The base-Jacobi separation                 │
  │      (`Jf0_q − Jf0_{q'}`, entering `Dsrc`) is `jacobi_twopoint_diff_bound`; the `(V·).1`-slot bound │
  │      (∝ `δ`) is homogeneous Jacobi growth (`jacobi_growth_bound`).  Then the double opNorm over     │
  │      `(δ,b)` gives `hbaseJ2 : ‖fderiv² (uniformFlowExp q) v − fderiv² (uniformFlowExp q') v‖ ≤ Λ·‖q−q'‖`.│
  │    • THE WELD: the `z₀`-anchored triangle (`ForwardFlowJet` one order up) + K-uniform reachability, │
  │      welding VELOCITY (J4-480) + BASE (`hbaseJ2`) into the joint `hFwd2` ⟹                          │
  │      `ChartSecondJet.chartSecondJet_continuousOn_of_forward2` UNCONDITIONAL ⟹ THE WALL FALLS.       │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT.  The endpoint SECOND-variation operator `δ ↦ (Vf δ 1).2.1` and its doubled ODE
  were ALREADY BUILT (R2-a `uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt`, J4-67); only the
  endpoint identification `_hLeq` was DISCARDED.  The banked two-point Grönwall engine
  `BasepointJetModulus.linODE_twopoint_diff_bound` is fully generic (any CLM coefficients + source terms)
  and applies to the `.2`-component ODE directly.  ⚠ THE NON-OBVIOUS FINDING: the naive full-doubled-norm
  Grönwall (the first-order `JacobiCLMExposure` pattern read literally) FAILS `hbaseJ2` — the full norm
  `‖Vf δ 1‖` is dominated by the `.1`-slot (∝ `δ`, independent of `b`), so it cannot deliver the `∝‖b‖`
  factor the operator norm `‖B₂ − B₂'‖ = sup_{‖δ‖,‖b‖≤1} ‖((B₂−B₂')δ)b‖` requires.  The `.2`-component
  inhomogeneous ODE (`secondVar_snd_hasDerivAt`, landed here) is the fix.  So `hbaseJ2` is a spec-exposure
  + a component-ODE + a two-point Grönwall assembly, NOT a new ODE-existence effort.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.SecondVariationModulus
#print axioms uniformFlowExp_secondVar_spec
#print axioms secondVar_snd_hasDerivAt
end AxiomChecks
