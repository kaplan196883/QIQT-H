/-
  UniformFlowExpFourthJetValueId — Plan v6 Task I (C³ climb, brick 4): the FOURTH-JET VALUE-IDENTITY
  (`Z1↑`), one order up from `UniformFlowThirdJetClose.uniformFlowExp_hessian_value_id` (`Z1`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  The genuine new content of the C³-unconditional climb:
  identifying the deep component of a genuine quadrupled-linearized field endpoint with the applied
  third Fréchet jet of `uniformFlowExp`, re-derived DIRECTLY on the uniform tube (NO `expRho`).

  ── WHAT LANDS (DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `uniformFlowExp_thirdJet_value_id` (**Z1↑**) — for a base point `q ∈ K`, an admissible base
      velocity `v` (`‖v‖ < ρ_K`), seeds `a b c`, a genuine velocity-Jacobi field `J` (seed `(0,b)`,
      along `uniformFlowTube q v`), a genuine `doubledField`-linearized field `U` (seed `((0,a),(0,0))`,
      along `(uniformFlowTube q v, J)`), and a genuine `quadrupledField`-linearized field `T` (seed
      `(((0,c),(0,0)),((0,0),(0,0)))`, along `((uniformFlowTube q v, J), U)`),
          `(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c a b
             = (T 1).2.2.1`.
      DERIVED, mirroring `Z1` ONE ORDER UP:
        (1) build the scalar-`s` quadruple supply `Q s = ((tube(v+s•c), Jˢ), Uˢ)` (mirror `Z1`'s `keyJ`
            + a new `keyU` for the doubled-linearized factor), confined in a compact convex product ball;
        (2) build the `quadrupledField`-linearized variation field `Vf` along the base curve `Q 0` (seed
            `Tseed`) via `linODE_exists_narrowpad_continuousOn`;
        (3) `quadrupledField_variation_exists_uncond` [J4-779] ⟹ `HasDerivAt (fun s => Q s 1) (Vf 1) 0`;
        (4) `Z1` [banked] at velocity `v+s•c` identifies `(Q s 1).2.2.1 = (Uˢ 1).2.1
            = (fderiv f₂ (v+s•c)) a b` on the open window ⟹ (project + `congr_of_eventuallyEq`)
            `HasDerivAt (fun s => (fderiv f₂ (v+s•c)) a b) ((Vf 1).2.2.1) 0`;
        (5) `uniformFlowExp_hessianMap_differentiableAt` [banked] + the directional/eval-CLM chain ⟹
            `HasDerivAt (fun s => (fderiv f₂ (v+s•c)) a b) (B₃ c a b) 0`;
        (6) `HasDerivAt.unique` ⟹ `B₃ c a b = (Vf 1).2.2.1`;
        (7) glue `Vf ≡ T` on `[0,1]` via `jacobiSol_unique` (`Jˢ|₀ ≡ J`) then `autonomousLinODE_unique`
            twice (`Uˢ|₀ ≡ U`, then `Vf ≡ T`), whence `(Vf 1).2.2.1 = (T 1).2.2.1`.
      The value id is `Z1` (a compiled theorem), NOT assumed.  Slot order: `B₃ · c a b` with `c` the
      derivative direction (`T`-seed), `a` the first Hessian slot (`U`-seed), `b` the second (`J`-seed) —
      matches the octuple supply (`uniformFlow_octupleEndpoint_component_hasFDerivAt`, seeds `a b c`)
      exactly, NO symmetry bridge needed.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowThirdJetClose
import QIQTH.UniformFlowThirdBoundClose
import QIQTH.UniformFlowQuadrupleVariation
import QIQTH.UniformFlowOctupleSupply
import QIQTH.QuadrupleFlowSupply
import QIQTH.DoubledFamilyConstruction
import QIQTH.DoubledVariationField
import QIQTH.BasepointFDeriv
import QIQTH.UniformFlowSecondFDeriv
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 1000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-- **Z1↑ — the fourth-jet value-identity.**  For a base point `q ∈ K`, an admissible base velocity `v`
    (`‖v‖ < ρ_K`), seeds `a b c`, a genuine velocity-Jacobi field `J` (seed `(0,b)`, along
    `uniformFlowTube q v`), a genuine `doubledField`-linearized field `U` (seed `((0,a),(0,0))`, along
    `(uniformFlowTube q v, J)`), and a genuine `quadrupledField`-linearized field `T` (seed
    `(((0,c),(0,0)),((0,0),(0,0)))`, along `((uniformFlowTube q v, J), U)`),
        `(fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c a b
           = (T 1).2.2.1`.
    DERIVED via the scalar-`s` quadruple supply + `quadrupledField_variation_exists_uncond` [J4-779]
    + `Z1` [banked] + `uniformFlowExp_hessianMap_differentiableAt` [banked] + ODE-uniqueness gluing. -/
theorem uniformFlowExp_thirdJet_value_id (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c : Point n)
    (J : ℝ → Point n × Point n)
    (hJ0 : J 0 = ((0 : Point n), b))
    (hJode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt J (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (J τ)) τ)
    (U : ℝ → St2 n)
    (hU0 : U 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))))
    (hUode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt U
        (fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, J τ) (U τ)) τ)
    (T : ℝ → St4 n)
    (hT0 : T 0 = ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
      (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))))
    (hTode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt T
        (fderiv ℝ (genericDoubled (doubledField g gi))
          ((uniformFlowTube g gi hC hK q v τ, J τ), U τ) (T τ)) τ) :
    (fderiv ℝ (fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w) v) c a b
      = (T 1).2.2.1 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hvρ : ‖v‖ < ρ := hv
  set f2 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w with hf2def
  set B₃ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n := fderiv ℝ f2 v with hB₃def
  have hD1 : HasFDerivAt f2 B₃ v :=
    (uniformFlowExp_hessianMap_differentiableAt g gi hC hK q hq v hv).hasFDerivAt
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- ===== Scalar-`s` window (perturbation direction `c`). =====
  set σ : ℝ := (ρ - ‖v‖) / (2 * (1 + ‖c‖)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact div_pos (by linarith) (by positivity)
  have hwin : ∀ s : ℝ, s ∈ Set.Icc (-σ) σ → ‖v + s • c‖ < ρ := by
    intro s hs
    have habs : |s| ≤ σ := abs_le.mpr ⟨hs.1, hs.2⟩
    have hσc : σ * ‖c‖ ≤ (ρ - ‖v‖) / 2 := by
      have hval : σ = (ρ - ‖v‖) / (2 * (1 + ‖c‖)) := by rw [hσdef]
      rw [hval, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg c, (show (0 : ℝ) < ρ - ‖v‖ by linarith)]
    have h1 : ‖v + s • c‖ ≤ ‖v‖ + |s| * ‖c‖ := by
      calc ‖v + s • c‖ ≤ ‖v‖ + ‖s • c‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖c‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |s| * ‖c‖ ≤ σ * ‖c‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg c)
    linarith
  have hadm0 : ‖v + (0 : ℝ) • c‖ ≤ ρ := by rw [zero_smul, add_zero]; exact hv.le
  -- ===== Confinement constants (mirror the octuple supply). =====
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  set Sdbl : Set (St2 n) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdbldef
  have hSdblcompact : IsCompact Sdbl := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨Kb2, hKb20, hKb2bd⟩ := doubledField_fderiv_bddOn_compact g gi hC hSdblcompact
  set Useed : St2 n := (((0 : Point n), a), ((0 : Point n), (0 : Point n))) with hUseeddef
  set Ubound : ℝ := ‖Useed‖ * Real.exp Kb2 with hUbounddef
  set Squad : Set (St4 n) :=
    Sdbl ×ˢ Metric.closedBall (0 : St2 n) Ubound with hSquaddef
  have hSquadcompact : IsCompact Squad := hSdblcompact.prod (isCompact_closedBall _ _)
  have hSquadconvex : Convex ℝ Squad :=
    ((convex_closedBall _ _).prod (convex_closedBall _ _)).prod (convex_closedBall _ _)
  obtain ⟨Kb3, hKb30, hKb3bd⟩ := quadrupledField_fderiv_bddOn_compact g gi hC hSquadcompact
  set Tseed : St4 n :=
    ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
      (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) with hTseeddef
  have hcontDbl : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  -- ===== Per-`s` velocity-Jacobi `Jc` + doubled-linearized `Uc`, confined. =====
  have key : ∀ s : ℝ,
      ∃ Jc : ℝ → Point n × Point n,
      ∃ Uc : ℝ → St2 n,
        (‖v + s • c‖ ≤ ρ →
          Jc 0 = ((0 : Point n), b) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Jc
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • c) τ) (Jc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
          ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Uc 0 = Useed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Uc
              (fderiv ℝ (doubledField g gi)
                (uniformFlowTube g gi hC hK q (v + s • c) τ, Jc τ) (Uc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound) ∧
          ContinuousOn Uc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro s
    by_cases h : ‖v + s • c‖ ≤ ρ
    · set P : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q (v + s • c) with hPdef
      have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + s • c) h τ hτoo).continuousAt).continuousWithinAt
      -- Jacobi factor.
      obtain ⟨Jc, hJc0, hJcode, hJcpad⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC P hPcont ((0 : Point n), b)
      have hfderivbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kb := by
        intro x hx
        refine hKbbd (P x) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖P x - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + s • c‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • c) h x hx
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
      -- doubled base curve `(P, Jc)`, padded continuous.
      have hYdblpad : ContinuousOn (fun τ => (P τ, Jc τ)) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hPcont.prodMk hJcpad
      set Adbl : ℝ → (St2 n →L[ℝ] St2 n) :=
        fun τ => fderiv ℝ (doubledField g gi) (P τ, Jc τ) with hAdbldef
      have hAdbl : ContinuousOn Adbl (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hcontDbl.comp_continuousOn hYdblpad
      obtain ⟨Uc, hUc0, hUcode, hUcpad⟩ :=
        linODE_exists_narrowpad_continuousOn Adbl hAdbl Useed
      have hUcont : ContinuousOn Uc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hUcode τ hτ).continuousAt).continuousWithinAt
      have hfderiv2bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (doubledField g gi) (P x, Jc x)‖ ≤ Kb2 := by
        intro x hx
        refine hKb2bd (P x, Jc x) ?_
        rw [hSdbldef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖P x - ((q, 0) : Point n × Point n)‖
              ≤ C₀ * ‖v + s • c‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • c) h x hx
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hJcbnd x hx
      have hUgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Uc x‖ ≤ gronwallBound ‖Useed‖ Kb2 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖Useed‖)
          (K := Kb2) (ε := 0) (a := 0) (b := 1) hUcont
          (fun x hx => (hUcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hUc0]))
          (fun x hx => by
            have hle' := (fderiv ℝ (doubledField g gi) (P x, Jc x)).le_opNorm (Uc x)
            calc ‖fderiv ℝ (doubledField g gi) (P x, Jc x) (Uc x)‖
                ≤ ‖fderiv ℝ (doubledField g gi) (P x, Jc x)‖ * ‖Uc x‖ := hle'
              _ ≤ Kb2 * ‖Uc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderiv2bd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb2 * ‖Uc x‖ + 0 := by ring)
      have hUcbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound := by
        intro τ hτ
        have h1 := hUgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hUbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb2 * τ ≤ Kb2 * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb20
          _ = Kb2 := mul_one _
      refine ⟨Jc, Uc,
        fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad, hUc0, ?_, hUcbnd, hUcpad⟩⟩
      intro τ hτ; have := hUcode τ hτ; rwa [hAdbldef] at this
    · exact ⟨fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
  set Jf : ℝ → ℝ → Point n × Point n := fun s => Classical.choose (key s) with hJfdef
  set Uf : ℝ → ℝ → St2 n := fun s => Classical.choose (Classical.choose_spec (key s)) with hUfdef
  have hspec : ∀ s : ℝ, ‖v + s • c‖ ≤ ρ →
      Jf s 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jf s)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • c) τ) (Jf s τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf s τ‖ ≤ Jbound) ∧
      ContinuousOn (Jf s) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Uf s 0 = Useed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Uf s)
          (fderiv ℝ (doubledField g gi)
            (uniformFlowTube g gi hC hK q (v + s • c) τ, Jf s τ) (Uf s τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uf s τ‖ ≤ Ubound) ∧
      ContinuousOn (Uf s) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    fun s => Classical.choose_spec (Classical.choose_spec (key s))
  -- The scalar-`s` quadruple family `Q s = ((tube(v+s•c), Jf s), Uf s)`.
  set Q : ℝ → ℝ → St4 n :=
    fun s t => ((uniformFlowTube g gi hC hK q (v + s • c) t, Jf s t), Uf s t) with hQdef
  -- Base curve `Q 0`, padded continuous.
  obtain ⟨hJf00, hJf0ode, hJf0bnd, hJf0pad, hUf00, hUf0ode, hUf0bnd, hUf0pad⟩ := hspec 0 hadm0
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + (0 : ℝ) • c) hadm0 τ hτoo).continuousAt).continuousWithinAt
  set W0 : ℝ → St4 n :=
    fun τ => ((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) τ, Jf 0 τ), Uf 0 τ) with hW0def
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    (hP0cont.prodMk hJf0pad).prodMk hUf0pad
  have hcontQuad : Continuous (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    (contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)
  set Aquad : ℝ → (St4 n →L[ℝ] St4 n) :=
    fun τ => fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) with hAquaddef
  have hAquad : ContinuousOn Aquad (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    hcontQuad.comp_continuousOn hW0pad
  obtain ⟨Vf, hVf0, hVfode, _⟩ := linODE_exists_narrowpad_continuousOn Aquad hAquad Tseed
  -- ===== The quadruple-variation derivative:  `HasDerivAt (fun s => Q s 1) (Vf 1) 0`. =====
  have hVar : HasDerivAt (fun s => Q s 1) (Vf 1) 0 := by
    refine quadrupledField_variation_exists_uncond g gi hC (S := Squad) (σ := σ)
      hSquadcompact hSquadconvex ht1 hσpos ?_ ?_ hVf0 ?_ ?_
    · -- hYode
      intro s hs τ hτ
      have hsρ : ‖v + s • c‖ ≤ ρ := (hwin s hs).le
      obtain ⟨_, hJsode, _, _, _, hUsode, _, _⟩ := hspec s hsρ
      have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + s • c) hsρ τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hYdbl := doubledField_prod_hasDerivAt g gi hP (hJsode τ hτ)
      exact genericDoubled_prod_hasDerivAt (doubledField g gi) hYdbl (hUsode τ hτ)
    · -- hVode : along `Q 0 = W0`
      intro τ hτ; have := hVfode τ hτ; rwa [hAquaddef] at this
    · -- hIC
      intro s hs
      have hsρ : ‖v + s • c‖ ≤ ρ := (hwin s hs).le
      obtain ⟨hJs0, _, _, _, hUs0, _, _, _⟩ := hspec s hsρ
      have h1 : uniformFlowTube g gi hC hK q (v + s • c) 0 = (q, v + s • c) :=
        uniformFlowTube_spec_ic g gi hC hK q hq (v + s • c) hsρ
      have h2 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) 0 = (q, v + (0 : ℝ) • c) :=
        uniformFlowTube_spec_ic g gi hC hK q hq (v + (0 : ℝ) • c) hadm0
      show ((uniformFlowTube g gi hC hK q (v + s • c) 0, Jf s 0), Uf s 0)
          - ((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) 0, Jf 0 0), Uf 0 0) = s • Tseed
      rw [h1, h2, hJs0, hJf00, hUs0, hUf00, hUseeddef, hTseeddef, zero_smul, add_zero]
      simp only [Prod.mk_sub_mk, sub_self, add_sub_cancel_left, Prod.smul_mk, smul_zero,
        Prod.mk_zero_zero]
    · -- hmem
      intro s hs τ hτ
      have hsρ : ‖v + s • c‖ ≤ ρ := (hwin s hs).le
      obtain ⟨_, _, hJsbnd, _, _, _, hUsbnd, _⟩ := hspec s hsρ
      show ((uniformFlowTube g gi hC hK q (v + s • c) τ, Jf s τ), Uf s τ) ∈ Squad
      rw [hSquaddef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [hSdbldef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖uniformFlowTube g gi hC hK q (v + s • c) τ - ((q, 0) : Point n × Point n)‖
              ≤ C₀ * ‖v + s • c‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • c) hsρ τ hτ
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hsρ hC₀nn
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hJsbnd τ hτ
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hUsbnd τ hτ
  -- ===== The projected deep component:  `HasDerivAt (fun s => (Q s 1).2.2.1) ((Vf 1).2.2.1) 0`. =====
  set proj : St4 n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      ((ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp
        (ContinuousLinearMap.snd ℝ (St2 n) (St2 n))) with hprojdef
  have hproj_apply : ∀ z : St4 n, proj z = z.2.2.1 := fun z => rfl
  have hproj : HasDerivAt (fun s => (Q s 1).2.2.1) ((Vf 1).2.2.1) 0 := by
    have h := proj.hasFDerivAt.comp_hasDerivAt 0 hVar
    simpa [hproj_apply] using h
  -- ===== `Z1` at velocity `v+s•c`:  `(Q s 1).2.2.1 = (f₂ (v+s•c)) a b`  eventually. =====
  have hEqS : (fun s => (Q s 1).2.2.1) =ᶠ[𝓝 (0 : ℝ)] (fun s => (f2 (v + s • c)) a b) := by
    have hballs : Metric.ball (0 : ℝ) σ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hσpos
    refine Filter.eventuallyEq_of_mem hballs (fun s hs => ?_)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    have hsmem : s ∈ Set.Icc (-σ) σ := ⟨by linarith [(abs_le.mp hs.le).1], (abs_le.mp hs.le).2⟩
    have hsρ : ‖v + s • c‖ < ρ := hwin s hsmem
    obtain ⟨hJs0, hJsode, _, _, hUs0, hUsode, _, _⟩ := hspec s hsρ.le
    have hz1 := uniformFlowExp_hessian_value_id g gi hC hK q hq (v + s • c) hsρ a b
      (Jf s) hJs0 hJsode (Uf s) hUs0 hUsode
    show (Q s 1).2.2.1 = (f2 (v + s • c)) a b
    rw [hf2def]
    exact hz1.symm
  have hLHS : HasDerivAt (fun s : ℝ => (f2 (v + s • c)) a b) ((Vf 1).2.2.1) 0 :=
    hproj.congr_of_eventuallyEq hEqS.symm
  -- ===== The directional/eval chain:  `HasDerivAt (fun s => (f₂ (v+s•c)) a b) (B₃ c a b) 0`. =====
  have hline : HasDerivAt (fun s : ℝ => v + s • c) c 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const c
    exact h1.const_add v
  have hD1' : HasFDerivAt f2 B₃ (v + (0 : ℝ) • c) := by simpa using hD1
  have hcomp : HasDerivAt (fun s : ℝ => f2 (v + s • c)) (B₃ c) 0 := by
    simpa using hD1'.comp_hasDerivAt 0 hline
  set E1 : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] (Point n →L[ℝ] Point n) :=
    ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n) a with hE1def
  set E2 : (Point n →L[ℝ] Point n) →L[ℝ] Point n :=
    ContinuousLinearMap.apply ℝ (Point n) b with hE2def
  set ev : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] Point n := E2.comp E1 with hevdef
  have hev_apply : ∀ T : Point n →L[ℝ] Point n →L[ℝ] Point n, ev T = T a b := fun T => rfl
  have hRHS : HasDerivAt (fun s : ℝ => (f2 (v + s • c)) a b) (B₃ c a b) 0 := by
    have h := ev.hasFDerivAt.comp_hasDerivAt 0 hcomp
    simpa [hev_apply] using h
  -- ===== Uniqueness of the scalar directional derivative:  `(Vf 1).2.2.1 = B₃ c a b`. =====
  have hVfB₃ : (Vf 1).2.2.1 = B₃ c a b := hLHS.unique hRHS
  -- ===== ODE-uniqueness gluing:  `Vf ≡ T` on `[0,1]`. =====
  -- Step A: `Jf 0 ≡ J`  (`jacobiSol_unique` along `tube v`).
  have htube0 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) = uniformFlowTube g gi hC hK q v := by
    rw [zero_smul, add_zero]
  have hTubeV_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (uniformFlowTube g gi hC hK q v) (geodesicField g gi (uniformFlowTube g gi hC hK q v τ)) τ :=
    fun τ hτ => uniformFlowTube_spec_ode g gi hC hK q hq v hvρ.le τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hKbtubeV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ)‖ ≤ Kb := by
    intro τ hτ
    refine hKbbd (uniformFlowTube g gi hC hK q v τ) ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖uniformFlowTube g gi hC hK q v τ - ((q, 0) : Point n × Point n)‖
        ≤ C₀ * ‖v‖ := uniformFlowTube_spec_conf g gi hC hK q hq v hvρ.le τ hτ
      _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ.le hC₀nn
  have hJf0odeV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Jf 0)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Jf 0 τ)) τ := by
    intro τ hτ; rw [← htube0]; exact hJf0ode τ hτ
  have hJeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, J τ = Jf 0 τ := by
    intro τ hτ
    refine jacobiSol_unique g gi hKb0 (Y0 := uniformFlowTube g gi hC hK q v) (J₁ := J) (J₂ := Jf 0)
      hTubeV_ode hKbtubeV hJode hJf0odeV ?_ hτ
    rw [hJ0, hJf00]
  -- Step B: `Uf 0 ≡ U`  (`autonomousLinODE_unique`, `doubledField` along `(tube v, J)`).
  have hbaseDbl_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (uniformFlowTube g gi hC hK q v t, J t))
        (doubledField g gi (uniformFlowTube g gi hC hK q v τ, J τ)) τ :=
    fun τ hτ => doubledField_prod_hasDerivAt g gi (hTubeV_ode τ hτ) (hJode τ hτ)
  have hJmemDbl : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      (uniformFlowTube g gi hC hK q v τ, J τ) ∈ Sdbl := by
    intro τ hτ
    rw [hSdbldef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖uniformFlowTube g gi hC hK q v τ - ((q, 0) : Point n × Point n)‖
          ≤ C₀ * ‖v‖ := uniformFlowTube_spec_conf g gi hC hK q hq v hvρ.le τ hτ
        _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hvρ.le hC₀nn
    · rw [Metric.mem_closedBall, dist_zero_right, hJeq τ hτ]; exact hJf0bnd τ hτ
  have hKbdblV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, J τ)‖ ≤ Kb2 :=
    fun τ hτ => hKb2bd _ (hJmemDbl τ hτ)
  have hUf0odeV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Uf 0)
        (fderiv ℝ (doubledField g gi) (uniformFlowTube g gi hC hK q v τ, J τ) (Uf 0 τ)) τ := by
    intro τ hτ
    have h := hUf0ode τ hτ
    rw [htube0, ← hJeq τ hτ] at h
    exact h
  have hUeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, U τ = Uf 0 τ := by
    intro τ hτ
    refine autonomousLinODE_unique (doubledField g gi) hKb20
      (Y0 := fun t => (uniformFlowTube g gi hC hK q v t, J t)) (J₁ := U) (J₂ := Uf 0)
      hbaseDbl_ode hKbdblV hUode hUf0odeV ?_ hτ
    rw [hU0, hUf00]
  -- Step C: `Vf ≡ T`  (`autonomousLinODE_unique`, `quadrupledField` along `Q 0 = W0`).
  have hbaseQ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      W0 τ = ((uniformFlowTube g gi hC hK q v τ, J τ), U τ) := by
    intro τ hτ
    show ((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) τ, Jf 0 τ), Uf 0 τ)
        = ((uniformFlowTube g gi hC hK q v τ, J τ), U τ)
    rw [htube0, ← hJeq τ hτ, ← hUeq τ hτ]
  -- `W0` is a `quadrupledField` integral curve (direct product-rule packaging, no rewrite).
  have hQ0_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt W0 (genericDoubled (doubledField g gi) (W0 τ)) τ := by
    intro τ hτ
    have hPtube0 := uniformFlowTube_spec_ode g gi hC hK q hq (v + (0 : ℝ) • c) hadm0 τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hYdbl0 := doubledField_prod_hasDerivAt g gi hPtube0 (hJf0ode τ hτ)
    exact genericDoubled_prod_hasDerivAt (doubledField g gi) hYdbl0 (hUf0ode τ hτ)
  -- `W0 τ ∈ Squad`, hence the linearized-coefficient bound.
  have hW0mem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W0 τ ∈ Squad := by
    intro τ hτ
    show ((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) τ, Jf 0 τ), Uf 0 τ) ∈ Squad
    rw [hSquaddef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [hSdbldef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖uniformFlowTube g gi hC hK q (v + (0 : ℝ) • c) τ - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + (0 : ℝ) • c‖ :=
              uniformFlowTube_spec_conf g gi hC hK q hq (v + (0 : ℝ) • c) hadm0 τ hτ
          _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm0 hC₀nn
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hJf0bnd τ hτ
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hUf0bnd τ hτ
  have hKbquadW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ)‖ ≤ Kb3 :=
    fun τ hτ => hKb3bd _ (hW0mem τ hτ)
  have hVfodeW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Vf (fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) (Vf τ)) τ := by
    intro τ hτ; have := hVfode τ hτ; rwa [hAquaddef] at this
  have hTodeW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt T (fderiv ℝ (genericDoubled (doubledField g gi)) (W0 τ) (T τ)) τ := by
    intro τ hτ; have h := hTode τ hτ; rw [← hbaseQ τ hτ] at h; exact h
  have hVeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Vf τ = T τ := by
    intro τ hτ
    refine autonomousLinODE_unique (genericDoubled (doubledField g gi)) hKb30
      (Y0 := W0) (J₁ := Vf) (J₂ := T)
      hQ0_ode hKbquadW0 hVfodeW0 hTodeW0 ?_ hτ
    rw [hVf0, hT0]
  -- ===== Assemble:  `B₃ c a b = (Vf 1).2.2.1 = (T 1).2.2.1`. =====
  rw [← hVfB₃, hVeq 1 ht1]

end QIQTH.ExpMap
