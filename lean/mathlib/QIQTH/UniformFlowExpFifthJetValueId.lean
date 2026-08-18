/-
  UniformFlowExpFifthJetValueId — Plan v7 Task M (C⁴ climb, brick 3): the FIFTH-JET VALUE-IDENTITY
  (`Z1↑↑`), one order up from `UniformFlowExpFourthJetValueId.uniformFlowExp_thirdJet_value_id` (`Z1↑`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  The genuine new content of the C⁴-unconditional climb:
  identifying the deep component of a genuine octupled-linearized field endpoint with the applied
  fourth Fréchet jet of `uniformFlowExp`, re-derived DIRECTLY on the uniform tube (NO `expRho`).

  ── WHAT LANDS (DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `uniformFlowExp_fourthJet_value_id` (**Z1↑↑**) — for a base point `q ∈ K`, an admissible base
      velocity `v` (`‖v‖ < ρ_K`), seeds `a b c d`, a genuine velocity-Jacobi field `J` (seed `(0,b)`),
      a genuine `doubledField`-linearized field `U` (seed `((0,a),0)`), a genuine `quadrupledField`-
      linearized field `T` (seed `(((0,c),0),0)`), and a genuine `octupledField`-linearized field `S`
      (seed `((((0,d),0),0),0)`, along `(((tube v, J), U), T)`),
          `(fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
              fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') v) d c a b = (S 1).2.2.2.1`.
      DERIVED, mirroring `Z1↑` ONE ORDER UP:
        (1) build the scalar-`s` octuple supply `Q s = (((tube(v+s•d), Jˢ), Uˢ), Tˢ)`, confined;
        (2) build the `octupledField`-linearized variation field `Vf` along `Q 0` (seed `Sseed`) via
            `linODE_exists_narrowpad_continuousOn`;
        (3) `octupledField_variation_exists_uncond` ⟹ `HasDerivAt (fun s => Q s 1) (Vf 1) 0`;
        (4) `Z1↑` [banked] at velocity `v+s•d` identifies `(Q s 1).2.2.2.1 = (fderiv f₃ (v+s•d)) c a b`
            on the open window ⟹ (project + `congr_of_eventuallyEq`)
            `HasDerivAt (fun s => (fderiv f₃ (v+s•d)) c a b) ((Vf 1).2.2.2.1) 0`;
        (5) `uniformFlowExp_thirdJetMap_differentiableAt` [banked] + directional/eval-CLM ⟹
            `HasDerivAt (fun s => (fderiv f₃ (v+s•d)) c a b) (B₄ d c a b) 0`;
        (6) `HasDerivAt.unique` ⟹ `B₄ d c a b = (Vf 1).2.2.2.1`;
        (7) glue `Vf ≡ S` on `[0,1]` via `jacobiSol_unique` (`Jˢ|₀ ≡ J`) then `autonomousLinODE_unique`
            three times (`Uˢ|₀ ≡ U`, `Tˢ|₀ ≡ T`, then `Vf ≡ S`), whence `(Vf 1).2.2.2.1 = (S 1).2.2.2.1`.
      The value id is `Z1↑` (a compiled theorem), NOT assumed.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowExpFourthJetValueId
import QIQTH.UniformFlowExpContDiffThreeUniform
import QIQTH.UniformFlowOctupleVariation
import QIQTH.UniformFlowOctupleField
import QIQTH.UniformFlowOctupleSupply
import QIQTH.UniformFlowThirdJetClose
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

/-- **Z1↑↑ — the fifth-jet value-identity.**  For `q ∈ K`, `‖v‖ < ρ_K`, seeds `a b c d`, a genuine
    velocity-Jacobi field `J` (seed `(0,b)`), a genuine `doubledField`-linearized field `U`
    (seed `((0,a),0)`), a genuine `quadrupledField`-linearized field `T` (seed `(((0,c),0),0)`), and a
    genuine `octupledField`-linearized field `S` (seed `((((0,d),0),0),0)`, along `(((tube v,J),U),T)`),
        `(fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
            fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') v) d c a b = (S 1).2.2.2.1`. -/
theorem uniformFlowExp_fourthJet_value_id (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c d : Point n)
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
          ((uniformFlowTube g gi hC hK q v τ, J τ), U τ) (T τ)) τ)
    (S : ℝ → St8 n)
    (hS0 : S 0 = (((((0 : Point n), d), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
      ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))))
    (hSode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt S
        (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
          (((uniformFlowTube g gi hC hK q v τ, J τ), U τ), T τ) (S τ)) τ) :
    (fderiv ℝ (fun w'' => fderiv ℝ (fun w' => fderiv ℝ (fun u =>
        fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w'') v) d c a b = (S 1).2.2.2.1 := by
  classical
  set ρ : ℝ := uniformFlowRadius g gi hC hK with hρdef
  set C₀ : ℝ := uniformFlowConst g gi hC hK with hC₀def
  have hρ0 : 0 < ρ := uniformFlowRadius_pos g gi hC hK
  have hC₀nn : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hvρ : ‖v‖ < ρ := hv
  set f3 : Point n → (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    fun w => fderiv ℝ (fun w' => fderiv ℝ (fun u => fderiv ℝ (uniformFlowExp g gi hC hK q) u) w') w
    with hf3def
  set B₄ : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n :=
    fderiv ℝ f3 v with hB₄def
  have hD1 : HasFDerivAt f3 B₄ v :=
    (uniformFlowExp_thirdJetMap_differentiableAt g gi hC hK q hq v hv).hasFDerivAt
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- ===== Scalar-`s` window (perturbation direction `d`). =====
  set σ : ℝ := (ρ - ‖v‖) / (2 * (1 + ‖d‖)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact div_pos (by linarith) (by positivity)
  have hwin : ∀ s : ℝ, s ∈ Set.Icc (-σ) σ → ‖v + s • d‖ < ρ := by
    intro s hs
    have habs : |s| ≤ σ := abs_le.mpr ⟨hs.1, hs.2⟩
    have hσd : σ * ‖d‖ ≤ (ρ - ‖v‖) / 2 := by
      have hval : σ = (ρ - ‖v‖) / (2 * (1 + ‖d‖)) := by rw [hσdef]
      rw [hval, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg d, (show (0 : ℝ) < ρ - ‖v‖ by linarith)]
    have h1 : ‖v + s • d‖ ≤ ‖v‖ + |s| * ‖d‖ := by
      calc ‖v + s • d‖ ≤ ‖v‖ + ‖s • d‖ := norm_add_le _ _
        _ = ‖v‖ + |s| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h2 : |s| * ‖d‖ ≤ σ * ‖d‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg d)
    linarith
  have hadm0 : ‖v + (0 : ℝ) • d‖ ≤ ρ := by rw [zero_smul, add_zero]; exact hv.le
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
  obtain ⟨Kb3, hKb30, hKb3bd⟩ := quadrupledField_fderiv_bddOn_compact g gi hC hSquadcompact
  set Tseed : St4 n :=
    ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
      (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) with hTseeddef
  set Tbound : ℝ := ‖Tseed‖ * Real.exp Kb3 with hTbounddef
  set Soct : Set (St8 n) :=
    Squad ×ˢ Metric.closedBall (0 : St4 n) Tbound with hSoctdef
  have hSoctcompact : IsCompact Soct := hSquadcompact.prod (isCompact_closedBall _ _)
  have hSoctconvex : Convex ℝ Soct :=
    (((convex_closedBall _ _).prod (convex_closedBall _ _)).prod (convex_closedBall _ _)).prod
      (convex_closedBall _ _)
  obtain ⟨Kb4, hKb40, hKb4bd⟩ := octupledField_fderiv_bddOn_compact g gi hC hSoctcompact
  set Sseed : St8 n :=
    (((((0 : Point n), d), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
      ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) with hSseeddef
  have hcontDbl : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  have hcontQuad : Continuous (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    (contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)
  -- ===== Per-`s` velocity-Jacobi `Jc` + doubled-lin `Uc` + quadrupled-lin `Tc`, confined. =====
  have key : ∀ s : ℝ,
      ∃ Jc : ℝ → Point n × Point n,
      ∃ Uc : ℝ → St2 n,
      ∃ Tc : ℝ → St4 n,
        (‖v + s • d‖ ≤ ρ →
          Jc 0 = ((0 : Point n), b) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Jc
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • d) τ) (Jc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
          ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Uc 0 = Useed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Uc
              (fderiv ℝ (doubledField g gi)
                (uniformFlowTube g gi hC hK q (v + s • d) τ, Jc τ) (Uc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound) ∧
          ContinuousOn Uc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Tc 0 = Tseed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Tc
              (fderiv ℝ (genericDoubled (doubledField g gi))
                ((uniformFlowTube g gi hC hK q (v + s • d) τ, Jc τ), Uc τ) (Tc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Tc τ‖ ≤ Tbound) ∧
          ContinuousOn Tc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro s
    by_cases h : ‖v + s • d‖ ≤ ρ
    · set P : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q (v + s • d) with hPdef
      have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + s • d) h τ hτoo).continuousAt).continuousWithinAt
      -- Jacobi factor.
      obtain ⟨Jc, hJc0, hJcode, hJcpad⟩ :=
        geodesicJacobi_narrowpad_continuousOn g gi hC P hPcont ((0 : Point n), b)
      have hfderivbd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (geodesicField g gi) (P x)‖ ≤ Kb := by
        intro x hx
        refine hKbbd (P x) ?_
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖P x - ((q, 0) : Point n × Point n)‖
            ≤ C₀ * ‖v + s • d‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • d) h x hx
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
              ≤ C₀ * ‖v + s • d‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • d) h x hx
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
      -- quadruple base curve `((P, Jc), Uc)`, padded continuous.
      have hYquadpad : ContinuousOn (fun τ => ((P τ, Jc τ), Uc τ)) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hYdblpad.prodMk hUcpad
      set Aquad : ℝ → (St4 n →L[ℝ] St4 n) :=
        fun τ => fderiv ℝ (genericDoubled (doubledField g gi)) ((P τ, Jc τ), Uc τ) with hAquaddef
      have hAquad : ContinuousOn Aquad (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hcontQuad.comp_continuousOn hYquadpad
      obtain ⟨Tc, hTc0, hTcode, hTcpad⟩ :=
        linODE_exists_narrowpad_continuousOn Aquad hAquad Tseed
      have hTcont : ContinuousOn Tc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hTcode τ hτ).continuousAt).continuousWithinAt
      have hfderiv3bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (genericDoubled (doubledField g gi)) ((P x, Jc x), Uc x)‖ ≤ Kb3 := by
        intro x hx
        refine hKb3bd ((P x, Jc x), Uc x) ?_
        rw [hSquaddef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [hSdbldef, Set.mem_prod]
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_eq_norm]
            calc ‖P x - ((q, 0) : Point n × Point n)‖
                ≤ C₀ * ‖v + s • d‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • d) h x hx
              _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
          · rw [Metric.mem_closedBall, dist_zero_right]; exact hJcbnd x hx
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hUcbnd x hx
      have hTgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Tc x‖ ≤ gronwallBound ‖Tseed‖ Kb3 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖Tseed‖)
          (K := Kb3) (ε := 0) (a := 0) (b := 1) hTcont
          (fun x hx => (hTcode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hTc0]))
          (fun x hx => by
            have hle' :=
              (fderiv ℝ (genericDoubled (doubledField g gi)) ((P x, Jc x), Uc x)).le_opNorm (Tc x)
            calc ‖fderiv ℝ (genericDoubled (doubledField g gi)) ((P x, Jc x), Uc x) (Tc x)‖
                ≤ ‖fderiv ℝ (genericDoubled (doubledField g gi)) ((P x, Jc x), Uc x)‖ * ‖Tc x‖ := hle'
              _ ≤ Kb3 * ‖Tc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderiv3bd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb3 * ‖Tc x‖ + 0 := by ring)
      have hTcbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Tc τ‖ ≤ Tbound := by
        intro τ hτ
        have h1 := hTgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hTbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb3 * τ ≤ Kb3 * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb30
          _ = Kb3 := mul_one _
      refine ⟨Jc, Uc, Tc,
        fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad, hUc0, ?_, hUcbnd, hUcpad, hTc0, ?_, hTcbnd, hTcpad⟩⟩
      · intro τ hτ; have := hUcode τ hτ; rwa [hAdbldef] at this
      · intro τ hτ; have := hTcode τ hτ; rwa [hAquaddef] at this
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
  set Jf : ℝ → ℝ → Point n × Point n := fun s => Classical.choose (key s) with hJfdef
  set Uf : ℝ → ℝ → St2 n := fun s => Classical.choose (Classical.choose_spec (key s)) with hUfdef
  set Tf : ℝ → ℝ → St4 n :=
    fun s => Classical.choose (Classical.choose_spec (Classical.choose_spec (key s))) with hTfdef
  have hspec : ∀ s : ℝ, ‖v + s • d‖ ≤ ρ →
      Jf s 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jf s)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + s • d) τ) (Jf s τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf s τ‖ ≤ Jbound) ∧
      ContinuousOn (Jf s) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Uf s 0 = Useed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Uf s)
          (fderiv ℝ (doubledField g gi)
            (uniformFlowTube g gi hC hK q (v + s • d) τ, Jf s τ) (Uf s τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uf s τ‖ ≤ Ubound) ∧
      ContinuousOn (Uf s) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Tf s 0 = Tseed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Tf s)
          (fderiv ℝ (genericDoubled (doubledField g gi))
            ((uniformFlowTube g gi hC hK q (v + s • d) τ, Jf s τ), Uf s τ) (Tf s τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Tf s τ‖ ≤ Tbound) ∧
      ContinuousOn (Tf s) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    fun s => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (key s)))
  -- The scalar-`s` octuple family `Q s = (((tube(v+s•d), Jf s), Uf s), Tf s)`.
  set Q : ℝ → ℝ → St8 n :=
    fun s t => (((uniformFlowTube g gi hC hK q (v + s • d) t, Jf s t), Uf s t), Tf s t) with hQdef
  -- Base curve `Q 0`, padded continuous.
  obtain ⟨hJf00, hJf0ode, hJf0bnd, hJf0pad, hUf00, hUf0ode, hUf0bnd, hUf0pad,
    hTf00, hTf0ode, hTf0bnd, hTf0pad⟩ := hspec 0 hadm0
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + (0 : ℝ) • d) hadm0 τ hτoo).continuousAt).continuousWithinAt
  set W0 : ℝ → St8 n :=
    fun τ => (((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) τ, Jf 0 τ), Uf 0 τ), Tf 0 τ) with hW0def
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    (((hP0cont.prodMk hJf0pad).prodMk hUf0pad).prodMk hTf0pad)
  have hcontOct : Continuous (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))) :=
    (contDiff_octupledField g gi hC).continuous_fderiv (by simp)
  set Aoct : ℝ → (St8 n →L[ℝ] St8 n) :=
    fun τ => fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (W0 τ) with hAoctdef
  have hAoct : ContinuousOn Aoct (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    hcontOct.comp_continuousOn hW0pad
  obtain ⟨Vf, hVf0, hVfode, _⟩ := linODE_exists_narrowpad_continuousOn Aoct hAoct Sseed
  -- ===== The octuple-variation derivative:  `HasDerivAt (fun s => Q s 1) (Vf 1) 0`. =====
  have hVar : HasDerivAt (fun s => Q s 1) (Vf 1) 0 := by
    refine octupledField_variation_exists_uncond g gi hC (S := Soct) (σ := σ)
      hSoctcompact hSoctconvex ht1 hσpos ?_ ?_ hVf0 ?_ ?_
    · -- hYode
      intro s hs τ hτ
      have hsρ : ‖v + s • d‖ ≤ ρ := (hwin s hs).le
      obtain ⟨_, hJsode, _, _, _, hUsode, _, _, _, hTsode, _, _⟩ := hspec s hsρ
      have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + s • d) hsρ τ
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have hYdbl := doubledField_prod_hasDerivAt g gi hP (hJsode τ hτ)
      have hQquad := genericDoubled_prod_hasDerivAt (doubledField g gi) hYdbl (hUsode τ hτ)
      exact genericDoubled_prod_hasDerivAt (genericDoubled (doubledField g gi)) hQquad (hTsode τ hτ)
    · -- hVode : along `Q 0 = W0`
      intro τ hτ; have := hVfode τ hτ; rwa [hAoctdef] at this
    · -- hIC
      intro s hs
      have hsρ : ‖v + s • d‖ ≤ ρ := (hwin s hs).le
      obtain ⟨hJs0, _, _, _, hUs0, _, _, _, hTs0, _, _, _⟩ := hspec s hsρ
      have h1 : uniformFlowTube g gi hC hK q (v + s • d) 0 = (q, v + s • d) :=
        uniformFlowTube_spec_ic g gi hC hK q hq (v + s • d) hsρ
      have h2 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) 0 = (q, v + (0 : ℝ) • d) :=
        uniformFlowTube_spec_ic g gi hC hK q hq (v + (0 : ℝ) • d) hadm0
      show ((((uniformFlowTube g gi hC hK q (v + s • d) 0, Jf s 0), Uf s 0), Tf s 0)
          - (((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) 0, Jf 0 0), Uf 0 0), Tf 0 0)) = s • Sseed
      rw [h1, h2, hJs0, hJf00, hUs0, hUf00, hTs0, hTf00, hUseeddef, hTseeddef, hSseeddef,
        zero_smul, add_zero]
      simp only [Prod.mk_sub_mk, sub_self, add_sub_cancel_left, Prod.smul_mk, smul_zero,
        Prod.mk_zero_zero]
    · -- hmem
      intro s hs τ hτ
      have hsρ : ‖v + s • d‖ ≤ ρ := (hwin s hs).le
      obtain ⟨_, _, hJsbnd, _, _, _, hUsbnd, _, _, _, hTsbnd, _⟩ := hspec s hsρ
      show (((uniformFlowTube g gi hC hK q (v + s • d) τ, Jf s τ), Uf s τ), Tf s τ) ∈ Soct
      rw [hSoctdef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [hSquaddef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [hSdbldef, Set.mem_prod]
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_eq_norm]
            calc ‖uniformFlowTube g gi hC hK q (v + s • d) τ - ((q, 0) : Point n × Point n)‖
                ≤ C₀ * ‖v + s • d‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + s • d) hsρ τ hτ
              _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hsρ hC₀nn
          · rw [Metric.mem_closedBall, dist_zero_right]; exact hJsbnd τ hτ
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hUsbnd τ hτ
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hTsbnd τ hτ
  -- ===== The projected deep component. =====
  set proj : St8 n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      ((ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp
        ((ContinuousLinearMap.snd ℝ (St2 n) (St2 n)).comp
          (ContinuousLinearMap.snd ℝ (St4 n) (St4 n)))) with hprojdef
  have hproj_apply : ∀ z : St8 n, proj z = z.2.2.2.1 := fun z => rfl
  have hproj : HasDerivAt (fun s => (Q s 1).2.2.2.1) ((Vf 1).2.2.2.1) 0 := by
    have h := proj.hasFDerivAt.comp_hasDerivAt 0 hVar
    simpa [hproj_apply] using h
  -- ===== `Z1↑` at velocity `v+s•d`:  `(Q s 1).2.2.2.1 = (f₃ (v+s•d)) c a b`  eventually. =====
  have hEqS : (fun s => (Q s 1).2.2.2.1) =ᶠ[𝓝 (0 : ℝ)] (fun s => (f3 (v + s • d)) c a b) := by
    have hballs : Metric.ball (0 : ℝ) σ ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hσpos
    refine Filter.eventuallyEq_of_mem hballs (fun s hs => ?_)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    have hsmem : s ∈ Set.Icc (-σ) σ := ⟨by linarith [(abs_le.mp hs.le).1], (abs_le.mp hs.le).2⟩
    have hsρ : ‖v + s • d‖ < ρ := hwin s hsmem
    obtain ⟨hJs0, hJsode, _, _, hUs0, hUsode, _, _, hTs0, hTsode, _, _⟩ := hspec s hsρ.le
    have hz1 := uniformFlowExp_thirdJet_value_id g gi hC hK q hq (v + s • d) hsρ a b c
      (Jf s) hJs0 hJsode (Uf s) hUs0 hUsode (Tf s) hTs0 hTsode
    show (Q s 1).2.2.2.1 = (f3 (v + s • d)) c a b
    rw [hf3def]
    exact hz1.symm
  have hLHS : HasDerivAt (fun s : ℝ => (f3 (v + s • d)) c a b) ((Vf 1).2.2.2.1) 0 :=
    hproj.congr_of_eventuallyEq hEqS.symm
  -- ===== The directional/eval chain:  `HasDerivAt (fun s => (f₃ (v+s•d)) c a b) (B₄ d c a b) 0`. =====
  have hline : HasDerivAt (fun s : ℝ => v + s • d) d 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • d) d 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const d
    exact h1.const_add v
  have hD1' : HasFDerivAt f3 B₄ (v + (0 : ℝ) • d) := by simpa using hD1
  have hcomp : HasDerivAt (fun s : ℝ => f3 (v + s • d)) (B₄ d) 0 := by
    simpa using hD1'.comp_hasDerivAt 0 hline
  set E1 : (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ]
      (Point n →L[ℝ] Point n →L[ℝ] Point n) :=
    ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n →L[ℝ] Point n) c with hE1def
  set E2 : (Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] (Point n →L[ℝ] Point n) :=
    ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n) a with hE2def
  set E3 : (Point n →L[ℝ] Point n) →L[ℝ] Point n :=
    ContinuousLinearMap.apply ℝ (Point n) b with hE3def
  set ev : (Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n) →L[ℝ] Point n :=
    E3.comp (E2.comp E1) with hevdef
  have hev_apply : ∀ T : Point n →L[ℝ] Point n →L[ℝ] Point n →L[ℝ] Point n, ev T = T c a b :=
    fun T => rfl
  have hRHS : HasDerivAt (fun s : ℝ => (f3 (v + s • d)) c a b) (B₄ d c a b) 0 := by
    have h := ev.hasFDerivAt.comp_hasDerivAt 0 hcomp
    simpa [hev_apply] using h
  -- ===== Uniqueness of the scalar directional derivative:  `(Vf 1).2.2.2.1 = B₄ d c a b`. =====
  have hVfB₄ : (Vf 1).2.2.2.1 = B₄ d c a b := hLHS.unique hRHS
  -- ===== ODE-uniqueness gluing:  `Vf ≡ S` on `[0,1]`. =====
  have htube0 : uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) = uniformFlowTube g gi hC hK q v := by
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
  -- Step A: `Jf 0 ≡ J`.
  have hJf0odeV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Jf 0)
        (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q v τ) (Jf 0 τ)) τ := by
    intro τ hτ; rw [← htube0]; exact hJf0ode τ hτ
  have hJeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, J τ = Jf 0 τ := by
    intro τ hτ
    refine jacobiSol_unique g gi hKb0 (Y0 := uniformFlowTube g gi hC hK q v) (J₁ := J) (J₂ := Jf 0)
      hTubeV_ode hKbtubeV hJode hJf0odeV ?_ hτ
    rw [hJ0, hJf00]
  -- Step B: `Uf 0 ≡ U`.
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
  -- Step C: `Tf 0 ≡ T`.
  have hbaseQuad_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => ((uniformFlowTube g gi hC hK q v t, J t), U t))
        (genericDoubled (doubledField g gi) ((uniformFlowTube g gi hC hK q v τ, J τ), U τ)) τ :=
    fun τ hτ => genericDoubled_prod_hasDerivAt (doubledField g gi) (hbaseDbl_ode τ hτ) (hUode τ hτ)
  have hUmemQuad : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ((uniformFlowTube g gi hC hK q v τ, J τ), U τ) ∈ Squad := by
    intro τ hτ
    rw [hSquaddef, Set.mem_prod]
    exact ⟨hJmemDbl τ hτ, by rw [Metric.mem_closedBall, dist_zero_right, hUeq τ hτ]; exact hUf0bnd τ hτ⟩
  have hKbquadV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (doubledField g gi)) ((uniformFlowTube g gi hC hK q v τ, J τ), U τ)‖ ≤ Kb3 :=
    fun τ hτ => hKb3bd _ (hUmemQuad τ hτ)
  have hTf0odeV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Tf 0)
        (fderiv ℝ (genericDoubled (doubledField g gi))
          ((uniformFlowTube g gi hC hK q v τ, J τ), U τ) (Tf 0 τ)) τ := by
    intro τ hτ
    have h := hTf0ode τ hτ
    rw [htube0, ← hJeq τ hτ, ← hUeq τ hτ] at h
    exact h
  have hTeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, T τ = Tf 0 τ := by
    intro τ hτ
    refine autonomousLinODE_unique (genericDoubled (doubledField g gi)) hKb30
      (Y0 := fun t => ((uniformFlowTube g gi hC hK q v t, J t), U t)) (J₁ := T) (J₂ := Tf 0)
      hbaseQuad_ode hKbquadV hTode hTf0odeV ?_ hτ
    rw [hT0, hTf00]
  -- Step D: `Vf ≡ S`  (`autonomousLinODE_unique`, `octupledField` along `Q 0 = W0`).
  have hbaseQ : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      W0 τ = (((uniformFlowTube g gi hC hK q v τ, J τ), U τ), T τ) := by
    intro τ hτ
    show (((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) τ, Jf 0 τ), Uf 0 τ), Tf 0 τ)
        = (((uniformFlowTube g gi hC hK q v τ, J τ), U τ), T τ)
    rw [htube0, ← hJeq τ hτ, ← hUeq τ hτ, ← hTeq τ hτ]
  have hQ0_ode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt W0 (genericDoubled (genericDoubled (doubledField g gi)) (W0 τ)) τ := by
    intro τ hτ
    have hPtube0 := uniformFlowTube_spec_ode g gi hC hK q hq (v + (0 : ℝ) • d) hadm0 τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hYdbl0 := doubledField_prod_hasDerivAt g gi hPtube0 (hJf0ode τ hτ)
    have hQuad0 := genericDoubled_prod_hasDerivAt (doubledField g gi) hYdbl0 (hUf0ode τ hτ)
    exact genericDoubled_prod_hasDerivAt (genericDoubled (doubledField g gi)) hQuad0 (hTf0ode τ hτ)
  have hW0mem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, W0 τ ∈ Soct := by
    intro τ hτ
    show (((uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) τ, Jf 0 τ), Uf 0 τ), Tf 0 τ) ∈ Soct
    rw [hSoctdef, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [hSquaddef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [hSdbldef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖uniformFlowTube g gi hC hK q (v + (0 : ℝ) • d) τ - ((q, 0) : Point n × Point n)‖
              ≤ C₀ * ‖v + (0 : ℝ) • d‖ :=
                uniformFlowTube_spec_conf g gi hC hK q hq (v + (0 : ℝ) • d) hadm0 τ hτ
            _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm0 hC₀nn
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hJf0bnd τ hτ
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hUf0bnd τ hτ
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hTf0bnd τ hτ
  have hKboctW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (W0 τ)‖ ≤ Kb4 :=
    fun τ hτ => hKb4bd _ (hW0mem τ hτ)
  have hVfodeW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt Vf (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (W0 τ) (Vf τ)) τ := by
    intro τ hτ; have := hVfode τ hτ; rwa [hAoctdef] at this
  have hSodeW0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt S (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (W0 τ) (S τ)) τ := by
    intro τ hτ; have h := hSode τ hτ; rw [← hbaseQ τ hτ] at h; exact h
  have hVeq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, Vf τ = S τ := by
    intro τ hτ
    refine autonomousLinODE_unique (genericDoubled (genericDoubled (doubledField g gi))) hKb40
      (Y0 := W0) (J₁ := Vf) (J₂ := S)
      hQ0_ode hKboctW0 hVfodeW0 hSodeW0 ?_ hτ
    rw [hVf0, hS0]
  -- ===== Assemble:  `B₄ d c a b = (Vf 1).2.2.2.1 = (S 1).2.2.2.1`. =====
  rw [← hVfB₄, hVeq 1 ht1]

end QIQTH.ExpMap
