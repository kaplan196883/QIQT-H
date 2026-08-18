/-
  UniformFlowHexadecupleSupply — Plan v7 Task M (C⁴ climb, brick 2): the HEXADECUPLE-flow SUPPLY, the
  base-velocity Fréchet derivative of the hexadecupled-flow (16-fold) endpoint — one order up from
  `UniformFlowOctupleSupply.uniformFlow_octupleEndpoint_baseVelocity_hasFDerivAt`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  NOT `a₁ = R/6`.  The mechanical "supply" half of the FIFTH velocity-jet climb
  of `uniformFlowExp`, re-derived DIRECTLY on the uniform tube (NO `expRho`).

  ── CONTEXT.  Each `genericDoubled` doubling of the geodesic field climbs one velocity-derivative order:
      `geodesicField` → D¹,  `doubledField` → D²,  `quadrupledField` → D³,  `octupledField` → D⁴ (banked).
  The FIFTH jet (⟹ C⁴) needs the base-velocity Fréchet derivative of the HEXADECUPLED-flow endpoint,
  built as a genuine confined
      `hexadecupleField = genericDoubled (octField8' g gi)`
  integral-curve family on the 16-fold phase space — mirroring the octuple supply one order up, now
  declared over the `def`-based `St16'`/`St8'` types (`NestedPhaseSpaceDef`) so the deep-nested instance
  search is cheap (Task L fix; the abbrev `St16` blew the elaboration budget even at 8M heartbeats).

  ── WHAT LANDS (DERIVED; NO `sorry`, NO new axioms, NO `expRho`).
    • `uniformFlow_hexadecupleEndpoint_baseVelocity_hasFDerivAt` — for `q ∈ K`, `‖v‖ < ρ_K`, seeds
        `a b c d`, there are a velocity-Jacobi family `Jf` (seed `(0,b)`), a `doubledField`-linearized
        family `Uf` (seed `((0,a),0)`), a `quadrupledField`-linearized family `Tf` (seed `(((0,c),0),0)`),
        and an `octupledField`-linearized family `Sf` (seed `((((0,d),0),0),0)`) such that the
        HEXADECUPLED-flow endpoint
          `δ ↦ (((((tube(v+δ) 1, Jf δ 1), Uf δ 1), Tf δ 1), Sf δ 1))`
        is Fréchet-differentiable at `0`.  A GENUINE confined 16-fold integral-curve family; the octuple
        base curve `(((tube, Jf), Uf), Tf)` is the banked octuple supply's confined curve; `Sf` is a
        genuine `octupledField`-linearized field along it (Grönwall-confined via
        `octupledField_fderiv_bddOn_compact`); the pair is a `hexadecupleField` integral curve
        (`genericDoubled_prod_hasDerivAt`); fed to `autonomousFlow_endpoint_hasFDerivAt_window_exists`
        with `Φ := hexadecupleField`, all 16-fold field regularity discharged from
        `UniformFlowHexadecupleField`.
    • `uniformFlow_hexadecupleEndpoint_component_hasFDerivAt` — the projected deep scalar-slot component
        `δ ↦ (Sf δ 1).2.2.2.1`, Fréchet-differentiable at `0`.

  ── HONEST FIREWALL (binding) — what the FIFTH JET still needs.
    The base-velocity Fréchet derivative of the hexadecuple endpoint lands here fully.  The per-seed
    FIFTH jet needs the value-IDENTIFICATION linking the hexadecuple deep component `(Sf δ 1).2.2.2.1` to
    the fourth jet at `v+δ` (the `Z1↑`-analogue one order up), a separate brick.  CARRIED.  NO `expRho`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import QIQTH.UniformFlowHexadecupleField
import QIQTH.UniformFlowOctupleSupply
import QIQTH.UniformFlowOctupleVariation
import QIQTH.NestedPhaseSpaceDef
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic QIQTH.AutonomousDep
open Set Filter
open scoped Topology NNReal

set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 1000000
set_option maxSynthPendingDepth 10

variable {n : ℕ}

/-- **The hexadecuple-flow supply.**  For `q ∈ K`, `‖v‖ < ρ_K`, and seeds `a b c d`, there are a
    velocity-Jacobi family `Jf`, a `doubledField`-linearized family `Uf`, a `quadrupledField`-linearized
    family `Tf`, and an `octupledField`-linearized family `Sf` such that the HEXADECUPLED-flow endpoint
      `δ ↦ (((((tube(v+δ) 1, Jf δ 1), Uf δ 1), Tf δ 1), Sf δ 1))`
    is Fréchet-differentiable at `0`.  GENUINE confined 16-fold integral-curve supply; NO `expRho`. -/
theorem uniformFlow_hexadecupleEndpoint_baseVelocity_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c d : Point n) :
    ∃ Jf : Point n → ℝ → Point n × Point n,
    ∃ Uf : Point n → ℝ → St2 n,
    ∃ Tf : Point n → ℝ → St4 n,
    ∃ Sf : Point n → ℝ → St8 n,
      (∀ δ : Point n, ‖δ‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ →
        Jf δ 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Jf δ)
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) ∧
        Uf δ 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Uf δ)
            (fderiv ℝ (doubledField g gi)
              (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) (Uf δ τ)) τ) ∧
        Tf δ 0 = ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
          (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Tf δ)
            (fderiv ℝ (genericDoubled (doubledField g gi))
              ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ) (Tf δ τ)) τ) ∧
        Sf δ 0 = (((((0 : Point n), d), ((0 : Point n), (0 : Point n))),
            (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
          ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
            (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Sf δ)
            (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
              (((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ), Tf δ τ) (Sf δ τ)) τ)) ∧
      ∃ L : Point n →L[ℝ] St16' n,
        HasFDerivAt
          (fun δ => ((((((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1), Tf δ 1),
            Sf δ 1)) : St16' n)) L 0 := by
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
  -- Geodesic-factor confinement + uniform `fderiv (geodesicField)` bound.
  have hAcompact : IsCompact (Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ)) :=
    isCompact_closedBall _ _
  obtain ⟨Kb, hKb0, hKbbd⟩ := geodesicField_fderiv_bddOn_compact g gi hC hAcompact
  set Jbound : ℝ := ‖((0 : Point n), b)‖ * Real.exp Kb with hJbounddef
  have hJbound0 : 0 ≤ Jbound := by rw [hJbounddef]; positivity
  -- Doubled base confinement + uniform `fderiv (doubledField)` bound.
  set Sdbl : Set (St2 n) :=
    Metric.closedBall ((q, 0) : Point n × Point n) (C₀ * ρ) ×ˢ
      Metric.closedBall (0 : Point n × Point n) Jbound with hSdbldef
  have hSdblcompact : IsCompact Sdbl := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨Kb2, hKb20, hKb2bd⟩ := doubledField_fderiv_bddOn_compact g gi hC hSdblcompact
  set Useed : St2 n := (((0 : Point n), a), ((0 : Point n), (0 : Point n))) with hUseeddef
  set Ubound : ℝ := ‖Useed‖ * Real.exp Kb2 with hUbounddef
  have hUbound0 : 0 ≤ Ubound := by rw [hUbounddef]; positivity
  -- Quadruple base confinement + uniform `fderiv (quadrupledField)` bound.
  set Squad : Set (St4 n) :=
    Sdbl ×ˢ Metric.closedBall (0 : St2 n) Ubound with hSquaddef
  have hSquadcompact : IsCompact Squad := hSdblcompact.prod (isCompact_closedBall _ _)
  obtain ⟨Kb3, hKb30, hKb3bd⟩ := quadrupledField_fderiv_bddOn_compact g gi hC hSquadcompact
  set Tseed : St4 n :=
    ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
      (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) with hTseeddef
  set Tbound : ℝ := ‖Tseed‖ * Real.exp Kb3 with hTbounddef
  have hTbound0 : 0 ≤ Tbound := by rw [hTbounddef]; positivity
  -- Octuple base confinement + uniform `fderiv (octupledField)` bound.
  set Soct : Set (St8 n) :=
    Squad ×ˢ Metric.closedBall (0 : St4 n) Tbound with hSoctdef
  have hSoctcompact : IsCompact Soct := hSquadcompact.prod (isCompact_closedBall _ _)
  obtain ⟨Kb4, hKb40, hKb4bd⟩ := octupledField_fderiv_bddOn_compact g gi hC hSoctcompact
  set Sseed : St8 n :=
    (((((0 : Point n), d), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
      ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
        (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) with hSseeddef
  set Sbound : ℝ := ‖Sseed‖ * Real.exp Kb4 with hSbounddef
  have hSbound0 : 0 ≤ Sbound := by rw [hSbounddef]; positivity
  -- The full hexadecuple confinement set (over the `def`-based `St16'`).
  set S : Set (St16' n) :=
    Soct ×ˢ Metric.closedBall (0 : St8 n) Sbound with hSdef
  have hScompact : IsCompact S := hSoctcompact.prod (isCompact_closedBall _ _)
  have hSconvex : Convex ℝ S :=
    ((((convex_closedBall _ _).prod (convex_closedBall _ _)).prod (convex_closedBall _ _)).prod
      (convex_closedBall _ _)).prod (convex_closedBall _ _)
  have hcontDbl : Continuous (fderiv ℝ (doubledField g gi)) :=
    (contDiff_doubledField g gi hC).continuous_fderiv (by simp)
  have hcontQuad : Continuous (fderiv ℝ (genericDoubled (doubledField g gi))) :=
    (contDiff_quadrupledField g gi hC).continuous_fderiv (by simp)
  have hcontOct : Continuous (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))) :=
    (contDiff_octupledField g gi hC).continuous_fderiv (by simp)
  -- Per-δ: velocity Jacobi `Jc`, doubled-linearized `Uc`, quadrupled-linearized `Tc`,
  -- octupled-linearized `Sc`, confined.
  have key : ∀ δ : Point n,
      ∃ Jc : ℝ → Point n × Point n,
      ∃ Uc : ℝ → St2 n,
      ∃ Tc : ℝ → St4 n,
      ∃ Sc : ℝ → St8 n,
        (‖v + δ‖ ≤ ρ →
          Jc 0 = ((0 : Point n), b) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Jc
              (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jc τ‖ ≤ Jbound) ∧
          ContinuousOn Jc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Uc 0 = Useed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Uc
              (fderiv ℝ (doubledField g gi)
                (uniformFlowTube g gi hC hK q (v + δ) τ, Jc τ) (Uc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uc τ‖ ≤ Ubound) ∧
          ContinuousOn Uc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Tc 0 = Tseed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Tc
              (fderiv ℝ (genericDoubled (doubledField g gi))
                ((uniformFlowTube g gi hC hK q (v + δ) τ, Jc τ), Uc τ) (Tc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Tc τ‖ ≤ Tbound) ∧
          ContinuousOn Tc (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
          Sc 0 = Sseed ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1,
            HasDerivAt Sc
              (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
                (((uniformFlowTube g gi hC hK q (v + δ) τ, Jc τ), Uc τ), Tc τ) (Sc τ)) τ) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Sc τ‖ ≤ Sbound) ∧
          ContinuousOn Sc (Set.Icc (-(1/2) : ℝ) (3/2))) := by
    intro δ
    by_cases h : ‖v + δ‖ ≤ ρ
    · set P : ℝ → Point n × Point n := uniformFlowTube g gi hC hK q (v + δ) with hPdef
      have hPcont : ContinuousOn P (Set.Icc (-(1/2) : ℝ) (3/2)) := by
        intro τ hτ
        have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) h τ hτoo).continuousAt).continuousWithinAt
      -- Jacobi factor.
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
              ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
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
                ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
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
      -- octuple base curve `(((P, Jc), Uc), Tc)`, padded continuous.
      have hYoctpad : ContinuousOn (fun τ => (((P τ, Jc τ), Uc τ), Tc τ)) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hYquadpad.prodMk hTcpad
      set Aoct : ℝ → (St8 n →L[ℝ] St8 n) :=
        fun τ => fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
          (((P τ, Jc τ), Uc τ), Tc τ) with hAoctdef
      have hAoct : ContinuousOn Aoct (Set.Icc (-(1/2) : ℝ) (3/2)) :=
        hcontOct.comp_continuousOn hYoctpad
      obtain ⟨Sc, hSc0, hScode, hScpad⟩ :=
        linODE_exists_narrowpad_continuousOn Aoct hAoct Sseed
      have hScont : ContinuousOn Sc (Set.Icc (0 : ℝ) 1) :=
        fun τ hτ => ((hScode τ hτ).continuousAt).continuousWithinAt
      have hfderiv4bd : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi))) (((P x, Jc x), Uc x), Tc x)‖ ≤ Kb4 := by
        intro x hx
        refine hKb4bd (((P x, Jc x), Uc x), Tc x) ?_
        rw [hSoctdef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [hSquaddef, Set.mem_prod]
          refine ⟨?_, ?_⟩
          · rw [hSdbldef, Set.mem_prod]
            refine ⟨?_, ?_⟩
            · rw [Metric.mem_closedBall, dist_eq_norm]
              calc ‖P x - ((q, 0) : Point n × Point n)‖
                  ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) h x hx
                _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left h hC₀nn
            · rw [Metric.mem_closedBall, dist_zero_right]; exact hJcbnd x hx
          · rw [Metric.mem_closedBall, dist_zero_right]; exact hUcbnd x hx
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hTcbnd x hx
      have hSgw : ∀ x ∈ Set.Icc (0 : ℝ) 1,
          ‖Sc x‖ ≤ gronwallBound ‖Sseed‖ Kb4 0 (x - 0) :=
        norm_le_gronwallBound_of_norm_deriv_right_le (δ := ‖Sseed‖)
          (K := Kb4) (ε := 0) (a := 0) (b := 1) hScont
          (fun x hx => (hScode x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt)
          (le_of_eq (by rw [hSc0]))
          (fun x hx => by
            have hle' :=
              (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
                (((P x, Jc x), Uc x), Tc x)).le_opNorm (Sc x)
            calc ‖fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
                    (((P x, Jc x), Uc x), Tc x) (Sc x)‖
                ≤ ‖fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
                    (((P x, Jc x), Uc x), Tc x)‖ * ‖Sc x‖ := hle'
              _ ≤ Kb4 * ‖Sc x‖ :=
                  mul_le_mul_of_nonneg_right (hfderiv4bd x (Set.Ico_subset_Icc_self hx)) (norm_nonneg _)
              _ = Kb4 * ‖Sc x‖ + 0 := by ring)
      have hScbnd : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Sc τ‖ ≤ Sbound := by
        intro τ hτ
        have h1 := hSgw τ hτ
        rw [sub_zero, gronwallBound_ε0] at h1
        refine h1.trans ?_
        rw [hSbounddef]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Real.exp_le_exp]
        calc Kb4 * τ ≤ Kb4 * 1 := mul_le_mul_of_nonneg_left hτ.2 hKb40
          _ = Kb4 := mul_one _
      refine ⟨Jc, Uc, Tc, Sc,
        fun _ => ⟨hJc0, hJcode, hJcbnd, hJcpad, hUc0, ?_, hUcbnd, hUcpad, hTc0, ?_, hTcbnd, hTcpad,
          hSc0, ?_, hScbnd, hScpad⟩⟩
      · intro τ hτ; have := hUcode τ hτ; rwa [hAdbldef] at this
      · intro τ hτ; have := hTcode τ hτ; rwa [hAquaddef] at this
      · intro τ hτ; have := hScode τ hτ; rwa [hAoctdef] at this
    · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun h' => absurd h' h⟩
  set Jf : Point n → ℝ → Point n × Point n := fun δ => Classical.choose (key δ) with hJfdef
  set Uf : Point n → ℝ → St2 n :=
    fun δ => Classical.choose (Classical.choose_spec (key δ)) with hUfdef
  set Tf : Point n → ℝ → St4 n :=
    fun δ => Classical.choose (Classical.choose_spec (Classical.choose_spec (key δ))) with hTfdef
  set Sf : Point n → ℝ → St8 n :=
    fun δ => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (key δ)))) with hSfdef
  have hspec : ∀ δ : Point n, ‖v + δ‖ ≤ ρ →
      Jf δ 0 = ((0 : Point n), b) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Jf δ)
          (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Jf δ τ‖ ≤ Jbound) ∧
      ContinuousOn (Jf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Uf δ 0 = Useed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Uf δ)
          (fderiv ℝ (doubledField g gi)
            (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) (Uf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Uf δ τ‖ ≤ Ubound) ∧
      ContinuousOn (Uf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Tf δ 0 = Tseed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Tf δ)
          (fderiv ℝ (genericDoubled (doubledField g gi))
            ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ) (Tf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Tf δ τ‖ ≤ Tbound) ∧
      ContinuousOn (Tf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) ∧
      Sf δ 0 = Sseed ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (Sf δ)
          (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
            (((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ), Tf δ τ) (Sf δ τ)) τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖Sf δ τ‖ ≤ Sbound) ∧
      ContinuousOn (Sf δ) (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    fun δ => Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (key δ))))
  -- The base hexadecuple curve `W0 = ((((tube v, Jf 0), Uf 0), Tf 0), Sf 0)`, padded continuous.
  have hP0cont : ContinuousOn (fun τ => uniformFlowTube g gi hC hK q (v + 0) τ)
      (Set.Icc (-(1/2) : ℝ) (3/2)) := by
    intro τ hτ
    have hτoo : τ ∈ Set.Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact ((uniformFlowTube_spec_ode g gi hC hK q hq (v + 0) hadm0 τ hτoo).continuousAt).continuousWithinAt
  obtain ⟨_, _, _, hJf0pad, _, _, _, hUf0pad, _, _, _, hTf0pad, _, _, _, hSf0pad⟩ := hspec 0 hadm0
  set W0 : ℝ → St16' n :=
    fun τ => (((((uniformFlowTube g gi hC hK q (v + 0) τ, Jf 0 τ), Uf 0 τ), Tf 0 τ),
      Sf 0 τ) : St16' n) with hW0def
  have hW0pad : ContinuousOn W0 (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    ((((hP0cont.prodMk hJf0pad).prodMk hUf0pad).prodMk hTf0pad).prodMk hSf0pad)
  -- The `hexadecupleField`-linearized field `Vf δ` along the fixed base hexadecuple curve `W0`.
  have hcontHex : Continuous
      (fderiv ℝ (genericDoubled (octField8' g gi))) :=
    (contDiff_hexField' g gi hC).continuous_fderiv (by simp)
  set Ahex : ℝ → (St16' n →L[ℝ] St16' n) :=
    fun τ => fderiv ℝ (genericDoubled (octField8' g gi)) (W0 τ)
    with hAhexdef
  have hAhex : ContinuousOn Ahex (Set.Icc (-(1/2) : ℝ) (3/2)) :=
    hcontHex.comp_continuousOn hW0pad
  -- The base-velocity seed CLM `δ ↦ (((((0,δ),0),0),0),0₈)` at the hexadecuple level.
  set seedInner : Point n →L[ℝ] St2 n :=
    (ContinuousLinearMap.inl ℝ (Point n × Point n) (Point n × Point n)).comp
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) with hseedInnerdef
  set seedQuad : Point n →L[ℝ] St4 n :=
    (ContinuousLinearMap.inl ℝ (St2 n) (St2 n)).comp seedInner with hseedQuaddef
  set seedOct : Point n →L[ℝ] St8 n :=
    (ContinuousLinearMap.inl ℝ (St4 n) (St4 n)).comp seedQuad with hseedOctdef
  set seedCLM : Point n →L[ℝ] St16' n :=
    (ContinuousLinearMap.inl ℝ (St8' n) (St8' n)).comp seedOct with hseedCLMdef
  -- Octuple-level seed (raw `St8`, abbrev — reduces cleanly), then wrap with the `St8'`-injection.
  have hseedOct_eq : ∀ δ : Point n,
      seedOct δ = (((((0 : Point n), δ), ((0 : Point n), (0 : Point n))),
          (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
        ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
          (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) := by
    intro δ
    simp [hseedOctdef, hseedQuaddef, hseedInnerdef, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.ext_iff]
  have hseedOctnorm : ∀ δ : Point n, ‖seedOct δ‖ = ‖δ‖ := by
    intro δ; rw [hseedOct_eq δ]; simp [Prod.norm_def, norm_nonneg]
  have hseedCLM_eq : ∀ δ : Point n, seedCLM δ = (seedOct δ, (0 : St8' n)) := by
    intro δ; rw [hseedCLMdef]; exact ContinuousLinearMap.inl_apply _
  have hseednorm : ∀ δ : Point n, ‖seedCLM δ‖ = ‖δ‖ := by
    intro δ
    rw [hseedCLM_eq δ]
    show ‖((seedOct δ, (0 : St8' n)) : St8' n × St8' n)‖ = ‖δ‖
    rw [Prod.norm_def]
    have e2 : ‖((seedOct δ, (0 : St8' n)) : St8' n × St8' n).2‖ = 0 := by simp
    have e1 : ‖((seedOct δ, (0 : St8' n)) : St8' n × St8' n).1‖ = ‖δ‖ := hseedOctnorm δ
    rw [e1, e2]; exact max_eq_left (norm_nonneg δ)
  -- The per-δ `hexadecupleField`-linearized field along `W0`, seed `seedCLM δ`.
  have varkey : ∀ δ : Point n,
      ∃ Vc : ℝ → St16' n,
        Vc 0 = seedCLM δ ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt Vc
            (fderiv ℝ (genericDoubled (octField8' g gi)) (W0 τ)
              (Vc τ)) τ) := by
    intro δ
    obtain ⟨Vc, hVc0, hVcode, _⟩ := linODE_exists_narrowpad_continuousOn Ahex hAhex (seedCLM δ)
    refine ⟨Vc, hVc0, fun τ hτ => ?_⟩
    have := hVcode τ hτ; rwa [hAhexdef] at this
  set Vf : Point n → ℝ → St16' n := fun δ => Classical.choose (varkey δ) with hVfdef
  -- The perturbed hexadecuple family `W δ = ((((tube (v+δ), Jf δ), Uf δ), Tf δ), Sf δ)`.
  set W : Point n → ℝ → St16' n :=
    fun δ t => (((((uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t), Uf δ t), Tf δ t),
      Sf δ t) : St16' n) with hWdef
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  -- Engine regularity inputs (from `UniformFlowHexadecupleField`).
  have hΦcd : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (genericDoubled (octField8' g gi)) :=
    contDiff_hexField' g gi hC
  have hdiff : ∀ x ∈ S, DifferentiableAt ℝ
      (genericDoubled (octField8' g gi)) x :=
    fun x _ => (hΦcd.differentiable (by simp)).differentiableAt
  have hΦcd' : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fderiv ℝ (genericDoubled (octField8' g gi))) :=
    hΦcd.fderiv_right (m := (⊤ : WithTop ℕ∞)) le_top
  have hdiff2 : ∀ x ∈ S, DifferentiableAt ℝ
      (fderiv ℝ (genericDoubled (octField8' g gi))) x :=
    fun x _ => (hΦcd'.differentiable (by simp)).differentiableAt
  obtain ⟨M₂, _hM₂0, hbound2⟩ := hexField_fderiv2_bddOn_compact g gi hC hScompact
  obtain ⟨Kf, hKf0, hKfbd⟩ := hexField_fderiv_bddOn_compact g gi hC hScompact
  set K₀ : NNReal := ⟨Kf, hKf0⟩ with hK₀def
  have hLip : LipschitzOnWith K₀
      (genericDoubled (octField8' g gi)) S :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hdiff x (by trivial))
      (fun x hx => by rw [← NNReal.coe_le_coe]; simpa [hK₀def] using hKfbd x hx)
      hSconvex
  -- Discharge the engine's supply hypotheses.
  have hWode : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (W δ)
        (genericDoubled (octField8' g gi) (W δ τ)) τ := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, hJfode, _, _, _, hUfode, _, _, _, hTfode, _, _, _, hSfode, _, _⟩ := hspec δ hadm
    have hP := uniformFlowTube_spec_ode g gi hC hK q hq (v + δ) hadm τ
      ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have hYode : HasDerivAt (fun t => (uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t))
        (doubledField g gi (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ)) τ :=
      doubledField_prod_hasDerivAt g gi hP (hJfode τ hτ)
    have hQode : HasDerivAt (fun t => ((uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t), Uf δ t))
        (genericDoubled (doubledField g gi)
          ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ)) τ :=
      genericDoubled_prod_hasDerivAt (doubledField g gi) hYode (hUfode τ hτ)
    have hRode : HasDerivAt
        (fun t => (((uniformFlowTube g gi hC hK q (v + δ) t, Jf δ t), Uf δ t), Tf δ t))
        (genericDoubled (genericDoubled (doubledField g gi))
          (((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ), Tf δ τ)) τ :=
      genericDoubled_prod_hasDerivAt (genericDoubled (doubledField g gi)) hQode (hTfode τ hτ)
    exact genericDoubled_prod_hasDerivAt (octField8' g gi) hRode (hSfode τ hτ)
  have hVode : ∀ δ : Point n, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (Vf δ)
        (fderiv ℝ (genericDoubled (octField8' g gi)) (W0 τ)
          (Vf δ τ)) τ :=
    fun δ => (Classical.choose_spec (varkey δ)).2
  have hV0 : ∀ δ : Point n, Vf δ 0 = seedCLM δ :=
    fun δ => (Classical.choose_spec (varkey δ)).1
  have hmem : ∀ δ : Point n, ‖δ‖ ≤ σ → ∀ τ ∈ Set.Icc (0 : ℝ) 1, W δ τ ∈ S := by
    intro δ hδ τ hτ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨_, _, hJfbnd, _, _, _, hUfbnd, _, _, _, hTfbnd, _, _, _, hSfbnd, _⟩ := hspec δ hadm
    rw [hWdef, hSdef]
    refine Set.mk_mem_prod ?_ ?_
    · rw [hSoctdef, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [hSquaddef, Set.mem_prod]
        refine ⟨?_, ?_⟩
        · rw [hSdbldef, Set.mem_prod]
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_eq_norm]
            calc ‖uniformFlowTube g gi hC hK q (v + δ) τ - ((q, 0) : Point n × Point n)‖
                ≤ C₀ * ‖v + δ‖ := uniformFlowTube_spec_conf g gi hC hK q hq (v + δ) hadm τ hτ
              _ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hadm hC₀nn
          · rw [Metric.mem_closedBall, dist_zero_right]; exact hJfbnd τ hτ
        · rw [Metric.mem_closedBall, dist_zero_right]; exact hUfbnd τ hτ
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hTfbnd τ hτ
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hSfbnd τ hτ
  have hKb : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (genericDoubled (octField8' g gi)) (W0 τ)‖ ≤ Kf := by
    intro τ hτ
    have hmem0 := hmem 0 h0σ τ hτ
    have hWW : W 0 τ = W0 τ := by rw [hWdef, hW0def]
    rw [hWW] at hmem0
    exact hKfbd (W0 τ) hmem0
  have hIC : ∀ δ : Point n, ‖δ‖ ≤ σ → W δ 0 - W 0 0 = seedCLM δ := by
    intro δ hδ
    have hadm : ‖v + δ‖ ≤ ρ := hle δ hδ
    obtain ⟨hJfδ0, _, _, _, hUfδ0, _, _, _, hTfδ0, _, _, _, hSfδ0, _, _, _⟩ := hspec δ hadm
    obtain ⟨hJf00, _, _, _, hUf00, _, _, _, hTf00, _, _, _, hSf00, _, _, _⟩ := hspec 0 hadm0
    have h1 : uniformFlowTube g gi hC hK q (v + δ) 0 = (q, v + δ) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + δ) hadm
    have h2 : uniformFlowTube g gi hC hK q (v + 0) 0 = (q, v + 0) :=
      uniformFlowTube_spec_ic g gi hC hK q hq (v + 0) hadm0
    -- Octuple-level IC (raw `St8`, abbrev — syntactic `Prod` subtraction) and the `Sf`-slot vanishing.
    have hoct : (((uniformFlowTube g gi hC hK q (v + δ) 0, Jf δ 0), Uf δ 0), Tf δ 0)
        - (((uniformFlowTube g gi hC hK q (v + 0) 0, Jf 0 0), Uf 0 0), Tf 0 0) = seedOct δ := by
      rw [hseedOct_eq δ, h1, h2, hJfδ0, hJf00, hUfδ0, hUf00, hTfδ0, hTf00, hUseeddef, hTseeddef]
      simp only [Prod.mk_sub_mk, sub_self, add_zero, add_sub_cancel_left, Prod.mk_zero_zero]
    have hsf : Sf δ 0 - Sf 0 0 = (0 : St8 n) := by rw [hSfδ0, hSf00, sub_self]
    simp only [hWdef]
    rw [hseedCLM_eq δ]
    exact Prod.ext hoct hsf
  -- Feed the abstract first-jet engine with `Φ := hexadecupleField`.
  obtain ⟨L, _hLeq, hFD⟩ :=
    autonomousFlow_endpoint_hasFDerivAt_window_exists
      (genericDoubled (octField8' g gi))
      (W := W) (V := Vf) (seed := seedCLM) (S := S) hKf0 hσ ht1 hSconvex hdiff hdiff2 hbound2 hLip
      hseednorm hWode hVode hV0 hIC hKb hmem
  refine ⟨Jf, Uf, Tf, Sf, ?_, L, ?_⟩
  · intro δ hδ
    obtain ⟨hJfδ0, hJfode, _, _, hUfδ0, hUfode, _, _, hTfδ0, hTfode, _, _, hSfδ0, hSfode, _, _⟩ :=
      hspec δ (hle δ hδ)
    exact ⟨hJfδ0, hJfode, hUfδ0, hUfode, hTfδ0, hTfode, hSfδ0, hSfode⟩
  · have hfe : (fun δ => W δ 1)
        = (fun δ => ((((((uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1), Tf δ 1),
          Sf δ 1)) : St16' n)) := by
      funext δ; rw [hWdef]
    rw [hfe] at hFD
    exact hFD

/-- **The projected deep scalar-slot component.**  Projecting `.2` (the `Sf` factor) then `.2.2.2.1` of
    the hexadecuple-flow endpoint derivative, the map `δ ↦ (Sf δ 1).2.2.2.1` is Fréchet-differentiable at
    `0`.  This is the object the fifth-jet value-identification (CARRIED) rewrites to the fourth jet.
    NO `expRho`. -/
theorem uniformFlow_hexadecupleEndpoint_component_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hv : ‖v‖ < uniformFlowRadius g gi hC hK) (a b c d : Point n) :
    ∃ Jf : Point n → ℝ → Point n × Point n,
    ∃ Uf : Point n → ℝ → St2 n,
    ∃ Tf : Point n → ℝ → St4 n,
    ∃ Sf : Point n → ℝ → St8 n,
      (∀ δ : Point n, ‖δ‖ ≤ uniformFlowRadius g gi hC hK - ‖v‖ →
        Jf δ 0 = ((0 : Point n), b) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Jf δ)
            (fderiv ℝ (geodesicField g gi) (uniformFlowTube g gi hC hK q (v + δ) τ) (Jf δ τ)) τ) ∧
        Uf δ 0 = (((0 : Point n), a), ((0 : Point n), (0 : Point n))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Uf δ)
            (fderiv ℝ (doubledField g gi)
              (uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ) (Uf δ τ)) τ) ∧
        Tf δ 0 = ((((0 : Point n), c), ((0 : Point n), (0 : Point n))),
          (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Tf δ)
            (fderiv ℝ (genericDoubled (doubledField g gi))
              ((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ) (Tf δ τ)) τ) ∧
        Sf δ 0 = (((((0 : Point n), d), ((0 : Point n), (0 : Point n))),
            (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n)))),
          ((((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))),
            (((0 : Point n), (0 : Point n)), ((0 : Point n), (0 : Point n))))) ∧
        (∀ τ ∈ Set.Icc (0 : ℝ) 1,
          HasDerivAt (Sf δ)
            (fderiv ℝ (genericDoubled (genericDoubled (doubledField g gi)))
              (((uniformFlowTube g gi hC hK q (v + δ) τ, Jf δ τ), Uf δ τ), Tf δ τ) (Sf δ τ)) τ)) ∧
      ∃ L₅ : Point n →L[ℝ] Point n,
        HasFDerivAt (fun δ => (Sf δ 1).2.2.2.1) L₅ 0 := by
  obtain ⟨Jf, Uf, Tf, Sf, hprops, L, hFD⟩ :=
    uniformFlow_hexadecupleEndpoint_baseVelocity_hasFDerivAt g gi hC hK q hq v hv a b c d
  refine ⟨Jf, Uf, Tf, Sf, hprops, ?_⟩
  set proj : St16' n →L[ℝ] Point n :=
    (ContinuousLinearMap.fst ℝ (Point n) (Point n)).comp
      ((ContinuousLinearMap.snd ℝ (Point n × Point n) (Point n × Point n)).comp
        ((ContinuousLinearMap.snd ℝ (St2 n) (St2 n)).comp
          ((ContinuousLinearMap.snd ℝ (St4 n) (St4 n)).comp
            (ContinuousLinearMap.snd ℝ (St8' n) (St8' n))))) with hprojdef
  refine ⟨proj.comp L, ?_⟩
  have hc := proj.hasFDerivAt.comp (0 : Point n) hFD
  have hfe : (⇑proj ∘ fun δ =>
      (((((( uniformFlowTube g gi hC hK q (v + δ) 1, Jf δ 1), Uf δ 1), Tf δ 1), Sf δ 1)) : St16' n))
      = (fun δ => (Sf δ 1).2.2.2.1) := by
    funext δ
    rfl
  rw [hfe] at hc
  exact hc

end QIQTH.ExpMap
