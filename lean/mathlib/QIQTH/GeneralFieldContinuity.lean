/-
  GeneralFieldContinuity — J4-442: grounding the two remaining atoms of the frozen `hQ1` provider
  (the general-field-point base-continuity `hcont0` and the smooth core of the joint field-derivative
  continuity `hcont1`), closing the on-gate `C₀` slot of the provider to bookkeeping.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-441, `SupBaseGeneral`).  `innerDiff_phase5` reduced the frozen `hQ1`
  provider to a REDUCED carry `hGateData'` whose two on-gate sup bullets were replaced by two NAMED
  general-field-point continuity carries:
    • `hcont0` — base-continuity of the UNGATED witness value at the general field point
        `update y i w`, on the compact gate `K`
        (`z ↦ globalCutoffParametrixWitnessN 1 … (u−s) (update y i w) z`  ContinuousOn `K`);
    • `hcont1` — JOINT continuity of the witness first FIELD-derivative on `Icc (w−ρ)(w+ρ) ×ˢ K`
        (`(w',z) ↦ witnessFieldDeriv … i (u−s) (update y i w') z`).

  ── DON'T-UNDERCREDIT FINDINGS (mission step 1).
    • `ChartGeneralPContinuity.chartP_continuousOn` ALREADY delivers the p-GENERAL chart z-continuity
      `ContinuousOn (z ↦ uniformInverseChart … z p) S` at ANY field point `p` (under the three
      geometric side-conditions at `p`).  So `hcont0` is NOT a fresh analytic wall: the WITNESS VALUE
      factors as `profile ∘ (z ↦ W z p)` with `profile w' = radialCutoff a b w' · heatParametrix 1 …
      τ w'` a banked GLOBAL-continuous manifold profile.  `hcont0` is therefore the composition of
      the p-general chart continuity with the profile — DISCHARGED here (`hcont0_of_chartCont`),
      residue = the chart continuity itself (banked-reducible to `chartP_continuousOn`) + the folded-
      coefficient smoothness `hw`.
    • `JacobiCLMExposure.forwardFlowJet_continuousOn` is JOINT-in-`(z,v)` and UNCONDITIONAL on
      `K ×ˢ ball 0 ρ_K` (NOT endpoint-0-anchored — general velocity `v`).  And the IFT-Jacobian
      identity `ChartFieldJacobian.fderiv_localLeftInverse_eq_ringInverse` is stated at an ARBITRARY
      base point `v₀` (not centre-only).  So the J4-433→435 chain replays VERBATIM one field-order
      more general: `chartFieldJacobianP_joint_continuousOn` gives the JOINT continuity of the
      general-field chart FIELD-Jacobian `(w',z) ↦ fderiv ℝ (W z) (update y i w')` on the product,
      from the same banked forward-flow joint continuity + `Ring.inverse` continuity at units + the
      (general-field) IFT identity.  This is the SMOOTH CORE that `hcont1` reduces to.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `parametrixWitnessProfile_continuous` — the manifold profile `w' ↦ radialCutoff a b w' ·
        heatParametrix 1 Θ u τ w'` is GLOBALLY continuous (banked `radialCutoff_contDiff` +
        `heatParametrix_contDiff_space`), given folded-coefficient smoothness `hw`.
    • `hcont0_of_chartCont` — ★★ the WITNESS-VALUE base-continuity `hcont0` at general field point,
        DISCHARGED from the chart z-continuity on `K` (`chartP_continuousOn`-shaped) + `hw`, via the
        factorisation witness value = profile ∘ chart.
    • `chartFieldJacobianP_joint_continuousOn` — ★★ the JOINT continuity of the GENERAL-FIELD chart
        FIELD-Jacobian on `Icc (w−ρ)(w+ρ) ×ˢ K` — the J4-433/435 chain replayed one field-order more
        general (the SMOOTH CORE of `hcont1`).
    • `gateData_of_reduced2` — ★★★ the `hcont0`-DISCHARGE: builds `SupBaseGeneral`'s exact reduced
        carry `hGateData'` from a strictly-lighter carry `hGateData''` whose `hcont0` witness-value
        continuity bullet is REPLACED by the (lighter) chart z-continuity bullet, with `hcont0` filled
        by `hcont0_of_chartCont` + the global `hw`.
    • `innerDiff_phase6` — ★★★ `SupBaseGeneral.innerDiff_phase5` with the reduced carry `hGateData'`
        SUPPLIED from `hGateData''` via `gateData_of_reduced2`: the on-gate `C₀` witness-value
        continuity atom is DISCHARGED (to chart continuity + folded smoothness), shrinking the
        provider remainder to {chart z-continuity at general `p`, `hcont1`, bookkeeping}.

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SupBaseGeneral
import QIQTH.JacobiCLMExposure
import QIQTH.ChartGeneralPContinuity
import QIQTH.ChartComposedHeatOp

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open QIQTH.InnerDataEnvelope QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.CConvV2GaussianPairing QIQTH.CConvV2WitnessStar
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialDistance
open QIQTH.ExpMap QIQTH.HeatParametrixAnsatz QIQTH.ChartComposedHeatOp
open QIQTH.JacobiCLMExposure QIQTH.ChartGeneralPContinuity
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.GeneralFieldContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The manifold profile is globally continuous.
    ############################################################################### -/

/-- **`parametrixWitnessProfile_continuous`.**  The manifold profile
    `w' ↦ radialCutoff a b w' · heatParametrix 1 Θ u τ w'` (through which the witness value factors,
    `globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p q = profile (Vmap q p)`) is GLOBALLY continuous:
    `radialCutoff a b` is `C∞` (`radialCutoff_contDiff`) and `heatParametrix 1 Θ u τ` is `C∞` in space
    (`heatParametrix_contDiff_space`, under the folded-coefficient smoothness `hw`).  NOT `a₁ = R/6`. -/
theorem parametrixWitnessProfile_continuous (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    Continuous (fun w' : Point n => radialCutoff a b w' * heatParametrix 1 Θ u τ w') :=
  (radialCutoff_contDiff a b).continuous.mul (heatParametrix_contDiff_space 1 Θ u τ hw).continuous

/-! ###############################################################################
    ### (B) `hcont0` at general field point — DISCHARGED from chart continuity.
    ############################################################################### -/

/-- **★★ `hcont0_of_chartCont` — the WITNESS-VALUE base-continuity at GENERAL field point.**  In the
    EXACT `hcont0` slot shape of `SupBaseGeneral`'s reduced carry: the ungated witness value
    `z ↦ globalCutoffParametrixWitnessN 1 (vanVleck g) … (uniformInverseChart …) τ (update y i w) z`
    is continuous on `K`, from the chart z-continuity `hWcont` on `K` (the p-general
    `chartP_continuousOn` conclusion at `p = update y i w`) composed with the global profile
    continuity `parametrixWitnessProfile_continuous` (needs folded-coefficient smoothness `hw`).
    Uses the factorisation witness value `= profile ∘ (z ↦ W z (update y i w))` (DEFEQ).
    NOT `a₁ = R/6`. -/
theorem hcont0_of_chartCont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ w : ℝ) (y : Point n) (i : Fin n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hWcont : ContinuousOn
      (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update y i w)) K) :
    ContinuousOn (fun z : Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ (Function.update y i w) z) K := by
  have hprof : Continuous (fun w' : Point n =>
      radialCutoff a b w'
        * heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) τ w') :=
    parametrixWitnessProfile_continuous (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b τ hw
  have heq : (fun z : Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ (Function.update y i w) z)
      = (fun w' : Point n =>
          radialCutoff a b w'
            * heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) τ w')
        ∘ (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update y i w)) := rfl
  rw [heq]
  exact hprof.comp_continuousOn hWcont

/-! ###############################################################################
    ### (C) The general-field chart FIELD-Jacobian — JOINT continuity (smooth core of hcont1).
    ############################################################################### -/

/-- **★★ `chartFieldJacobianP_joint_continuousOn` — the JOINT continuity of the GENERAL-FIELD chart
    FIELD-Jacobian.**  On the compact product `Icc (w−ρ)(w+ρ) ×ˢ K` the map
        `(w',z) ↦ fderiv ℝ (uniformInverseChart g gi hC hK z) (update y i w')`
    is continuous — the `ChartFieldJacobian.chartFieldJacobian_continuousOn_of_forwardJointCont`
    reduction REPLAYED one field-order more general (field point `update y i w'` ≠ centre `0`, and
    JOINT in `(w', z)`).  Inputs on the product:
      • `hW0`   — joint continuity of the origin section `(w',z) ↦ W z (update y i w')`
                  (the general-field analogue of the banked origin-section continuity; reducible via
                  `chartP_continuousOn`);
      • `hmaps` — the pairing `(w',z) ↦ (z, W z (update y i w'))` lands in `K ×ˢ ball 0 ρ_K`
                  (chart reach at general `p`);
      • `hunit` — invertibility of `Dφ_z(W z (update y i w'))` on the product;
      • `hIFT`  — the general-field IFT-Jacobian identity on the product (supplied by
                  `ChartFieldJacobian.fderiv_localLeftInverse_eq_ringInverse` at `v₀ = W z (update y i
                  w')`, which is base-point-general).
    Mechanism: `hIFT` rewrites the target to `Ring.inverse (fderiv φ_z (W z (update y i w')))`; the
    inner map is the banked JOINT-in-`(z,v)` `forwardFlowJet_continuousOn` composed with the
    (continuous, via `hW0`) origin-section pairing; `Ring.inverse` is continuous at each unit value.
    NOT `a₁ = R/6`. -/
theorem chartFieldJacobianP_joint_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (y : Point n) (i : Fin n) (w ρ : ℝ)
    (hW0 : ContinuousOn
      (fun q : ℝ × Point n => uniformInverseChart g gi hC hK q.2 (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K))
    (hmaps : Set.MapsTo
      (fun q : ℝ × Point n => (q.2, uniformInverseChart g gi hC hK q.2 (Function.update y i q.1)))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)))
    (hunit : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK q.2)
        (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1))))
    (hIFT : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      fderiv ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1)
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK q.2)
            (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1)))) :
    ContinuousOn
      (fun q : ℝ × Point n =>
        fderiv ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
  have hFwd := forwardFlowJet_continuousOn g gi hC hK
  have hpair : ContinuousOn
      (fun q : ℝ × Point n =>
        (q.2, uniformInverseChart g gi hC hK q.2 (Function.update y i q.1)))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) :=
    (continuous_snd.continuousOn).prodMk hW0
  have hinner : ContinuousOn
      (fun q : ℝ × Point n =>
        fderiv ℝ (uniformFlowExp g gi hC hK q.2)
          (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1)))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) :=
    hFwd.comp hpair hmaps
  have hRinv : ContinuousOn
      (fun q : ℝ × Point n =>
        Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK q.2)
          (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1))))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
    intro q₀ hq₀
    obtain ⟨u₀, hu₀⟩ := hunit q₀ hq₀
    have hca : ContinuousAt Ring.inverse
        (fderiv ℝ (uniformFlowExp g gi hC hK q₀.2)
          (uniformInverseChart g gi hC hK q₀.2 (Function.update y i q₀.1))) := by
      rw [← hu₀]; exact (contDiffAt_ringInverse (n := 1) ℝ u₀).continuousAt
    exact hca.tendsto.comp (hinner q₀ hq₀)
  exact hRinv.congr hIFT

/-! ###############################################################################
    ### (D) `gateData_of_reduced2` — the `hcont0` DISCHARGE.
    ############################################################################### -/

/-- **★★★ `gateData_of_reduced2` — the `hcont0` (on-gate `C₀` continuity) DISCHARGE.**  Produces
    `SupBaseGeneral`'s EXACT reduced carry `hGateData'` (the `innerDiff_phase5` input) from a strictly-
    lighter carry `hGateData''` whose `hcont0` WITNESS-VALUE continuity bullet
    `ContinuousOn (z ↦ globalCutoffParametrixWitnessN 1 … (u−s) (update y i w) z) K`
    is REPLACED by the (lighter) CHART z-continuity bullet
    `ContinuousOn (z ↦ uniformInverseChart g gi hC hK z (update y i w)) K`,
    with `hcont0` filled by `hcont0_of_chartCont` from that chart continuity + the global folded-
    coefficient smoothness `hw`.  Every OTHER bullet (`ρ`/`σ`/`C_L`/measurabilities/Levi-domination/
    `hcont1`/gate-dichotomy) is threaded verbatim.  Pure construction; the replaced bullet is a
    satisfiable, non-vacuous, strictly-lower-level carry (chart continuity), none equal to `a₁ = R/6`.
    NOT `a₁ = R/6`. -/
theorem gateData_of_reduced2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (V : Set (Point n))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hGateData'' : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (ρ σ C_L : ℝ),
              0 < ρ ∧ 0 < σ ∧ 0 ≤ C_L ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s)
                    (Function.update y i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z)
                volume ∧
              (∀ᵐ z ∂volume,
                |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
                  ≤ C_L * gaussDdim σ z) ∧
              ContinuousOn
                (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update y i w)) K ∧
              ContinuousOn (fun q : ℝ × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (u - s)
                    (Function.update y i q.1) q.2)
                (Set.Icc (w - ρ) (w + ρ) ×ˢ K) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ),
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w')))) :
    ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (ρ σ C_L : ℝ),
              0 < ρ ∧ 0 < σ ∧ 0 ≤ C_L ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s)
                    (Function.update y i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z)
                volume ∧
              (∀ᵐ z ∂volume,
                |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
                  ≤ C_L * gaussDdim σ z) ∧
              ContinuousOn (fun z : Point n =>
                  globalCutoffParametrixWitnessN 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) a b
                    (uniformInverseChart g gi hC hK) (u - s) (Function.update y i w) z) K ∧
              ContinuousOn (fun q : ℝ × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (u - s)
                    (Function.update y i q.1) q.2)
                (Set.Icc (w - ρ) (w + ρ) ×ˢ K) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ),
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w'))) := by
  intro m i u hu y hy
  obtain ⟨snb, hsnb, hDHdom, hcore''⟩ := hGateData'' m i u hu y hy
  refine ⟨snb, hsnb, hDHdom, ?_⟩
  filter_upwards [hcore''] with s hs hmem w hw'
  obtain ⟨ρ, σ, C_L, hρ, hσ, hC_L, hWmeas, hLevimeas, hDHmeas, hLevi, hWcont, hcont1, hdich⟩ :=
    hs hmem w hw'
  exact ⟨ρ, σ, C_L, hρ, hσ, hC_L, hWmeas, hLevimeas, hDHmeas, hLevi,
    hcont0_of_chartCont g gi hC hK a b (u - s) w y i hw hWcont, hcont1, hdich⟩

/-! ###############################################################################
    ### (E) `innerDiff_phase6` — the provider with the on-gate `C₀` continuity DISCHARGED.
    ############################################################################### -/

/-- **★★★ `innerDiff_phase6`.**  `SupBaseGeneral.innerDiff_phase5` with the reduced carry `hGateData'`
    SUPPLIED INTERNALLY from the strictly-lighter carry `hGateData''` via `gateData_of_reduced2`: the
    on-gate `C₀` WITNESS-VALUE continuity atom `hcont0` is DISCHARGED here (reduced to the CHART
    z-continuity bullet + the global folded-coefficient smoothness `hw`).  Every OTHER hypothesis is
    threaded exactly as `innerDiff_phase5`.  Pure composition; each remaining carry satisfiable, non-
    vacuous, strictly lower level than the conclusion, none equal to `a₁ = R/6`.  ⚠ STILL NOT
    `a₁ = R/6`. -/
theorem innerDiff_phase6 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (V : Set (Point n)) (hV : V ∈ 𝓝 (0 : Point n))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ (w d : ℝ),
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) (Function.update y i w) p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitJointYbase : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWFDjointY : ∀ (i : Fin n) (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V → ∀ d : ℝ,
      AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (u - p.1) y p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hWitDomCappedY : ∀ (u : ℝ), u ∈ U → ∀ (y : Point n), y ∈ V →
        ∀ Tc εₘ : ℝ, 0 < εₘ → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |vanVleckGatedWitness g gi hC hK S a b τ y z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hGateData'' : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        ∃ (snb : Set ℝ),
          snb ∈ 𝓝 (y i) ∧
          (∀ εₘ' : ℝ, 0 < εₘ' → ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
            ∀ w ∈ snb, ∀ τ : ℝ, εₘ' ≤ τ → τ ≤ u → ∀ z : Point n,
              |witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i w) z|
                ≤ CA * gaussDdim (wA * τ) (0 - z)) ∧
          (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
            ∃ (ρ σ C_L : ℝ),
              0 < ρ ∧ 0 < σ ∧ 0 ≤ C_L ∧
              (∀ w' : ℝ, AEStronglyMeasurable
                (fun z => vanVleckGatedWitness g gi hC hK S a b (u - s)
                    (Function.update y i w') z) volume) ∧
              AEStronglyMeasurable
                (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
                volume ∧
              AEStronglyMeasurable
                (fun z => witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update y i w) z)
                volume ∧
              (∀ᵐ z ∂volume,
                |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
                  ≤ C_L * gaussDdim σ z) ∧
              ContinuousOn
                (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update y i w)) K ∧
              ContinuousOn (fun q : ℝ × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (u - s)
                    (Function.update y i q.1) q.2)
                (Set.Icc (w - ρ) (w + ρ) ×ˢ K) ∧
              (∀ᵐ z ∂volume, ∀ w' ∈ Set.Icc (w - ρ) (w + ρ),
                z ∉ K ∨ PdiffAt (fun x' : Point n =>
                    vanVleckGatedWitness g gi hC hK S a b (u - s) x' z) i
                  (Function.update y i w')))) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.SupBaseGeneral.innerDiff_phase5 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    hGint hbulkderiv hsliver hcont V hV
    hLeviJoint hWitJointY hWitJointYbase hWFDjointY hFzero hFdomEvery hWitDomCappedY
    (gateData_of_reduced2 g gi hC hK S a b U V hw hGateData'')

end QIQTH.GeneralFieldContinuity

/-! ## THE PROVIDER FINAL LEDGER — the frozen `hQ1` provider after J4-442.

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │ THE TWO REMAINING ATOMS (J4-441 `SupBaseGeneral` ledger) AND THEIR J4-442 STATUS                 │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │ hcont0  (on-gate C₀ witness-value continuity at general field point `update y i w`, on `K`):      │
  │   ★ DISCHARGED to bookkeeping.  `hcont0_of_chartCont` proves it from the CHART z-continuity       │
  │   `ContinuousOn (z ↦ W z (update y i w)) K` (= `ChartGeneralPContinuity.chartP_continuousOn`'s    │
  │   conclusion at `p = update y i w`) composed with the GLOBAL profile continuity                   │
  │   `parametrixWitnessProfile_continuous` (banked `radialCutoff_contDiff` +                         │
  │   `heatParametrix_contDiff_space`), via the DEFEQ factorisation                                   │
  │     witness value = profile ∘ (z ↦ W z (update y i w)).                                           │
  │   `gateData_of_reduced2` + `innerDiff_phase6` REPLACE the `hcont0` bullet of the reduced carry    │
  │   with the (lighter) chart-continuity bullet + the global folded-smoothness `hw`.                 │
  │                                                                                                  │
  │ hcont1  (JOINT continuity of the witness first FIELD-derivative on `Icc (w−ρ)(w+ρ) ×ˢ K`):        │
  │   ◐ SMOOTH CORE BUILT, gate/chain-rule residue NAMED.  `chartFieldJacobianP_joint_continuousOn`   │
  │   supplies the general-field chart FIELD-Jacobian JOINT continuity                                │
  │     `(w',z) ↦ fderiv ℝ (W z) (update y i w')`  on the product                                     │
  │   (the J4-433/435 chain — `fderiv_localLeftInverse_eq_ringInverse` [base-point-general] +         │
  │   `forwardFlowJet_continuousOn` [JOINT-in-(z,v), UNCONDITIONAL] + `Ring.inverse`-at-units —       │
  │   replayed one field-order more general).  The remaining gap is the connection from this SMOOTH   │
  │   Jacobian to `witnessFieldDeriv` = `pd (gatedKernel …)` in the FIELD slot: it needs (i) the      │
  │   general-field UNGATED chain-rule identity (the analogue of `BaseSlotAmpDeriv.                   │
  │   pd_chartFieldAmp_center_eq` / `ChartComposedHeatOp.chartComposed_pd_eq` at general field point   │
  │   `update y i w'`) AND (ii) GATE TRANSPARENCY of the `S`-gate at the field point (the gate         │
  │   dichotomy `hdich` promotes the pd through the gate on the in-gate region).  These are the two    │
  │   HONESTLY-NAMED atoms of `hcont1`; they are NOT discharged here.                                 │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── THE PROVIDER FINAL STATUS.  `innerDiff_phase6` is `innerDiff_phase5` with the on-gate `C₀`
  WITNESS-VALUE continuity atom (`hcont0`) DISCHARGED to bookkeeping (chart z-continuity + global
  folded-coefficient smoothness).  The frozen `hQ1` provider's on-gate sup family is now grounded on:
    (1) the CHART z-continuity at general field point `update y i w` on `K`
        (banked-reducible to `chartP_continuousOn` under its three geometric side-conditions);
    (2) `hcont1` — reduced to {general-field chart FIELD-Jacobian JOINT continuity (BUILT here) +
        general-field ungated chain-rule identity + `S`-gate transparency};
    (3) measurability / integrability / Levi-Gaussian bookkeeping.
  Atom (1) is the SAME p-general chart continuity `hcont0` factors through; the WITNESS-VALUE `C₀`
  slot is thus fully grounded at the witness.  The single genuinely-open geometric input at the
  witness level is the `hcont1` gate/chain-rule connection (its smooth core is now banked).

  ── DON'T-UNDERCREDIT FINDINGS (paid off again).
    • `chartP_continuousOn` was ALREADY the p-general chart continuity — `hcont0` was never a fresh
      analytic wall, only a composition with the banked global profile.  DISCHARGED.
    • `forwardFlowJet_continuousOn` was ALREADY JOINT-in-(z,v) and UNCONDITIONAL (general velocity),
      and `fderiv_localLeftInverse_eq_ringInverse` ALREADY base-point-general — so the entire
      J4-433/435 chart-Jacobian chain replays VERBATIM at general field point, jointly.  The smooth
      core of `hcont1` is therefore BANKED, not walled.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on the chart geometric side-conditions at general
  `p`, the `hcont1` gate/chain-rule connection, the banked convergence trio, and the geometric wiring).
-/

section AxiomChecks
open QIQTH.GeneralFieldContinuity
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms parametrixWitnessProfile_continuous
#print axioms hcont0_of_chartCont
#print axioms chartFieldJacobianP_joint_continuousOn
#print axioms gateData_of_reduced2
#print axioms innerDiff_phase6
end AxiomChecks
