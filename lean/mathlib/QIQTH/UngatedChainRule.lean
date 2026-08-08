/-
  UngatedChainRule — J4-443: the last witness-level geometric atom of the frozen `hQ1` provider —
  the general-field UNGATED chain-rule identity + `S`-gate transparency, discharging `hcont1`
  (the JOINT continuity of the witness first FIELD-derivative) to its smooth core + a named gate carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE RESIDUE (post J4-442, `GeneralFieldContinuity`).  `innerDiff_phase6` discharged the on-gate
  `C₀` witness-value continuity atom `hcont0`, and BUILT the smooth core of `hcont1`
  (`chartFieldJacobianP_joint_continuousOn` — the JOINT continuity of the general-field chart
  FIELD-Jacobian `(w',z) ↦ fderiv ℝ (W z) (update y i w')`).  What remained of `hcont1`:
    (i)  the general-field UNGATED chain-rule identity connecting `witnessFieldDeriv` (= the field-pd
         of the gated kernel) to the smooth Jacobian chain, and
    (ii) the `S`-gate transparency at the field point (inside the gate, the gated kernel equals the
         ungated composite, so their field-pd's agree).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `pd_component_eq` — the (a,i) matrix entry of a Jacobian is the `pd` of the component: from a
        `DifferentiableAt` chart, `pd (fun y => φ y a) i x = fderiv ℝ φ x eᵢ a`.  (Extracted from the
        `pd_comp` internals; the bridge from the smooth-core CLM to the coordinate `pd`.)
    • `witnessFieldDeriv_eq_ungatedComposite_of_gate` — ★ THE `S`-GATE TRANSPARENCY.  At an in-gate
        field point (`z ∈ K`, `S z ∈ 𝓝 p`) the gated kernel is a NEIGHBOURHOOD germ of the ungated
        composite, so `witnessFieldDeriv = pd` of the ungated composite (`pd_congr_of_eventuallyEq`).
    • `witnessFieldDeriv_gateChain_eq` — ★★ THE GENERAL-FIELD UNGATED CHAIN RULE for the witness.
        Composing transparency with `pd_comp` at the `C^∞` manifold profile
        `prof w' = radialCutoff a b w'·heatParametrix 1 Θ* u* τ w'`, at an in-gate field point:
          `witnessFieldDeriv … i τ p z = ∑ c, pd prof c (W z p) · pd (fun x'' => W z x'' c) i p`,
        `W z = uniformInverseChart g gi hC hK z`.  The general-field analogue of
        `BaseSlotAmpDeriv.pd_chartFieldAmp_center_eq` / `ChartComposedHeatOp.chartComposed_pd_eq`.
    • `chartFieldJacobianComponent_jointContinuousOn` — ★ the component bridge: from the J4-442 smooth
        core (the chart FIELD-Jacobian CLM joint continuity) + per-point chart differentiability, the
        scalar chart field-jet `(w',z) ↦ pd (fun x'' => W z x'' c) i (update y i w')` is jointly
        continuous (CLM-eval `clm_apply` + `continuous_apply` + `pd_component_eq` congr).
    • `witnessFieldDeriv_jointContinuousOn` — ★★★ `hcont1`, DISCHARGED.  On the product
        `Icc (w−ρ)(w+ρ) ×ˢ K`, GIVEN the smooth-core geometry inputs (`hW0`/`hmaps`/`hunit`/`hIFT` —
        the recognized J3 chart carries), per-point chart differentiability `hWdiff`, and the in-gate
        transparency carry `hGate` (the field point stays in the open gate `S z`), the witness first
        field-derivative `(w',z) ↦ witnessFieldDeriv … i τ (update y i w') z` is jointly continuous:
        the gate-chain identity rewrites it to `∑ c, [prof-pd ∘ hW0] · [chart field-jet from the
        smooth core]`, each factor jointly continuous.

  ── THE `hcont1` VERDICT.  `hcont1` is DISCHARGED to bookkeeping at the WITNESS level: the two named
  atoms (i) ungated chain rule and (ii) `S`-gate transparency are BOTH PROVED here; the joint
  continuity assembles from them + the banked J4-442 smooth core.  The residual carries are:
    • the smooth-core geometry inputs `hW0`/`hmaps`/`hunit`/`hIFT` (already the J3 chart-Jacobian
      carries, banked-reducible to `forwardFlowJet_continuousOn` + the IFT identity);
    • `hWdiff` — per-point chart differentiability on the product (a strictly-lighter jet than the
      Jacobian continuity the smooth core already delivers);
    • `hGate` — the in-gate transparency: `S z ∈ 𝓝 (update y i w')` on the product.  This is the honest
      GATE carry — the field point stays inside the open gate; genuine, satisfiable (near the field
      centre with `S z` a neighbourhood of the reach), NON-vacuous, NOT the conclusion, NOT a₁ = R/6.

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.GeneralFieldContinuity

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open QIQTH.InnerDataEnvelope QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialDistance
open QIQTH.ExpMap QIQTH.HeatParametrixAnsatz QIQTH.ChartComposedHeatOp
open QIQTH.JacobiCLMExposure QIQTH.ChartGeneralPContinuity QIQTH.GeneralFieldContinuity
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.UngatedChainRule

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The component bridge — the (a,i) Jacobian entry is the `pd` of the component.
    ############################################################################### -/

/-- **`pd_component_eq`.**  For a chart `φ` differentiable at `x`, the `i`-th coordinate `pd` of the
    `a`-th component equals the `(a,i)` matrix entry of the Fréchet derivative:
      `pd (fun y => φ y a) i x = fderiv ℝ φ x (Pi.single i 1) a`.
    Extracted from the `pd_comp` internals; the bridge from the smooth-core Jacobian CLM to the
    coordinate `pd`.  NOT `a₁ = R/6`. -/
theorem pd_component_eq (φ : Point n → Point n) (i a : Fin n) (x : Point n)
    (hφ : DifferentiableAt ℝ φ x) :
    pd (fun y => φ y a) i x = fderiv ℝ φ x (Pi.single i (1 : ℝ)) a := by
  have hHF : HasFDerivAt (fun y => φ y a)
      ((ContinuousLinearMap.proj a).comp (fderiv ℝ φ x)) x := by
    have h := ((ContinuousLinearMap.proj a).hasFDerivAt).comp x hφ.hasFDerivAt
    exact h
  rw [pd_eq_fderiv (fun y => φ y a) i x hHF.differentiableAt, hHF.fderiv]
  rfl

/-! ###############################################################################
    ### (B) The `S`-gate transparency — in-gate, `witnessFieldDeriv` = ungated composite pd.
    ############################################################################### -/

/-- **★ `witnessFieldDeriv_eq_ungatedComposite_of_gate` — THE `S`-GATE TRANSPARENCY.**  At an in-gate
    field point (`z ∈ K` and the field gate `S z` a NEIGHBOURHOOD of `p`), the gated witness slice
    `x' ↦ vanVleckGatedWitness … τ x' z` equals the ungated composite
    `x' ↦ globalCutoffParametrixWitnessN 1 Θ* u* a b W τ x' z` ON A NEIGHBOURHOOD of `p`
    (`gatedKernel_apply_of_mem`), so their field-`pd`'s agree (`pd_congr_of_eventuallyEq`):
      `witnessFieldDeriv … i τ p z
         = pd (fun x' => globalCutoffParametrixWitnessN 1 Θ* u* a b W τ x' z) i p`.
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_ungatedComposite_of_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (hzK : z ∈ K) (hgate : S z ∈ nhds p) :
    witnessFieldDeriv g gi hC hK S a b i τ p z
      = pd (fun x' : Point n => globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) τ x' z) i p := by
  unfold witnessFieldDeriv
  apply QIQTH.D2HExpandRecon.pd_congr_of_eventuallyEq
  filter_upwards [hgate] with x' hx'
  simp only [vanVleckGatedWitness]
  exact gatedKernel_apply_of_mem K S _ τ hzK hx'

/-! ###############################################################################
    ### (C) The general-field UNGATED chain rule for the witness.
    ############################################################################### -/

/-- **★★ `witnessFieldDeriv_gateChain_eq` — THE GENERAL-FIELD UNGATED CHAIN RULE.**  Composing the
    `S`-gate transparency with the coordinate chain rule `pd_comp` at the `C^∞` manifold profile
    `prof w' = radialCutoff a b w' · heatParametrix 1 Θ* u* τ w'` (through which the ungated composite
    factors: `globalCutoffParametrixWitnessN 1 Θ* u* a b W τ x' z = prof (W z x')`, DEFEQ), the witness
    first field-derivative at an in-gate field point is IDENTIFIED EXACTLY:
      `witnessFieldDeriv … i τ p z
         = ∑ c, pd prof c (W z p) · pd (fun x'' => W z x'' c) i p`,
    `W z = uniformInverseChart g gi hC hK z`.  The general-field analogue of
    `BaseSlotAmpDeriv.pd_chartFieldAmp_center_eq`.  Conditional on the in-gate carry `hgate`, the chart
    differentiability `hWdiff`, and the folded-coefficient smoothness `hw` (⇒ `prof` is `C^∞`).
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gateChain_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hzK : z ∈ K) (hgate : S z ∈ nhds p)
    (hWdiff : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) p) :
    witnessFieldDeriv g gi hC hK S a b i τ p z
      = ∑ c, pd (fun w' : Point n =>
              radialCutoff a b w'
                * heatParametrix 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
            (uniformInverseChart g gi hC hK z p)
          * pd (fun x'' : Point n => uniformInverseChart g gi hC hK z x'' c) i p := by
  have hProfCD : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun w' : Point n => radialCutoff a b w'
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) τ w') :=
    (radialCutoff_contDiff a b).mul
      (heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) τ hw)
  rw [witnessFieldDeriv_eq_ungatedComposite_of_gate g gi hC hK S a b i τ p z hzK hgate]
  simp only [globalCutoffParametrixWitnessN]
  exact pd_comp
    (fun w' : Point n => radialCutoff a b w'
      * heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) τ w')
    (uniformInverseChart g gi hC hK z) i p
    (hProfCD.contDiffAt.differentiableAt (by simp)) hWdiff

/-! ###############################################################################
    ### (D) The component bridge from the J4-442 smooth core — joint continuity.
    ############################################################################### -/

/-- **★ `chartFieldJacobianComponent_jointContinuousOn` — the component bridge.**  From the J4-442
    smooth core (the chart FIELD-Jacobian CLM joint continuity `hFderivJoint`) and per-point chart
    differentiability `hWdiff`, the SCALAR chart field-jet
      `(w',z) ↦ pd (fun x'' => W z x'' c) i (update y i w')`
    is jointly continuous on `Icc (w−ρ)(w+ρ) ×ˢ K`: evaluate the continuous CLM at `Pi.single i 1`
    (`ContinuousOn.clm_apply`), extract component `c` (`continuous_apply`), then `congr` onto the
    coordinate `pd` via `pd_component_eq`.  NOT `a₁ = R/6`. -/
theorem chartFieldJacobianComponent_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (y : Point n) (i : Fin n) (w ρ : ℝ) (c : Fin n)
    (hFderivJoint : ContinuousOn
      (fun q : ℝ × Point n =>
        fderiv ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K))
    (hWdiff : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1)) :
    ContinuousOn
      (fun q : ℝ × Point n =>
        pd (fun x'' : Point n => uniformInverseChart g gi hC hK q.2 x'' c) i (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
  have hclm : ContinuousOn
      (fun q : ℝ × Point n =>
        (fderiv ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1))
          (Pi.single i (1 : ℝ)) c)
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) :=
    (continuous_apply c).comp_continuousOn (hFderivJoint.clm_apply continuousOn_const)
  refine hclm.congr (fun q hq => ?_)
  exact pd_component_eq (uniformInverseChart g gi hC hK q.2) i c (Function.update y i q.1)
    (hWdiff q hq)

/-! ###############################################################################
    ### (E) `hcont1` — the JOINT continuity of the witness first FIELD-derivative, DISCHARGED.
    ############################################################################### -/

/-- **★★★ `witnessFieldDeriv_jointContinuousOn` — `hcont1`, DISCHARGED.**  On the product
    `Icc (w−ρ)(w+ρ) ×ˢ K`, the witness first field-derivative
      `(w',z) ↦ witnessFieldDeriv … i τ (update y i w') z`
    is jointly continuous.  Route: the gate-chain identity `witnessFieldDeriv_gateChain_eq` rewrites
    it (via `ContinuousOn.congr`) to the SMOOTH sum
      `∑ c, pd prof c (W z (update y i w')) · pd (fun x'' => W z x'' c) i (update y i w')`,
    whose two factors are jointly continuous:
      • FACTOR 1 = `pd prof c` (`prof` is `C^∞`, `contDiff_pd_inf`) composed with the origin section
        `hW0`;
      • FACTOR 2 = the chart field-jet, from the J4-442 smooth core
        `chartFieldJacobianP_joint_continuousOn` (supplied INTERNALLY from `hW0`/`hmaps`/`hunit`/`hIFT`)
        via the component bridge `chartFieldJacobianComponent_jointContinuousOn`.
    Carries, all satisfiable / non-vacuous / none the conclusion:
      • the smooth-core geometry inputs `hW0`/`hmaps`/`hunit`/`hIFT` (the J3 chart-Jacobian carries),
      • `hWdiff` — per-point chart differentiability on the product,
      • `hGate` — the in-gate transparency `S z ∈ 𝓝 (update y i w')` on the product (the honest GATE
        carry: the field point stays in the open gate),
      • `hw` — folded-coefficient smoothness (⇒ `prof` is `C^∞`).
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (y : Point n) (w ρ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
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
            (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1))))
    (hWdiff : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK q.2) (Function.update y i q.1))
    (hGate : ∀ q ∈ Set.Icc (w - ρ) (w + ρ) ×ˢ K,
      S q.2 ∈ nhds (Function.update y i q.1)) :
    ContinuousOn
      (fun q : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i τ (Function.update y i q.1) q.2)
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
  -- the C∞ profile
  have hProfCD : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun w' : Point n => radialCutoff a b w'
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) τ w') :=
    (radialCutoff_contDiff a b).mul
      (heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) τ hw)
  -- the J4-442 smooth core: the chart FIELD-Jacobian CLM joint continuity
  have hFderivJoint := chartFieldJacobianP_joint_continuousOn g gi hC hK y i w ρ hW0 hmaps hunit hIFT
  -- FACTOR 1: pd prof c ∘ (origin section)
  have hF1 : ∀ c : Fin n, ContinuousOn
      (fun q : ℝ × Point n =>
        pd (fun w' : Point n => radialCutoff a b w'
              * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
          (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1)))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) := by
    intro c
    simpa [Function.comp] using
      (contDiff_pd_inf _ hProfCD c).continuous.comp_continuousOn hW0
  -- FACTOR 2: the chart field-jet from the smooth core
  have hF2 : ∀ c : Fin n, ContinuousOn
      (fun q : ℝ × Point n =>
        pd (fun x'' : Point n => uniformInverseChart g gi hC hK q.2 x'' c) i
          (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) :=
    fun c => chartFieldJacobianComponent_jointContinuousOn g gi hC hK y i w ρ c hFderivJoint hWdiff
  -- the smooth sum is jointly continuous
  have hSum : ContinuousOn
      (fun q : ℝ × Point n =>
        ∑ c, pd (fun w' : Point n => radialCutoff a b w'
                * heatParametrix 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
              (uniformInverseChart g gi hC hK q.2 (Function.update y i q.1))
            * pd (fun x'' : Point n => uniformInverseChart g gi hC hK q.2 x'' c) i
                (Function.update y i q.1))
      (Set.Icc (w - ρ) (w + ρ) ×ˢ K) :=
    continuousOn_finsetSum _ (fun c _ => (hF1 c).mul (hF2 c))
  refine hSum.congr (fun q hq => ?_)
  exact witnessFieldDeriv_gateChain_eq g gi hC hK S a b i τ (Function.update y i q.1) q.2
    hw hq.2 (hGate q hq) (hWdiff q hq)

end QIQTH.UngatedChainRule

/-! ## THE PROVIDER FINAL LEDGER — the frozen `hQ1` provider after J4-443.

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │ hcont0 (on-gate C₀ witness-value continuity):  ★ DISCHARGED (J4-442 `hcont0_of_chartCont` /       │
  │   `innerDiff_phase6`).                                                                            │
  │                                                                                                  │
  │ hcont1 (JOINT continuity of the witness first FIELD-derivative on `Icc (w−ρ)(w+ρ) ×ˢ K`):         │
  │   ★★★ DISCHARGED at the WITNESS level (`witnessFieldDeriv_jointContinuousOn`).  Both named atoms   │
  │   are PROVED here:                                                                                │
  │     (i)  the general-field UNGATED chain-rule identity `witnessFieldDeriv_gateChain_eq`            │
  │            (transparency ∘ `pd_comp` at the `C^∞` manifold profile);                              │
  │     (ii) the `S`-gate transparency `witnessFieldDeriv_eq_ungatedComposite_of_gate`                │
  │            (`gatedKernel_apply_of_mem` germ + `pd_congr_of_eventuallyEq`).                        │
  │   The joint continuity then assembles: gate-chain identity ⇒ `∑ c [prof-pd ∘ hW0]·[chart          │
  │   field-jet]`, the chart field-jet from the J4-442 smooth core                                    │
  │   `chartFieldJacobianP_joint_continuousOn` via the component bridge                               │
  │   `chartFieldJacobianComponent_jointContinuousOn`.                                                │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── THE PROVIDER FINAL STATUS.  With `hcont0` (J4-442) and `hcont1` (J4-443) BOTH discharged at the
  witness level, the frozen `hQ1` provider's on-gate `C₀` sup family is grounded on ONLY:
    (1) the CHART geometry carries `hW0`/`hmaps`/`hunit`/`hIFT` (banked-reducible to
        `forwardFlowJet_continuousOn` + `fderiv_localLeftInverse_eq_ringInverse`, the J3 chart chain);
    (2) `hWdiff` — per-point chart differentiability (strictly lighter than the Jacobian continuity the
        smooth core already delivers);
    (3) `hGate` — the in-gate transparency `S z ∈ 𝓝 (update y i w')` on the product (the honest GATE
        carry: the field point stays in the open gate);
    (4) `hw` — folded-coefficient smoothness (van-Vleck / transport smoothness bank);
    (5) measurability / integrability / Levi-Gaussian bookkeeping.
  There is NO remaining genuinely-open geometric analytic wall at the witness level for `hcont1`: the
  two atoms are proved, the smooth core is banked.  The residue is exactly the enumerated bookkeeping +
  the geometry / gate carries (1)–(3), each satisfiable, non-vacuous, none the conclusion.

  ── DON'T-UNDERCREDIT FINDINGS (paid off again).
    • `pd_comp` (`ResidualChartTransport`, base-general) IS the general-field chain rule — the witness
      ungated composite factors DEFEQ through the `C^∞` profile, so no fresh chain-rule wall; only the
      `S`-gate germ + `pd_congr_of_eventuallyEq` (banked) was needed for transparency.
    • The J4-442 smooth core `chartFieldJacobianP_joint_continuousOn` delivers the chart FIELD-Jacobian
      CLM joint continuity DIRECTLY; the scalar field-jet is a `clm_apply` + `continuous_apply` +
      `pd_component_eq` bridge away — NOT a fresh analytic wall.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on the chart geometry carries, the gate carry, the
  banked convergence trio, and the geometric wiring).
-/

section AxiomChecks
open QIQTH.UngatedChainRule
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms pd_component_eq
#print axioms witnessFieldDeriv_eq_ungatedComposite_of_gate
#print axioms witnessFieldDeriv_gateChain_eq
#print axioms chartFieldJacobianComponent_jointContinuousOn
#print axioms witnessFieldDeriv_jointContinuousOn
end AxiomChecks
