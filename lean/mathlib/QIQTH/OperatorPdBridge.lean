/-
  OperatorPdBridge — J4-486: the OPERATOR ⇄ `pd`-coordinate bridge for the chart SECOND jet — wiring
  the proved (conditional) operator second-jet `Hfwd2Weld.chartSecondJet_continuousOn_of_reach` into
  the `pd`-iterated (coordinate) form the a₁=R/6 consumer chains speak.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3
  only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  J4-484 (`Hfwd2Weld.chartSecondJet_continuousOn_of_reach`) delivered the chart Hessian
  in OPERATOR form — the base-continuity, on `U ⊆ K`, of the field-centre SECOND Fréchet jet
        `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0`,
  gated by the (I1) reachability input `hReach`.  The consumer chains speak the `pd`-iterated
  (coordinate) dialect.  This brick supplies the DICTIONARY (`pd ∘ pd` = a coordinate of `fderiv²`) and
  pushes the operator result through it.

  ## THE COORDINATE GATE (this file, DERIVED — pure Mathlib).  The second-order analogue of the
  first-order `pd_component_eq` (`pd (φ·a) i x = (fderiv φ x eᵢ)ₐ`).  For a vector field `φ` that is
  differentiable NEAR `x` (so `pd (φ·c) j` = the `(c,j)`-coordinate of `fderiv φ` in a nbhd) and whose
  operator first-jet `y ↦ fderiv ℝ φ y` is differentiable AT `x`,
        `pd (fun y => pd (fun x' => φ x' c) j y) i x
           = fderiv ℝ (fun y => fderiv ℝ φ y) x (eᵢ) (eⱼ) c`
  (`pd_pd_component_eq`).  Mechanism (the `PullbackMetric` `Θ`-contraction pattern one order lower):
  the inner `pd` equals `Λ (fderiv φ ·)` near `x` with the scalar evaluation CLM
  `Λ = projᵨ ∘L (apply eⱼ)`; `pd_congr_nhds` transports; `pd_eq_fderiv` + the CLM chain rule
  (`Λ.hasFDerivAt.comp`) extract the outer coordinate.

  ## THE OPERATOR RESULT, IN COORDINATES (this file, DERIVED — conditional on the SAME inputs).
  `chartSecondJetComponent_continuousOn_of_reach` feeds `chartSecondJet_continuousOn_of_reach` through
  the coordinate gate: the base-varying, field-centre-`0`, `pd`-iterated raw-chart Hessian
        `z ↦ pd (fun y => pd (fun x' => uniformInverseChart … z x' c) j y) i 0`
  is base-continuous on `U`.  The operator jet is `evalCLM`-contracted (a continuous linear map) and
  `.congr`'d onto the `pd`-iterated coordinate via the gate; the sole non-bookkeeping carry beyond
  `chartSecondJet`'s own inputs is the per-`z` chart-centre `C²` (`hreg`) needed for the gate's
  differentiability side-conditions.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `pd_component_eq'` — the first-order coordinate extractor (`pd (φ·a) i x = (fderiv φ x eᵢ)ₐ`),
      re-proved inline (the `pd_comp` internals; avoids importing the heavy `UngatedChainRule`).

    * `pd_pd_component_eq` — ★ THE COORDINATE GATE (pure Mathlib): `pd ∘ pd` of a vector-field
      component = the `(eᵢ,eⱼ,c)` coordinate of the operator SECOND jet `fderiv ℝ (fderiv ℝ φ)`.

    * `chartSecondJetComponent_continuousOn_of_reach` — ★★ the chart operator second-jet
      (`chartSecondJet_continuousOn_of_reach`), pushed into `pd`-iterated coordinate form: the
      base-varying field-centre raw-chart Hessian coordinate is base-continuous on `U`, carrying the
      SAME `hReach`/`hW0`/`horigin`/`hunit`/`hid2` inputs + the per-`z` `hreg`.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion):
    * `hReach` — the (I1) K-uniform reachability (inherited verbatim from `chartSecondJet`).
    * `hW0`/`horigin`/`hunit`/`hid2` — `chartSecondJet`'s standing geometric carries.
    * `hreg` — the per-`z` chart-centre `C²` (a chart-smoothness fact, satisfiable on a small ball).

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Hfwd2Weld

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.HbaseJ2Assembly QIQTH.Flow3Regularity QIQTH.JacobiCLMExposure QIQTH.ChartFieldJacobian
open QIQTH.Hfwd2Weld QIQTH.ChartSecondJet
open scoped Topology

namespace QIQTH.OperatorPdBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The first-order coordinate extractor (re-proved inline).
    ############################################################################### -/

/-- **`pd_component_eq'`.**  For a chart `φ` differentiable at `x`, the `i`-th coordinate `pd` of the
    `a`-th component is the `(a,i)` matrix entry of the Fréchet derivative:
      `pd (fun y => φ y a) i x = fderiv ℝ φ x (Pi.single i 1) a`.
    Re-proved inline (identical to `UngatedChainRule.pd_component_eq`) to keep the import surface light.
    NOT `a₁ = R/6`. -/
theorem pd_component_eq' (φ : Point n → Point n) (i a : Fin n) (x : Point n)
    (hφ : DifferentiableAt ℝ φ x) :
    pd (fun y => φ y a) i x = fderiv ℝ φ x (Pi.single i (1 : ℝ)) a := by
  have hHF : HasFDerivAt (fun y => φ y a)
      ((ContinuousLinearMap.proj a).comp (fderiv ℝ φ x)) x := by
    have h := (ContinuousLinearMap.proj a).hasFDerivAt.comp x hφ.hasFDerivAt
    exact h
  rw [pd_eq_fderiv (fun y => φ y a) i x hHF.differentiableAt, hHF.fderiv]
  rfl

/-! ###############################################################################
    ### ★ (B) THE COORDINATE GATE — `pd ∘ pd` = a coordinate of `fderiv²` (pure Mathlib).
    ############################################################################### -/

/-- **★ `pd_pd_component_eq` — THE COORDINATE GATE.**  The second-order analogue of `pd_component_eq'`.
    For a vector field `φ : Point n → Point n` differentiable in a NEIGHBOURHOOD of `x` (`hφ`) whose
    operator first-jet `y ↦ fderiv ℝ φ y` is differentiable AT `x` (`hφ2`),
      `pd (fun y => pd (fun x' => φ x' c) j y) i x
         = fderiv ℝ (fun y => fderiv ℝ φ y) x (Pi.single i 1) (Pi.single j 1) c`.
    Mechanism: the inner `pd (fun x' => φ x' c) j` equals — near `x`, via `pd_component_eq'` — the
    scalar evaluation `Λ (fderiv ℝ φ ·)`, `Λ = projᵨ ∘L (apply eⱼ)`; `pd_congr_nhds` transports the
    outer `pd`, `pd_eq_fderiv` + the CLM chain rule (`Λ.hasFDerivAt.comp`) extract the `eᵢ`-coordinate,
    and the evaluation CLM `simp`-unfolds to the `(eᵢ,eⱼ,c)` contraction.  NOT `a₁ = R/6`. -/
theorem pd_pd_component_eq (φ : Point n → Point n) (c i j : Fin n) (x : Point n)
    (hφ : ∀ᶠ y in nhds x, DifferentiableAt ℝ φ y)
    (hφ2 : DifferentiableAt ℝ (fun y => fderiv ℝ φ y) x) :
    pd (fun y => pd (fun x' => φ x' c) j y) i x
      = fderiv ℝ (fun y => fderiv ℝ φ y) x (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) c := by
  classical
  set Λ : (Point n →L[ℝ] Point n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj c).comp
      (ContinuousLinearMap.apply ℝ (Point n) (Pi.single j (1 : ℝ))) with hΛdef
  -- inner `pd` = `Λ (fderiv φ ·)` on a neighbourhood of `x`.
  have hev : (fun y => pd (fun x' => φ x' c) j y)
      =ᶠ[nhds x] (fun y => Λ (fderiv ℝ φ y)) := by
    filter_upwards [hφ] with y hy
    have hpc := pd_component_eq' φ j c y hy
    simp only [hΛdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.proj_apply]
    exact hpc
  -- differentiate `Λ ∘ (fderiv φ)` at `x` via the CLM chain rule.
  have hcomp : HasFDerivAt (fun y => Λ (fderiv ℝ φ y))
      (Λ.comp (fderiv ℝ (fun y => fderiv ℝ φ y) x)) x :=
    Λ.hasFDerivAt.comp x hφ2.hasFDerivAt
  rw [QIQTH.PullbackMetric.pd_congr_nhds i x hev, pd_eq_fderiv _ i x hcomp.differentiableAt,
    hcomp.fderiv]
  simp only [hΛdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.proj_apply]

/-! ###############################################################################
    ### ★★ (C) THE OPERATOR RESULT, IN COORDINATES — `chartSecondJet` ⇒ `pd`-iterated.
    ############################################################################### -/

/-- **★★ `chartSecondJetComponent_continuousOn_of_reach`.**  The chart operator SECOND jet
    (`Hfwd2Weld.chartSecondJet_continuousOn_of_reach`), pushed through the coordinate gate
    (`pd_pd_component_eq`) into `pd`-iterated form: on `U ⊆ K`, the base-varying, field-centre-`0`,
    `pd`-iterated raw-chart Hessian coordinate
        `z ↦ pd (fun y => pd (fun x' => uniformInverseChart … z x' c) j y) i 0`
    is base-continuous.  Mechanism: `evalCLM T = ((T eᵢ) eⱼ) c` is a continuous linear contraction;
    `evalCLM.continuous.comp_continuousOn (chartSecondJet_continuousOn_of_reach …)` gives the
    continuity of the contracted operator jet, and `.congr` (per-`z` via the gate, with the per-`z`
    chart-centre `C²` `hreg` supplying the gate's differentiability side-conditions) lands the
    `pd`-iterated form.  Carries exactly `chartSecondJet`'s inputs + `hreg`.  NOT `a₁ = R/6`. -/
theorem chartSecondJetComponent_continuousOn_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hid2 : ∀ z ∈ U,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))))
    (hreg : ∀ z ∈ U, ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n))
    (c i j : Fin n) :
    ContinuousOn
      (fun z : Point n =>
        pd (fun y => pd (fun x' => uniformInverseChart g gi hC hK z x' c) j y) i 0) U := by
  classical
  -- the operator second jet, base-continuous (the J4-484 weld, conditional on `hReach`).
  have hOp := chartSecondJet_continuousOn_of_reach g gi hC hK hUK hReach hW0 horigin hunit hid2
  -- the evaluation CLM `T ↦ ((T eᵢ) eⱼ) c`.
  set E2 : (Point n →L[ℝ] (Point n →L[ℝ] Point n)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj c).comp
      ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single j (1 : ℝ))).comp
        (ContinuousLinearMap.apply ℝ (Point n →L[ℝ] Point n) (Pi.single i (1 : ℝ)))) with hE2def
  -- per-`z` gate side-conditions from `hreg`.
  have hev1 : ∀ z ∈ U, ∀ᶠ y in nhds (0 : Point n),
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) y := by
    intro z hz
    filter_upwards [(hreg z hz).eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hev2 : ∀ z ∈ U,
      DifferentiableAt ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0 := by
    intro z hz
    exact ((hreg z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine (E2.continuous.comp_continuousOn hOp).congr (fun z hz => ?_)
  rw [pd_pd_component_eq (uniformInverseChart g gi hC hK z) c i j 0 (hev1 z hz) (hev2 z hz)]
  simp only [hE2def, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply]

end QIQTH.OperatorPdBridge

/-! ## THE BRIDGE LEDGER (post J4-486).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE BRIDGE.  J4-484 delivered the chart Hessian in OPERATOR form                                  │
  │  (`chartSecondJet_continuousOn_of_reach`: `z ↦ fderiv²(W_z) 0` base-continuous on `U`, gated by    │
  │  `hReach`).  This brick supplies the OPERATOR ⇄ `pd`-coordinate dictionary and pushes it through.  │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE COORDINATE GATE.  `pd_pd_component_eq` (pure Mathlib): for `φ` diff. near `x` with `fderiv φ`  │
  │  diff. at `x`,  `pd (pd (φ·c) j) i x = fderiv²φ x (eᵢ)(eⱼ) c`.  The second-order analogue of the    │
  │  first-order `pd_component_eq` (banked as `UngatedChainRule.pd_component_eq`, re-proved here inline  │
  │  as `pd_component_eq'`).  Built from the `PullbackMetric` evaluation-CLM contraction pattern one    │
  │  order lower — NOT a fresh analytic wall.                                                          │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE OPERATOR RESULT, IN COORDINATES.  `chartSecondJetComponent_continuousOn_of_reach`: the        │
  │  base-varying, field-centre-`0`, `pd`-iterated raw-chart Hessian coordinate                        │
  │      `z ↦ pd (fun y => pd (fun x' => uniformInverseChart … z x' c) j y) i 0`                        │
  │  is base-continuous on `U`, carrying EXACTLY `chartSecondJet`'s inputs                             │
  │  (`hReach`/`hW0`/`horigin`/`hunit`/`hid2`) + the per-`z` chart-centre `C²` (`hreg`).               │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TWO CONSUMERS — the HONEST routing (⚠ NOT the naive "both served by the one wall").

  ── CONSUMER `hcont2` (BaseSlotAmpDeriv / SupFamilyFirstOrder's `C₂` spec).  Its base structure MATCHES
  `chartSecondJet` (base `z = p.2` VARYING, field centre `0`).  BUT `hcont2` is the second field-partial
  of the AMPLITUDE
        `pd (fun y => pd (chartAmp … p.1 p.2 ·) i y) i 0`,  `chartAmp … τ z = manifoldAmp … τ ∘ W_z`,
  whose 2nd-order chain rule (`PullbackNaturalityLocal.pd_pd_comp_local`) expands into
        `∑ₐ (∑ᵦ pd²(manifoldAmp)·pd(W_z·b))·pd(W_z·a)  +  ∑ₐ pd(manifoldAmp)·pd²(W_z·a)`,
  so `hcont2` needs FOUR jointly-continuous blocks:
      (1) `pd²(manifoldAmp)∘W_z 0` — the manifold-amplitude SECOND-derivative joint continuity (the
          2nd-order analogue of `SupFamilyFirstOrder.manifoldAmp_fderiv_continuous`) — NOT built;
      (2) `pd(manifoldAmp)∘W_z 0` — banked (`manifoldAmp_fderiv_continuous`);
      (3) `pd(W_z·b) 0` — chart FIRST jet coordinate, base-varying (banked
          `chartFieldJacobian_continuousOn` + `pd_component_eq'`);
      (4) `pd²(W_z·a) 0` — the chart SECOND jet coordinate, base-varying — ★ DELIVERED HERE by
          `chartSecondJetComponent_continuousOn_of_reach`.
  ⇒ `hcont2` OUTCOME: the raw-chart SECOND-jet block (4) — the ONLY block that rode on a genuine
  second-variation analytic wall — now rests on the ONE (I1) `hReach` input via `chartSecondJet`, in the
  exact `pd`-iterated dialect.  The residue (1)+(3)+the `pd_pd_comp_local` assembly is pure-Mathlib /
  banked chain-rule bookkeeping, NOT an analytic wall — the J4-487 amplitude-chain-rule brick.

  ── CONSUMER `hWc2cont` (SmoothCarrierGrounding `hComposite2_grounded`).  ⚠ DONT-UNDERCREDIT / the naive
  "convergent wall" framing is IMPRECISE here.  `hWc2cont` is
        `pd (fun y => pd (fun z => uniformInverseChart … 0 z a') j y) i p.2`  over field points `p.2`,
  i.e. the field-Hessian of the SINGLE base-`0` chart `W₀`, at a VARYING FIELD point — base FIXED at `0`.
  `chartSecondJet` is the ORTHOGONAL object: base VARYING, field pinned to `0`.  So `hWc2cont` is NOT an
  instance of the convergent wall and is NOT served by `chartSecondJet`.  It is ALREADY DISCHARGED,
  UNCONDITIONALLY, by the banked single-chart route `ChartJetFactsDischarge.hWc2cont_of_contDiffOn_ball`
  (its `pd_pd_continuousOn_open` from `ContDiffOn ℝ 2 W₀ (ball 0 ρc)`) — and is in fact ALREADY wired
  into `heatOpGatedWitness_jointContinuousOn_chartFree`.  It needs neither (I1) nor this bridge.

  ── NET.  Of the two consumers: `hWc2cont` was ALREADY served (banked, unconditional, distinct object);
  `hcont2`'s sole genuine second-variation block is now served (this bridge + J4-484 + (I1)).  The
  "single convergent wall" is really the `hcont2` raw-chart SECOND-jet block ALONE; `hWc2cont` was a
  false twin (a single-chart field-Hessian, not a base-varying jet).

  ── DONT-UNDERCREDIT findings.
    * `hWc2cont` is ALREADY discharged unconditionally (`ChartJetFactsDischarge.hWc2cont_of_contDiffOn_
      ball`, wired into `heatOpGatedWitness_jointContinuousOn_chartFree`); it is a SINGLE-CHART
      field-Hessian, NOT the base-varying operator jet — the ChartSecondJet ledger's "both bottom out on
      the same object" overstated the convergence for `hWc2cont`.
    * The coordinate gate is NOT a new wall: `PullbackMetric` already carries the exact evaluation-CLM
      contraction pattern (`proj ∘L (apply eⱼ) ∘L (apply eᵢ)`) one order higher; `pd_pd_component_eq` is
      that pattern one order lower.  `pd_component_eq` (first order) was banked in `UngatedChainRule`.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1) `hReach`, the J4-487 amplitude chain rule +
  `manifoldAmp` second-derivative continuity, the banked convergence trio, and the geometric wiring).
-/

section AxiomChecks
open QIQTH.OperatorPdBridge
#print axioms pd_component_eq'
#print axioms pd_pd_component_eq
#print axioms chartSecondJetComponent_continuousOn_of_reach
end AxiomChecks
