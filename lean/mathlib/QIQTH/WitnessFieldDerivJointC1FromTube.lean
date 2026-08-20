/-
  WitnessFieldDerivJointC1FromTube — J4-887: the CLIMB-ONE-DERIVATIVE-UP bridge from J4-884's
  abstract-`K` joint `C²` regularity of `uniformInverseChart` near the diagonal to the JOINT `C¹`
  regularity of the FIELD-derivative kernel `witnessFieldDeriv` — the object `hbint`
  (`FieldHessianJointContinuityClosed.hbint_concrete_reduced_to_jointC1`, J4-878) reduced to.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.

  This brick supplies the missing analytic ENGINE the J4-443 C⁰ joint-continuity result
  (`UngatedChainRule.witnessFieldDeriv_jointContinuousOn`) needed to climb ONE derivative up:
  the general "partial-Fréchet-derivative of a jointly `C²` map is jointly `C¹`" operator, and its
  instantiation at the concrete chart field-jet.  From these it derives — on ANY open set `U` on
  which the JOINT chart `(z,y) ↦ uniformInverseChart g gi hC hK z y` is jointly `ContDiffOn ℝ 2` —
  that the on-gate value of the field-derivative kernel (the gate-chain SMOOTH FORM
  `∑ c, ∂prof_c(chart z y)·∂ᵢ(chart z ·)_c(y)`) is jointly `ContDiffOn ℝ 1`.  Combined with
  `UniformFlowCoherentChartReconciliationGeneralK.uniformInverseChart_jointContDiffOn_tube` (J4-884),
  this delivers the field-derivative kernel's joint `C¹` regularity CONCRETELY on an open TUBE around
  the interior diagonal, for the abstract compact `K` the capstone quantifies over.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE DOES **NOT** DO (the honest limit — it does NOT fully discharge `hbint`).

  `hbint_concrete_reduced_to_jointC1` (J4-878) needs joint `C¹` of the field-derivative kernel on an
  OPEN `U ⊇ K ×ˢ concreteKx` — a neighbourhood of the WHOLE base×reach product, which contains
  OFF-diagonal, OFF-gate points.  This file supplies the regularity on the interior-diagonal TUBE and
  the general engine that turns "joint `C²` chart + gate transparency" into "joint `C¹` witness."  It
  does NOT close the residual gap, which comprises exactly:
    (a) the b-support of the witness (radius `b` flow-tube around the diagonal) sitting inside the
        UNQUANTIFIED J4-884 tube — the tube's size vs `b` is not controlled;
    (b) OFF-gate vanishing on a joint NEIGHBOURHOOD (the hard set-indicator gate
        `if q ∈ K then if p ∈ S q` of `gatedKernel` needs the complement of the gate to be jointly
        open around each off-gate base×point);
    (c) MATCHED-CUTOFF gluing across the gate boundary `∂(S z)` (the smooth `radialCutoff a b` must
        already vanish there since `b < c`), needed to certify joint `C¹` across the hard indicator.
  These three constitute the honest remaining content of `hbint`; this brick does NOT manufacture
  them.  `hbint` is NOT closed here.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UngatedChainRule
import QIQTH.UniformFlowCoherentChartReconciliationGeneralK

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation QIQTH.WitnessMeasDeriv
open QIQTH.InnerDataEnvelope QIQTH.WitnessDerivDomination QIQTH.ResidueBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialDistance
open QIQTH.ExpMap QIQTH.HeatParametrixAnsatz QIQTH.ChartComposedHeatOp
open QIQTH.JacobiCLMExposure QIQTH.ChartGeneralPContinuity QIQTH.GeneralFieldContinuity
open QIQTH.UngatedChainRule
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.WitnessFieldDerivJointC1FromTube

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the general analytic engine (provider-independent, reusable) — one order up.
    ############################################################################### -/

/-- **★ `partialFDeriv_jointContDiffOn` — the partial-Fréchet-derivative-of-jointly-`C²` engine.**
    The `C¹` analogue (one derivative up) of the banked C⁰ engine
    `FieldHessianJointContinuityClosed.partialFDeriv_norm_jointContinuousOn`.  For ANY
    `Ψ : E × F → G` that is `ContDiffOn ℝ 2` on an OPEN set `U ⊆ E × F`, the PARTIAL-in-`y`
    Fréchet-derivative map
        `(z,y) ↦ fderiv ℝ (fun y' => Ψ (z, y')) y`
    is itself `ContDiffOn ℝ 1` on `U` (valued in `F →L[ℝ] G`).

    Mechanism.  `ContDiffOn.fderiv_of_isOpen` (with `1 + 1 ≤ 2`) gives the JOINT first derivative
    `fderiv ℝ Ψ` `ContDiffOn ℝ 1 U`.  Post-composition with the FIXED `inr : F →L E × F` is a
    bounded bilinear operation, so `ContDiffOn.clm_comp` against a constant keeps it `ContDiffOn ℝ 1`;
    the chain rule through the affine section `y' ↦ (z, y')` (derivative `inr`,
    `hasFDerivAt_prodMk_right`) identifies the partial-in-`y` derivative with that composite, and
    `ContDiffOn.congr` transports.  NOT `a₁ = R/6`. -/
theorem partialFDeriv_jointContDiffOn
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set (E × F)} (hU : IsOpen U)
    (Ψ : E × F → G) (hΨ : ContDiffOn ℝ 2 Ψ U) :
    ContDiffOn ℝ 1 (fun p : E × F => fderiv ℝ (fun y => Ψ (p.1, y)) p.2) U := by
  -- The JOINT first derivative is `ContDiffOn ℝ 1` on the open `U`.
  have hfd : ContDiffOn ℝ 1 (fun p : E × F => fderiv ℝ Ψ p) U :=
    hΨ.fderiv_of_isOpen hU (by norm_num)
  -- Post-compose with the fixed `inr`.
  have hcomp : ContDiffOn ℝ 1
      (fun p : E × F => (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) U :=
    hfd.clm_comp contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  have hdiff : DifferentiableAt ℝ Ψ p :=
    (hΨ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hchain : HasFDerivAt (fun y : F => Ψ (p.1, y))
      ((fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) p.2 :=
    (hdiff.hasFDerivAt).comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
  exact hchain.fderiv

/-! ###############################################################################
    ### C1 — the concrete chart field-jet, jointly `C¹` from joint `C²` of the chart.
    ############################################################################### -/

/-- **★★ `chartFieldJacobianComponent_jointContDiffOn` — the component bridge, one order up.**
    The `C¹` analogue of `UngatedChainRule.chartFieldJacobianComponent_jointContinuousOn` (J4-443).
    From a JOINT `ContDiffOn ℝ 2` datum of the joint chart `(z,y) ↦ uniformInverseChart g gi hC hK z y`
    on an OPEN `U`, the SCALAR chart field-jet
        `(z,y) ↦ pd (fun x'' => uniformInverseChart g gi hC hK z x'' c) i y`
    is jointly `ContDiffOn ℝ 1` on `U`.  Instantiates `partialFDeriv_jointContDiffOn` at the
    vector-valued chart, evaluates the resulting CLM at `Pi.single i 1` (`ContDiffOn.clm_apply`),
    extracts component `c` (post-compose the coordinate projection `ContinuousLinearMap.proj c`), and
    `congr`s onto the coordinate `pd` via `pd_component_eq`.  NOT `a₁ = R/6`. -/
theorem chartFieldJacobianComponent_jointContDiffOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i c : Fin n)
    {U : Set (Point n × Point n)} (hU : IsOpen U)
    (hchartC2 : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) U) :
    ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        pd (fun x'' : Point n => uniformInverseChart g gi hC hK p.1 x'' c) i p.2) U := by
  -- (1) partial-in-`y` fderiv of the joint chart, jointly `C¹`.
  have hjac : ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        fderiv ℝ (fun y => uniformInverseChart g gi hC hK p.1 y) p.2) U :=
    partialFDeriv_jointContDiffOn hU
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) hchartC2
  -- (2) evaluate at `Pi.single i 1`, extract component `c`.
  have happ : ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        (fderiv ℝ (fun y => uniformInverseChart g gi hC hK p.1 y) p.2)
          (Pi.single i (1 : ℝ)) c) U := by
    have h1 : ContDiffOn ℝ 1
        (fun p : Point n × Point n =>
          (fderiv ℝ (fun y => uniformInverseChart g gi hC hK p.1 y) p.2)
            (Pi.single i (1 : ℝ))) U :=
      hjac.clm_apply contDiffOn_const
    have h2 := ((ContinuousLinearMap.proj c : Point n →L[ℝ] ℝ).contDiff).comp_contDiffOn h1
    simpa [Function.comp, ContinuousLinearMap.proj_apply] using h2
  -- (3) `congr` onto the coordinate `pd`.
  refine happ.congr (fun p hp => ?_)
  have hjointdiff : DifferentiableAt ℝ
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) p :=
    (hchartC2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hsec : HasFDerivAt (fun y : Point n => ((p.1, y) : Point n × Point n))
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hslicediff : DifferentiableAt ℝ
      (fun y => uniformInverseChart g gi hC hK p.1 y) p.2 := by
    have h := (hjointdiff.hasFDerivAt).comp p.2 hsec
    simpa [Function.comp] using h.differentiableAt
  exact pd_component_eq (fun y => uniformInverseChart g gi hC hK p.1 y) i c p.2 hslicediff

/-! ###############################################################################
    ### C2 — the gate-chain SMOOTH FORM (= on-gate `witnessFieldDeriv`), jointly `C¹`.
    ############################################################################### -/

/-- **★★★ `witnessFieldDeriv_smoothForm_jointContDiffOn` — the on-gate witness field-derivative,
    jointly `C¹` from joint `C²` of the chart.**  On ANY open `U` where the joint chart is
    `ContDiffOn ℝ 2`, the gate-chain SMOOTH FORM
        `(z,y) ↦ ∑ c, ∂prof_c(chart z y) · pd (fun x'' => chart z x'' c) i y`
    — the value of `witnessFieldDeriv g gi hC hK S a b i τ y z` at every IN-GATE point, per
    `UngatedChainRule.witnessFieldDeriv_gateChain_eq` — is jointly `ContDiffOn ℝ 1` on `U`.
    (`prof w' = radialCutoff a b w' · heatParametrix 1 (vanVleck g) (transportCoeff …) τ w'`, `C^∞`.)
    Factor A = `pd prof c ∘ (joint chart)` (C^∞ profile ∘ joint `C²` chart); Factor B = the chart
    field-jet (`chartFieldJacobianComponent_jointContDiffOn`); `.mul` + `ContDiffOn.sum`.
    `hw` = folded-coefficient smoothness (⇒ `prof` is `C^∞`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_smoothForm_jointContDiffOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    {U : Set (Point n × Point n)} (hU : IsOpen U)
    (hchartC2 : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) U) :
    ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        ∑ c, pd (fun w' : Point n =>
                radialCutoff a b w'
                  * heatParametrix 1 (vanVleck g)
                      (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
              (uniformInverseChart g gi hC hK p.1 p.2)
            * pd (fun x'' : Point n => uniformInverseChart g gi hC hK p.1 x'' c) i p.2) U := by
  -- the `C^∞` profile `prof`.
  have hProfCD : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun w' : Point n => radialCutoff a b w'
        * heatParametrix 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) τ w') :=
    (radialCutoff_contDiff a b).mul
      (heatParametrix_contDiff_space 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) τ hw)
  have hchart1 : ContDiffOn ℝ 1
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) U :=
    hchartC2.of_le (by norm_num)
  refine ContDiffOn.sum (fun c _ => ?_)
  -- Factor A: `pd prof c ∘ (joint chart)`.
  have hFA : ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        pd (fun w' : Point n =>
              radialCutoff a b w'
                * heatParametrix 1 (vanVleck g)
                    (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
          (uniformInverseChart g gi hC hK p.1 p.2)) U := by
    have hpd1 : ContDiff ℝ (1 : WithTop ℕ∞)
        (fun w' : Point n => pd (fun w'' : Point n =>
            radialCutoff a b w''
              * heatParametrix 1 (vanVleck g)
                  (transportCoeff (transportOp (vanVleck g) g gi)) τ w'') c w') :=
      (contDiff_pd_inf _ hProfCD c).of_le (by exact_mod_cast le_top)
    have h := hpd1.comp_contDiffOn hchart1
    simpa [Function.comp] using h
  -- Factor B: the chart field-jet.
  have hFB : ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        pd (fun x'' : Point n => uniformInverseChart g gi hC hK p.1 x'' c) i p.2) U :=
    chartFieldJacobianComponent_jointContDiffOn g gi hC hK i c hU hchartC2
  exact hFA.mul hFB

/-! ###############################################################################
    ### C3 — the ON-GATE joint `C¹` of the field-derivative kernel (the honest reduction).
    ############################################################################### -/

/-- **★ `witnessFieldDeriv_jointContDiffOn_onGate` — the field-derivative kernel is jointly `C¹` on any
    open IN-GATE set carrying joint `C²` of the chart.**  The one-derivative-up analogue of the J4-443
    C⁰ `witnessFieldDeriv_jointContinuousOn`.  On an OPEN `V` where (i) the joint chart is
    `ContDiffOn ℝ 2` and (ii) EVERY point is in-gate (`p.1 ∈ K` and the field gate `S p.1` is a
    NEIGHBOURHOOD of the field point `p.2`), the field-derivative kernel `(z,y) ↦ witnessFieldDeriv …
    y z` is jointly `ContDiffOn ℝ 1` on `V`: it equals the gate-chain SMOOTH FORM there
    (`witnessFieldDeriv_gateChain_eq`), which is jointly `C¹`
    (`witnessFieldDeriv_smoothForm_jointContDiffOn`).

    ⚠ HONEST NOTE.  This is a CONDITIONAL reduction, NOT a discharge of `hbint`.  `hbint`
    (`hbint_concrete_reduced_to_jointC1`, J4-878) needs the joint `C¹` on an open `U ⊇ K ×ˢ concreteKx`
    — a set with OFF-gate points where hypothesis (ii) FAILS (the witness is `0` there, not the smooth
    form, so the gate-chain identity does not hold).  This lemma's antecedent is SATISFIABLE (on a
    genuine open in-gate region inside the tube), non-vacuous, and never the conclusion; but it does
    NOT cover `K ×ˢ concreteKx`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_jointContDiffOn_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    {V : Set (Point n × Point n)} (hV : IsOpen V)
    (hchartC2 : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) V)
    (hgate : ∀ p ∈ V, p.1 ∈ K ∧ S p.1 ∈ nhds p.2) :
    ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) V := by
  have hsmooth := witnessFieldDeriv_smoothForm_jointContDiffOn g gi hC hK a b i τ hw hV hchartC2
  refine hsmooth.congr (fun p hp => ?_)
  obtain ⟨hzK, hgt⟩ := hgate p hp
  have hjointdiff : DifferentiableAt ℝ
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) p :=
    (hchartC2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hsec : HasFDerivAt (fun y : Point n => ((p.1, y) : Point n × Point n))
      (ContinuousLinearMap.inr ℝ (Point n) (Point n)) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hWdiff : DifferentiableAt ℝ (uniformInverseChart g gi hC hK p.1) p.2 := by
    have h := (hjointdiff.hasFDerivAt).comp p.2 hsec
    simpa [Function.comp] using h.differentiableAt
  exact witnessFieldDeriv_gateChain_eq g gi hC hK S a b i τ p.2 p.1 hw hzK hgt hWdiff

/-! ###############################################################################
    ### C4 — the CONCRETE TUBE CAPSTONE (non-vacuous): the on-gate witness field-derivative
    ###      is jointly `C¹` on an open tube around the interior diagonal, for the abstract `K`.
    ############################################################################### -/

/-- **★★ `witnessFieldDeriv_smoothForm_jointContDiffOn_tube` — CONCRETE, NON-VACUOUS realization.**
    For the ARBITRARY compact `K` the capstone quantifies over, there is an OPEN set `T` containing the
    WHOLE interior diagonal `{(z,z) : z ∈ interior K}` on which the on-gate field-derivative kernel
    (the gate-chain SMOOTH FORM) is jointly `ContDiffOn ℝ 1`.  Feeds
    `UniformFlowCoherentChartReconciliationGeneralK.uniformInverseChart_jointContDiffOn_tube` (J4-884,
    joint `C²` of the chart on the tube) into `witnessFieldDeriv_smoothForm_jointContDiffOn`.  This is
    the genuine regularity object the field-derivative kernel inherits from the chart's abstract-`K`
    second-order joint regularity — the concrete, unconditional (given `hw`) `C¹`-analogue of J4-884.
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_smoothForm_jointContDiffOn_tube (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ T : Set (Point n × Point n), IsOpen T ∧
      (∀ z ∈ interior K, ((z, z) : Point n × Point n) ∈ T) ∧
      ContDiffOn ℝ 1
        (fun p : Point n × Point n =>
          ∑ c, pd (fun w' : Point n =>
                  radialCutoff a b w'
                    * heatParametrix 1 (vanVleck g)
                        (transportCoeff (transportOp (vanVleck g) g gi)) τ w') c
                (uniformInverseChart g gi hC hK p.1 p.2)
              * pd (fun x'' : Point n => uniformInverseChart g gi hC hK p.1 x'' c) i p.2) T := by
  obtain ⟨T, hTopen, hTdiag, hTcd⟩ := uniformInverseChart_jointContDiffOn_tube g gi hC hK
  exact ⟨T, hTopen, hTdiag,
    witnessFieldDeriv_smoothForm_jointContDiffOn g gi hC hK a b i τ hw hTopen hTcd⟩

/-! ###############################################################################
    ### C5 — NON-VACUITY of the abstract engine (independent of the concrete chart).
    ############################################################################### -/

/-- **NON-VACUITY.**  The abstract engine `partialFDeriv_jointContDiffOn` fires on a genuine
    non-degenerate input: a `ContDiffOn ℝ 2` bilinear-shaped map `Ψ (z,y) = y` (the second
    projection, jointly `C^∞`) on `univ` yields the (constant) partial-Fréchet derivative
    `fun _ => ContinuousLinearMap.id ℝ F`, jointly `ContDiffOn ℝ 1`.  So the engine's antecedent is
    inhabited by a real (non-`0`) map and the conclusion holds — no unsatisfiable antecedent, never the
    conclusion in disguise.  NOT `a₁ = R/6`. -/
theorem partialFDeriv_engine_nonvacuous
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ContDiffOn ℝ 1
      (fun p : E × F => fderiv ℝ (fun y => (Prod.snd : E × F → F) (p.1, y)) p.2)
      (Set.univ : Set (E × F)) :=
  partialFDeriv_jointContDiffOn isOpen_univ (fun q : E × F => q.2)
    (contDiff_snd.contDiffOn)

end QIQTH.WitnessFieldDerivJointC1FromTube

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.WitnessFieldDerivJointC1FromTube
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms partialFDeriv_jointContDiffOn
#print axioms chartFieldJacobianComponent_jointContDiffOn
#print axioms witnessFieldDeriv_smoothForm_jointContDiffOn
#print axioms witnessFieldDeriv_jointContDiffOn_onGate
#print axioms witnessFieldDeriv_smoothForm_jointContDiffOn_tube
#print axioms partialFDeriv_engine_nonvacuous
end AxiomChecks
