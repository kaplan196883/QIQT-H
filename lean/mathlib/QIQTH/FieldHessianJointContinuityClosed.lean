/-
  FieldHessianJointContinuityClosed — J4-878: the JOINT `(z,x)`-continuity residual of `hbint`
  (J4-877) REDUCED to a clean JOINT `C¹` regularity carry of the field-derivative kernel — the
  "climb one derivative up" analytic step, DISCHARGED to the SAME single named geometric wall
  (`JointRNCRegularityInterface.JointSecondOrderRNCRegularity`: the geodesic normal-coordinate inverse
  chart is jointly `C²` near the diagonal), rather than a NEW open object.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the JOINT `(z,x)`-
  continuity residual of `hbint` (the sole genuine content J4-877 left, per its own audit) to a JOINT
  `ContDiffOn ℝ 1` carry of the joint field-derivative kernel `(z,y) ↦ witnessFieldDeriv … y z` — a
  standard, satisfiable joint-regularity input, EQUAL to the campaign's already-named single irreducible
  wall (joint `C²` of `uniformInverseChart` near the diagonal).  It does **NOT** close `hbint`.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the partial-fderiv-of-joint-`C¹` engine, and its concrete wiring into `hbint`.

  J4-877 reduced `hbint` to the SOLE residual: JOINT `(z,x)`-continuity of the field-Hessian norm
  `(z,x) ↦ ‖fderiv ℝ (fun y => witnessFieldDeriv … y z) x‖` on `K ×ˢ concreteKx`.  Its own audit found
  the nearest banked joint result (`UngatedChainRule.witnessFieldDeriv_jointContinuousOn`, J4-443) is
  the FIRST field-derivative on a 1-D slice — one derivative BELOW.  This brick supplies the missing
  "one derivative up" analytic step as a SHARP, general, Mathlib-only engine, and traces the honest
  residual to the campaign's already-named geometric frontier.

    1. `partialFDeriv_norm_jointContinuousOn` — ★ THE ENGINE (provider-independent).  For ANY
       `Ψ : E × F → H` that is `ContDiffOn ℝ 1` on an OPEN `U ⊆ E × F`, the partial-in-`y` Fréchet-
       derivative norm `(z,y) ↦ ‖fderiv ℝ (fun y' => Ψ (z, y')) y‖` is `ContinuousOn U`.  Mechanism:
       `ContDiffOn.continuousOn_fderiv_of_isOpen` gives the joint `fderiv ℝ Ψ` `ContinuousOn U`; the
       partial-in-`y` derivative equals `(fderiv ℝ Ψ (z,y)).comp (inr)` (chain rule through the affine
       section `y' ↦ (z, y')`, whose derivative is `ContinuousLinearMap.inr`); `ContinuousOn.clm_comp`
       (post-composition with the fixed `inr`) + `ContinuousOn.congr` + `ContinuousOn.norm`.  NO joint
       `C²` demanded — joint `C¹` of the FIRST-order kernel `Ψ` (⇔ joint `C²` of the witness) suffices.
    2. `fieldHessian_norm_jointContinuousOn_of_jointC1` — ★★ instantiation at the concrete joint field-
       derivative kernel `Ψ (z,y) := witnessFieldDeriv … y z`: from an OPEN `U ⊇ K ×ˢ concreteKx` on
       which `Ψ` is jointly `ContDiffOn ℝ 1`, the field-Hessian norm is `ContinuousOn (K ×ˢ concreteKx)`
       — EXACTLY the residual `hbint_concrete_of_jointContinuousOn` (J4-877) consumes.
    3. `hbint_concrete_reduced_to_jointC1` — ★★★ THE `hbint` FIELD, REDUCED a.e. to the joint-`C¹` carry
       (plus the standard `BL`-continuity).  Chains (2) through
       `FieldHessianJointContinuity.hbint_concrete_of_jointContinuousOn`.  So the Berge/supremum + the
       support-localization + the "climb one derivative up" scaffolding of `hbint` is ALL discharged; the
       honest remaining content is the JOINT `ContDiffOn ℝ 1` carry — the same joint-`C²`-chart frontier.

  So the entire `hbint` chain is now `hbint ⟸ {BL-continuity, joint `C¹` of the field-derivative kernel}`,
  and the joint-`C¹` carry is EXACTLY the standard "the geodesic normal-coordinate inverse chart is
  jointly `C²` near the diagonal" — the single irreducible wall the campaign (J4-681→791) repeatedly
  identified (`JointRNCRegularityInterface.JointSecondOrderRNCRegularity`).  hbint is NOT a NEW wall.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FieldHessianJointContinuity
import QIQTH.ChartJetXUniformBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open scoped Topology BigOperators

namespace QIQTH.FieldHessianJointContinuityClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the general analytic engine (provider-independent, reusable).
    ############################################################################### -/

/-- **★ `partialFDeriv_norm_jointContinuousOn` — the partial-fderiv-of-joint-`C¹` engine.**  For ANY
    `Ψ : E × F → H` that is `ContDiffOn ℝ 1` on an OPEN set `U ⊆ E × F`, the map
        `(z,y) ↦ ‖fderiv ℝ (fun y' => Ψ (z, y')) y‖`
    (the norm of the PARTIAL Fréchet derivative in the second slot) is `ContinuousOn U`.

    Mechanism.  `ContDiffOn.continuousOn_fderiv_of_isOpen` gives `ContinuousOn (fun p => fderiv ℝ Ψ p) U`
    (the JOINT first derivative is continuous, `Ψ` being `C¹` on the open `U`).  At each `p ∈ U`, `Ψ` is
    differentiable, and the affine section `y' ↦ (p.1, y')` has Fréchet derivative
    `ContinuousLinearMap.inr ℝ E F` (`hasFDerivAt_prodMk_right`), so the chain rule gives
        `fderiv ℝ (fun y' => Ψ (p.1, y')) p.2 = (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)`.
    Post-composition with the FIXED `inr` is continuous (`ContinuousOn.clm_comp` against a constant), so
    the composed form is `ContinuousOn U`; `ContinuousOn.congr` transports the pointwise identity, and
    `ContinuousOn.norm` finishes.  NO joint `C²` demanded.  NOT `a₁ = R/6`. -/
theorem partialFDeriv_norm_jointContinuousOn
    {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set (E × F)} (hU : IsOpen U)
    (Ψ : E × F → H) (hΨ : ContDiffOn ℝ 1 Ψ U) :
    ContinuousOn (fun p : E × F => ‖fderiv ℝ (fun y => Ψ (p.1, y)) p.2‖) U := by
  -- The JOINT first derivative is continuous on the open `U`.
  have hfd : ContinuousOn (fun p : E × F => fderiv ℝ Ψ p) U :=
    hΨ.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Post-compose with the fixed `inr` — continuous.
  have hcomp : ContinuousOn
      (fun p : E × F => (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) U :=
    hfd.clm_comp continuousOn_const
  -- The partial-in-`y` derivative equals that composite (chain rule through the affine section).
  have hcongr : ContinuousOn
      (fun p : E × F => fderiv ℝ (fun y => Ψ (p.1, y)) p.2) U := by
    refine hcomp.congr (fun p hp => ?_)
    have hdiff : DifferentiableAt ℝ Ψ p :=
      (hΨ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
    have hchain : HasFDerivAt (fun y : F => Ψ (p.1, y))
        ((fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) p.2 :=
      (hdiff.hasFDerivAt).comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
    exact hchain.fderiv
  exact hcongr.norm

/-! ###############################################################################
    ### C1 — the concrete field-Hessian norm joint continuity from the joint `C¹` carry.
    ############################################################################### -/

/-- **★★ `fieldHessian_norm_jointContinuousOn_of_jointC1`.**  The EXACT joint `(z,x)`-continuity
    residual `hbint_concrete_of_jointContinuousOn` (J4-877) consumes — `ContinuousOn (fun p =>
    ‖fderiv ℝ (fun y => witnessFieldDeriv … y p.1) p.2‖) (K ×ˢ concreteKx)` — produced from a JOINT
    `ContDiffOn ℝ 1` carry of the joint field-derivative kernel `Ψ (z,y) := witnessFieldDeriv … y z` on
    an OPEN neighbourhood `U ⊇ K ×ˢ concreteKx`.  Instantiates the general engine
    `partialFDeriv_norm_jointContinuousOn` and restricts to the compact product with `.mono`.

    The carry — joint `C¹` of the first field-derivative kernel — is exactly joint `C²` of the witness
    (gate transparency: the witness factors as `prof ∘ chart`, `prof` `C^∞`), i.e. the standard
    "geodesic normal-coordinate inverse chart is jointly `C²` near the diagonal," the campaign's single
    named irreducible wall (`JointRNCRegularityInterface`).  NOT `a₁ = R/6`. -/
theorem fieldHessian_norm_jointContinuousOn_of_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)}
    {U : Set (Point n × Point n)} (hU : IsOpen U) (hsub : K ×ˢ Kx ⊆ U)
    (hjointC1 : ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) U) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
      (K ×ˢ Kx) :=
  (partialFDeriv_norm_jointContinuousOn hU
    (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1)
    hjointC1).mono hsub

/-! ###############################################################################
    ### C2 — the `hbint` field, REDUCED a.e. to the joint `C¹` carry (+ `BL`-continuity).
    ############################################################################### -/

/-- **★★★ J4-878 — `hbint_concrete_reduced_to_jointC1`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, REDUCED a.e. to: the standard
    `BL`-continuity on `K`; and a JOINT `ContDiffOn ℝ 1` carry of the joint field-derivative kernel
    `(z,y) ↦ witnessFieldDeriv … y z` on an OPEN `U ⊇ K ×ˢ concreteKx` (per a.e. `s`).  Chains
    `fieldHessian_norm_jointContinuousOn_of_jointC1` (this file) through
    `FieldHessianJointContinuity.hbint_concrete_of_jointContinuousOn` (J4-877).

    So the entire `hbint` chain is now `hbint ⟸ {BL-continuity, joint `C¹` of the field-derivative
    kernel}`; the "climb one derivative up" JOINT-continuity scaffolding of J4-877 is DISCHARGED, and the
    honest residual is the joint-`C¹` carry = joint-`C²`-chart frontier (the single named wall).  `K`
    nonempty; radii `0 < a < b < c < δ₀`, `b < uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem hbint_concrete_reduced_to_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ U : Set (Point n × Point n), IsOpen U ∧ K ×ˢ concreteKx g gi hC hK b ⊆ U ∧
              ContDiffOn ℝ 1
                (fun p : Point n × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (t - s) p.2 p.1) U) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨δ₀, hδ₀, hcore⟩ :=
    hbint_concrete_of_jointContinuousOn g gi hC hK hKne a b ha hab hbρ i t m BL
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hBL hcarry
  refine hcore c hbc hcδ S hSeq hBL ?_
  filter_upwards [hcarry] with s hs hsU
  obtain ⟨U, hU, hsub, hcd⟩ := hs hsU
  exact fieldHessian_norm_jointContinuousOn_of_jointC1 g gi hC hK S a b i (t - s) hU hsub hcd

/-! ###############################################################################
    ### C3 — NON-VACUITY of the joint `C¹` carry.
    ############################################################################### -/

/-- **NON-VACUITY.**  The joint `C¹` carry is inhabited at the empty gate `S := fun _ => ∅` with the
    OPEN neighbourhood `U := univ`: there `closure (S z) = ∅`, so every field point is off the gate and
    `witnessFieldDeriv … y z = 0` (`witnessFieldDeriv_eqZero_of_notMem_closure`); the joint kernel is
    thus the constant `0`, which is `ContDiffOn ℝ 1` on `univ`.  So the reduction fires — no unsatisfiable
    antecedent (no J4-548/847 trap), never the conclusion.  (The genuinely non-trivial carry — joint `C¹`
    of the CONCRETE non-empty-gate kernel = joint `C²` of the chart — is the honest frontier that
    remains.)  NOT `a₁ = R/6`. -/
theorem jointC1_carry_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ) :
    ContDiffOn ℝ 1
      (fun p : Point n × Point n =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.2 p.1)
      (Set.univ : Set (Point n × Point n)) := by
  have hzero : (fun p : Point n × Point n =>
      witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.2 p.1)
      = fun _ => (0 : ℝ) := by
    funext p
    exact QIQTH.ChartJetXUniformBound.witnessFieldDeriv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.1 p.2 (by simp)
  rw [hzero]
  exact contDiffOn_const

end QIQTH.FieldHessianJointContinuityClosed

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.FieldHessianJointContinuityClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms partialFDeriv_norm_jointContinuousOn
#print axioms fieldHessian_norm_jointContinuousOn_of_jointC1
#print axioms hbint_concrete_reduced_to_jointC1
#print axioms jointC1_carry_nonvacuous
end AxiomChecks
