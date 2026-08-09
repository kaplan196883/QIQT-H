/-
  ChartSecondJet — J4-479: the SECOND field-jet of the uniform inverse chart — THE CONVERGENT WALL.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  (possibly the first of several) brick of the convergence-trio campaign.  No `sorry` (header prose
  excepted), no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no result that is a
  conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ── THE OBJECT (the convergent wall).  BOTH consumer chains bottom out on the SAME geometric analytic
  object: the SECOND field-jet of the `.choose`-built uniform inverse chart
        `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0`
  — the chart HESSIAN at the field centre `0`, as the base `z` varies.
    • the a₁=R/6 htermBox chain (`SmoothCarrierGrounding.hComposite2_grounded`) needs `hWc2cont`
      (the `pd (fun y => pd (W₀·a') j y) i` chart-Hessian joint continuity);
    • the C₂/hcont2 derivative-sup chain (`BaseSlotAmpDeriv.baseSlotAmpDeriv2_sup_onCollar`) needs
      the second field-derivative field's joint continuity.
  Both are the SECOND-order analogue of the FIRST-order object `z ↦ fderiv ℝ (uniformInverseChart … z) 0`
  that the J4-433/435 chain (`ChartFieldJacobian` / `JacobiCLMExposure`) already banked UNCONDITIONALLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PLAN.

  ### (i) THE 2nd-ORDER IFT ALGEBRA (this file, DERIVED — the star).  The first-order chain banks
  `fderiv_localLeftInverse_eq_ringInverse`: for a left-inverse germ `W (φ v) = v` with invertible
  forward derivative, `fderiv ℝ W (φ v₀) = Ring.inverse (fderiv ℝ φ v₀)`.  DIFFERENTIATE this.  The
  pointwise identity holds in a NEIGHBOURHOOD (the germ level):
        `∀ᶠ y in 𝓝 (φ v₀), fderiv ℝ W y = Ring.inverse (fderiv ℝ φ (W y))`,
  so the operator-valued first-jet map `y ↦ fderiv ℝ W y` agrees near `φ v₀` with the composite
        `Ring.inverse ∘ (fderiv ℝ φ) ∘ W`.
  The chain rule on that composite — innermost `W` (derivative `Ring.inverse (Dφ)`, the first-order
  identity), middle `fderiv ℝ φ` (derivative `fderiv² φ = fderiv ℝ (fderiv ℝ φ) v₀`), outer
  `Ring.inverse` (derivative `−mulLeftRight ℝ R (Dφ)⁻¹ (Dφ)⁻¹`, `hasFDerivAt_ringInverse`) — gives the
  clean ALGEBRAIC identity
        `fderiv ℝ (fun y => fderiv ℝ W y) (φ v₀)
            = (−mulLeftRight ℝ R Iφ Iφ) ∘L ((fderiv ℝ (fderiv ℝ φ) v₀) ∘L Iφ)`,   `Iφ = Ring.inverse (Dφ)`.
  This is `hasFDerivAt_fderiv_localLeftInverse` / `fderiv_fderiv_localLeftInverse_eq` (DERIVED here).

  ### (ii) THE FORWARD SECOND JET (the named atom + the reduction — the honest carry).  Composing the
  2nd-order IFT identity per base `z` (at the field centre, `φ_z (W_z 0) = 0`) with base-continuity of
  the ingredients reduces the chart-Hessian base-continuity to the joint continuity of the FORWARD
  SECOND jet
        `hFwd2 : ContinuousOn ((z,v) ↦ fderiv ℝ (fun w => fderiv ℝ (uniformFlowExp … z) w) v)
                   (K ×ˢ ball 0 ρ)`
  (plus the BANKED forward FIRST jet `JacobiCLMExposure.forwardFlowJet_continuousOn`, the banked
  origin-section continuity, and the nondegeneracy).  Unlike the FIRST-order carry (discharged in
  J4-435 by the endpoint velocity-Jacobi Grönwall over the C²-banked flow), `hFwd2` requires the flow
  to be C³ in the velocity slot (the velocity-slot half of the second-jet triangle is
  `contDiffAt.fderiv_right` at order 3, needing `contDiffAt3_uniformFlowExp`, only C² is banked) AND
  the SECOND-variation Grönwall — a strictly higher, genuinely multi-brick ODE effort.  So `hFwd2` is
  the honest named carry, and `chartSecondJet_of_forward2` is the conditional reduction.

  ### SPLIT POINTS.
    • SPLIT A (this file): the abstract 2nd-order IFT algebra (i) — `hasFDerivAt_fderiv_localLeftInverse`
      / `fderiv_fderiv_localLeftInverse_eq` — DERIVED, pure Mathlib, no chart.
    • SPLIT B (this file): the concrete chart 2nd-jet IFT identity + the conditional reduction
      `chartSecondJet_of_forward2` (ii), carrying `hFwd2`.
    • SPLIT C (future J4-480+): discharge `hFwd2` (C³ flow regularity + second-variation Grönwall) and
      wire the operator-level 2nd jet to the `pd`-iterated consumer shapes (`hWc2cont`/`hcont2`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `hasFDerivAt_fderiv_localLeftInverse` — ★ THE ABSTRACT 2nd-ORDER IFT IDENTITY (`HasFDerivAt`
      form, pure Mathlib).  Differentiates the ring-inverse first-order identity: the operator-valued
      first-jet map `y ↦ fderiv ℝ W y` has, at `φ v₀`, the Fréchet derivative
      `(−mulLeftRight ℝ R Iφ Iφ) ∘L ((fderiv ℝ (fderiv ℝ φ) v₀) ∘L Iφ)`, `Iφ = Ring.inverse (fderiv φ v₀)`.

    * `fderiv_fderiv_localLeftInverse_eq` — ★ the `fderiv` form of the same identity.

    * `chartSecondJet_eq_of_forward2` — ★★ the concrete chart 2nd-jet IFT identity at the field centre,
      per base `z`, from the abstract identity + banked per-`z` regularity carries.

    * `chartSecondJet_continuousOn_of_forward2` — ★★★ THE REDUCTION (`chartSecondJet_of_forward2`).
      Base-continuity of the chart SECOND field-jet `z ↦ fderiv ℝ (fun y => fderiv ℝ (W z) y) 0` on `U`,
      REDUCED to the forward SECOND jet `hFwd2` (+ banked forward first jet / origin / nondeg / the
      per-`z` 2nd-jet identity).

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion):
    * `hFwd2` — the forward SECOND jet joint continuity (the second-order analogue of the J4-434/435
      `hFwd`; a TRUE geodesic-flow fact, discharge = C³ flow regularity + second-variation Grönwall).
    * the per-`z` 2nd-jet regularity facts (germ-in-nbhd, C² of `φ_z`/`W_z`, nondeg) — geometric.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartFieldJacobian
import QIQTH.JacobiCLMExposure

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartFieldJacobian QIQTH.JacobiCLMExposure
open scoped Topology

namespace QIQTH.ChartSecondJet

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE ABSTRACT 2nd-ORDER IFT-JACOBIAN IDENTITY (pure Mathlib).
    ############################################################################### -/

/-- **★ `hasFDerivAt_fderiv_localLeftInverse` — the abstract 2nd-order IFT-Jacobian identity.**
    DIFFERENTIATES the first-order identity `fderiv ℝ W (φ v₀) = Ring.inverse (fderiv ℝ φ v₀)`.  In a
    complete normed `ℝ`-space `E`, let `φ W : E → E`, `v₀ : E` with:
      * `hWd`   — `W` differentiable at `φ v₀`;
      * `hφ2`   — `φ` twice differentiable at `v₀` (`fderiv ℝ φ` differentiable at `v₀`);
      * `hgerm` — the FIRST-order IFT identity holds in a NEIGHBOURHOOD:
                  `∀ᶠ y in 𝓝 (φ v₀), fderiv ℝ W y = Ring.inverse (fderiv ℝ φ (W y))`;
      * `hWpt`  — `W (φ v₀) = v₀` (left inverse at the point);
      * `hunit` — `IsUnit (fderiv ℝ φ v₀)`.
    Then the operator-valued first-jet map `y ↦ fderiv ℝ W y` has, at `φ v₀`, the Fréchet derivative
        `(−mulLeftRight ℝ R Iφ Iφ) ∘L ((fderiv ℝ (fderiv ℝ φ) v₀) ∘L Iφ)`,
    with `R = E →L[ℝ] E` and `Iφ = Ring.inverse (fderiv ℝ φ v₀)`.  Chain rule on
    `Ring.inverse ∘ (fderiv ℝ φ) ∘ W` (`hgerm` = the germ), transferred to `fderiv ℝ W` by
    `HasFDerivAt.congr_of_eventuallyEq`.  NOT `a₁ = R/6`. -/
theorem hasFDerivAt_fderiv_localLeftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ W : E → E} {v₀ : E}
    (hWd : DifferentiableAt ℝ W (φ v₀))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) v₀)
    (hgerm : ∀ᶠ y in 𝓝 (φ v₀), fderiv ℝ W y = Ring.inverse (fderiv ℝ φ (W y)))
    (hWpt : W (φ v₀) = v₀)
    (hunit : IsUnit (fderiv ℝ φ v₀)) :
    HasFDerivAt (fun y => fderiv ℝ W y)
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            (Ring.inverse (fderiv ℝ φ v₀)) (Ring.inverse (fderiv ℝ φ v₀))).comp
        ((fderiv ℝ (fderiv ℝ φ) v₀).comp (Ring.inverse (fderiv ℝ φ v₀))))
      (φ v₀) := by
  classical
  obtain ⟨u, hu⟩ := hunit
  -- `Ring.inverse (fderiv φ v₀) = ↑u⁻¹`.
  have hRinv_eq : Ring.inverse (fderiv ℝ φ v₀) = ↑u⁻¹ := by
    rw [← hu, Ring.inverse_unit]
  -- first-order identity at the point, from the germ.
  have hfdW : fderiv ℝ W (φ v₀) = Ring.inverse (fderiv ℝ φ v₀) := by
    have h := hgerm.self_of_nhds; rw [hWpt] at h; exact h
  -- INNERMOST: `W` at `φ v₀`, derivative `Ring.inverse (fderiv φ v₀)`.
  have hW' : HasFDerivAt W (Ring.inverse (fderiv ℝ φ v₀)) (φ v₀) := by
    have h := hWd.hasFDerivAt; rwa [hfdW] at h
  -- MIDDLE: `fderiv ℝ φ` at `W (φ v₀) = v₀`, derivative `fderiv ℝ (fderiv ℝ φ) v₀`.
  have hmid : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) v₀) (W (φ v₀)) := by
    rw [hWpt]; exact hφ2.hasFDerivAt
  have hM : HasFDerivAt (fun y => fderiv ℝ φ (W y))
      ((fderiv ℝ (fderiv ℝ φ) v₀).comp (Ring.inverse (fderiv ℝ φ v₀))) (φ v₀) :=
    hmid.comp (φ v₀) hW'
  -- OUTER: `Ring.inverse` at `fderiv ℝ φ (W (φ v₀)) = fderiv ℝ φ v₀ = ↑u`.
  have hRinvderiv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
        (Ring.inverse (fderiv ℝ φ v₀)) (Ring.inverse (fderiv ℝ φ v₀)))
      (fderiv ℝ φ (W (φ v₀))) := by
    have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rw [hWpt, ← hu]
    simpa only [Ring.inverse_unit] using h
  have hF := hRinvderiv.comp (φ v₀) hM
  -- transfer to `fderiv ℝ W` via the germ (eventual equality).
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hgerm] with y hy using hy

/-- **★ `fderiv_fderiv_localLeftInverse_eq` — the `fderiv` form of the 2nd-order IFT identity.**
    Same hypotheses as `hasFDerivAt_fderiv_localLeftInverse`; the value of `fderiv` of the operator-
    valued first-jet map:
      `fderiv ℝ (fun y => fderiv ℝ W y) (φ v₀)
          = (−mulLeftRight ℝ R Iφ Iφ) ∘L ((fderiv ℝ (fderiv ℝ φ) v₀) ∘L Iφ)`.
    NOT `a₁ = R/6`. -/
theorem fderiv_fderiv_localLeftInverse_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {φ W : E → E} {v₀ : E}
    (hWd : DifferentiableAt ℝ W (φ v₀))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) v₀)
    (hgerm : ∀ᶠ y in 𝓝 (φ v₀), fderiv ℝ W y = Ring.inverse (fderiv ℝ φ (W y)))
    (hWpt : W (φ v₀) = v₀)
    (hunit : IsUnit (fderiv ℝ φ v₀)) :
    fderiv ℝ (fun y => fderiv ℝ W y) (φ v₀)
      = (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            (Ring.inverse (fderiv ℝ φ v₀)) (Ring.inverse (fderiv ℝ φ v₀))).comp
        ((fderiv ℝ (fderiv ℝ φ) v₀).comp (Ring.inverse (fderiv ℝ φ v₀))) :=
  (hasFDerivAt_fderiv_localLeftInverse hWd hφ2 hgerm hWpt hunit).fderiv

/-! ###############################################################################
    ### ★★ THE CONCRETE CHART 2nd-JET IFT IDENTITY (at the field centre).
    ############################################################################### -/

variable {n : ℕ}

/-- **★★ `chartSecondJet_eq_of_forward2` — the concrete chart 2nd-jet IFT identity.**  For a base `z`
    with the per-`z` regularity carries (inverse chart `W_z` differentiable at `0`; forward `φ_z`
    twice differentiable at `W_z 0`; the FIRST-order IFT identity in a NEIGHBOURHOOD of `0`; the right
    inverse `φ_z (W_z 0) = 0`; `Dφ_z(W_z 0)` a unit), the chart SECOND field-jet at the field centre `0`
    is the 2nd-order ring-inverse expression:
      `fderiv ℝ (fun y => fderiv ℝ (W_z) y) 0
          = (−mulLeftRight ℝ R I I) ∘L ((fderiv ℝ (fderiv ℝ φ_z) (W_z 0)) ∘L I)`,   `I = Ring.inverse (Dφ_z(W_z 0))`.
    Immediate from `fderiv_fderiv_localLeftInverse_eq` at `v₀ = W_z 0`, rewriting `φ_z (W_z 0) = 0`.
    NOT `a₁ = R/6`. -/
theorem chartSecondJet_eq_of_forward2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0)
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0))
    (hgerm : ∀ᶠ y in 𝓝 (0 : Point n),
      fderiv ℝ (uniformInverseChart g gi hC hK z) y
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z y)))
    (hRI : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0)
    (hunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0))) :
    fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
      = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))).comp
        ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
              (uniformInverseChart g gi hC hK z 0)).comp
          (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)))) := by
  set φ := uniformFlowExp g gi hC hK z with hφdef
  set W := uniformInverseChart g gi hC hK z with hWdef
  have hWd' : DifferentiableAt ℝ W (φ (W 0)) := by rw [hRI]; exact hWd
  have hgerm' : ∀ᶠ y in 𝓝 (φ (W 0)),
      fderiv ℝ W y = Ring.inverse (fderiv ℝ φ (W y)) := by rw [hRI]; exact hgerm
  have hWpt : W (φ (W 0)) = W 0 := by rw [hRI]
  have h := fderiv_fderiv_localLeftInverse_eq (φ := φ) (W := W) (v₀ := W 0)
    hWd' hφ2 hgerm' hWpt hunit
  rw [hRI] at h
  exact h

/-! ###############################################################################
    ### ★★★ THE REDUCTION — chart 2nd-jet base-continuity ⟸ forward SECOND jet.
    ############################################################################### -/

/-- **★★★ `chartSecondJet_continuousOn_of_forward2` — THE REDUCTION (`chartSecondJet_of_forward2`).**
    The base-continuity of the chart SECOND field-jet at the field centre `0`,
        `ContinuousOn (fun z => fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0) U`,
    is REDUCED to:
      • `hW0`    — base-continuity of the origin section `z ↦ W_z 0` (banked);
      • `hFwd2`  — THE NAMED ATOM: joint-in-`(z,v)` continuity of the FORWARD SECOND jet
                   `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v` on `K ×ˢ ball 0 ρ`
                   (the second-order analogue of the J4-434/435 `hFwd`; a TRUE geodesic-flow fact,
                   discharge = C³ flow regularity + second-variation Grönwall — the honest carry);
      • the BANKED forward FIRST jet `JacobiCLMExposure.forwardFlowJet_continuousOn` (UNCONDITIONAL);
      • `horigin`— the origin smallness `‖W_z 0‖ < ρ` (so the section maps `U` into `K ×ˢ ball 0 ρ`);
      • `hunit`  — invertibility of `Dφ_z(W_z 0)` on `U`;
      • `hid2`   — the per-`z` 2nd-jet IFT identity on `U` (supplied by `chartSecondJet_eq_of_forward2`).
    Mechanism: `hid2` rewrites the target to the 2nd-order ring-inverse expression `E_z`; its two
    building blocks — `I_z = Ring.inverse (Dφ_z(W_z 0))` (banked forward first jet + `Ring.inverse`
    continuity at units) and `D2_z = fderiv ℝ (fderiv ℝ φ_z) (W_z 0)` (`hFwd2` ∘ the in-ball origin
    section) — are base-continuous on `U`; the final `−mulLeftRight`/`.comp` assembly is continuous by
    the CLM-application / CLM-composition combinators.  NOT `a₁ = R/6`. -/
theorem chartSecondJet_continuousOn_of_forward2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hFwd2 : ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK p.1)) p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)))
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
              (uniformInverseChart g gi hC hK z 0))))) :
    ContinuousOn
      (fun z : Point n => fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0) U := by
  classical
  -- banked forward FIRST jet + the origin section.
  have hFwd1 := forwardFlowJet_continuousOn g gi hC hK
  have hpair : ContinuousOn
      (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U :=
    continuousOn_id.prodMk hW0
  have hmaps : Set.MapsTo (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
    fun z hz => ⟨hUK hz, by rw [mem_ball_zero_iff]; exact horigin z hz⟩
  -- FIRST-jet inner: `z ↦ Dφ_z(W_z 0)`, continuous; hence `I_z = Ring.inverse (…)`.
  have hinner1 : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0)) U :=
    hFwd1.comp hpair hmaps
  have hI : ContinuousOn
      (fun z : Point n => Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0))) U := by
    intro z₀ hz₀
    obtain ⟨u₀, hu₀⟩ := hunit z₀ hz₀
    have hca : ContinuousAt Ring.inverse
        (fderiv ℝ (uniformFlowExp g gi hC hK z₀) (uniformInverseChart g gi hC hK z₀ 0)) := by
      rw [← hu₀]; exact (contDiffAt_ringInverse (n := 1) ℝ u₀).continuousAt
    exact hca.tendsto.comp (hinner1 z₀ hz₀)
  -- SECOND-jet inner: `z ↦ D2_z = fderiv (fderiv φ_z) (W_z 0)`, continuous via `hFwd2`.
  have hD2 : ContinuousOn
      (fun z : Point n => fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
        (uniformInverseChart g gi hC hK z 0)) U :=
    hFwd2.comp hpair hmaps
  -- assemble `E_z = (−mulLeftRight I_z I_z) ∘L (D2_z ∘L I_z)` — continuous.
  have hInner : ContinuousOn
      (fun z : Point n => (fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
          (uniformInverseChart g gi hC hK z 0)).comp
        (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0)))) U :=
    hD2.clm_comp hI
  have hML1 : ContinuousOn
      (fun z : Point n => ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
        (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0)))) U :=
    continuousOn_const.clm_apply hI
  have hML2 : ContinuousOn
      (fun z : Point n => ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
        (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0)))
        (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0)))) U :=
    hML1.clm_apply hI
  have hE : ContinuousOn
      (fun z : Point n => (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0))))) U :=
    hML2.neg.clm_comp hInner
  exact hE.congr hid2

end QIQTH.ChartSecondJet

/-! ## THE SECOND-JET LEDGER (post J4-479).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE CONVERGENT WALL.  Both consumer chains bottom out on the SAME object — the chart SECOND      │
  │  field-jet at the field centre `z ↦ fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart … z) y) 0`:  │
  │    • a₁=R/6 htermBox: `SmoothCarrierGrounding.hComposite2_grounded` needs `hWc2cont`;             │
  │    • C₂/hcont2 derivative-sup: `BaseSlotAmpDeriv.baseSlotAmpDeriv2_sup_onCollar` needs `hcont2`.  │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (i) THE 2nd-ORDER IFT ALGEBRA — DERIVED (pure Mathlib).  Differentiating the first-order         │
  │  ring-inverse identity (`ChartFieldJacobian.fderiv_localLeftInverse_eq_ringInverse`) yields        │
  │      `fderiv (fderiv W) (φ v₀) = (−mulLeftRight R Iφ Iφ) ∘L ((fderiv (fderiv φ) v₀) ∘L Iφ)`,       │
  │  `Iφ = Ring.inverse (fderiv φ v₀)` — `hasFDerivAt_fderiv_localLeftInverse` /                       │
  │  `fderiv_fderiv_localLeftInverse_eq` (chain rule via `hasFDerivAt_ringInverse` + the germ).        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  (ii) THE REDUCTION — `chartSecondJet_continuousOn_of_forward2`.  Per-base the identity            │
  │  (`chartSecondJet_eq_of_forward2`) rewrites the chart 2nd-jet to `E_z`; its two blocks are         │
  │  base-continuous: `I_z = Ring.inverse (Dφ_z(W_z 0))` from the BANKED-UNCONDITIONAL forward FIRST   │
  │  jet (`JacobiCLMExposure.forwardFlowJet_continuousOn`) + `Ring.inverse` continuity, and            │
  │  `D2_z = fderiv (fderiv φ_z) (W_z 0)` from the NAMED ATOM `hFwd2` ∘ the in-ball origin section;    │
  │  the `−mulLeftRight`/`.comp` assembly is continuous by the CLM combinators.                        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE MISSING INGREDIENT.  `hFwd2` = joint-in-`(z,v)` continuity of the FORWARD SECOND jet          │
  │      `(z,v) ↦ fderiv ℝ (fderiv ℝ (uniformFlowExp … z)) v`   on `K ×ˢ ball 0 ρ`.                    │
  │  The second-order analogue of the J4-434/435 `hFwd`.  Discharge (future J4-480): the velocity-slot │
  │  half needs the flow C³ (`contDiffAt3_uniformFlowExp`; only C² banked) and the SECOND-variation    │
  │  Grönwall (the `fderiv²`-analogue of `JacobiCLMExposure`'s endpoint velocity-Jacobi CLM).          │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  WIRING (future).  This brick delivers the OPERATOR-level 2nd jet `z ↦ fderiv² (W_z) 0`; the       │
  │  consumers carry `pd`-iterated scalar-partial shapes (`hWc2cont`/`hcont2`).  Bridging operator     │
  │  ⇄ `pd`-iterated (the second-order analogue of `BaseSlotAmpDeriv.pd_chartAmp_center_eq`) is the    │
  │  wiring split, alongside discharging `hFwd2`.                                                      │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.ChartSecondJet
#print axioms hasFDerivAt_fderiv_localLeftInverse
#print axioms fderiv_fderiv_localLeftInverse_eq
#print axioms chartSecondJet_eq_of_forward2
#print axioms chartSecondJet_continuousOn_of_forward2
end AxiomChecks
