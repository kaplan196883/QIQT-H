/-
  HmeasReducedToJointC1 — J4-1040: the `hmeas` field of `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries`
  REDUCED, at the CONCRETE flow-ball gate, to the SAME single named geometric wall `hbint` already
  carries — the joint `ContDiffOn ℝ 1` regularity of the field-derivative kernel
  (`JointRNCRegularityInterface.JointSecondOrderRNCRegularity`) — rather than an independent obstacle.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}; hCConv is NOT closed here.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FINDING.

  `KPrimeMeasurabilityScaffolding.hK'meas_witness` (J4-797) reduces `MixedEnvelopeAssembly`'s `hmeas`
  field — `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ x, AEStronglyMeasurable (z ↦ kPrime … x z)` — to two carries:
  a banked Levi z-measurability family `hLeviFam` (suppliable from `FixedGateSourceProviders`, ⟸
  `LeviSeriesLocalData`/`hEmeas`, an ALREADY-NAMED carry, untouched here) and an honest BARE
  second-field-derivative z-measurability family `hFderivFam`
    (`∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ x, AEStronglyMeasurable (z ↦ fderiv ℝ (y ↦ witnessFieldDeriv … y z) x)`)
  which J4-797 left as a genuinely carried (never-derived) hypothesis.

  This file DISCHARGES `hFderivFam`, for the CONCRETE flow-ball gate, down to EXACTLY the joint `C¹`
  carry that `FieldHessianJointContinuityClosed.hbint_concrete_reduced_to_jointC1` (J4-878) ALREADY
  needs for `hbint` — i.e. `hFderivFam` is NOT a new/independent wall: it collapses onto the SAME
  named residual.  The mechanism, for a FIXED `x`:
    • `x ∉ concreteKx` (a FIXED, `z`-independent compact set): `z ↦ fderiv … x` is IDENTICALLY ZERO on
      ALL of `Point n` — both on `K` (`FieldHessianJointContinuity.fieldHessian_vanish_off_concreteKx`)
      and off `K` (`HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`) —
      so `aestronglyMeasurable_const` applies directly.
    • `x ∈ concreteKx`: `z ↦ fderiv … x` is `0` off `K` (same off-`K` vanishing lemma) and
      `ContinuousOn K` on `K` — the latter a SLICE, at fixed `x`, of the joint `(z,x)`-continuity of the
      CLM-valued field-Hessian (built here as `partialFDeriv_jointContinuousOn`, the CLM-valued analog of
      `FieldHessianJointContinuityClosed.partialFDeriv_norm_jointContinuousOn`, one algebraic step before
      the `.norm` that file takes) — reducing to the SAME joint `C¹` carry.  `K` compact hence closed
      hence measurable, so `ContinuousOn.aestronglyMeasurable` + `aestronglyMeasurable_indicator_iff`
      lift the `K`-local fact to a genuine global `AEStronglyMeasurable` on all of `Point n`.

  ## WHAT LANDS (ns `QIQTH.HmeasReducedToJointC1`).
    • `partialFDeriv_jointContinuousOn` — ★ the CLM-valued (not just norm) partial-fderiv-of-joint-`C¹`
      engine, provider-independent.
    • `fieldHessianCLM_jointContinuousOn_of_jointC1` — instantiation at the concrete field-derivative
      kernel.
    • `fieldHessianCLM_zContinuousOn_of_jointC1` — the fixed-`x` SLICE, `ContinuousOn K`.
    • `hFderivFam_ofX_of_jointC1` — the fixed-`x`, `x ∈ concreteKx` case: global `AEStronglyMeasurable`
      via the closed-set/indicator route.
    • `hFderivFam_concrete_reduced_to_jointC1` — ★★★ the FULL `hFderivFam` family (∀ x, including
      `x ∉ concreteKx`), reduced a.e. to the joint `C¹` carry alone.
    • `hmeas_concrete_reduced_to_jointC1` — ★★★★ the CAPSTONE: `MixedEnvelopeAssembly`'s exact `hmeas`
      shape, reduced to {`hLeviFam` (already-named, untouched), the joint `C¹` carry (= `hbint`'s
      residual)}.  So `hmeas` is NOT an independent obstacle of `fb` — once the joint-`C¹`-chart wall is
      supplied (for `hbint`), `hmeas` comes along for free.

  ## HONEST RESIDUAL (unchanged).  The joint `ContDiffOn ℝ 1` carry itself is NOT discharged here — it
  remains the campaign's single named irreducible geometric wall.  `hLeviFam` is untouched (separate,
  already-named carry).  `hbint`'s OWN `hbnd` sub-carry and `hBFpeak` are UNTOUCHED by this file.  NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FieldHessianJointContinuityClosed
import QIQTH.HZMassIntegrabilityAttempt
import QIQTH.KPrimeMeasurabilityScaffolding

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.FderivBulkConcrete
open QIQTH.FieldHessianJointContinuity QIQTH.FieldHessianJointContinuityClosed
open QIQTH.HZMassIntegrabilityAttempt QIQTH.KPrimeMeasurabilityScaffolding QIQTH.ExpMap
open scoped Topology Interval BigOperators

namespace QIQTH.HmeasReducedToJointC1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the CLM-valued (not merely norm) partial-fderiv-of-joint-`C¹` engine.
    ############################################################################### -/

/-- **★ `partialFDeriv_jointContinuousOn`.**  For ANY `Ψ : E × F → H` that is `ContDiffOn ℝ 1` on an
    OPEN `U ⊆ E × F`, the CLM-VALUED partial Fréchet derivative in the second slot,
      `(z,y) ↦ fderiv ℝ (fun y' ↦ Ψ (z, y')) y`,
    is `ContinuousOn U`.  The CLM-valued analog of
    `FieldHessianJointContinuityClosed.partialFDeriv_norm_jointContinuousOn`, one algebraic step before
    the `.norm` that file takes: same chain-rule mechanism (`ContDiffOn.continuousOn_fderiv_of_isOpen` +
    post-composition with the fixed `ContinuousLinearMap.inr`), stopping short of taking norms so the
    CLM itself — not just its magnitude — is exhibited as continuous.  NOT `a₁ = R/6`. -/
theorem partialFDeriv_jointContinuousOn
    {E F H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set (E × F)} (hU : IsOpen U)
    (Ψ : E × F → H) (hΨ : ContDiffOn ℝ 1 Ψ U) :
    ContinuousOn (fun p : E × F => fderiv ℝ (fun y => Ψ (p.1, y)) p.2) U := by
  have hfd : ContinuousOn (fun p : E × F => fderiv ℝ Ψ p) U :=
    hΨ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hcomp : ContinuousOn
      (fun p : E × F => (fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) U :=
    hfd.clm_comp continuousOn_const
  refine hcomp.congr (fun p hp => ?_)
  have hdiff : DifferentiableAt ℝ Ψ p :=
    (hΨ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hp)
  have hchain : HasFDerivAt (fun y : F => Ψ (p.1, y))
      ((fderiv ℝ Ψ p).comp (ContinuousLinearMap.inr ℝ E F)) p.2 :=
    (hdiff.hasFDerivAt).comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
  exact hchain.fderiv

/-! ###############################################################################
    ### §1 — instantiation at the concrete field-derivative kernel.
    ############################################################################### -/

/-- **★★ `fieldHessianCLM_jointContinuousOn_of_jointC1`.**  The CLM-valued joint `(z,x)`-continuity of
    the field-Hessian, from a JOINT `ContDiffOn ℝ 1` carry of the joint field-derivative kernel
    `Ψ (z,y) := witnessFieldDeriv … y z` on an OPEN neighbourhood `U ⊇ K ×ˢ Kx`.  NOT `a₁ = R/6`. -/
theorem fieldHessianCLM_jointContinuousOn_of_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)}
    {U : Set (Point n × Point n)} (hU : IsOpen U) (hsub : K ×ˢ Kx ⊆ U)
    (hjointC1 : ContDiffOn ℝ 1
      (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) U) :
    ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2)
      (K ×ˢ Kx) :=
  (partialFDeriv_jointContinuousOn hU
    (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1)
    hjointC1).mono hsub

/-! ###############################################################################
    ### §2 — the fixed-`x` slice: `ContinuousOn K` at `x ∈ Kx`.
    ############################################################################### -/

/-- **★★ `fieldHessianCLM_zContinuousOn_of_jointC1`.**  At a FIXED `x ∈ Kx`, the `z`-slice of the joint
    CLM-continuity is `ContinuousOn K`.  NOT `a₁ = R/6`. -/
theorem fieldHessianCLM_zContinuousOn_of_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)}
    (hjoint : ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2)
      (K ×ˢ Kx))
    (x : Point n) (hx : x ∈ Kx) :
    ContinuousOn (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x) K := by
  have hpair : ContinuousOn (fun z : Point n => (z, x)) K :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hcomp : ContinuousOn
      (fun z : Point n =>
        (fun p : Point n × Point n =>
          fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2) (z, x))
      K :=
    hjoint.comp hpair (fun z hz => ⟨hz, hx⟩)
  simpa using hcomp

/-! ###############################################################################
    ### §3 — fixed-`x` global `AEStronglyMeasurable`, `x ∈ concreteKx` case.
    ############################################################################### -/

/-- **★★★ `hFderivFam_ofX_of_jointC1`.**  At a FIXED `x ∈ concreteKx`, the global (all of `Point n`)
    `AEStronglyMeasurable` of `z ↦ fderiv … x`, from: `ContinuousOn K` on the compact `K` (§2) and `= 0`
    off `K` (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`).  Route: `K` closed hence measurable;
    `ContinuousOn.aestronglyMeasurable` gives the LOCAL fact on `volume.restrict K`;
    `aestronglyMeasurable_indicator_iff` lifts to the GLOBAL indicator; the off-`K` vanishing identifies
    the indicator with the true function.  NOT `a₁ = R/6`. -/
theorem hFderivFam_ofX_of_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)}
    (hjoint : ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2)
      (K ×ˢ Kx))
    (x : Point n) (hx : x ∈ Kx) :
    AEStronglyMeasurable (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
      (volume : Measure (Point n)) := by
  have hcontK : ContinuousOn
      (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x) K :=
    fieldHessianCLM_zContinuousOn_of_jointC1 g gi hC hK S a b i τ hjoint x hx
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hlocal : AEStronglyMeasurable
      (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
      ((volume : Measure (Point n)).restrict K) :=
    hcontK.aestronglyMeasurable hKm
  have hindic : AEStronglyMeasurable
      (K.indicator (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x))
      (volume : Measure (Point n)) :=
    (aestronglyMeasurable_indicator_iff hKm).2 hlocal
  have heq : K.indicator (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
      = fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x := by
    funext z
    by_cases hz : z ∈ K
    · simp [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz,
        witnessFieldHessian_fderiv_eqZero_of_base_notMem_K g gi hC hK S a b i τ z hz x]
  rwa [heq] at hindic

/-! ###############################################################################
    ### §4 — the FULL `hFderivFam` family (∀ x), at the CONCRETE flow-ball gate.
    ############################################################################### -/

/-- **★★★★ `hFderivFam_concrete_reduced_to_jointC1`.**  THE FULL `hFderivFam` shape — ∀ `x : Point n`
    (not merely `x ∈ concreteKx`) — reduced, at the CONCRETE flow-ball gate, to the SOLE genuine
    residual: a joint `ContDiffOn ℝ 1` carry of the joint field-derivative kernel on an OPEN
    `U ⊇ K ×ˢ concreteKx`.  For `x ∉ concreteKx` the function is IDENTICALLY ZERO on all of `Point n`
    (both vanishing lemmas fire, no continuity needed); for `x ∈ concreteKx`, §3 applies.  `K` nonempty;
    radii `0 < a < b < c < δ₀`, `b < uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem hFderivFam_concrete_reduced_to_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (τ : ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∃ U : Set (Point n × Point n), IsOpen U ∧ K ×ˢ concreteKx g gi hC hK b ⊆ U ∧
            ContDiffOn ℝ 1
              (fun p : Point n × Point n => witnessFieldDeriv g gi hC hK S a b i τ p.2 p.1) U) →
        ∀ x : Point n,
          AEStronglyMeasurable
            (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
            (volume : Measure (Point n)) := by
  obtain ⟨δ₀, hδ₀, hvan⟩ := fieldHessian_vanish_off_concreteKx g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hcarry x
  obtain ⟨U, hU, hsub, hjointC1⟩ := hcarry
  have hjoint : ContinuousOn
      (fun p : Point n × Point n =>
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2)
      (K ×ˢ concreteKx g gi hC hK b) :=
    fieldHessianCLM_jointContinuousOn_of_jointC1 g gi hC hK S a b i τ hU hsub hjointC1
  by_cases hx : x ∈ concreteKx g gi hC hK b
  · exact hFderivFam_ofX_of_jointC1 g gi hC hK S a b i τ hjoint x hx
  · have hzero : ∀ z : Point n,
        fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 := by
      intro z
      by_cases hz : z ∈ K
      · exact hvan c hbc hcδ S hSeq i τ z hz x hx
      · exact witnessFieldHessian_fderiv_eqZero_of_base_notMem_K g gi hC hK S a b i τ z hz x
    have heq : (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x)
        = fun _ => (0 : Point n →L[ℝ] ℝ) := funext hzero
    rw [heq]
    exact aestronglyMeasurable_const

/-! ###############################################################################
    ### §5 — CAPSTONE: `hmeas`, reduced to {`hLeviFam`, the joint `C¹` carry}.
    ############################################################################### -/

/-- **★★★★★ CAPSTONE — `hmeas_concrete_reduced_to_jointC1`.**  The EXACT `hmeas` field of
    `MixedEnvelopeAssembly.mixedEnvelope_of_named_carries` — `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ x,
    AEStronglyMeasurable (z ↦ kPrime … x z)` — at the CONCRETE flow-ball gate, reduced to:
    the ALREADY-NAMED `hLeviFam` (banked-suppliable, untouched), plus a.e. `s` the SAME joint `C¹`
    carry `hbint_concrete_reduced_to_jointC1` (J4-878) already needs.  So `hmeas` is NOT an
    independent obstacle of `fb`.  Chains `KPrimeMeasurabilityScaffolding.hK'meas_witness` (J4-797)
    through `hFderivFam_concrete_reduced_to_jointC1` (§4).  `K` nonempty; radii
    `0 < a < b < c < δ₀`, `b < uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem hmeas_concrete_reduced_to_jointC1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            AEStronglyMeasurable
              (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
              (volume : Measure (Point n))) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ U : Set (Point n × Point n), IsOpen U ∧ K ×ˢ concreteKx g gi hC hK b ⊆ U ∧
              ContDiffOn ℝ 1
                (fun p : Point n × Point n =>
                  witnessFieldDeriv g gi hC hK S a b i (t - s) p.2 p.1) U) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          ∀ x : Point n,
            AEStronglyMeasurable (fun z => kPrime g gi hC hK S a b i t s x z)
              (volume : Measure (Point n)) := by
  obtain ⟨δ₀, hδ₀, hvan⟩ := fieldHessian_vanish_off_concreteKx g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hLeviFam hcarry
  have hFderivFam : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ x : Point n,
      AEStronglyMeasurable
        (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
        (volume : Measure (Point n)) := by
    filter_upwards [hcarry] with s hs hmem x
    obtain ⟨U, hU, hsub, hjointC1⟩ := hs hmem
    have hjoint : ContinuousOn
        (fun p : Point n × Point n =>
          fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2)
        (K ×ˢ concreteKx g gi hC hK b) :=
      fieldHessianCLM_jointContinuousOn_of_jointC1 g gi hC hK S a b i (t - s) hU hsub hjointC1
    by_cases hx : x ∈ concreteKx g gi hC hK b
    · exact hFderivFam_ofX_of_jointC1 g gi hC hK S a b i (t - s) hjoint x hx
    · have hzero : ∀ z : Point n,
          fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x = 0 := by
        intro z
        by_cases hz : z ∈ K
        · exact hvan c hbc hcδ S hSeq i (t - s) z hz x hx
        · exact witnessFieldHessian_fderiv_eqZero_of_base_notMem_K g gi hC hK S a b i (t - s) z hz x
      have heq : (fun z => fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
          = fun _ => (0 : Point n →L[ℝ] ℝ) := funext hzero
      rw [heq]
      exact aestronglyMeasurable_const
  have hK'm := hK'meas_witness g gi hC hK S a b i t m hLeviFam hFderivFam
  filter_upwards [hK'm] with s hs hmem x
  exact hs hmem x (Set.mem_univ x)

end QIQTH.HmeasReducedToJointC1

section AxiomChecks
open QIQTH.HmeasReducedToJointC1
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms partialFDeriv_jointContinuousOn
#print axioms fieldHessianCLM_jointContinuousOn_of_jointC1
#print axioms fieldHessianCLM_zContinuousOn_of_jointC1
#print axioms hFderivFam_ofX_of_jointC1
#print axioms hFderivFam_concrete_reduced_to_jointC1
#print axioms hmeas_concrete_reduced_to_jointC1
end AxiomChecks
