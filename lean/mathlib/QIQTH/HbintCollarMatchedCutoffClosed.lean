/-
  HbintCollarMatchedCutoffClosed — J4-888: the COLLAR / matched-cutoff architecture of J4-872/873
  LIFTED to the JOINT `(z,x)` setting, applied to `hbint`'s joint field-Hessian CONTINUITY residual.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick LIFTS the collar/dead-zone
  argument of J4-872/873 to the joint `(z,x)` variable and REDUCES `hbint`'s joint field-Hessian
  continuity residual (J4-877/878) to the strictly-smaller ON-CLOSED-CORE-GRAPH continuity plus a
  matched-cutoff SEAM-vanishing input.  It does **NOT** close `hbint`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the collar, lifted to the joint `(z,x)` variable.

  J4-872 (`GateFatExteriorConcreteDischarge`) / J4-873 (`HGateBoundedConcreteDischarge`) closed the
  `hFd`/`hgate` residuals of `MixedDirectionsFieldHessianEnvelope` by the COLLAR / DEAD-ZONE argument:
  at the concrete flow-ball gate `S z = φ_z '' ball 0 c` with the radial margin `b < c`, the field
  witness (and its Fréchet derivative) vanishes IDENTICALLY off the per-`z` compact CORE
  `closure (φ_z '' ball 0 b)` — so the sup over the OPEN gate collapses to the compact core, sidestepping
  the hard-indicator boundary jump WITHOUT any open-map / frontier characterization.

  Those two bricks needed only BOUNDEDNESS (`BddAbove`) on the core, which pastes trivially (a max of two
  bounds).  `hbint` is structurally harder: it needs the field-Hessian norm to be jointly `ContinuousOn`
  `K ×ˢ concreteKx` (a Berge parametrised-supremum input), and CONTINUITY does not paste for free across
  the core seam.  This brick performs the faithful joint lift of the collar as far as it honestly goes:

    * `fieldHessian_fderiv_eqZero_off_jointGraph` — the collar's off-core vanishing, LIFTED to a
      JOINT-OPEN statement.  The joint field-Hessian `(z,x) ↦ fderiv ℝ (fun y => witnessFieldDeriv …
      y z) x` vanishes at EVERY `(z,x)` off the COMPACT joint graph
      `jointCore := (fun (z,v) => (z, φ_z v)) '' (K ×ˢ closedBall 0 b)` — via the per-`z` off-core
      collar (`fieldHessian_zero_offCore`, J4-873) for `z ∈ K` and the `q ∉ K` gate branch
      (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`) for `z ∉ K`.  This dissolves residual (b)
      of J4-887 (the "off-gate joint neighbourhood" concern): the complement of `jointCore` is JOINTLY
      OPEN, and the field-Hessian is `0` on it.

    * `fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous` — the matched-cutoff pasting.  The
      field-Hessian norm is `ContinuousOn (K ×ˢ concreteKx)` GIVEN (i) its continuity on the
      strictly-smaller compact ON-CORE-GRAPH `(K ×ˢ concreteKx) ∩ jointCore`, and (ii) a matched-cutoff
      SEAM-vanishing input (`f = 0` at the core-graph points that are limits of off-graph points).
      `ContinuousOn.union_of_isClosed` pastes the two CLOSED pieces (`f = 0` on the closed dead-zone
      `closure ((K ×ˢ concreteKx) \ jointCore)` via the off-graph vanishing + seam).

    * `hbint_reduced_to_coreGraphContinuity` — chains the pasting through
      `FieldHessianJointContinuity.hbint_concrete_of_jointContinuousOn` (J4-877): the `hbint` field
      REDUCED a.e. to {`BL`-continuity; ON-CORE-GRAPH continuity; matched-cutoff seam-vanishing}.

  ## WHAT THIS FILE DOES **NOT** DO — the honest limit (residual (a) survives).
  The ON-CORE-GRAPH continuity `ContinuousOn f ((K ×ˢ concreteKx) ∩ jointCore)` is EXACTLY J4-887's
  residual (a): it needs the joint chart `C²` on a neighbourhood of the FIXED-radius closed `b`-tube over
  ALL of `K`, whereas J4-884's tube is an UNQUANTIFIED qualitative neighbourhood of the INTERIOR-`K`
  diagonal.  The Lebesgue-number lemma turns per-point `ContDiffAt` into a uniform tube radius `ρ`, but
  gives NO `ρ ≥ b` guarantee and NO boundary-`K` coverage — so it does not dissolve residual (a).  The
  matched-cutoff seam-vanishing (residual (c)) is left as an explicit, satisfiable input (dischargeable
  from `radialCutoff`'s smoothness at radius `b`, as in J4-873's collar computation).  `hbint` is NOT
  closed.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FieldHessianJointContinuity
import QIQTH.HGateBoundedConcreteDischarge
import QIQTH.HZMassIntegrabilityAttempt

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open scoped Topology BigOperators

namespace QIQTH.HbintCollarMatchedCutoffClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the compact joint core-graph and its off-graph field-Hessian vanishing.
    ############################################################################### -/

/-- The COMPACT joint core-graph `jointCore := (fun (z,v) => (z, φ_z v)) '' (K ×ˢ closedBall 0 b)`.
    Unlike `concreteKx` (the `x`-space projection, which forgets the base), the graph keeps the base
    coordinate, so `(z,x) ∈ jointCore` forces `x = φ_z v` for the SAME `z`.  This is the joint analogue
    of the per-`z` compact core `φ_z '' closedBall 0 b`. -/
noncomputable def jointCore (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) : Set (Point n × Point n) :=
  (fun p : Point n × Point n => (p.1, uniformFlowExp g gi hC hK p.1 p.2)) ''
    (K ×ˢ Metric.closedBall 0 b)

/-- **★ `jointCore_isCompact`.**  The joint core-graph is compact: it is the image of the compact
    `K ×ˢ closedBall 0 b` (`b < uniformFlowRadius`) under the `ContinuousOn` joint map
    `(z,v) ↦ (z, φ_z v)` (first slot `continuous_fst`, second slot `uniformFlowExp_joint_continuousOn`).
    NOT `a₁ = R/6`. -/
theorem jointCore_isCompact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    IsCompact (jointCore g gi hC hK b) := by
  have hsub : (K ×ˢ Metric.closedBall (0 : Point n) b)
      ⊆ (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
    Set.prod_mono (le_refl K) (Metric.closedBall_subset_ball hbρ)
  have hcont : ContinuousOn
      (fun p : Point n × Point n => (p.1, uniformFlowExp g gi hC hK p.1 p.2))
      (K ×ˢ Metric.closedBall (0 : Point n) b) := by
    refine ContinuousOn.prodMk continuousOn_fst ?_
    exact (QIQTH.FlowJointContinuity.uniformFlowExp_joint_continuousOn g gi hC hK).mono hsub
  exact (hK.prod (isCompact_closedBall (0 : Point n) b)).image_of_continuousOn hcont

/-- **★ `jointCore_isClosed`.**  Compact ⟹ closed (the ambient product is Hausdorff). -/
theorem jointCore_isClosed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    IsClosed (jointCore g gi hC hK b) :=
  (jointCore_isCompact g gi hC hK b hbρ).isClosed

/-- The per-`z` compact `φ_z '' closedBall 0 b` (a slice of `jointCore`), needed to convert an
    off-`closedBall`-image `x` into an off-`closure (φ_z '' ball 0 b)` `x`. -/
theorem closedBall_image_isClosed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ)
    (hbρ : b < uniformFlowRadius g gi hC hK) (z : Point n) (hz : z ∈ K) :
    IsClosed (uniformFlowExp g gi hC hK z '' Metric.closedBall (0 : Point n) b) := by
  have hmaps : Set.MapsTo (fun w : Point n => (z, w)) (Metric.closedBall 0 b)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    exact ⟨hz, by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_le_of_lt hw hbρ⟩
  have hincl : ContinuousOn (fun w : Point n => (z, w)) (Metric.closedBall 0 b) :=
    continuousOn_const.prodMk continuousOn_id
  have hcont : ContinuousOn (uniformFlowExp g gi hC hK z) (Metric.closedBall 0 b) := by
    have h := (QIQTH.FlowJointContinuity.uniformFlowExp_joint_continuousOn g gi hC hK).comp
      hincl hmaps
    simpa using h
  exact ((isCompact_closedBall (0 : Point n) b).image_of_continuousOn hcont).isClosed

/-- **★★ `fieldHessian_fderiv_eqZero_off_jointGraph` — the collar's off-core vanishing, LIFTED to a
    JOINT-OPEN statement.**  For the concrete flow-ball gate (`0 < a < b < c < δ₀`,
    `b < uniformFlowRadius`), the joint field-Hessian `(z,x) ↦ fderiv ℝ (fun y => witnessFieldDeriv …
    y z) x` vanishes at EVERY joint point `(z,x)` OFF the compact joint core-graph `jointCore`.

    Two cases.  `z ∈ K`: `(z,x) ∉ jointCore` forces `x ∉ φ_z '' closedBall 0 b`
    (else `(z,x) = (z, φ_z v)` with `‖v‖ ≤ b` would be in `jointCore`), so `x` is off the closed
    `φ_z '' closedBall 0 b ⊇ closure (φ_z '' ball 0 b)` — the per-`z` collar
    `fieldHessian_zero_offCore` (J4-873) fires.  `z ∉ K`: the `q ∉ K` gate branch kills the whole
    field-Hessian (`witnessFieldHessian_fderiv_eqZero_of_base_notMem_K`).  So the field-Hessian is `0`
    on the JOINTLY OPEN complement of `jointCore`.  NOT `a₁ = R/6`. -/
theorem fieldHessian_fderiv_eqZero_off_jointGraph (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (p : Point n × Point n),
          p ∉ jointCore g gi hC hK b →
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2 = 0 := by
  obtain ⟨δ₀, hδ₀, hoff⟩ :=
    QIQTH.HGateBoundedConcreteDischarge.fieldHessian_zero_offCore g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq i τ p hp
  by_cases hzK : p.1 ∈ K
  · -- `z ∈ K`: off the joint graph ⟹ off the per-`z` closed `closedBall`-image ⟹ off the core.
    have hxNotClosedBall : p.2 ∉ uniformFlowExp g gi hC hK p.1 '' Metric.closedBall (0 : Point n) b := by
      intro hx
      obtain ⟨v, hv, hvx⟩ := hx
      exact hp ⟨(p.1, v), ⟨hzK, hv⟩, by rw [Prod.ext_iff]; exact ⟨rfl, hvx⟩⟩
    have hxNotCore : p.2 ∉ closure (uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) b) := by
      intro hx
      have hsub : closure (uniformFlowExp g gi hC hK p.1 '' Metric.ball (0 : Point n) b)
          ⊆ uniformFlowExp g gi hC hK p.1 '' Metric.closedBall (0 : Point n) b := by
        refine closure_minimal ?_ (closedBall_image_isClosed g gi hC hK b hbρ p.1 hzK)
        exact Set.image_mono Metric.ball_subset_closedBall
      exact hxNotClosedBall (hsub hx)
    exact hoff c hbc hcδ S hSeq i τ p.1 hzK p.2 hxNotCore
  · -- `z ∉ K`: the `q ∉ K` gate branch kills the field-Hessian everywhere.
    exact QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
      g gi hC hK S a b i τ p.1 hzK p.2

/-! ###############################################################################
    ### C1 — the matched-cutoff pasting: joint continuity from on-core-graph continuity + seam.
    ############################################################################### -/

/-- **★★★ J4-888 — `fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous`.**  The MATCHED-CUTOFF
    PASTING, joint lift of J4-873's `hgate_concrete_of_coreContinuousOn`.  The field-Hessian norm
    `f (z,x) := ‖fderiv ℝ (fun y => witnessFieldDeriv … y z) x‖` is `ContinuousOn (K ×ˢ concreteKx)`
    GIVEN:
      (i) `hcore`  — its continuity on the ON-CORE-GRAPH `(K ×ˢ concreteKx) ∩ jointCore` (residual (a),
          the joint chart-`C²`-on-the-closed-`b`-tube frontier);
      (ii) `hseam` — matched-cutoff SEAM-vanishing: `f p = 0` at every on-core-graph point `p` that is a
          limit of off-graph points (`p ∈ closure ((K ×ˢ concreteKx) \ jointCore)`) — dischargeable from
          `radialCutoff`'s vanishing at radius `b`.
    Off the graph `f = 0` (`fieldHessian_fderiv_eqZero_off_jointGraph`), so the DEAD-ZONE
    `dead := closure ((K ×ˢ concreteKx) \ jointCore) ∩ (K ×ˢ concreteKx)` carries `f ≡ 0` (off-graph by
    the collar, on the seam by `hseam`), hence `f` is continuous there.  `ContinuousOn.union_of_isClosed`
    pastes the two CLOSED pieces (`(K ×ˢ concreteKx) ∩ jointCore` and `dead`), whose union is all of
    `K ×ˢ concreteKx`.  NOT `a₁ = R/6`. -/
theorem fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ),
          ContinuousOn
            (fun p : Point n × Point n =>
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
            ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b) →
          (∀ p ∈ (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b,
              p ∈ closure ((K ×ˢ concreteKx g gi hC hK b) \ jointCore g gi hC hK b) →
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖ = 0) →
          ContinuousOn
            (fun p : Point n × Point n =>
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
            (K ×ˢ concreteKx g gi hC hK b) := by
  obtain ⟨δ₀, hδ₀, hoff⟩ := fieldHessian_fderiv_eqZero_off_jointGraph g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq i τ hcore hseam
  set D : Set (Point n × Point n) := K ×ˢ concreteKx g gi hC hK b with hDdef
  set Γ : Set (Point n × Point n) := jointCore g gi hC hK b with hΓdef
  set f : Point n × Point n → ℝ :=
    fun p => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖ with hfdef
  -- `D` is closed (compact product), `Γ` is closed.
  have hDcompact : IsCompact D :=
    hK.prod (concreteKx_isCompact g gi hC hK b hbρ)
  have hDclosed : IsClosed D := hDcompact.isClosed
  have hΓclosed : IsClosed Γ := jointCore_isClosed g gi hC hK b hbρ
  -- The dead-zone: the closure of the off-graph part of `D`, intersected with `D`.
  set dead : Set (Point n × Point n) := closure (D \ Γ) ∩ D with hdeaddef
  have hdeadClosed : IsClosed dead := isClosed_closure.inter hDclosed
  have honGraphClosed : IsClosed (D ∩ Γ) := hDclosed.inter hΓclosed
  -- `f = 0` on the dead-zone: off-graph points by the collar, seam points by `hseam`.
  have hfdead : ∀ p ∈ dead, f p = 0 := by
    intro p hp
    obtain ⟨hpcl, hpD⟩ := hp
    by_cases hpΓ : p ∈ Γ
    · exact hseam p ⟨hpD, hpΓ⟩ hpcl
    · -- off the graph: the collar vanishing.
      show ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖ = 0
      rw [hoff c hbc hcδ S hSeq i τ p hpΓ, norm_zero]
  -- `f` is continuous on the closed dead-zone (it is `0` there).
  have hcontDead : ContinuousOn f dead :=
    (continuousOn_const (c := (0 : ℝ))).congr hfdead
  -- Paste the two closed pieces.
  have hUnion : ContinuousOn f ((D ∩ Γ) ∪ dead) :=
    hcore.union_of_isClosed hcontDead honGraphClosed hdeadClosed
  -- `D ⊆ (D ∩ Γ) ∪ dead`: on-graph points land left, off-graph points land in the dead-zone.
  have hcover : D ⊆ (D ∩ Γ) ∪ dead := by
    intro p hp
    by_cases hpΓ : p ∈ Γ
    · exact Or.inl ⟨hp, hpΓ⟩
    · exact Or.inr ⟨subset_closure ⟨hp, hpΓ⟩, hp⟩
  exact hUnion.mono hcover

/-! ###############################################################################
    ### C2 — the `hbint` field, REDUCED a.e. to on-core-graph continuity + seam + `BL`-continuity.
    ############################################################################### -/

/-- **★★★ J4-888 — `hbint_reduced_to_coreGraphContinuity`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, REDUCED a.e. to:
      • the standard `BL`-continuity on `K`;
      • ON-CORE-GRAPH continuity of the field-Hessian norm on `(K ×ˢ concreteKx) ∩ jointCore` (per
        a.e. `s`) — residual (a), the joint chart-`C²`-on-closed-`b`-tube frontier;
      • matched-cutoff SEAM-vanishing (per a.e. `s`) — residual (c), dischargeable from `radialCutoff`.
    Chains the matched-cutoff pasting `fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous` (this
    file) through `FieldHessianJointContinuity.hbint_concrete_of_jointContinuousOn` (J4-877).

    So the OFF-gate/off-core scaffolding (residual (b), J4-887) is now DISCHARGED via the JOINT-OPEN
    collar `fieldHessian_fderiv_eqZero_off_jointGraph`, and `hbint`'s joint-continuity residual is
    reduced to the strictly-smaller ON-CORE-GRAPH continuity plus the matched-cutoff seam — the faithful
    joint lift of J4-873's `hgate_concrete_of_coreContinuousOn`.  `K` nonempty; radii `0 < a < b < c
    < δ₀`, `b < uniformFlowRadius`.  `hbint` is NOT closed — the on-core-graph continuity remains open.
    NOT `a₁ = R/6`. -/
theorem hbint_reduced_to_coreGraphContinuity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ContinuousOn
              (fun p : Point n × Point n =>
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖)
              ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b)) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ p ∈ (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b,
              p ∈ closure ((K ×ˢ concreteKx g gi hC hK b) \ jointCore g gi hC hK b) →
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖ = 0) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨δ₁, hδ₁, hjoint⟩ :=
    hbint_concrete_of_jointContinuousOn g gi hC hK hKne a b ha hab hbρ i t m BL
  obtain ⟨δ₂, hδ₂, hpaste⟩ :=
    fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous g gi hC hK a b ha hab hbρ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro c hbc hcδ S hSeq hBL hcore hseam
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (min_le_right _ _)
  refine hjoint c hbc hcδ₁ S hSeq hBL ?_
  filter_upwards [hcore, hseam] with s hcores hseams hsU
  exact hpaste c hbc hcδ₂ S hSeq i (t - s) (hcores hsU) (hseams hsU)

/-! ###############################################################################
    ### C3 — NON-VACUITY of the reduced carries (empty gate).
    ############################################################################### -/

/-- **NON-VACUITY.**  At the empty gate `S := fun _ => ∅` the field-Hessian is identically `0`
    (`witnessFieldHessian_fderiv_eqZero_of_notMem_closure`, since `closure ∅ = ∅`), so BOTH reduced
    carries — the on-core-graph continuity and the matched-cutoff seam-vanishing — hold trivially
    (a constant-`0` norm is `ContinuousOn` and `= 0`).  No unsatisfiable antecedent (no J4-548/847
    trap), never the conclusion.  (The genuinely non-trivial on-core-graph continuity of the CONCRETE
    non-empty-gate field-Hessian = the joint chart-`C²`-on-`b`-tube frontier — residual (a) — is the
    honest wall that remains.)  NOT `a₁ = R/6`. -/
theorem coreGraphContinuity_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ) :
    ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
      ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b) := by
  have hzero : (fun p : Point n × Point n =>
      ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
      = fun _ => (0 : ℝ) := by
    funext p
    rw [QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.1 p.2 (by simp), norm_zero]
  rw [hzero]
  exact continuousOn_const

end QIQTH.HbintCollarMatchedCutoffClosed

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HbintCollarMatchedCutoffClosed
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms jointCore_isCompact
#print axioms jointCore_isClosed
#print axioms closedBall_image_isClosed
#print axioms fieldHessian_fderiv_eqZero_off_jointGraph
#print axioms fieldHessian_norm_jointContinuousOn_of_coreGraphContinuous
#print axioms hbint_reduced_to_coreGraphContinuity
#print axioms coreGraphContinuity_nonvacuous
end AxiomChecks
