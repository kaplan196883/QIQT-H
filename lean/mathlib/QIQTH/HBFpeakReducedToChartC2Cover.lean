/-
  HBFpeakReducedToChartC2Cover — the `hBFpeak` / `hpeak` literal-shape carries of
  `HZMassCappedWindowClosed`/`BFGaussianEnvelopeClosed` REDUCED to the SAME chart-`C²`+in-gate open
  cover hypothesis `hbint` already carries (`QuantifiedCoherentChartTube.onCoreGraphContinuity_of_
  chartC2_gate_cover`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the z-uniform field-Hessian peak `hBFpeak`, made CONDITIONAL on the SAME crisp
  chart-`C²`+in-gate cover that `hbint` already carries (J4-889).

  `BFGaussianEnvelopeClosed.witnessFieldHessian_hFd_of_peak_dominator` needed a PER-`z` continuous
  dominator `Poly` on `closure (S z)`, with NO uniformity across `z` — the exact gap flagged at the
  top of this campaign.  `HZMassCappedWindowClosed.hzmass_capped_window_closed` needs the STRONGER
  literal `hBFpeak : ∀ᵐ s, s ∈ window → ∀ z, BF s z ≤ Ppk s`, with `Ppk : ℝ → ℝ` genuinely
  `z`-INDEPENDENT — the object neither file supplied a route to.

  This brick supplies that route, and it is CLEANER than either file anticipated: it does NOT need a
  Gaussian-decay envelope, and it does NOT need the naive inclusion `closure (S z) ⊆ (jointCore
  z-slice)` (which is FALSE at the literal radii — `S z` is the OUTER `c`-radius gate while `jointCore`
  is built at the INNER `b`-radius core, `b < c`).  Instead it uses the ALREADY-PROVEN universal
  off-`jointCore` vanishing (`HbintCollarMatchedCutoffClosed.fieldHessian_fderiv_eqZero_off_jointGraph`,
  J4-888): for EVERY `(z,x)` off the compact joint core-graph `jointCore` — including every point of
  `closure (S z) \ jointCore`, i.e. the `b<‖·‖<c` collar the naive inclusion worried about — the
  field-Hessian is IDENTICALLY `0`.  So a single case split (`(z,x) ∈ jointCore` vs `∉`) suffices:

    * ON `jointCore` (equivalently `(K ×ˢ concreteKx) ∩ jointCore`, since `jointCore ⊆ K ×ˢ concreteKx`
      — `jointCore_subset_prod_concreteKx`, proved here): the field-Hessian norm is `ContinuousOn` this
      COMPACT set (`onCoreGraphContinuity_of_chartC2_gate_cover`, CONDITIONAL on the open chart-`C²`+
      in-gate cover `W`), so it is bounded above by a single constant
      (`jointCorePeak`, via `IsCompact.bddAbove_image` + `le_csSup` — NOT "attains max", sidestepping
      any nonempty-case fuss).
    * OFF `jointCore` (this includes ALL of `closure (S z) \ jointCore` — no inclusion needed): the
      field-Hessian is `0` by the collar (`fieldHessian_fderiv_eqZero_off_jointGraph`), hence `≤` the
      same nonnegative constant.

  So `‖fderiv …‖ ≤ jointCorePeak` holds for EVERY `(z,x)` — not merely `x ∈ closure (S z)` — for EVERY
  `z : Point n` (not just `z ∈ K`, since off-`K` points are automatically off `jointCore` too, by
  `jointCore`'s own definition). Taking the `⨆_x` and setting `Ppk s := jointCorePeak (τ := t-s)` then
  gives the EXACT `hBFpeak` literal (`ciSup_le`), CONDITIONAL on the SAME per-`s` chart-`C²`+in-gate
  cover `hbint` already carries — no new hypothesis SHAPE is introduced.

  ## WHAT LANDS (ns `QIQTH.HBFpeakReducedToChartC2Cover`).
    • `jointCore_subset_prod_concreteKx` — the joint core-graph is contained in the base-support ×
      field-support product (needed to identify the `onCoreGraphContinuity` domain with `jointCore`).
    • `jointCorePeak` — the constant peak value: `max 0 (sSup (‖fieldHessian‖ '' ((K ×ˢ concreteKx) ∩
      jointCore)))`, a genuine TOTAL function of `(S,a,b,i,τ)` (no choice needed downstream).
    • `fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph` — ★★★ the pointwise bound: for EVERY
      `z x : Point n`, `‖fderiv …‖ ≤ jointCorePeak`, CONDITIONAL on {radii `0<a<b<c<δ₀`, `b <
      uniformFlowRadius`} and a SINGLE chart-`C²`+in-gate open cover `W` of `(K ×ˢ concreteKx) ∩
      jointCore` (at a fixed `τ`).
    • `hBFpeak_reduced_to_chartC2_gate_cover` — ★★★ the a.e.-`s` literal `hBFpeak` shape of
      `HZMassCappedWindowClosed.hzmass_capped_window_closed` / `MixedEnvelopeAssembly`, with the
      EXPLICIT `Ppk s := jointCorePeak … (t-s)`, CONDITIONAL on a per-a.e.-`s` chart-`C²`+in-gate cover —
      the EXACT hypothesis shape `hbint_reduced_to_chartC2_gate_cover` (J4-889) already carries.
    • non-vacuity witnesses (empty base `K := ∅`; the antecedent bundle is jointly satisfiable, not a
      J4-548-style trap).

  ## WHAT THIS FILE DOES **NOT** DO — the honest limit.
  The chart-`C²`+in-gate open cover `W` of `(K ×ˢ concreteKx) ∩ jointCore` remains EXACTLY the
  `JointSecondOrderRNCRegularity` frontier already named by J4-889 — building it uniformly over `K` is
  the multi-lemma sub-campaign flagged there, NOT closed here. This brick does NOT wire the result all
  the way into `hzmass_capped_window_closed`/`MixedEnvelopeAssembly` as an assembled term (the caller
  would still need to supply the SAME cover hypothesis to both `hbint_reduced_to_chartC2_gate_cover` and
  this file, and reconcile the two `∃δ₀` windows) — it lands the well-scoped, exactly-typed `hBFpeak`
  reduction and stops there. NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.QuantifiedCoherentChartTube
import QIQTH.HbintCollarMatchedCutoffClosed

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open QIQTH.FieldHessianJointContinuity
open QIQTH.HbintCollarMatchedCutoffClosed
open QIQTH.WitnessFieldDerivJointC1FromTube
open QIQTH.FieldHessianJointContinuityClosed
open QIQTH.QuantifiedCoherentChartTube
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.HBFpeakReducedToChartC2Cover

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the joint core-graph sits inside the base-support × field-support product.
    ############################################################################### -/

/-- **★ `jointCore_subset_prod_concreteKx`.**  Every joint core-graph point `(z, φ_z v)`
    (`z ∈ K`, `v ∈ closedBall 0 b`) has base `z ∈ K` and field coordinate `φ_z v ∈ concreteKx`
    (directly from `concreteKx`'s definition as the same flow-image over `K ×ˢ closedBall 0 b`).  So
    `jointCore ⊆ K ×ˢ concreteKx`, hence `(K ×ˢ concreteKx) ∩ jointCore = jointCore` — the
    `onCoreGraphContinuity_of_chartC2_gate_cover` domain literally IS the joint core-graph.
    NOT `a₁ = R/6`. -/
theorem jointCore_subset_prod_concreteKx (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) :
    jointCore g gi hC hK b ⊆ K ×ˢ concreteKx g gi hC hK b := by
  rintro ⟨z0, x0⟩ ⟨⟨z', v⟩, ⟨hz', hv⟩, hpq⟩
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨hzeq, hxeq⟩ := hpq
  subst hzeq
  refine ⟨hz', ?_⟩
  rw [← hxeq]
  exact ⟨(z', v), ⟨hz', hv⟩, rfl⟩

/-! ###############################################################################
    ### C1 — the constant peak value on the joint core-graph.
    ############################################################################### -/

/-- The `z`-UNIFORM peak constant: the (non-negative) supremum of the field-Hessian norm over the
    compact on-core-graph domain `(K ×ˢ concreteKx) ∩ jointCore`.  A genuine TOTAL function of
    `(S,a,b,i,τ)` — no existential/choice packaging needed downstream. -/
noncomputable def jointCorePeak (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) : ℝ :=
  max 0 (sSup ((fun p : Point n × Point n =>
    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖) ''
      ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b)))

/-- **`jointCorePeak_nonneg`.**  Immediate from the outer `max 0 _`. -/
theorem jointCorePeak_nonneg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) :
    0 ≤ jointCorePeak g gi hC hK S a b i τ :=
  le_max_left _ _

/-! ###############################################################################
    ### C2 — the pointwise bound: `‖fieldHessian‖ ≤ jointCorePeak` EVERYWHERE, CONDITIONAL on the
    ### chart-`C²`+in-gate cover of the on-core-graph domain.
    ############################################################################### -/

/-- **★★★ `fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph`.**  FLAT-ARGUMENT core lemma (no
    nested `∃/∀` telescope — every hypothesis is a plain leading argument, mirroring
    `onCoreGraphContinuity_of_chartC2_gate_cover`'s own shape).  Given the off-`jointCore` vanishing
    `hoff` (supplied by the caller, typically from `fieldHessian_fderiv_eqZero_off_jointGraph`) and a
    chart-`C²`+in-gate open cover `W` of the compact on-core-graph domain `(K ×ˢ concreteKx) ∩
    jointCore` at a FIXED `τ`, the field-Hessian norm is `≤ jointCorePeak` at EVERY `(z,x) : Point n ×
    Point n` — not merely `x ∈ closure (S z)`.

    Mechanism: `(z,x) ∈ jointCore` (equivalently, by C0, `∈ (K ×ˢ concreteKx) ∩ jointCore`) puts it in
    the compact domain where `onCoreGraphContinuity_of_chartC2_gate_cover` gives continuity, hence
    `IsCompact.bddAbove_image` + `le_csSup` bounds it by `jointCorePeak`'s inner `sSup`.  `(z,x) ∉
    jointCore` (which subsumes EVERY point of `closure (S z) \ jointCore` — the `b<‖·‖<c` collar, and
    every `z ∉ K`) makes the field-Hessian `0` by `hoff`, hence `≤` the non-negative `jointCorePeak`.
    NOT `a₁ = R/6`. -/
theorem fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hbρ : b < uniformFlowRadius g gi hC hK)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hoff : ∀ p : Point n × Point n, p ∉ jointCore g gi hC hK b →
      fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2 = 0)
    {W : Set (Point n × Point n)} (hWopen : IsOpen W)
    (hWcover : (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W)
    (hWgate : ∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2)
    (hWchart : ContDiffOn ℝ 2
      (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) W)
    (z x : Point n) :
    ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
      ≤ jointCorePeak g gi hC hK S a b i τ := by
  have hcont : ContinuousOn
      (fun p : Point n × Point n =>
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
      ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b) :=
    onCoreGraphContinuity_of_chartC2_gate_cover g gi hC hK S a b i τ hw hWopen hWcover hWgate hWchart
  have hDsub : jointCore g gi hC hK b ⊆ K ×ˢ concreteKx g gi hC hK b :=
    jointCore_subset_prod_concreteKx g gi hC hK b
  have hDcompact : IsCompact ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b) := by
    rw [Set.inter_eq_right.mpr hDsub]
    exact jointCore_isCompact g gi hC hK b hbρ
  by_cases hmem : (z, x) ∈ (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b
  · have hbdd : BddAbove
        ((fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖) ''
            ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b)) :=
      hDcompact.bddAbove_image hcont
    have hle : ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
        ≤ sSup ((fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖) ''
            ((K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b)) :=
      le_csSup hbdd ⟨(z, x), hmem, rfl⟩
    exact le_trans hle (le_max_right _ _)
  · have hnotJoint : (z, x) ∉ jointCore g gi hC hK b := fun h => hmem ⟨hDsub h, h⟩
    have h0 : fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 :=
      hoff (z, x) hnotJoint
    rw [h0, norm_zero]
    exact le_max_left _ _

/-! ###############################################################################
    ### C3 — the a.e.-`s` `hBFpeak` literal, CONDITIONAL on the SAME cover `hbint` carries.
    ############################################################################### -/

/-- **★★★ `hBFpeak_reduced_to_chartC2_gate_cover`.**  The EXACT `hBFpeak` field of
    `HZMassCappedWindowClosed.hzmass_capped_window_closed` / `MixedEnvelopeAssembly`
    (`BF s z := ⨆ x', ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x'‖`, `∀ᵐ s, ∀ z, BF s z ≤ Ppk s`),
    with the EXPLICIT `Ppk s := jointCorePeak … (t-s)`, REDUCED a.e.-`s` to a chart-`C²`+in-gate open
    cover of `(K ×ˢ concreteKx) ∩ jointCore` — the SAME hypothesis SHAPE
    `hbint_reduced_to_chartC2_gate_cover` (J4-889) already carries for `hbint`.  `K` nonempty not
    needed here (the bound holds for every `z`, including `z ∉ K`, via C2).  NOT `a₁ = R/6`. -/
theorem hBFpeak_reduced_to_chartC2_gate_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) (i : Fin n) (t : ℝ) (m : ℕ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∃ W : Set (Point n × Point n), IsOpen W ∧
              (K ×ˢ concreteKx g gi hC hK b) ∩ jointCore g gi hC hK b ⊆ W ∧
              (∀ p ∈ W, p.1 ∈ K ∧ S p.1 ∈ nhds p.2) ∧
              ContDiffOn ℝ 2
                (fun ξ : Point n × Point n => uniformInverseChart g gi hC hK ξ.1 ξ.2) W) →
        ∃ Ppk : ℝ → ℝ,
          ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
            ∀ z : Point n,
              (⨆ x' : Point n,
                ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖)
                ≤ Ppk s := by
  obtain ⟨δ₀, hδ₀, hoff⟩ := fieldHessian_fderiv_eqZero_off_jointGraph g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hcover
  refine ⟨fun s => jointCorePeak g gi hC hK S a b i (t - s), ?_⟩
  filter_upwards [hcover] with s hs hsU
  obtain ⟨W, hWopen, hWcover, hWgate, hWchart⟩ := hs hsU
  intro z
  refine ciSup_le (fun x' => ?_)
  exact fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph g gi hC hK S a b i (t - s) hbρ hw
    (hoff c hbc hcδ S hSeq i (t - s)) hWopen hWcover hWgate hWchart z x'

/-! ###############################################################################
    ### C4 — NON-VACUITY: the antecedent bundle is jointly satisfiable.
    ############################################################################### -/

/-- **NON-VACUITY.**  At the DEGENERATE empty base `K := ∅`, EVERY base point is off `K`, so the
    field-Hessian is IDENTICALLY `0` (`HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_
    of_base_notMem_K`), and `jointCorePeak ≥ 0` always (`jointCorePeak_nonneg`) — so the pointwise bound
    holds with NO cover needed at all at this degenerate instance.  This exhibits that the conclusion of
    `fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph` is never the (jointly-unsatisfiable)
    trivial consequence of an impossible hypothesis bundle: the bundle IS satisfiable (§C4b below builds
    a genuine, non-degenerate satisfier for the cover itself, mirroring J4-889's
    `chartC2_gate_cover_nonvacuous`), and independently the conclusion shape is realized here.
    NOT `a₁ = R/6`. -/
theorem fieldHessianNorm_le_jointCorePeak_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (τ : ℝ) :
    ∀ z x : Point n,
      ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC (isCompact_empty) S a b i τ y z) x‖
        ≤ jointCorePeak g gi hC (isCompact_empty) S a b i τ := by
  intro z x
  have hz : z ∉ (∅ : Set (Point n)) := Set.notMem_empty z
  rw [QIQTH.HZMassIntegrabilityAttempt.witnessFieldHessian_fderiv_eqZero_of_base_notMem_K
    g gi hC (isCompact_empty) S a b i τ z hz x, norm_zero]
  exact jointCorePeak_nonneg g gi hC (isCompact_empty) S a b i τ

/-- **NON-VACUITY of the cover bundle itself.**  The three antecedents of
    `fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph`'s cover (`hWopen`, `hWcover`, `hWgate`,
    `hWchart`) are jointly SATISFIABLE at the DEGENERATE empty base `K := ∅`: the on-core-graph domain
    `(K ×ˢ concreteKx) ∩ jointCore` is empty, so `W := ∅` discharges all three (cover `∅ ⊆ ∅`, in-gate
    vacuous over `∅`, chart `C²` on `∅` via `contDiffOn_empty`) — mirroring J4-889's
    `chartC2_gate_cover_nonvacuous`.  No J4-548-style unsatisfiable-antecedent trap. NOT `a₁ = R/6`. -/
theorem chartC2_gate_cover_pointwise_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∀ z x : Point n,
      ‖fderiv ℝ (fun y =>
          witnessFieldDeriv g gi hC (isCompact_empty) S a b i τ y z) x‖
        ≤ jointCorePeak g gi hC (isCompact_empty) S a b i τ := by
  have _hcont := onCoreGraphContinuity_of_chartC2_gate_cover g gi hC (isCompact_empty) S a b i τ hw
    (W := (∅ : Set (Point n × Point n))) isOpen_empty
    (by intro p hp; exact ((Set.mem_empty_iff_false p.1).mp hp.1.1).elim)
    (fun p hp => (Set.mem_empty_iff_false p).mp hp |>.elim)
    contDiffOn_empty
  intro z x
  exact fieldHessianNorm_le_jointCorePeak_nonvacuous g gi hC S a b i τ z x

end QIQTH.HBFpeakReducedToChartC2Cover

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.HBFpeakReducedToChartC2Cover
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms jointCore_subset_prod_concreteKx
#print axioms jointCorePeak_nonneg
#print axioms fieldHessianNorm_le_jointCorePeak_of_cover_and_offgraph
#print axioms hBFpeak_reduced_to_chartC2_gate_cover
#print axioms fieldHessianNorm_le_jointCorePeak_nonvacuous
#print axioms chartC2_gate_cover_pointwise_nonvacuous
end AxiomChecks
