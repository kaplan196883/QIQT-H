/-
  FieldHessianJointContinuity — J4-877: the `z`-CONTINUITY (Berge parametrised-supremum) residual of
  `hbint` (J4-876) REDUCED to a single clean JOINT `(z,x)`-continuity residual of the field-Hessian
  norm on a FIXED compact `K ×ˢ Kx`, via a from-scratch `ContinuousOn`-Berge engine and a
  `univ`-supremum localization.  This DISCHARGES the Berge/supremum scaffolding and the
  support-localization scaffolding that `HbintReducedToZContinuity` (J4-876) left inside `hbint`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the `z`-continuity
  residual of the `hbint` field of `MixedDirectionsFieldHessianEnvelope` to the JOINT `(z,x)`-continuity
  of the field-Hessian norm on a fixed compact `K ×ˢ Kx`; it does **NOT** close `hbint`.  No `sorry`, no
  new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ADVANCE — the `ContinuousOn`-Berge engine, and the `univ`-supremum localization.

  `HbintReducedToZContinuity` (J4-876) reduced `hbint` to the residual `ContinuousOn (z ↦ BL s z · BF s z)
  K`, where `BF s z := ⨆ x : Point n, ‖fderiv (y ↦ witnessFieldDeriv … y z) x‖` is an UNCOUNTABLE
  supremum over the WHOLE field space `x : Point n`.  Its own diagnosis: closing this needs a
  Berge-maximum-theorem argument fed by JOINT `(x,z)` control of the field-Hessian.  Mathlib has only the
  GLOBAL Berge lemma `IsCompact.continuous_sSup` (which needs `Continuous ↿f` — false here across `∂K`,
  a vacuity trap).  This brick supplies the missing `ContinuousOn` engine and localizes the `univ`-sup:

    1. `continuousOn_sSup_image_of_continuousOn` — ★ the from-scratch `ContinuousOn`-Berge engine: a
       function `f : Z → X → ℝ` that is `ContinuousOn (↿f)` on `P ×ˢ Kx` (`Kx` compact) has
       `z ↦ sSup (f z '' Kx)` `ContinuousOn P`.  Proved by transporting `IsCompact.continuous_sSup` to the
       compact SUBTYPE `↥Kx` (which has `CompactSpace`), NO global continuity across `∂K` demanded.
    2. `ciSup_eq_sSup_image_of_vanishing` — ★ the localization: a NONNEGATIVE `F : X → ℝ` that VANISHES
       off a nonempty compact `Kx` has `(⨆ x, F x) = sSup (F '' Kx)` (`BddAbove (F '' Kx)`).  This turns
       the `univ`-sup `BF` into a compact-set `sSup` the Berge engine consumes.
    3. `BF_zContinuousOn_of_jointContinuousOn` — ★★ chaining (1)+(2): given a fixed compact `Kx` off which
       the field-Hessian vanishes (`z ∈ K`) and JOINT `(z,x)`-continuity of the field-Hessian norm on
       `K ×ˢ Kx`, `BF` is `ContinuousOn K`.
    4. `hbint_of_jointContinuousOn` — ★★★ the `hbint` field, REDUCED a.e. to the joint-continuity residual
       (with `BL` continuity + support vanishing), via `HbintReducedToZContinuity.hbint_of_zContinuousOn_K`.

  So the Berge/supremum + support-localization scaffolding of `hbint`'s `z`-continuity residual is
  DISCHARGED; the honest remaining content is the JOINT `(z,x)`-continuity of the field-Hessian norm on
  the fixed compact `K ×ˢ Kx` — a genuinely new analytic object one derivative above the banked FIRST
  field-derivative slice joint continuity (`UngatedChainRule.witnessFieldDeriv_jointContinuousOn`), which
  remains open.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HbintReducedToZContinuity
import QIQTH.HGateBoundedConcreteDischarge
import QIQTH.FlowJointContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.HZMassIntegrabilityAttempt
open scoped Topology BigOperators

namespace QIQTH.FieldHessianJointContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### C0 — the general analytic engines (provider-independent, reusable).
    ############################################################################### -/

/-- **★ `continuousOn_sSup_image_of_continuousOn` — the `ContinuousOn`-Berge engine.**  If
    `f : Z → X → ℝ` is `ContinuousOn (fun p => f p.1 p.2)` on `P ×ˢ Kx` with `Kx` COMPACT, then the
    parametrised supremum `z ↦ sSup (f z '' Kx)` is `ContinuousOn P`.  Proved by transporting Mathlib's
    GLOBAL `IsCompact.continuous_sSup` to the compact SUBTYPE `↥Kx` (which carries `CompactSpace`, so
    `univ` is compact), then converting `Continuous` on `↥P` back to `ContinuousOn P` — NO global
    continuity of `↿f` across `Pᶜ` is demanded (avoiding the `∂K` vacuity trap).  NOT `a₁ = R/6`. -/
theorem continuousOn_sSup_image_of_continuousOn
    {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    {P : Set Z} {Kx : Set X} (hKx : IsCompact Kx)
    (f : Z → X → ℝ) (hf : ContinuousOn (fun p : Z × X => f p.1 p.2) (P ×ˢ Kx)) :
    ContinuousOn (fun z => sSup (f z '' Kx)) P := by
  haveI : CompactSpace ↥Kx := isCompact_iff_compactSpace.mp hKx
  set f' : ↥P → ↥Kx → ℝ := fun z x => f ↑z ↑x with hf'def
  have hcont' : Continuous (fun p : ↥P × ↥Kx => f' p.1 p.2) := by
    have hmap : Continuous (fun p : ↥P × ↥Kx => ((↑p.1 : Z), (↑p.2 : X))) := by fun_prop
    have hmem : ∀ p : ↥P × ↥Kx, ((↑p.1 : Z), (↑p.2 : X)) ∈ P ×ˢ Kx := fun p => ⟨p.1.2, p.2.2⟩
    exact hf.comp_continuous hmap hmem
  have hberge : Continuous (fun z : ↥P => sSup (f' z '' (univ : Set ↥Kx))) :=
    IsCompact.continuous_sSup isCompact_univ hcont'
  have himg : ∀ z : ↥P, f' z '' (univ : Set ↥Kx) = f ↑z '' Kx := by
    intro z
    ext y
    simp only [hf'def, Set.image_univ, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨↑x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [continuousOn_iff_continuous_restrict]
  refine hberge.congr (fun z => ?_)
  show sSup (f' z '' univ) = sSup (f ↑z '' Kx)
  rw [himg]

/-- **★ `ciSup_eq_sSup_image_of_vanishing` — the `univ`-supremum localization.**  A NONNEGATIVE function
    `F : X → ℝ` that VANISHES off a NONEMPTY compact set `Kx` (with `BddAbove (F '' Kx)`) satisfies
    `(⨆ x, F x) = sSup (F '' Kx)`.  Off `Kx` the value is `0 ≤ sSup (F '' Kx)` (the sup is `≥ 0` as `Kx`
    is nonempty and `F ≥ 0`), so the whole-space supremum equals the compact-set supremum.  This turns the
    uncountable `univ`-sup `BF` into a compact-set `sSup` the Berge engine consumes.  NOT `a₁ = R/6`. -/
theorem ciSup_eq_sSup_image_of_vanishing
    {X : Type*} {Kx : Set X} (hKxne : Kx.Nonempty)
    (F : X → ℝ) (hnonneg : ∀ x, 0 ≤ F x) (hvanish : ∀ x ∉ Kx, F x = 0)
    (hbddKx : BddAbove (F '' Kx)) :
    (⨆ x, F x) = sSup (F '' Kx) := by
  obtain ⟨x₀, hx₀⟩ := hKxne
  haveI : Nonempty X := ⟨x₀⟩
  have hsup_nonneg : 0 ≤ sSup (F '' Kx) :=
    le_trans (hnonneg x₀) (le_csSup hbddKx ⟨x₀, hx₀, rfl⟩)
  obtain ⟨B, hB⟩ := id hbddKx
  have hBnn : 0 ≤ max B 0 := le_max_right _ _
  have hbddrange : BddAbove (Set.range F) := by
    refine ⟨max B 0, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ Kx
    · exact le_trans (hB ⟨x, hx, rfl⟩) (le_max_left _ _)
    · rw [hvanish x hx]; exact hBnn
  refine le_antisymm ?_ ?_
  · refine ciSup_le (fun x => ?_)
    by_cases hx : x ∈ Kx
    · exact le_csSup hbddKx ⟨x, hx, rfl⟩
    · rw [hvanish x hx]; exact hsup_nonneg
  · refine csSup_le ⟨F x₀, ⟨x₀, hx₀, rfl⟩⟩ ?_
    rintro _ ⟨x, _, rfl⟩
    exact le_ciSup hbddrange x

/-- **★★ `continuousOn_ciSup_of_jointContinuousOn` — the ABSTRACT `z`-continuity engine.**  For an
    ARBITRARY family `F : Z → Point n → ℝ` that is NONNEGATIVE, VANISHES off a nonempty compact `Kx` (for
    `z ∈ P`), and is JOINTLY `ContinuousOn (P ×ˢ Kx)`, the `univ`-supremum `z ↦ ⨆ x, F z x` is
    `ContinuousOn P`.  Chains `continuousOn_sSup_image_of_continuousOn` (Berge) with
    `ciSup_eq_sSup_image_of_vanishing` (localization).  Fully abstract — NO field terms — so the concrete
    instantiation (below) meets the heavy `witnessFieldDeriv` terms only through a single syntactic
    beta-match.  NOT `a₁ = R/6`. -/
theorem continuousOn_ciSup_of_jointContinuousOn
    {Z : Type*} [TopologicalSpace Z] {P : Set Z}
    {Kx : Set (Point n)} (hKx : IsCompact Kx) (hKxne : Kx.Nonempty)
    (F : Z → Point n → ℝ) (hnonneg : ∀ z x, 0 ≤ F z x)
    (hvanish : ∀ z ∈ P, ∀ x ∉ Kx, F z x = 0)
    (hjoint : ContinuousOn (fun p : Z × Point n => F p.1 p.2) (P ×ˢ Kx)) :
    ContinuousOn (fun z => ⨆ x : Point n, F z x) P := by
  have hberge : ContinuousOn (fun z => sSup (F z '' Kx)) P :=
    continuousOn_sSup_image_of_continuousOn hKx F hjoint
  refine hberge.congr (fun z hz => ?_)
  have hFzOn : ContinuousOn (F z) Kx :=
    hjoint.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun x hx => ⟨hz, hx⟩)
  exact ciSup_eq_sSup_image_of_vanishing hKxne (F z) (fun x => hnonneg z x)
    (fun x hx => hvanish z hz x hx) (hKx.bddAbove_image hFzOn)

/-! ###############################################################################
    ### C1 — `BF` `z`-continuity from JOINT `(z,x)` field-Hessian-norm continuity.
    ############################################################################### -/

/-- **★★ `BF_zContinuousOn_of_jointContinuousOn`.**  The envelope `BF s z := ⨆ x, ‖fderiv (y ↦
    witnessFieldDeriv … y z) x‖` is `ContinuousOn K` in the base `z`, given: a FIXED nonempty compact `Kx`
    off which the field-Hessian vanishes for every `z ∈ K` (`hvanish`); and JOINT `(z,x)`-continuity of the
    field-Hessian norm on `K ×ˢ Kx` (`hjoint`).  A direct instantiation of the abstract engine
    `continuousOn_ciSup_of_jointContinuousOn` at the field-Hessian norm.  NOT `a₁ = R/6`. -/
theorem BF_zContinuousOn_of_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) {Kx : Set (Point n)} (hKx : IsCompact Kx) (hKxne : Kx.Nonempty)
    (hvanish : ∀ z ∈ K, ∀ x ∉ Kx,
      fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0)
    (hjoint : ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y p.1) p.2‖)
        (K ×ˢ Kx)) :
    ContinuousOn
      (fun z => ⨆ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖) K :=
  continuousOn_ciSup_of_jointContinuousOn hKx hKxne
    (fun z x => ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖)
    (fun z x => norm_nonneg _)
    (fun z hz x hx => by
      show ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖ = 0
      rw [hvanish z hz x hx]; exact norm_zero)
    hjoint

/-! ###############################################################################
    ### C2 — the `hbint` field, REDUCED a.e. to the joint-continuity residual.
    ############################################################################### -/

/-- **★★★ J4-877 — `hbint_of_jointContinuousOn`.**  The EXACT `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE envelope `BF s z := ⨆ x, ‖fderiv …‖`, REDUCED
    a.e. to: `BL`-continuity on `K`; a fixed nonempty compact `Kx` off which the field-Hessian vanishes
    (`z ∈ K`); and JOINT `(z,x)`-continuity of the field-Hessian norm on `K ×ˢ Kx`.  Chains
    `BF_zContinuousOn_of_jointContinuousOn` (this file) through
    `HbintReducedToZContinuity.hbint_of_zContinuousOn_K` (J4-876, the compact-support integrability
    engine).  So `hbint`'s Berge/supremum + support-localization scaffolding is DISCHARGED; the honest
    residual is the joint `(z,x)`-continuity of the field-Hessian norm.  NOT `a₁ = R/6`. -/
theorem hbint_of_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (BL : ℝ → Point n → ℝ)
    {Kx : Set (Point n)} (hKx : IsCompact Kx) (hKxne : Kx.Nonempty)
    (hBL : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K)
    (hvanish : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ z ∈ K, ∀ x ∉ Kx,
          fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x = 0)
    (hjoint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ContinuousOn
          (fun p : Point n × Point n =>
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y p.1) p.2‖)
          (K ×ˢ Kx)) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z *
        (⨆ x : Point n,
          ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  refine QIQTH.HbintReducedToZContinuity.hbint_of_zContinuousOn_K
    g gi hC hK S a b i t m BL ?_
  filter_upwards [hBL, hvanish, hjoint] with s hBLs hvans hjs hsU
  exact (hBLs hsU).mul
    (BF_zContinuousOn_of_jointContinuousOn g gi hC hK S a b i (t - s) hKx hKxne
      (hvans hsU) (hjs hsU))

/-! ###############################################################################
    ### C2b — the CONCRETE `Kx` and off-`Kx` vanishing, DISCHARGED from banked infra.
    ### (Sharpens the reduction: the vanishing + support scaffolding is now discharged,
    ###  leaving the JOINT continuity as the SOLE genuine residual.)
    ############################################################################### -/

/-- The fixed compact field support `Kx := φ '' (K ×ˢ closedBall 0 b)` — the image of the base support
    times the closed velocity ball under the joint flow.  Contains every per-`z` core
    `closure (φ_z '' ball 0 b)` (`z ∈ K`). -/
noncomputable def concreteKx (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) : Set (Point n) :=
  (fun p : Point n × Point n => uniformFlowExp g gi hC hK p.1 p.2) '' (K ×ˢ Metric.closedBall 0 b)

/-- **★ `concreteKx_isCompact`.**  `concreteKx` is compact: the joint flow is `ContinuousOn`
    `K ×ˢ ball 0 (uniformFlowRadius)` (`uniformFlowExp_joint_continuousOn`), restricts to the compact
    `K ×ˢ closedBall 0 b` (`b < uniformFlowRadius`), whose continuous image is compact.  NOT `a₁ = R/6`. -/
theorem concreteKx_isCompact (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    IsCompact (concreteKx g gi hC hK b) := by
  have hsub : (K ×ˢ Metric.closedBall (0 : Point n) b)
      ⊆ (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
    Set.prod_mono (le_refl K) (Metric.closedBall_subset_ball hbρ)
  have hcont : ContinuousOn (fun p : Point n × Point n => uniformFlowExp g gi hC hK p.1 p.2)
      (K ×ˢ Metric.closedBall (0 : Point n) b) :=
    (QIQTH.FlowJointContinuity.uniformFlowExp_joint_continuousOn g gi hC hK).mono hsub
  exact (hK.prod (isCompact_closedBall (0 : Point n) b)).image_of_continuousOn hcont

/-- **★ `concreteKx_nonempty`.**  For `K` nonempty and `0 ≤ b`, `concreteKx` is nonempty (`φ z₀ 0` for
    any `z₀ ∈ K`, since `0 ∈ closedBall 0 b`).  NOT `a₁ = R/6`. -/
theorem concreteKx_nonempty (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) (hKne : K.Nonempty) (hb : 0 ≤ b) :
    (concreteKx g gi hC hK b).Nonempty := by
  obtain ⟨z₀, hz₀⟩ := hKne
  exact ⟨uniformFlowExp g gi hC hK z₀ 0,
    ⟨(z₀, 0), ⟨hz₀, by simp [Metric.mem_closedBall, hb]⟩, rfl⟩⟩

/-- **★ `core_subset_concreteKx`.**  For `z ∈ K` and `b < uniformFlowRadius`, the per-`z` compact core
    `closure (φ_z '' ball 0 b)` is contained in `concreteKx`.  Each `φ_z v` (`v ∈ ball 0 b ⊆ closedBall 0
    b`) is `φ (z,v)` with `(z,v) ∈ K ×ˢ closedBall 0 b`, so `φ_z '' ball 0 b ⊆ concreteKx`; closing on the
    compact (hence closed) `concreteKx` gives the closure inclusion.  NOT `a₁ = R/6`. -/
theorem core_subset_concreteKx (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (b : ℝ) (hbρ : b < uniformFlowRadius g gi hC hK)
    (z : Point n) (hz : z ∈ K) :
    closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b)
      ⊆ concreteKx g gi hC hK b := by
  have hballsub : uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b
      ⊆ concreteKx g gi hC hK b := by
    rintro w ⟨v, hv, rfl⟩
    exact ⟨(z, v), ⟨hz, Metric.ball_subset_closedBall hv⟩, rfl⟩
  exact closure_minimal hballsub (concreteKx_isCompact g gi hC hK b hbρ).isClosed

/-- **★★ `fieldHessian_vanish_off_concreteKx`.**  DISCHARGES the off-`Kx` vanishing hypothesis of
    `BF_zContinuousOn_of_jointContinuousOn` at `Kx = concreteKx`, for the CONCRETE flow-ball gate:
    a.e. `s`, for `z ∈ K` and any `x ∉ concreteKx`, the field-Hessian is `0` — because
    `x ∉ concreteKx ⊇ core(z)` puts `x` off the core, where `fieldHessian_zero_offCore` (J4-873) gives
    vanishing.  Radii `0 < a < b < c < δ₀`, `b < uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem fieldHessian_vanish_off_concreteKx (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbρ : b < uniformFlowRadius g gi hC hK) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i : Fin n) (τ : ℝ) (z : Point n), z ∈ K →
          ∀ x ∉ concreteKx g gi hC hK b,
            fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x = 0 := by
  obtain ⟨δ₀, hδ₀, hoff⟩ :=
    QIQTH.HGateBoundedConcreteDischarge.fieldHessian_zero_offCore g gi hC hK a b ha hab
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq i τ z hz x hxKx
  have hxcore : x ∉ closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) b) :=
    fun h => hxKx (core_subset_concreteKx g gi hC hK b hbρ z hz h)
  exact hoff c hbc hcδ S hSeq i τ z hz x hxcore

/-- **★★★ J4-877 — `hbint_concrete_of_jointContinuousOn`.**  The `hbint` field of
    `MixedDirectionsFieldHessianEnvelope`, at the CONCRETE flow-ball gate, REDUCED a.e. to the SOLE genuine
    residual — JOINT `(z,x)`-continuity of the field-Hessian norm on `K ×ˢ concreteKx` — PLUS the standard
    `BL`-continuity.  The off-`Kx` vanishing + support scaffolding is DISCHARGED internally
    (`fieldHessian_vanish_off_concreteKx`, `concreteKx_isCompact`, `concreteKx_nonempty`).  Requires `K`
    nonempty (else the goal is degenerate but the concrete `Kx` machinery needs an inhabitant); radii
    `0 < a < b < c < δ₀`, `b < uniformFlowRadius`.  NOT `a₁ = R/6`. -/
theorem hbint_concrete_of_jointContinuousOn (g gi : Point n → Fin n → Fin n → ℝ)
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
              (K ×ˢ concreteKx g gi hC hK b)) →
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
          Integrable (fun z => BL s z *
            (⨆ x : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖)) volume := by
  obtain ⟨δ₀, hδ₀, hvan⟩ := fieldHessian_vanish_off_concreteKx g gi hC hK a b ha hab hbρ
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hbc hcδ S hSeq hBL hjoint
  have hb0 : (0 : ℝ) ≤ b := le_of_lt (lt_trans ha hab)
  refine hbint_of_jointContinuousOn g gi hC hK S a b i t m BL
    (concreteKx_isCompact g gi hC hK b hbρ) (concreteKx_nonempty g gi hC hK b hKne hb0)
    hBL ?_ hjoint
  filter_upwards with s hsU
  exact fun z hz x hx => hvan c hbc hcδ S hSeq i (t - s) z hz x hx

/-! ###############################################################################
    ### C3 — NON-VACUITY of the joint-continuity residual.
    ############################################################################### -/

/-- **NON-VACUITY.**  The joint-continuity residual of `BF_zContinuousOn_of_jointContinuousOn` is
    inhabited at the empty gate `S := fun _ => ∅` with any nonempty compact `Kx`: there the field is
    identically `0` on the gate, the field-Hessian norm is the constant `0`, hence trivially jointly
    `ContinuousOn` and vanishing off `Kx`.  So the reduction fires — no unsatisfiable antecedent (no
    J4-548/847 trap), never the conclusion.  (The genuinely non-trivial residual — joint `(z,x)`-continuity
    of the CONCRETE field-Hessian norm — is the honest new-analysis content that remains open.)
    NOT `a₁ = R/6`. -/
theorem BF_residual_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (τ : ℝ)
    {Kx : Set (Point n)} :
    ContinuousOn
        (fun p : Point n × Point n =>
          ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
        (K ×ˢ Kx) := by
  have hzero : (fun p : Point n × Point n =>
      ‖fderiv ℝ (fun y =>
        witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ y p.1) p.2‖)
      = fun _ => (0 : ℝ) := by
    funext p
    rw [QIQTH.ChartJetXUniformBound.witnessFieldHessian_fderiv_eqZero_of_notMem_closure
      g gi hC hK (fun _ => (∅ : Set (Point n))) a b i τ p.1 p.2
      (by simp)]
    exact norm_zero
  rw [hzero]; exact continuousOn_const

end QIQTH.FieldHessianJointContinuity

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.FieldHessianJointContinuity
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms continuousOn_sSup_image_of_continuousOn
#print axioms ciSup_eq_sSup_image_of_vanishing
#print axioms continuousOn_ciSup_of_jointContinuousOn
#print axioms BF_zContinuousOn_of_jointContinuousOn
#print axioms hbint_of_jointContinuousOn
#print axioms concreteKx_isCompact
#print axioms concreteKx_nonempty
#print axioms core_subset_concreteKx
#print axioms fieldHessian_vanish_off_concreteKx
#print axioms hbint_concrete_of_jointContinuousOn
#print axioms BF_residual_nonvacuous
end AxiomChecks
