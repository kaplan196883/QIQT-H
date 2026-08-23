/-
  HCompVbaseVevalLeftInverseBridge — J4-1052: the witness-bundle IDENTIFICATION attempt flagged by
  J4-1051's honest scope map ("option (a): a comparison theorem identifying J4-1050's and
  `nb_common_chart_radius`'s two independent CoV witness bundles at a shared V/f'").

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1050's literal `kPrime` CoV capstone exposes a base-slot left-inverse `Vbase` of
  `Wb(z) := uniformInverseChart z x` (from `BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_
  generalK`, on an open set `S' ∋ x`). `ChartEvalSlotRadiusMerge.nb_common_chart_radius` (J4-1015)
  exposes an eval-slot left-inverse `Veval` (plus derivative field `f'`) of `We(z) := uniformInverseChart
  x z` (from `ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0`, on `ball x ρ`). J4-1051's `gpt-5.6-sol`
  consult (Q2) confirmed these remain two SEPARATE existential tuples that no prior file relates.

  `EvalBaseSlotCoordinateBridge` (J4-1048) banked the ABSTRACT algebraic facts (`bridge_image_eq`,
  `bridge_left_inverse`, `bridge_hasFDerivAt`, `bridge_det_abs`) relating any `Wb`/`We` pair satisfying a
  raw pointwise bridge `Wb z = -T(We z)`, plus the CONCRETE raw bridge radius for `uniformInverseChart`/
  `terminalVelAt` — but explicitly did NOT instantiate the abstract facts at the two ACTUAL bundles above
  (its own honesty firewall: "does NOT instantiate §1's abstract facts at J4-1012's/J4-1046's ACTUAL
  `V`/`f'` objects … remains a SEPARATE, NOT-attempted next step").

  THIS DISPATCH attempts exactly that instantiation. A `gpt-5.6-sol` (high) consult BEFORE writing this
  file confirmed: (1) the instantiation of `bridge_left_inverse` at the two real bundles, on the concrete
  shared domain `D := S' ∩ ball x (min r ρ)`, is architecturally sound and non-vacuous — `D` is open,
  contains `x` (since `x ∈ S'` and `min r ρ > 0`), and the required `hVb`/`hVe` hypotheses are literally
  the bundles' own exposed left-inverse facts restricted to `D`, no circularity; (2) verdict
  **GO-BUT-LIMITED-USE**: the resulting relation `∀ w ∈ We '' D, Vbase (-T w) = Veval w` is an honest
  algebraic IDENTIFICATION of the two left-inverses through `T := terminalVelAt x` alone — it does
  **NOT** literally identify `Vbase = Veval` (they are genuinely different functions, related only via
  `T`), and it does **NOT** enable an integral change-of-variables substitution `w ↦ -T(w)`, because a
  measure-transport / Jacobian control for `T` is missing except pointwise at the single point `z = x`
  (where `T`'s differentiability is actually known) — useless for an integral bound. Sol's flagged
  higher-priority alternative (a pointwise weight/Jacobian comparison pulled back to the shared source
  domain `D`, avoiding `T` entirely) is NOT attempted here — it is a separate, larger, unattempted task.

  THIS FILE supplies `vbase_veval_left_inverse_bridge` — the concrete instantiation of
  `bridge_left_inverse` at the actual `Vbase` (from `BaseSlotM1M4Assembly`) and `Veval` (from
  `ChartIFTPackageGeneralQ0`) bundles, on the shared domain `D`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`. It resolves
  ONLY the algebraic left-inverse relation between the two independently-packaged CoV witnesses, per
  Sol's GO-BUT-LIMITED-USE verdict. It does **NOT**:
    • identify `Vbase` and `Veval` as the SAME function — they remain genuinely different, related only
      through `T := terminalVelAt x`;
    • establish any Jacobian/derivative relation between the two bundles generically (only at the single
      point `z = x`, per `EvalBaseSlotCoordinateBridge`'s own honesty note on `T`'s regularity — NOT
      attempted here, and not useful for an integral bound even if attempted);
    • enable an integral change-of-variables substitution through `T`, or compose into any bound on
      `nb`'s `term1`;
    • touch the amplitude/weight-domination question (J4-1012's/J4-879's moment-weight comparison),
      which remains entirely separate and unresolved;
    • discharge `hxmem`'s GENERAL reach over all of `K` (remains DEFINITIVELY CLOSED OFF, cp988–991).
  `Bfac`'s other 3 summands and `fb` remain untouched. No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited (NEW FILE).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.EvalBaseSlotCoordinateBridge
import QIQTH.BaseSlotM1M4Assembly
import QIQTH.ChartIFTPackageGeneralQ0

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.EvalBaseSlotCoordinateBridge
open scoped Topology

namespace QIQTH.HCompVbaseVevalLeftInverseBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `vbase_veval_left_inverse_bridge`.**  The concrete witness-bundle identification: for the
    BASE-slot left-inverse `Vbase` of `Wb(z) := uniformInverseChart z x` (from `BaseSlotM1M4Assembly`,
    valid on `S' ∋ x`) and the EVAL-slot left-inverse `Veval` of `We(z) := uniformInverseChart x z`
    (from `ChartIFTPackageGeneralQ0`, valid on `ball x ρ`), there is a genuinely SHARED open domain
    `D := S' ∩ ball x (min r ρ)` (`x ∈ D`) on which the two left-inverses are related through
    `T := terminalVelAt x` alone:
        `∀ w ∈ We '' D, Vbase (-T w) = Veval w`.
    Confirmed GO-BUT-LIMITED-USE by `gpt-5.6-sol` (high) before this file was written: this does NOT
    identify `Vbase = Veval`, and does NOT enable an integral CoV substitution (no Jacobian control for
    `T` off the single point `z = x`). NOT `a₁ = R/6`. -/
theorem vbase_veval_left_inverse_bridge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxint : x ∈ interior K) :
    ∃ (S' : Set (Point n)) (Vbase : Point n → Point n)
      (ρ : ℝ) (hρ : 0 < ρ) (Veval : Point n → Point n)
      (D : Set (Point n)),
      IsOpen D ∧ x ∈ D ∧
      ∀ w ∈ (fun z => uniformInverseChart g gi hC hK x z) '' D,
        Vbase (-terminalVelAt g gi hC hK x w) = Veval w := by
  have hxKnhds : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨S', Vbase, hS'open, hxS', _hinj_b, hVbase, _hfd_b, _hJpos_b⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hxint
  obtain ⟨ρ, hρ, Veval, f', _hballmeas, _hfd_e, _hinj_e, hVeval, _hJpos_e, _hnbhd⟩ :=
    QIQTH.ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0 g gi hC hK hxint
  obtain ⟨r, hr, hbridgeRaw⟩ :=
    QIQTH.EvalBaseSlotCoordinateBridge.evalBase_slot_coordinate_bridge_radius g gi hC hK hxKnhds
  set m : ℝ := min r ρ with hmdef
  have hm : 0 < m := lt_min hr hρ
  set D : Set (Point n) := S' ∩ Metric.ball x m with hDdef
  have hDopen : IsOpen D := hS'open.inter Metric.isOpen_ball
  have hxD : x ∈ D := ⟨hxS', Metric.mem_ball_self hm⟩
  refine ⟨S', Vbase, ρ, hρ, Veval, D, hDopen, hxD, ?_⟩
  have hbridge : ∀ z ∈ D, uniformInverseChart g gi hC hK z x
      = -terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z) := by
    intro z hz
    have hzr : dist z x < r :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_left _ _)
    exact hbridgeRaw z hzr
  have hVb : ∀ z ∈ D, Vbase (uniformInverseChart g gi hC hK z x) = z :=
    fun z hz => hVbase z hz.1
  have hVe : ∀ z ∈ D, Veval (uniformInverseChart g gi hC hK x z) = z := by
    intro z hz
    have hzρ : dist z x < ρ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz.2) (min_le_right _ _)
    exact hVeval z (Metric.mem_ball.mpr hzρ)
  exact QIQTH.EvalBaseSlotCoordinateBridge.bridge_left_inverse
    (fun z => uniformInverseChart g gi hC hK z x) (fun z => uniformInverseChart g gi hC hK x z)
    (terminalVelAt g gi hC hK x) Vbase Veval D hbridge hVb hVe

end QIQTH.HCompVbaseVevalLeftInverseBridge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompVbaseVevalLeftInverseBridge
#print axioms vbase_veval_left_inverse_bridge
end AxiomChecks
