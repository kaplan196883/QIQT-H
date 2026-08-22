/-
  ChartEvalSlotDomainContainment — J4-1014: the domain-containment fact Sol `gpt-5.6-sol` (high,
  J4-1013's dispatch plan-review) flagged as missing — `W_x''(ball x ρ) ⊆ ball 0 R` — derived from the
  ALREADY-BANKED `ContDiffAt ℝ 2` + diagonal-value facts of `JointRNCRegularityInterfaceLocalGeneralK`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1012's `evalSlot_terminalVel_weighted_CoV` transports a weighted integral over
  `ball x ρ` (ρ from an IFT-package existential) onto the chart-image integral over
  `W_x '' (ball x ρ)`, `W_x := uniformInverseChart g gi hC hK x`.  J4-1013's honesty firewall recorded
  precisely the missing piece needed to reconcile this image with `terminalVelAt_chartReplace_
  sliver_bound`'s domain `ball 0 R` (R an INDEPENDENT existential, from `terminalVelAt_nearIsometry_
  data`, J4-879): "no domain-containment fact `W_x''(ball x ρ) ⊆ ball 0 R` is derivable from the banked
  chart∘exp=id germ alone — would need `ContinuousAt W_x x` with `W_x x = 0`, not yet banked in usable
  form."

  Both ingredients Sol named turn out to ALREADY be banked, in
  `JointRNCRegularityInterfaceLocalGeneralK.lean` (J4-884/1006 campaign), at GENERAL interior `x` and
  GENERAL compact `K` — exactly the generality `nb`'s assembly needs:
    • `uniformInverseChart_slice_contDiffAt_diag_generalK : ContDiffAt ℝ 2 W_x x`
      (⟹ `ContinuousAt W_x x` via `ContDiffAt.continuousAt`, one Mathlib step);
    • `uniformInverseChart_slice_value_diag_generalK : W_x x = 0`.

  THIS FILE supplies the assembly Sol's finding called for, gpt-5.6-sol (high, this dispatch,
  plan-reviewed before Lean) confirming the route is genuinely mechanical (via
  `Metric.continuousAt_iff` + the pointwise unwinding `dist (W_x z) 0 = ‖W_x z‖`) with NO additional
  analytic content:
    • `uniformInverseChart_slice_ball_mapsTo_diag_generalK` — for ARBITRARY interior `x`, compact `K`,
      and ARBITRARY target radius `R > 0`, produces an explicit `ρ > 0` with
          `Set.MapsTo W_x (Metric.ball x ρ) (Metric.ball 0 R)`.
    • `uniformInverseChart_slice_ball_image_subset_diag_generalK` — the equivalent SET-IMAGE form
          `W_x '' (Metric.ball x ρ) ⊆ Metric.ball 0 R`.
    • `uniformInverseChart_slice_ball_mapsTo_diag_generalK_min` — the SHRINK-STABILITY corollary: the
      same containment holds for every `ρ' ≤ ρ` (needed to intersect this domain constraint against
      OTHER independently-existential radii, e.g. J4-1012's IFT-package `ρ` or J4-1013's reversal-link
      `r`, via a `min` — since `Metric.ball x ρ' ⊆ Metric.ball x ρ` for `ρ' ≤ ρ`, and `MapsTo` is
      monotone under domain-shrinking).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  discharges Sol's NAMED missing domain-containment fact (item (b) of J4-1012's remaining scope /
  J4-1013's honesty-firewall item), and its shrink-stability corollary, so that a FUTURE dispatch can
  build a "master radius" `min(ρ_IFT, ρ_domain, r_reversal)` satisfying all three ball-domain
  constraints simultaneously.  It does **NOT**:
    • actually build that master-radius composition (no attempt to invoke J4-1012's
      `evalSlot_terminalVel_weighted_CoV` or J4-1013's `reversal_link_ball_integral` here — those
      existentials' internal witnesses, `V`/`f'`/the CoV data, are NOT reusable "for free" at a smaller
      sub-radius without re-deriving `hfd`/`hinj`/`hJpos` there; only the pure metric/topological
      MapsTo-monotonicity fact is supplied);
    • discharge, or make any progress on, `terminalVelAt_chartReplace_sliver_bound`'s substantive
      hypotheses `hWint` (integrability) / `hmom` (moment bound) — gpt-5.6-sol (high, this dispatch)
      confirmed explicitly: `MapsTo`/image-containment supplies ONLY geometric domain compatibility
      (`W_x '' ball x ρ ⊆ ball 0 R`), NOT equality of domains, NOT Jacobian/weight domination, NOT
      integrability, NOT the moment bound — those remain SEPARATE, substantive, NOT-attempted;
    • compose into any literal difference-form bound on `nb`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.JointRNCRegularityInterfaceLocalGeneralK

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocalGeneralK
open scoped Topology

namespace QIQTH.ChartEvalSlotDomainContainment

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §1 — the domain-containment fact: `W_x''(ball x ρ) ⊆ ball 0 R`, general `x`, `K`, `R`.
    ############################################################################### -/

/-- **★★ `uniformInverseChart_slice_ball_mapsTo_diag_generalK` — the domain-containment fact Sol
    (J4-1013's plan-review) named as missing.**  For an ARBITRARY compact `K`, interior base point
    `x ∈ interior K`, and ARBITRARY target radius `R > 0`, there is `ρ > 0` such that the eval-slot
    chart `W_x := uniformInverseChart g gi hC hK x` maps `Metric.ball x ρ` into `Metric.ball 0 R`.
    Route: `ContinuousAt W_x x` (from `uniformInverseChart_slice_contDiffAt_diag_generalK`'s
    `ContDiffAt ℝ 2`, via `ContDiffAt.continuousAt`) at the value `W_x x = 0`
    (`uniformInverseChart_slice_value_diag_generalK`), unwound through `Metric.continuousAt_iff`.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_slice_ball_mapsTo_diag_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (x : Point n) (hx : x ∈ interior K)
    (R : ℝ) (hR : 0 < R) :
    ∃ ρ > (0 : ℝ),
      Set.MapsTo (uniformInverseChart g gi hC hK x) (Metric.ball x ρ) (Metric.ball 0 R) := by
  set W : Point n → Point n := uniformInverseChart g gi hC hK x with hWdef
  have hWcd : ContDiffAt ℝ 2 W x :=
    uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK x hx
  have hW0 : W x = 0 := uniformInverseChart_slice_value_diag_generalK g gi hC hK x hx
  have hcont : ContinuousAt W x := hWcd.continuousAt
  obtain ⟨ρ, hρ, hspec⟩ := Metric.continuousAt_iff.mp hcont R hR
  refine ⟨ρ, hρ, ?_⟩
  intro z hz
  have hzd : dist z x < ρ := Metric.mem_ball.mp hz
  have hWd : dist (W z) (W x) < R := hspec hzd
  rw [hW0] at hWd
  exact Metric.mem_ball.mpr hWd

/-- **`uniformInverseChart_slice_ball_image_subset_diag_generalK`** — the equivalent SET-IMAGE form
    of the domain-containment fact: `W_x '' (Metric.ball x ρ) ⊆ Metric.ball 0 R`.  NOT `a₁ = R/6`. -/
theorem uniformInverseChart_slice_ball_image_subset_diag_generalK
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (x : Point n) (hx : x ∈ interior K)
    (R : ℝ) (hR : 0 < R) :
    ∃ ρ > (0 : ℝ),
      (uniformInverseChart g gi hC hK x) '' (Metric.ball x ρ) ⊆ Metric.ball 0 R := by
  obtain ⟨ρ, hρ, hmaps⟩ :=
    uniformInverseChart_slice_ball_mapsTo_diag_generalK g gi hC hK x hx R hR
  exact ⟨ρ, hρ, hmaps.image_subset⟩

/-! ###############################################################################
    ### §2 — shrink-stability: the same containment holds for every `ρ' ≤ ρ`.
    ############################################################################### -/

/-- **`uniformInverseChart_slice_ball_mapsTo_diag_generalK_min`** — the SHRINK-STABILITY corollary:
    given the witness `ρ` from `uniformInverseChart_slice_ball_mapsTo_diag_generalK`, the SAME
    containment `Set.MapsTo W_x (Metric.ball x ρ') (Metric.ball 0 R)` holds for every `0 < ρ' ≤ ρ`,
    since `Metric.ball x ρ' ⊆ Metric.ball x ρ` and `MapsTo` is monotone under domain-shrinking.  This
    is the fact a FUTURE "master radius" `min(ρ_IFT, ρ_domain, r_reversal)` composition would invoke.
    NOT `a₁ = R/6`. -/
theorem uniformInverseChart_slice_ball_mapsTo_diag_generalK_min
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (x : Point n) (hx : x ∈ interior K)
    (R : ℝ) (hR : 0 < R) :
    ∃ ρ > (0 : ℝ), ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ →
      Set.MapsTo (uniformInverseChart g gi hC hK x) (Metric.ball x ρ') (Metric.ball 0 R) := by
  obtain ⟨ρ, hρ, hmaps⟩ :=
    uniformInverseChart_slice_ball_mapsTo_diag_generalK g gi hC hK x hx R hR
  refine ⟨ρ, hρ, fun ρ' hρ'0 hρ'ρ => ?_⟩
  have hsub : Metric.ball x ρ' ⊆ Metric.ball x ρ := Metric.ball_subset_ball hρ'ρ
  exact hmaps.mono_left hsub

end QIQTH.ChartEvalSlotDomainContainment

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.ChartEvalSlotDomainContainment
#print axioms uniformInverseChart_slice_ball_mapsTo_diag_generalK
#print axioms uniformInverseChart_slice_ball_image_subset_diag_generalK
#print axioms uniformInverseChart_slice_ball_mapsTo_diag_generalK_min
end AxiomChecks
