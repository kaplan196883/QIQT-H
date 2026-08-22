/-
  ChartEvalSlotRadiusMerge — the RADIUS-MERGE resolution for `hcomp`'s near-carry `nb`: the eval-slot
  weighted change-of-variables (J4-1012), lifted to hold UNIFORMLY on every sub-ball `ball x ρ'`
  (`ρ' ≤ ρ`) reusing the SAME chart data `V, f'`, and then a COMMON-radius lemma synchronizing that
  uniform CoV with J4-1013's reversal-link ball integral and J4-1014's domain containment on a single
  radius `ρ*`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1012's `evalSlot_terminalVel_weighted_CoV` proves the weighted CoV for ONE specific `ρ`
  produced by the eval-slot IFT package (`chartIFTPackage_generalQ0`), so it could not be intersected
  with the INDEPENDENT existential radii of J4-1013 (reversal link `r`) / J4-1014 (domain containment
  `ρ_dom`) without re-deriving the CoV at the smaller radius.  The key observation (confirmed by
  `gpt-5.6-sol`, high): the ABSTRACT CoV `ChartGeneralChangeVarEvalSlot.chart_general_change_variables`
  holds for ANY measurable subset `S' ⊆ S` on which the M1–M4 data still hold — and M1–M4 are all
  `.mono`-HEREDITARY to sub-balls:
    • M1 `HasFDerivWithinAt W (f' z) (ball q₀ ρ) z`  →  `.mono (ball_subset_ball …)` on `ball q₀ ρ'`;
    • M2 `Set.InjOn W (ball q₀ ρ)`                     →  `.mono (ball_subset_ball …)`;
    • M3 `∀ z ∈ ball q₀ ρ, V (W z) = z`               →  restriction to `ball q₀ ρ'`;
    • M4 `∀ z ∈ ball q₀ ρ, 0 < |det (f' z)|`          →  restriction.
  So the uniform-radius CoV, reusing the SAME `V, f'` at every `ρ' ≤ ρ`, is a mechanical restriction —
  NOT a re-derivation.  This is exactly the piece J4-1014's report flagged as "not free": it IS free,
  via `.mono`.  With it, the three ball-domain constraints merge on `ρ* := min(ρ_CoV, r_rev, ρ_dom)`.

  THIS FILE supplies:
    • `chart_general_change_variables_concrete_generalQ0_uniform` — the generic-`φ` eval-slot CoV,
      uniform in `ρ' ≤ ρ` (single `V, f'`), amplitude `B` universally quantified inside.
    • `evalSlot_terminalVel_weighted_CoV_uniform` — its `φ := gaussDdim τ ∘ terminalVelAt … x`
      instantiation, uniform in `ρ' ≤ ρ`.
    • `nb_common_chart_radius` — a SINGLE radius `ρ*` at which, for every `ρ' ≤ ρ*`, all three hold
      simultaneously: (i) the uniform weighted CoV, (ii) the reversal-link ball integral, (iii) the
      domain containment `W_x (ball x ρ') ⊆ ball 0 R`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It resolves
  ONLY the RADIUS-MERGE bookkeeping obstruction (uniform-in-`ρ'` CoV + a common radius for the three
  ball constraints).  It does **NOT**:
    • discharge `terminalVelAt_chartReplace_sliver_bound`'s `_hWint` integrability hypothesis (that
      needs measurability of the `terminalVelAt`-composed Gaussian on all of `ball 0 R`, an ODE
      dependence-on-initial-data API gap, NOT touched here);
    • establish the Jacobian/weight DOMINATION identifying the CoV weight `B (V w)/|det (f' (V w))|`
      with J4-879's pure moment weight `‖w‖^k` — domain SYNCHRONIZATION is not weight domination;
    • compose these identities into any literal difference-form bound on `nb`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartGeneralChangeVarEvalSlot
import QIQTH.ReversalLinkBallIntegral
import QIQTH.ChartEvalSlotDomainContainment

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocalGeneralK
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.ChartGeneralChangeVarEvalSlot
open QIQTH.ReversalLinkBallIntegral
open QIQTH.ChartEvalSlotDomainContainment
open scoped Topology

namespace QIQTH.ChartEvalSlotRadiusMerge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the uniform-in-`ρ'` generic-`φ` eval-slot change of variables.
    ############################################################################### -/

/-- **★★ `chart_general_change_variables_concrete_generalQ0_uniform`.**  The generic-`φ` eval-slot CoV
    (J4-1012), lifted to hold on EVERY sub-ball `ball q₀ ρ'` (`0 < ρ' ≤ ρ`) with the SAME chart data
    `V, f'` and for EVERY amplitude `B`:
        `∫ z in ball q₀ ρ', φ (W z) · B z = ∫ w in W '' (ball q₀ ρ'), φ w · (B (V w) / |det (f' (V w))|)`.
    Route: obtain `ρ, V, f'` and M1–M4 from `chartIFTPackage_generalQ0` ONCE; for each `ρ' ≤ ρ`,
    `Metric.ball q₀ ρ' ⊆ Metric.ball q₀ ρ`, and M1–M4 restrict by `.mono` / membership restriction.
    NOT `a₁ = R/6`. -/
theorem chart_general_change_variables_concrete_generalQ0_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (φ : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ → ∀ B : Point n → ℝ,
        (∫ z in Metric.ball q₀ ρ', φ (uniformInverseChart g gi hC hK q₀ z) * B z)
          = ∫ w in (uniformInverseChart g gi hC hK q₀) '' (Metric.ball q₀ ρ'),
              φ w * (B (V w) / |(f' (V w)).det|) := by
  obtain ⟨ρ, hρ, V, f', _hS, hfd, hinj, hV, hJpos, _⟩ :=
    QIQTH.ChartIFTPackageGeneralQ0.chartIFTPackage_generalQ0 g gi hC hK hq₀
  refine ⟨ρ, hρ, V, f', fun ρ' _hρ'0 hρ'ρ B => ?_⟩
  have hsub : Metric.ball q₀ ρ' ⊆ Metric.ball q₀ ρ := Metric.ball_subset_ball hρ'ρ
  exact chart_general_change_variables φ (Metric.ball q₀ ρ')
    (uniformInverseChart g gi hC hK q₀) V f' (fun z => |(f' z).det|) B
    measurableSet_ball
    (fun z hz => (hfd z (hsub hz)).mono hsub)
    (hinj.mono hsub)
    (fun z hz => hV z (hsub hz))
    (fun _ _ => rfl)
    (fun z hz => hJpos z (hsub hz))

/-- **★★ `evalSlot_terminalVel_weighted_CoV_uniform`.**  The `φ := gaussDdim τ ∘ terminalVelAt … x`
    instantiation of the uniform CoV, at base `q₀ := x`, uniform in `ρ' ≤ ρ`.  NOT `a₁ = R/6`. -/
theorem evalSlot_terminalVel_weighted_CoV_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxint : x ∈ interior K)
    (τ : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρ → ∀ B : Point n → ℝ,
        (∫ z in Metric.ball x ρ',
            gaussDdim τ (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
          = ∫ w in (uniformInverseChart g gi hC hK x) '' (Metric.ball x ρ'),
              gaussDdim τ (terminalVelAt g gi hC hK x w) * (B (V w) / |(f' (V w)).det|) :=
  chart_general_change_variables_concrete_generalQ0_uniform g gi hC hK hxint
    (fun w => gaussDdim τ (terminalVelAt g gi hC hK x w))

/-! ###############################################################################
    ### §2 — the common radius synchronizing all three ball constraints.
    ############################################################################### -/

/-- **★★★ `nb_common_chart_radius` — the radius-merge payoff.**  For interior base `x`, heat time `τ`,
    and target radius `R > 0`, there is a SINGLE radius `ρ* > 0` and chart data `V, f'` such that for
    EVERY `0 < ρ' ≤ ρ*` all three ingredients hold simultaneously on `ball x ρ'`:
      (i) the uniform weighted CoV (§1), for every amplitude `B`;
      (ii) the reversal-link ball integral (J4-1013), for every amplitude `B`;
      (iii) the domain containment `W_x (ball x ρ') ⊆ ball 0 R` (J4-1014).
    Built as `ρ* := min (min ρ_CoV r_rev) ρ_dom` — the "common radius" merge the three independent
    existentials previously blocked.  This SYNCHRONIZES the domains ONLY; it does NOT dominate the CoV
    Jacobian/weight against J4-879's moment weight, and does NOT compose into an `nb` bound.  NOT
    `a₁ = R/6`. -/
theorem nb_common_chart_radius
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxint : x ∈ interior K)
    (τ : ℝ) (R : ℝ) (hR : 0 < R) :
    ∃ ρstar > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ ρstar →
        (∀ B : Point n → ℝ,
          (∫ z in Metric.ball x ρ',
              gaussDdim τ (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
            = ∫ w in (uniformInverseChart g gi hC hK x) '' (Metric.ball x ρ'),
                gaussDdim τ (terminalVelAt g gi hC hK x w) * (B (V w) / |(f' (V w)).det|))
        ∧ (∀ B : Point n → ℝ,
          (∫ z in Metric.ball x ρ', gaussDdim τ (uniformInverseChart g gi hC hK z x) * B z)
            = ∫ z in Metric.ball x ρ',
                gaussDdim τ (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
        ∧ Set.MapsTo (uniformInverseChart g gi hC hK x) (Metric.ball x ρ') (Metric.ball 0 R) := by
  have hxKnhds : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨ρ1, hρ1, V, f', hcov⟩ :=
    evalSlot_terminalVel_weighted_CoV_uniform g gi hC hK hxint τ
  obtain ⟨r, hr, hrev⟩ := reversal_link_ball_integral g gi hC hK hxKnhds τ
  obtain ⟨ρ3, hρ3, hdom⟩ :=
    uniformInverseChart_slice_ball_mapsTo_diag_generalK_min g gi hC hK x hxint R hR
  refine ⟨min (min ρ1 r) ρ3, lt_min (lt_min hρ1 hr) hρ3, V, f',
    fun ρ' hρ'0 hρ'le => ⟨?_, ?_, ?_⟩⟩
  · exact hcov ρ' hρ'0 (le_trans hρ'le (le_trans (min_le_left _ _) (min_le_left _ _)))
  · exact hrev ρ' hρ'0 (le_trans hρ'le (le_trans (min_le_left _ _) (min_le_right _ _)))
  · exact hdom ρ' hρ'0 (le_trans hρ'le (min_le_right _ _))

end QIQTH.ChartEvalSlotRadiusMerge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.ChartEvalSlotRadiusMerge
#print axioms chart_general_change_variables_concrete_generalQ0_uniform
#print axioms evalSlot_terminalVel_weighted_CoV_uniform
#print axioms nb_common_chart_radius
end AxiomChecks
