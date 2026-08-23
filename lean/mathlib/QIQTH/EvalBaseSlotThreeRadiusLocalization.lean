/-
  EvalBaseSlotThreeRadiusLocalization — J4-1049: the geometric common-ball localization glueing
  J4-1048's raw base/eval coordinate bridge, J4-1012's eval-slot weighted CoV, and J4-1046's
  `hxmem`/`hd`-free literal `kPrime` base-slot CoV identity's shrunk domain `S''` into ONE common ball.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  J4-1048's own honest scope note flagged two open items: (1) instantiating its abstract
  bridge at J4-1012's / J4-1046's ACTUAL `V`/`f'` bundles, and (2) reconciling the THREE independently
  existentially-quantified radii (J4-1048's raw-bridge radius `r`, J4-1012's eval-slot CoV radius `ρ`,
  J4-1046's shrunk-domain radius `R`/open set `S''`).

  A plan-review by `gpt-5.6-sol` (high, this dispatch) gave a BLUNT **NO-GO** on any real three-way
  composition of the underlying INTEGRAL IDENTITIES today: J4-1012's uniform-in-`ρ'` CoV variant
  (`evalSlot_terminalVel_weighted_CoV_uniform`, `ChartEvalSlotRadiusMerge.lean`) IS `.mono`-hereditary to
  sub-balls (that is exactly what makes `nb_common_chart_radius` in the same file legitimate), but
  J4-1046's `kPrime_baseField_CoV_of_jetBundle_fullLocalDischarge` is **NOT** of that uniform shape — its
  `S''`, `V`, `PI`, `PJ`, `Q` are a ONE-SHOT existential output (not parameterized `∀ ρ'' ≤ ρ_something`
  reusing the SAME witnesses), so there is NO `.mono`-style principle letting the literal `kPrime`
  integral identity be transported from `S''` to a smaller ball for free — doing so would require
  re-deriving J4-1046's entire IFT/local-coverage construction at the smaller domain (comparable in
  scope to what `ChartEvalSlotRadiusMerge` did for J4-1012, but NOT attempted here). Likewise
  `bridge_hasFDerivAt`/`bridge_left_inverse` cannot be applied to J4-1012's/J4-1046's concrete `V`/`f'`
  witnesses directly: no theorem identifies those two UNRELATED `V`'s, `bridge_left_inverse` needs
  genuine left-inverse hypotheses for BOTH charts simultaneously (available in each source file
  separately but never brought together), and `bridge_hasFDerivAt` needs `HasFDerivAt (terminalVelAt … x)`
  at a general point `We z`, currently known only via `ContDiffAt ℝ 2` AT THE SINGLE POINT `0` — not a
  full-neighborhood differentiability fact.

  Sol's own suggested salvage — the largest HONEST, non-vacuous lemma buildable today — is purely
  GEOMETRIC bookkeeping: from `IsOpen S''` and `x ∈ S''` (J4-1046's own witnesses), extract an explicit
  ball `ball x ρS ⊆ S''` (`Metric.isOpen_iff`), then combine `ρS` with J4-1012's `ρ` and J4-1048's `r`
  into a SINGLE common radius `ε := min (min ρS ρ) r`, giving one ball `ball x ε` simultaneously inside
  ALL THREE previously-independent domains — WITHOUT claiming this lets the literal `kPrime` integral
  identity, the eval-slot CoV identity, or the raw bridge identity be COMBINED into a single formula.

  THIS FILE supplies exactly that, generic AND concrete:
    §1 `common_ball_of_open_and_two_radii` — the ABSTRACT geometric localization lemma (generic `S''`,
       `ρ`, `r`, `R`): produces one `ε > 0` with `ball x ε` inside `S''`, `ball x ρ`, `ball x r`, and
       `ball x R` simultaneously.
    §2 `evalBaseSlot_common_domain_ball` — the CONCRETE instantiation at THIS campaign's actual objects:
       calls J4-1012's `evalSlot_terminalVel_weighted_CoV_uniform` (for `ρ`, `V`, `f'`, and the uniform
       CoV identity) and J4-1048's `evalBase_slot_coordinate_bridge_radius` (for `r` and the raw
       pointwise bridge) DIRECTLY (no side-condition-existence gap for either), takes J4-1046's shrunk
       domain `S''`/`R` as an EXPLICIT HYPOTHESIS (deriving it concretely requires resolving J4-1046's
       own `∀ c, (side conditions) → …` universal quantifier at a witness `c` — a genuinely separate,
       parameter-dependent satisfiability question, NOT re-attempted here; J4-1046's own dispatch only
       sympy-checked satisfiability "for generic positive constants", never proved existence as a
       standalone lemma) — and concludes: a single `ε > 0` such that on `ball x ε`, SIMULTANEOUSLY (a)
       `ball x ε ⊆ S''`, (b) `ball x ε ⊆ ball x R`, (c) the eval-slot weighted CoV identity holds for
       EVERY amplitude `B` (reusing the SAME `V, f'`), and (d) the raw base/eval pointwise bridge
       `w_b(z) = -T_x(w_e(z))` holds for every `z ∈ ball x ε`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`. No `sorry`, no
  new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited (NEW FILE).

  ── WHAT THIS FILE DOES **NOT** DO.  It does **NOT** combine the three domains' INTEGRAL IDENTITIES
  into one formula — `ball x ε ⊆ S''` does NOT imply `∫_{S''} = ∫_{ball x ε}` (no restriction principle
  for J4-1046's one-shot integral identity is available or invoked). It does **NOT** derive J4-1046's
  `S''`/`R` from scratch (taken as an explicit hypothesis — resolving its `∀ c, …` side-condition
  satisfiability is a separate, not-attempted task). It does **NOT** instantiate `bridge_hasFDerivAt`,
  `bridge_det_abs`, or `bridge_left_inverse` at J4-1012's/J4-1046's concrete `V`/`f'` (confirmed
  genuinely blocked by `gpt-5.6-sol`, high: unrelated witnesses, missing full-neighborhood
  differentiability of `terminalVelAt`, missing joint left-inverse hypotheses). It does **NOT** compose
  any of this into a literal difference-form bound on `nb`, and does **NOT** discharge `r6`, `nb`,
  `hCConv`, or any part of `hcomp`. `Bfac`'s other 3 summands and `fb` remain untouched. `a₁ = R/6`
  remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartEvalSlotRadiusMerge
import QIQTH.EvalBaseSlotCoordinateBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open QIQTH.GeodesicReversalRouteAtPoint
open QIQTH.ChartEvalSlotRadiusMerge
open QIQTH.EvalBaseSlotCoordinateBridge
open scoped Topology

namespace QIQTH.EvalBaseSlotThreeRadiusLocalization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the ABSTRACT geometric common-ball localization lemma.
    ############################################################################### -/

/-- **`common_ball_of_open_and_two_radii`.**  Pure metric-space bookkeeping: given an open set `S''`
    containing `x` with `S'' ⊆ ball x R`, and two further positive radii `ρ, r`, there is a SINGLE
    `ε > 0` with `ball x ε` simultaneously inside `S''`, `ball x R`, `ball x ρ`, and `ball x r`.  NO
    claim is made about any integral / CoV identity transporting to `ball x ε` — this is ONLY the
    domain-inclusion fact.  NOT `a₁ = R/6`. -/
theorem common_ball_of_open_and_two_radii {x : Point n} {S'' : Set (Point n)}
    (hSopen : IsOpen S'') (hxS : x ∈ S'') {R : ℝ} (hSR : S'' ⊆ Metric.ball x R)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    ∃ ε > (0 : ℝ), ε ≤ ρ ∧ ε ≤ r ∧
      Metric.ball x ε ⊆ S'' ∧ Metric.ball x ε ⊆ Metric.ball x R := by
  obtain ⟨ρS, hρS, hballS⟩ := Metric.isOpen_iff.mp hSopen x hxS
  refine ⟨min (min ρS ρ) r, by positivity,
    le_trans (min_le_left _ _) (min_le_right _ _), min_le_right _ _, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))).trans hballS
  · exact ((Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))).trans hballS).trans
      hSR

/-! ###############################################################################
    ### §2 — the CONCRETE instantiation at `uniformInverseChart`/`terminalVelAt`.
    ############################################################################### -/

/-- **★★ `evalBaseSlot_common_domain_ball`.**  Concrete campaign instantiation: calls J4-1012's
    `evalSlot_terminalVel_weighted_CoV_uniform` (eval-slot weighted CoV, uniform in sub-radius) and
    J4-1048's `evalBase_slot_coordinate_bridge_radius` (raw base/eval pointwise bridge) DIRECTLY —
    both unconditional given `hxint`/`hxKmem` — and takes J4-1046's shrunk-domain witnesses `S''`, `R`
    as an EXPLICIT hypothesis (its own derivation needs resolving a separate, parameter-dependent
    side-condition satisfiability question, not attempted here).  Concludes: a single `ε > 0` with
    `ball x ε` inside `S''` and `ball x R`, on which BOTH (i) the eval-slot weighted CoV identity holds
    for every amplitude `B` (SAME `V, f'` reused, via J4-1012's `.mono`-hereditary uniform variant) AND
    (ii) the raw pointwise bridge `uniformInverseChart z x = -terminalVelAt x (uniformInverseChart x z)`
    holds for every `z ∈ ball x ε`.  Does NOT combine (i)/(ii) with J4-1046's own `S''`-integral
    identity into one formula.  NOT `a₁ = R/6`. -/
theorem evalBaseSlot_common_domain_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x : Point n} (hxint : x ∈ interior K) (τ : ℝ)
    {S'' : Set (Point n)} {R : ℝ} (hSopen : IsOpen S'') (hxS : x ∈ S'')
    (hSR : S'' ⊆ Metric.ball x R) :
    ∃ ε > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      Metric.ball x ε ⊆ S'' ∧ Metric.ball x ε ⊆ Metric.ball x R ∧
      (∀ B : Point n → ℝ,
        (∫ z in Metric.ball x ε,
            gaussDdim τ (terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) * B z)
          = ∫ w in (uniformInverseChart g gi hC hK x) '' (Metric.ball x ε),
              gaussDdim τ (terminalVelAt g gi hC hK x w) * (B (V w) / |(f' (V w)).det|)) ∧
      (∀ z : Point n, dist z x < ε →
        uniformInverseChart g gi hC hK z x
          = -terminalVelAt g gi hC hK x (uniformInverseChart g gi hC hK x z)) := by
  obtain ⟨ρ, hρ, V, f', hCoVuniform⟩ :=
    evalSlot_terminalVel_weighted_CoV_uniform g gi hC hK hxint τ
  have hxKmem : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxint
  obtain ⟨r, hr, hbridge⟩ := evalBase_slot_coordinate_bridge_radius g gi hC hK hxKmem
  obtain ⟨ε, hε, hερ, hεr, hεS, hεR⟩ :=
    common_ball_of_open_and_two_radii hSopen hxS hSR hρ hr
  refine ⟨ε, hε, V, f', hεS, hεR, ?_, ?_⟩
  · intro B
    exact hCoVuniform ε hε hερ B
  · intro z hz
    exact hbridge z (lt_of_lt_of_le hz hεr)

end QIQTH.EvalBaseSlotThreeRadiusLocalization

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.EvalBaseSlotThreeRadiusLocalization
#print axioms common_ball_of_open_and_two_radii
#print axioms evalBaseSlot_common_domain_ball
end AxiomChecks
