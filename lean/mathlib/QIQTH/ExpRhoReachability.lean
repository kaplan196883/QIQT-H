/-
  ExpRhoReachability — J4-485: interrogating the (I1) uniform reachability gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is an
  AUDIT of the ONE non-bankable input at the base of the convergent wall, plus the two honest,
  DERIVED interface lemmas that make the dependency explicit.  No `sorry` (header prose excepted),
  no `:= True`, no new axioms, no vacuous / unsatisfiable hypothesis, no result that is a
  conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE INTERROGATION.

  J4-484 (`Hfwd2Weld`) reduced the entire convergent wall to the SINGLE input
      `hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q`,
  the K-uniform reachability / injectivity radius.  This brick interrogates whether `hReach` is
  PROVABLE-in-repo, PROVABLE-with-reformulation, or a GENUINE geometric INPUT.

  ── WHAT `expRho` ACTUALLY IS (from `ExpMap.lean`).
      `expRho g gi hC p := (exists_confined_tube_family g gi hC p).choose`,
  and `exists_confined_tube_family` merely re-Skolemizes `geodesic_apriori_confinement g gi hC p`,
  whose statement is
      `∃ ρ > 0, ∃ C₀ ≥ 0, ∃ Y, ∀ ‖v‖ ≤ ρ, (confined geodesic tube through (p,v))`.
  So `expRho p` is `Classical.choose` of a **bare existential over a downward-closed set of admissible
  radii** — an ARBITRARY admissible confinement radius, NOT the supremum / maximal one.  It is marked
  `attribute [irreducible]` (its body unfolds to the enormous Picard–Lindelöf witness).  There is NO
  banked continuity, NO lower semicontinuity, NO uniform-over-`K` lower bound, and NO banked relation
  to the SEPARATE opaque `uniformFlowRadius` choose (which comes from
  `geodesic_apriori_confinement_uniform`, a DIFFERENT existential).

  ── THE ORDER-SWAP DIAGNOSIS.  Pointwise reachability is FREE: for every `q` one may take
  `ρ_q := expRho g gi hC q > 0` (`expRho_pos`), so
      `∀ q ∈ K, ∃ ρ > 0, ρ ≤ expRho g gi hC q`      (`expRho_reachability_pointwise`, DERIVED below).
  The wall's `hReach` needs the QUANTIFIERS SWAPPED — a SINGLE `ρ` (namely `uniformFlowRadius`) below
  ALL of them:
      `∃ ρ > 0, ∀ q ∈ K, ρ ≤ expRho g gi hC q`   with moreover  `uniformFlowRadius ≤ ρ`.
  Swapping `∀q ∃ρ` ↝ `∃ρ ∀q` over a compact `K` is EXACTLY the classical
  "positive infimum of a lower-semicontinuous function on a compact set" move — and it works PRECISELY
  WHEN the function is lower semicontinuous.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MATH VERDICT:  **GENUINE-INPUT** (matching the repo's `UNPROVABLE` / `GATING` labels),
     with the caveat that the underlying GEOMETRIC fact is TRUE-in-principle.

  * TRUE-in-principle.  For a smooth spray the injectivity / confinement radius of the geodesic flow
    IS lower semicontinuous in the base point (a small base perturbation can only shrink the
    confinement radius continuously-from-below), and an lsc function on a nonempty compact set attains
    a positive infimum.  So a uniform positive lower bound on the confinement radius over compact `K`
    DOES exist mathematically.

  * NOT provable from the repo's objects.  The repo's `expRho` is an ARBITRARY `Classical.choose`
    witness of a bare existential, NOT the maximal confinement radius.  For such a `.choose`, lower
    semicontinuity GENUINELY FAILS: the selector may return `ρ_max(q)/2` at one base and
    `ρ_max(q)/1000` at an arbitrarily close base — nothing constrains it.  `expRho` is moreover
    `irreducible`, so no property of it beyond `expRho_pos` and `expTube_spec` can ever be recovered.
    Hence `hReach` is NOT derivable in-repo, and NOT even after mere massaging.

  * The DISCHARGE that WOULD work (and why it is a separate multi-session campaign, absent from
    Mathlib).  One must (i) RECAST the confinement radius as the SUPREMUM of admissible radii
    `ρ_max(q) := sSup {ρ | confinement holds on the ρ-ball}` (a NEW definition, replacing the arbitrary
    `.choose`), (ii) prove `ρ_max` lower semicontinuous — the smooth-dependence-of-flows / injectivity-
    radius-lsc theorem, which **Mathlib does not have** (no C¹-in-initial-condition Picard–Lindelöf
    flow, confirmed in `UniformFlowNondeg.lean`), (iii) take the positive compact infimum, and (iv)
    ensure that infimum dominates the (separately chosen, opaque) `uniformFlowRadius` — a SECOND
    inter-selector obstruction, since `uniformFlowRadius` is itself an arbitrary confinement-existence
    radius, explicitly `NOT ≤ expRho in general` (`CommonNondegRadius.lean`).

  This EXACTLY reproduces the repo's standing labels: `UniformFlowNondeg` ("UNPROVABLE — `expRho`
  carries no continuity"), `CommonNondegRadius` ("`ρ` … is NOT `≤ expRho` in general … requires a NEW
  lemma … lower semicontinuity of `expRho` over the compact `K`, which is not present in the
  substrate"), and the repo-wide `hr_lt : ∀ q ∈ K, r < expRho q` carried as a HYPOTHESIS, never a
  conclusion (`UniformExpSecondJet`, `BasepointSecondJet`, `FlowVelocitySecondJet`, …).

  ── RECOMMENDATION.  `hReach` (the (I1) uniform injectivity radius) should JOIN the `a₁ = R/6`
  labelled-geometric-input list (the option-(b) precedent already in force for `a₁ = R/6` itself in
  `HEAT_KERNEL_GAP_PLAN.md` / the G3 PhysicalInputs): carry it as an explicit, satisfiable,
  non-vacuous geometric input until the injectivity-radius-lsc smooth-dependence campaign (a general
  C¹-in-IC flow theorem for Mathlib) can discharge it.  It is NOT a modular-analytic or
  regularity TODO reachable as a loop-brick.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `expRho_reachability_pointwise` — the honest "pointwise reachability is FREE" record: for every
      `q ∈ K` there is a positive radius `≤ expRho q` (namely `expRho q` itself).  Pinpoints that the
      obstruction is PURELY the `∀q ∃ρ` ↝ `∃ρ ∀q` order swap over compact `K`, i.e. lower
      semicontinuity of `expRho` — nothing else.

    * `chartSecondJet_continuousOn_of_uniform_injectivity_radius` — ★ THE INPUT INTERFACE, DERIVED.
      Reformulates the residual input in its STANDARD geometric form — a uniform injectivity radius
      `ρ` over `K` with `uniformFlowRadius ≤ ρ ≤ expRho q ∀ q ∈ K` (exactly the lsc-compact-infimum
      target of the (I1) campaign) — and shows it SUFFICES: it derives `hReach` (`le_trans`) and feeds
      `Hfwd2Weld.chartSecondJet_continuousOn_of_reach`, yielding the chart SECOND field-jet base
      continuity.  This SEPARATES the two sub-obstructions (uniform lower bound on `expRho`;
      domination of `uniformFlowRadius`) and names the discharge target precisely.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion):
    * the uniform injectivity radius `ρ` with `uniformFlowRadius ≤ ρ ≤ expRho q` — the (I1) input.
    * the per-`z` chart carries `hW0`/`horigin`/`hunit`/`hid2` (geometric; from the reduction).

  ⚠ THE WALL DID NOT FALL OUTRIGHT.  The verdict is GENUINE-INPUT: the convergent wall remains
  CONDITIONAL on `hReach` (equivalently, on the uniform injectivity radius).  What this brick adds is
  the AUDITED verdict + the standard-form interface, NOT a discharge.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Hfwd2Weld

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.HbaseJ2Assembly QIQTH.Flow3Regularity QIQTH.JacobiCLMExposure QIQTH.ChartFieldJacobian
open scoped Topology

namespace QIQTH.ExpRhoReachability

variable {n : ℕ}

/-! ###############################################################################
    ### THE POINTWISE-FREE RECORD — the obstruction is purely the order swap.
    ############################################################################### -/

/-- **`expRho_reachability_pointwise` — pointwise reachability is FREE.**  For every `q ∈ K` there is
    a positive radius below the injectivity radius `expRho g gi hC q` — take `expRho g gi hC q` itself
    (`expRho_pos`).  This is the `∀ q ∈ K, ∃ ρ > 0, ρ ≤ expRho q` form.  It pinpoints that the ONLY
    obstruction to the wall's `hReach` (`∃ ρ > 0, ∀ q ∈ K, ρ ≤ expRho q`, with `uniformFlowRadius ≤ ρ`)
    is the quantifier SWAP `∀q ∃ρ ↝ ∃ρ ∀q` over the compact `K` — i.e. lower semicontinuity of the
    opaque `.choose` selector `expRho`, which genuinely fails for an arbitrary (non-maximal) witness.
    NOT `a₁ = R/6`. -/
theorem expRho_reachability_pointwise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (K : Set (Point n)) :
    ∀ q ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ expRho g gi hC q :=
  fun q _ => ⟨expRho g gi hC q, expRho_pos g gi hC q, le_refl _⟩

/-! ###############################################################################
    ### ★ THE INPUT INTERFACE — the residual input in its standard geometric form.
    ############################################################################### -/

/-- **★ `chartSecondJet_continuousOn_of_uniform_injectivity_radius` — the (I1) input interface, DERIVED.**
    The residual geometric input at the base of the convergent wall, stated in its STANDARD form: a
    uniform injectivity radius `ρ` over the compact base `K` with
        `uniformFlowRadius g gi hC hK ≤ ρ`  and  `∀ q ∈ K, ρ ≤ expRho g gi hC q`.
    This is EXACTLY the "positive infimum of the (lower-semicontinuous) confinement radius over compact
    `K`, dominating the uniform-flow radius" statement targeted by the (I1) smooth-dependence campaign.
    Given it, `hReach` follows by `le_trans`, and `Hfwd2Weld.chartSecondJet_continuousOn_of_reach`
    yields the chart SECOND field-jet base continuity on `U`.  Separates the two sub-obstructions
    (uniform lower bound on `expRho`; domination of `uniformFlowRadius`) and names the discharge target
    precisely.  NOT a discharge of the input — the wall stays CONDITIONAL.  NOT `a₁ = R/6`. -/
theorem chartSecondJet_continuousOn_of_uniform_injectivity_radius
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)} (hUK : U ⊆ K)
    (ρ : ℝ) (hρge : uniformFlowRadius g gi hC hK ≤ ρ)
    (hlb : ∀ q ∈ K, ρ ≤ expRho g gi hC q)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (horigin : ∀ z ∈ U,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
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
  have hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q :=
    fun q hq => le_trans hρge (hlb q hq)
  exact QIQTH.Hfwd2Weld.chartSecondJet_continuousOn_of_reach g gi hC hK hUK hReach hW0 horigin hunit
    hid2

end QIQTH.ExpRhoReachability

/-! ## THE REACHABILITY VERDICT.

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE INPUT.  `hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q` — the K-uniform  │
  │  reachability / injectivity radius, the SOLE non-bankable residue at the base of the convergent   │
  │  wall (J4-484, `Hfwd2Weld`).                                                                       │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE OBJECT.  `expRho p = (exists_confined_tube_family g gi hC p).choose` = `Classical.choose` of  │
  │  a bare existential `∃ ρ > 0, (confined tube on ρ-ball)` — an ARBITRARY admissible radius, NOT the │
  │  maximal one; `irreducible`; no continuity / lsc / uniform lower bound; no banked relation to the  │
  │  SEPARATE opaque `uniformFlowRadius`.                                                              │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE VERDICT.  **GENUINE-INPUT.**  Pointwise reachability is FREE (order `∀q ∃ρ`,                  │
  │  `expRho_reachability_pointwise`); the wall needs the SWAP `∃ρ ∀q` over compact `K`, i.e. a        │
  │  positive compact infimum of `expRho`, which requires `expRho` lower semicontinuous.  For an       │
  │  arbitrary `.choose` witness lsc GENUINELY FAILS, and `irreducible` forbids recovering it.  The    │
  │  geometric fact is TRUE-in-principle (injectivity radius of a smooth spray IS lsc), but the        │
  │  discharge needs a RECAST (maximal-radius definition) + the injectivity-radius-lsc /               │
  │  C¹-in-IC-flow theorem ABSENT FROM MATHLIB + domination of the opaque `uniformFlowRadius`.  Matches │
  │  the repo's `UNPROVABLE` (`UniformFlowNondeg`) and `NOT ≤ expRho in general` (`CommonNondegRadius`) │
  │  labels and the repo-wide `hr_lt` hypothesis carries.                                              │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  WHAT LANDED.  (1) `expRho_reachability_pointwise` — the order-swap diagnosis (pointwise free).    │
  │  (2) `chartSecondJet_continuousOn_of_uniform_injectivity_radius` — the residual input restated in  │
  │  its STANDARD form (uniform injectivity radius `uniformFlowRadius ≤ ρ ≤ expRho q ∀q∈K`) and shown  │
  │  to SUFFICE, feeding `Hfwd2Weld.chartSecondJet_continuousOn_of_reach`.  NEITHER discharges the      │
  │  input; the wall stays CONDITIONAL.                                                                │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  RECOMMENDATION.  `hReach` / the uniform injectivity radius JOINS the `a₁ = R/6` labelled          │
  │  geometric-input list (option-(b) precedent): carry it explicitly (satisfiable, non-vacuous) until │
  │  the injectivity-radius-lsc smooth-dependence campaign (general C¹-in-IC Picard–Lindelöf flow for  │
  │  Mathlib) can discharge it.                                                                        │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT.  The gate was ALREADY named precisely at the `hFwd2` boundary (J4-484) and the
  underlying obstruction ALREADY diagnosed repo-wide (`CommonNondegRadius` (a): "`ρ` … is NOT `≤ expRho`
  in general … lower semicontinuity of `expRho` over the compact `K`, which is not present in the
  substrate"; `UniformFlowNondeg`: "UNPROVABLE — `expRho` carries no continuity"; `hr_lt` carried as a
  HYPOTHESIS across `UniformExpSecondJet` / `BasepointSecondJet` / `FlowVelocitySecondJet`).  This
  brick did NOT discover the gap; it AUDITS it to a firm verdict (GENUINE-INPUT, with the true-in-
  principle caveat and the exact discharge path), adds the order-swap diagnosis, and lands the
  standard-form input interface.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.ExpRhoReachability
#print axioms expRho_reachability_pointwise
#print axioms chartSecondJet_continuousOn_of_uniform_injectivity_radius
end AxiomChecks
