/-
  C2AggregatorPhase6 — J4-490: routing the (I1)-only phase-6 sup family into the downstream
  collar-carry aggregator slot — the C₂ sup-constant now drawn from `hReach` ALONE (no `hid2`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3
  only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  `Hid2Germ.supConstant_phase6` grounds the whole sup family `M₀`/`M₁`/`M₂`
  (= `C₀`/`C₁`/`C₂`) on the SINGLE carried input (I1) `hReach`: the SIX geometric carriers AND the
  2nd-order IFT residue `hid2` are all supplied internally from the bank (J4-488 / J4-489).  Its output
  packages the three bounds on TWO radii — `C₀` on an inner `ρ₀`, `C₁`/`C₂` on the outer `ρ`.

  The DOWNSTREAM aggregator `AmplitudeDataOnCollar.amplitudeDataOn_concrete` consumes the three
  collar sup-constants as SEPARATE carries `hM₀chart`/`hM₁chart`/`hM₂chart`, each of the shape
      `∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z → |·| ≤ M`,
  ALL on a COMMON radius `r₀`.  The prior route to that slot supplied `C₂` from `supConstant_phase5`
  (carrying the isolated `hid2` residue).  THIS BRICK swaps the source to the (I1)-only phase-6 family
  and reconciles the two radii onto `r₀ := min ρ ρ₀`, delivering all three carries from (I1) `hReach`
  ALONE — the `hid2` carry is GONE.

  ## THE GATE (radius monotonicity).  `collarRegime r₀ c τ₀ τ z` contains the conjunct `‖z‖ < r₀`, so
  it is ANTITONE in `r₀`: a bound proven on a LARGER radius restricts to any SMALLER one
  (`collarRegime_mono`).  Hence the `C₀` bound (radius `ρ₀`) and the `C₁`/`C₂` bounds (radius `ρ`) all
  hold on `min ρ ρ₀`.  No new hypothesis, no unsatisfiable side-condition: (I1) `hReach` is the same
  inhabited input `supConstant_phase6` itself is stated with, and `min ρ ρ₀ > 0`.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `collarRegime_mono` — the collar predicate is antitone in the chart radius `r₀`.
    * `collarSupConstants_of_reach` — ★★★ the three collar sup-constants `M₀`/`M₁`/`M₂` on a COMMON
      radius `r₀ = min ρ ρ₀`, in the EXACT `amplitudeDataOn_concrete.hM·chart` carry shape, from (I1)
      `hReach` ALONE.  The C₂ sup-constant is now drawn from the (I1)-only phase-6 family; `hid2` GONE.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion): (I1) `hReach` ONLY.  ⚠ NOT
    `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1), the banked convergence trio, and the geometric
    wiring).
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.Hid2Germ

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartFieldC2General QIQTH.GeodesicGronwall QIQTH.JacobiCLMExposure
open QIQTH.ChartFieldJacobian QIQTH.ChartSecondJet QIQTH.AmplitudeSecondJet
open QIQTH.SupFamilyFirstOrder QIQTH.SupConstantFamily QIQTH.AmplitudeDataOnCollar
open QIQTH.HrepGermFactorization QIQTH.C2CarrierCollapse QIQTH.Hid2Germ
open scoped Topology ContDiff

namespace QIQTH.C2AggregatorPhase6

variable {n : ℕ}

/-! ###############################################################################
    ### THE COLLAR PREDICATE IS ANTITONE IN THE CHART RADIUS `r₀`.
    ############################################################################### -/

/-- **`collarRegime_mono` — the collar predicate is antitone in the chart radius.**  Since
    `collarRegime r c τ₀ τ z` contains the conjunct `‖z‖ < r`, enlarging the radius (`r ≤ r'`) only
    weakens that conjunct, so the predicate is preserved.  This is the sole ingredient reconciling the
    two phase-6 radii onto a common one.  NOT `a₁ = R/6`. -/
theorem collarRegime_mono {K : Set (Point n)} {r r' c τ₀ τ : ℝ} {z : Point n}
    (h : r ≤ r') (hreg : collarRegime (K := K) r c τ₀ τ z) :
    collarRegime (K := K) r' c τ₀ τ z := by
  obtain ⟨hτ, hττ₀, hzK, hzr, hzc⟩ := hreg
  exact ⟨hτ, hττ₀, hzK, lt_of_lt_of_le hzr h, hzc⟩

/-! ###############################################################################
    ### ★★★ THE COLLAR SUP-CONSTANTS ON A COMMON RADIUS — the (I1)-only downstream slot.
    ############################################################################### -/

/-- **★★★ `collarSupConstants_of_reach` — the three collar sup-constants on a COMMON radius, from
    (I1) `hReach` ALONE.**  From `Hid2Germ.supConstant_phase6` (the (I1)-only sup family, with the six
    geometric carriers AND the 2nd-order residue `hid2` discharged internally from the bank), extract
    the three amplitude sup-bounds `M₀`/`M₁`/`M₂` and reconcile their two phase-6 radii (`C₀` on `ρ₀`,
    `C₁`/`C₂` on `ρ`) onto `r₀ := min ρ ρ₀` via `collarRegime_mono`.  The output is EXACTLY the three
    `AmplitudeDataOnCollar.amplitudeDataOn_concrete` carries `hM₀chart`/`hM₁chart`/`hM₂chart`
    (with `r₀` common), so the downstream collar bundle's C₂ sup-constant is now drawn from the
    (I1)-only phase-6 family — the isolated `hid2` carry is ELIMINATED.  NOT `a₁ = R/6`. -/
theorem collarSupConstants_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      ∃ M₀ M₁ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
        (∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
            |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
        ∧ (∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
            |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
        ∧ (∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
            |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂) := by
  obtain ⟨ρ, hρ0, hC0, hC1, hC2⟩ :=
    supConstant_phase6 g gi hC hK h0Kmem hg hgi hgpos a b c τ₀ i hReach
  obtain ⟨ρ₀, hρ₀0, M₀, hM₀0, hb0⟩ := hC0
  obtain ⟨M₁, hM₁0, hb1⟩ := hC1
  obtain ⟨M₂, hM₂0, hb2⟩ := hC2
  refine ⟨min ρ ρ₀, lt_min hρ0 hρ₀0, M₀, M₁, M₂, hM₀0, hM₁0, hM₂0, ?_, ?_, ?_⟩
  · intro τ z hreg
    exact hb0 τ z (collarRegime_mono (min_le_right ρ ρ₀) hreg)
  · intro τ z hreg
    exact hb1 τ z (collarRegime_mono (min_le_left ρ ρ₀) hreg)
  · intro τ z hreg
    exact hb2 τ z (collarRegime_mono (min_le_left ρ ρ₀) hreg)

end QIQTH.C2AggregatorPhase6

/-! ## THE AGGREGATOR LEDGER (post J4-490).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE SWAP.  `supConstant_phase6` (J4-489) grounds `C₀`/`C₁`/`C₂` on (I1) `hReach` ALONE, packaging  │
  │  the bounds on TWO radii (`C₀` on `ρ₀`, `C₁`/`C₂` on `ρ`).  The downstream collar bundle             │
  │  `AmplitudeDataOnCollar.amplitudeDataOn_concrete` consumes the three sup-constants as SEPARATE       │
  │  carries `hM₀chart`/`hM₁chart`/`hM₂chart`, ALL on a COMMON radius `r₀`.                              │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE RECONCILIATION.  `collarRegime` is ANTITONE in `r₀` (it contains `‖z‖ < r₀`), so a bound on a   │
  │  larger radius restricts to a smaller one (`collarRegime_mono`).  Setting `r₀ := min ρ ρ₀` lands all │
  │  three carries on ONE radius from (I1) `hReach` ALONE — `collarSupConstants_of_reach`.               │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE OUTCOME.  The downstream C₂ sup-constant (`hM₂chart`) is now drawn from the (I1)-only phase-6   │
  │  family.  The isolated second-order `hid2` residue is ELIMINATED from the aggregator's hypothesis    │
  │  list: what was `supConstant_phase5` + a separate `hid2`-carry is now `supConstant_phase6` alone.    │
  │  C₀ unconditional · C₁ geometric-closed · C₂ on (I1) ALONE.  NEVER `a₁ = R/6`.                       │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── DONT-UNDERCREDIT findings.
    * The whole (I1)-only sup family was ALREADY banked in `Hid2Germ.supConstant_phase6`; this brick is
      a THIN adapter — it only reshapes the two-radius package onto the common radius the downstream
      collar bundle consumes.  No sup-family re-derivation, no `supConstant_phase4`/vanVleck Π
      re-application (the monolith trap avoided): `supConstant_phase6` is applied ONCE as a compiled
      lemma and its output destructured.
    * `collarRegime`'s antitonicity in `r₀` is immediate from its definition (`‖z‖ < r₀`) — the sole
      reconciliation ingredient; no analytic content.
    * The `amplitudeDataOn_concrete` carry shapes (`hM₀chart`/`hM₁chart`/`hM₂chart`) match the phase-6
      conjuncts VERBATIM (the C₀/C₁/C₂ slots), so the delivered bounds plug straight into that bundle's
      slots with `r₀` in the `r₀`/`c`/`τ₀` positions.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1) `hReach`, the banked convergence trio, and
    the geometric wiring).
-/

section AxiomChecks
open QIQTH.C2AggregatorPhase6
#print axioms collarRegime_mono
#print axioms collarSupConstants_of_reach
end AxiomChecks
