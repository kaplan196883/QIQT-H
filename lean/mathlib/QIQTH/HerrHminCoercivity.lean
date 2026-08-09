/-
  HerrHminCoercivity — J4-455 (Sol #20's item (vi)): the group-(1) `herr`/`hmin` carries (I1)/(I2) of
  the a₁ = R/6 campaign — the ℓ² near-isometry cubic-error bound and the coercivity that
  `SlotInstantiationVIII`'s `hdom_comp2_ptwise`/`hcomp_final2` consume as STANDING inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  WHAT THE CONSUMER DEMANDS.  `SlotInstantiationVIII.hdom_comp2_ptwise` / `hcomp_final2` /
  `slotInstantiation_phase8` carry, with `W z := uniformInverseChart g gi hC hK z 0`:
    • `herr : ∀ z, |rncRadialSq (W z) − rncRadialSq z| ≤ L'·‖z‖³`   — the ℓ² near-isometry cubic error;
    • `hmin : ∀ z, ½·rncRadialSq z ≤ rncRadialSq (W z)`             — the coercivity (feeds `gaussDdim_replace_bound`).
  Both are stated **WHOLE-SPACE** (`∀ z`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WHOLE-SPACE GATE  (run BEFORE the build; the verdict is BINDING).

  VERDICT: the whole-space `∀ z` demand is **UNSATISFIABLE** — the honest shapes are GATE-RESTRICTED.

  REASON (audited from the definition, not guessed).  `uniformInverseChart g gi hC hK z` is the
  `.choose` chart inverse for `z ∈ K` and the ZERO DEFAULT `fun _ => 0` for `z ∉ K` (see the `dif`
  branch in `UniformChartRadius`).  Hence for EVERY base point `z ∉ K`,
      `W z = uniformInverseChart g gi hC hK z 0 = 0`,   so   `rncRadialSq (W z) = 0`
  (`uniformInverseChart_off_K`).  The chart is UNCONTROLLED off `K`; it collapses to the origin.  Now:
    • `hmin` at any `z ∉ K` with `z ≠ 0` reads `½·rncRadialSq z ≤ 0`, i.e. `rncRadialSq z ≤ 0`, FALSE
      (`rncRadialSq z > 0` for `z ≠ 0`).  The coercivity constant `½` is FIXED, so there is NO freedom:
      whole-space `hmin` is **definitively unsatisfiable** whenever some `z ∉ K` is nonzero — and `K` is
      compact, so `Kᶜ` is a nonempty open set containing nonzero points.  (`wholeSpace_coercivity_unsatisfiable`.)
    • `herr` at `z ∉ K` reads `rncRadialSq z ≤ L'·‖z‖³`; for `z ∉ K` with SMALL `‖z‖` (the gap between
      the origin and `K`'s near-origin coverage) the LHS `~ ‖z‖²` beats the RHS `~ ‖z‖³`, so `herr` too
      generically fails whole-space (it survives only if `0 ∈ interior K`, i.e. no such small gap).

  CONSEQUENCE FOR RE-FIRING (honest wall → next brick).  Because whole-space `hmin` is unsatisfiable,
  `hdom_comp2_ptwise`/`hcomp_final2`/`slotInstantiation_phase8` — as literally stated with `∀ z` —
  cannot be instantiated with TRUE hypotheses; they are only VACUOUSLY discharged, never USABLE.  The
  correct architecture must GATE the domination: on the gate ball `K ∩ ball 0 r` the factored integrand
  `hessGaussFactor·(ρ−1)·qc` is dominated by `comparisonDom2` (via the honest `herr`/`hmin` proved
  here), while OFF the gate (`collarᶜ ∩ (K ∩ ball 0 r)ᶜ`) the factored form is the WRONG object — there
  `W z = 0` forces `ρ = exp(rncRadialSq z/4τ)`, whence the factored integrand grows like `‖z‖²` and is
  NOT integrable, so the true gated residual (a decaying `baseKernelW` far-field object, NOT the
  factored form) must be dominated by a DIFFERENT leg.  That re-engineering of the off-gate comparison
  leg is left as an ENUMERATED WALL for Sol #22 / J4-456; it is NOT an identity or scaling gap in
  group (1) — it is the gate-vs-far-field split of the comparison integrand.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (all DERIVED from banked bricks; NO `sorry`, no `:= True`, no new axioms; std-3).

    * `uniformInverseChart_off_K` — the off-`K` collapse `W z = 0` (the GATE evidence).
    * `wholeSpace_coercivity_unsatisfiable` — the GATE certificate: a nonzero `z ∉ K` refutes whole-space `hmin`.
    * `herr_gate` — the GATE-RESTRICTED cubic error `|rncRadialSq (W z) − rncRadialSq z| ≤ (L·n)·‖z‖³`
      on `z ∈ K`, `‖z‖ < r`, from `chartW0_rncRadialSq_error` + `rncRadialSq ≤ n·‖z‖²`.
    * `hmin_gate` — the GATE-RESTRICTED coercivity `½·rncRadialSq z ≤ rncRadialSq (W z)` on the same
      ball, from the near-isometry LOWER bound with `L·‖z‖ ≤ ½` (shrunk radius).
    * `herrHmin_gate` — the PACKAGE: a single `r > 0` and `L' ≥ 0` carrying BOTH gate-restricted shapes.

  These discharge the (I1)/(I2) carries on the gate — the region where the chart is actually controlled
  — which is exactly the region the geometry can honestly supply.  ⚠ NOT `a₁ = R/6`.
-/
import QIQTH.AmplitudeDataOnCollar

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.AmplitudeDataOnCollar
open scoped Topology BigOperators

namespace QIQTH.HerrHminCoercivity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — THE GATE:  off-`K` collapse of the uniform inverse chart.
    ############################################################################### -/

/-- **★ `uniformInverseChart_off_K`.**  THE GATE EVIDENCE.  Off the compact base set `K` the uniform
    inverse chart is the ZERO DEFAULT (`fun _ => 0` in its definition), so its origin coordinate
    collapses to `0`:  for every `z ∉ K`,  `uniformInverseChart g gi hC hK z 0 = 0`.
    This is why the whole-space `hmin`/`herr` demands are unsatisfiable.  ⚠ NOT `a₁ = R/6`. -/
theorem uniformInverseChart_off_K (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {z : Point n} (hz : z ∉ K) :
    uniformInverseChart g gi hC hK z 0 = 0 := by
  simp only [uniformInverseChart, dif_neg hz]

/-- **★★ `wholeSpace_coercivity_unsatisfiable`.**  THE GATE VERDICT (certificate).  The whole-space
    coercivity `∀ z, ½·rncRadialSq z ≤ rncRadialSq (W z)` is FALSE as soon as there is a NONZERO base
    point off `K`: at such `z₀`, `W z₀ = 0` (off-`K` collapse) forces the RHS to `0`, while
    `rncRadialSq z₀ > 0`.  Since `K` is compact (so `Kᶜ` is a nonempty open set with nonzero points),
    this refutes the literal `∀ z` shape carried by `hdom_comp2_ptwise`/`hcomp_final2`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem wholeSpace_coercivity_unsatisfiable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {z₀ : Point n} (hz₀ : z₀ ∉ K) (hz₀0 : z₀ ≠ 0) :
    ¬ (∀ z, (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)) := by
  intro hmin
  have h := hmin z₀
  rw [uniformInverseChart_off_K g gi hC hK hz₀, rncRadialSq_zero] at h
  have hpos : 0 < rncRadialSq z₀ := rncRadialSq_pos hz₀0
  linarith

/-! ###############################################################################
    ### §2 — THE GATE-RESTRICTED `herr` and `hmin` (from the banked near-isometry error).
    ############################################################################### -/

/-- **★ `herr_gate`.**  THE GATE-RESTRICTED cubic near-isometry error (I1), DISCHARGED.  There is a
    single `r > 0` and constant `L' ≥ 0` such that on the gate ball `z ∈ K`, `‖z‖ < r`,
      `|rncRadialSq (W z) − rncRadialSq z| ≤ L'·‖z‖³`,   `W z := uniformInverseChart g gi hC hK z 0`.
    Route: the banked `chartW0_rncRadialSq_error` gives the two-sided error `≤ L·‖z‖·rncRadialSq z`;
    the sup-norm bound `rncRadialSq z ≤ n·‖z‖²` upgrades it to `L·n·‖z‖³ =: L'·‖z‖³`.  (Whole-space is
    UNSATISFIABLE — see THE WHOLE-SPACE GATE.)  ⚠ NOT `a₁ = R/6`. -/
theorem herr_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∃ L' : ℝ, 0 ≤ L' ∧ ∀ z ∈ K, ‖z‖ < r →
      |rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3 := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := chartW0_rncRadialSq_error g gi hC hK
  refine ⟨r₀, hr₀, L * (n : ℝ), by positivity, ?_⟩
  intro z hzK hzr
  obtain ⟨hlow, hup⟩ := hbd z hzK hzr
  set W : Point n := uniformInverseChart g gi hC hK z 0 with hWdef
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hle : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
  -- `L·‖z‖·rncRadialSq z ≤ L·n·‖z‖³`.
  have hcoef : (0 : ℝ) ≤ L * ‖z‖ := mul_nonneg hL0 (norm_nonneg z)
  have herrbd : L * ‖z‖ * rncRadialSq z ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hle hcoef
    nlinarith [this]
  -- assemble the two-sided error into `|·|`.
  have habs : |rncRadialSq W - rncRadialSq z| ≤ L * ‖z‖ * rncRadialSq z :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans habs herrbd

/-- **★ `hmin_gate`.**  THE GATE-RESTRICTED coercivity (I2), DISCHARGED.  There is a single `r > 0`
    such that on the gate ball `z ∈ K`, `‖z‖ < r`,
      `½·rncRadialSq z ≤ rncRadialSq (W z)`,   `W z := uniformInverseChart g gi hC hK z 0`.
    Route: the near-isometry LOWER bound `rncRadialSq z − L·‖z‖·rncRadialSq z ≤ rncRadialSq (W z)` from
    `chartW0_rncRadialSq_error`, shrinking the radius so `L·‖z‖ ≤ ½` (the source of the `c = 1/2`).
    (Whole-space is UNSATISFIABLE — see THE WHOLE-SPACE GATE.)  ⚠ NOT `a₁ = R/6`. -/
theorem hmin_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := chartW0_rncRadialSq_error g gi hC hK
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), ?_⟩
  intro z hzK hzr
  have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨hlow, _⟩ := hbd z hzK hzr₀
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  -- `L·‖z‖ ≤ 1/2`.
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hzrL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
    linarith
  -- `L·‖z‖·rncRadialSq z ≤ ½·rncRadialSq z`, then close via `hlow`.
  have hprod : L * ‖z‖ * rncRadialSq z ≤ (1 / 2 : ℝ) * rncRadialSq z :=
    mul_le_mul_of_nonneg_right hLz hb0
  linarith

/-! ###############################################################################
    ### §3 — PACKAGE — the group-(1) gate-restricted `herr` ∧ `hmin`.
    ############################################################################### -/

/-- **★★★ `herrHmin_gate`.**  THE PHASE-9 PACKAGE.  A SINGLE `r > 0` and constant `L' ≥ 0` carrying
    BOTH gate-restricted group-(1) inputs on `z ∈ K`, `‖z‖ < r`:
      (I1)  `|rncRadialSq (W z) − rncRadialSq z| ≤ L'·‖z‖³`,   and
      (I2)  `½·rncRadialSq z ≤ rncRadialSq (W z)`,
    `W z := uniformInverseChart g gi hC hK z 0`, `L' = L·n`.  This is the HONEST discharge of the (I1)/
    (I2) carries of `SlotInstantiationVIII` — on the gate ball, the only region where the uniform
    inverse chart is controlled (THE WHOLE-SPACE GATE: `∀ z` is unsatisfiable, `W z = 0` off `K`).
    The gate-vs-far-field re-fire of the off-collar comparison leg is deferred to Sol #22 / J4-456.
    ⚠ NOT `a₁ = R/6`. -/
theorem herrHmin_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∃ L' : ℝ, 0 ≤ L' ∧ ∀ z ∈ K, ‖z‖ < r →
      (|rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
      ∧ ((1 / 2 : ℝ) * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)) := by
  obtain ⟨r₀, hr₀, L, hL0, hbd⟩ := chartW0_rncRadialSq_error g gi hC hK
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), L * (n : ℝ), by positivity, ?_⟩
  intro z hzK hzr
  have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨hlow, hup⟩ := hbd z hzK hzr₀
  set W : Point n := uniformInverseChart g gi hC hK z 0 with hWdef
  have hb0 : (0 : ℝ) ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hle : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := rncRadialSq_le_nsq z
  have hcoef : (0 : ℝ) ≤ L * ‖z‖ := mul_nonneg hL0 (norm_nonneg z)
  have herrbd : L * ‖z‖ * rncRadialSq z ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have := mul_le_mul_of_nonneg_left hle hcoef
    nlinarith [this]
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hzrL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
    linarith
  have hprod : L * ‖z‖ * rncRadialSq z ≤ (1 / 2 : ℝ) * rncRadialSq z :=
    mul_le_mul_of_nonneg_right hLz hb0
  refine ⟨?_, by linarith⟩
  have habs : |rncRadialSq W - rncRadialSq z| ≤ L * ‖z‖ * rncRadialSq z :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_trans habs herrbd

end QIQTH.HerrHminCoercivity

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HerrHminCoercivity
#print axioms uniformInverseChart_off_K
#print axioms wholeSpace_coercivity_unsatisfiable
#print axioms herr_gate
#print axioms hmin_gate
#print axioms herrHmin_gate
end AxiomChecks

/-! ###############################################################################
    ## J4-455 LEDGER — Sol #20's item (vi): the group-(1) `herr`/`hmin` carries.
    ###############################################################################

  THE WHOLE-SPACE GATE — VERDICT: **UNSATISFIABLE** (gate-restricted correction MANDATORY).
    • `uniformInverseChart g gi hC hK z 0 = 0` for every `z ∉ K` (`uniformInverseChart_off_K`) — the
      chart is the ZERO DEFAULT off the compact base set (audited from the `dif` branch of the def).
    • Hence whole-space `hmin` (`∀ z, ½·r²_z ≤ r²_{Wz}`) FAILS at any nonzero `z ∉ K`
      (`wholeSpace_coercivity_unsatisfiable`): the RHS is `0`, the LHS `> 0`.  The `½` is fixed, so no
      constant choice rescues it.  `K` compact ⟹ `Kᶜ` nonempty open ⟹ such `z` exist.
    • Whole-space `herr` likewise fails in the small-`‖z‖` gap off `K` (LHS `~‖z‖²` beats RHS `~‖z‖³`),
      unless `0 ∈ interior K`.

  OUTCOMES.
    (I1) `herr` — PROVED GATE-RESTRICTED (`herr_gate`, `herrHmin_gate`): `|r²_{Wz} − r²_z| ≤ (L·n)·‖z‖³`
         on `z ∈ K`, `‖z‖ < r`.  From `chartW0_rncRadialSq_error` (banked) + `rncRadialSq ≤ n‖z‖²`.
    (I2) `hmin` — PROVED GATE-RESTRICTED (`hmin_gate`, `herrHmin_gate`): `½·r²_z ≤ r²_{Wz}` on the same
         ball.  From the near-isometry LOWER bound with the radius shrunk so `L·‖z‖ ≤ ½`.
    RE-FIRE of `hcomp_final2` — WALLED → Sol #22 / J4-456.  Whole-space `hmin` being unsatisfiable,
    `hdom_comp2_ptwise`/`hcomp_final2`/`slotInstantiation_phase8` (literal `∀ z`) are only vacuously
    dischargeable.  The honest fix (gate-vs-far-field split of the comparison integrand) is NOT an
    identity/scaling gap: off the gate the factored form `hessGaussFactor·(ρ−1)·qc` is the WRONG object
    (`W z = 0 ⟹ ρ = exp(r²_z/4τ)`, integrand `~‖z‖²`, non-integrable) — the true gated residual is a
    decaying `baseKernelW` far-field object needing a SEPARATE dominating leg.  That re-engineering is
    the enumerated wall for the next brick.

  DON'T-UNDERCREDIT FINDINGS.  The heavy lifting was ALREADY BANKED: `chartW0_rncRadialSq_error`
  (`InverseChartDisplacement`, itself from `chartW0_displacement`'s `ApproximatesLinearOn` root +
  bootstrap) supplies the two-sided error `≤ L·‖z‖·r²_z` with the `W z = −z + O(‖z‖²)` sign already
  fixed; `rncRadialSq_le_nsq` (`AmplitudeDataOnCollar`) supplies `r²_z ≤ n‖z‖²`; `chartW0_nearIsometry`
  ALREADY carries the `c = 1/2` coarse-coercivity in the exact form (an alternative route to `hmin_gate`).
  This brick is pure ASSEMBLY + the honest GATE audit — no new geometry.

  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack; this brick
  closes only the gate-restricted group-(1) `herr`/`hmin` inputs and RECORDS the whole-space
  unsatisfiability, NOT any physical `R/6` claim.
-/
