/-
  CensusTwoTermBallLocal — the BALL-LOCAL adapter for the flat two-term Gaussian census bound,
  resolving the newly-surfaced GLOBAL-vs-BALL boundedness mismatch (N1) at the CoV ⟶ two-term junction
  of the `hCensusBound` (`hCross`) assembly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure REAL-ANALYSIS adapter brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHY THIS EXISTS (a NEW mismatch surfaced by the full-assembly attempt, beyond G1/G2/G3).
  With structural gap G1 fixed (`BaseVaryingIFTCommonWitness`, J4-943), attempting to monolithize the
  literal `hCensusBound` (`HCrossDerivEngineWired.hcross_of_censusIntegral_bound`, J4-929) reaches the
  CoV ⟶ two-term junction, where `two_term_census_bound_uniform` / `_combined`
  (`GaussTauTraceChartTransported`) is the flat trace-cancellation core.  That core demands the
  transported weights `q₁, q₂` be **globally** bounded (`hq₁bnd : ∀ z, |q₁ z| ≤ M₁`,
  `hq₂bnd : ∀ z, |q₂ z| ≤ M₂`), but the common-witness transport (`commonWitness_ampF_transport`,
  `commonWitness_CfieldF_transport`, and the Levi F-factor `census_ampF_leviF_transported_ratio_regularity`)
  delivers boundedness ONLY on an image ball `ball 0 σ'`.  That is a genuine signature mismatch (N1) —
  it is NOT a gap in G1/G2/G3; it is a NEW interface obstruction discovered only when the pieces are
  actually threaded.

  ## THE FIX (truncate + integrate over the ball).  The mismatch dissolves once one notices the census
  is ultimately integrated over a **ball** (the CoV image ball / the on-gate ball), not all of `ℝⁿ`.
  Truncating the weights to `0` off `ball 0 r` (`Set.indicator (ball 0 r) q`) makes them **globally**
  bounded — `|indicator q z| ≤ M` for every `z` (on the ball `≤ M`, off it `= 0 ≤ M`) — WITHOUT
  changing the center-Lipschitz data on `ball 0 r` (the indicator agrees with `q` there, and `0 ∈ ball 0 r`
  so the center value `q 0` is preserved).  Setting the two-term superset `Ω := ball 0 r` (so `Ω ⊇ ball 0 r`
  trivially) and restoring the un-truncated integrand on `ball 0 r` by `setIntegral_congr_fun` yields the
  SAME `Cpair/√τ` bound from purely BALL-LOCAL weight regularity.

  ## WHAT LANDS.
    • `two_term_census_bound_ballLocal` — ★★ the BALL-LOCAL flat two-term Gaussian census bound: for
        `0<τ≤T`, `r>0`, `q₁, q₂` measurable, bounded + (`q₁`) center-Lipschitz ONLY on `ball 0 r`,
          `|∫_{ball 0 r}(∑ᵢ(zᵢ²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{ball 0 r} gaussDdim τ z·q₂ z|
             ≤ (L·(n²(16√2+1)) + (3n·M₁·√2ⁿ·(4(2n+1)/r²) + M₂)·√T)/√τ`  —
        the exact `Cpair/√τ` shape `hCensusBound`'s ball bound consumes, now from ball-local data.
    • `two_term_census_bound_ballLocal_hyp_satisfiable` — non-vacuity with TEETH that exercise the ACTUAL
        N1 point: `q₁ = ‖z‖²`, `q₂ = ‖z‖` are locally bounded on `ball 0 1` but GLOBALLY UNBOUNDED, so
        the global two-term core would reject them (`sin`/`cos` would NOT exercise N1 — Sol).

  ## HONEST STATUS (blunt, extreme-stakes; gpt-5.6-sol high adversarially audited — corrected below).
  This removes ONLY the global-vs-ball boundedness mismatch (N1), and ONLY for the **ball-local
  subproblem** (integration over the same `ball 0 r`).  It does NOT close `hCensusBound`/`hCross`, and it
  does NOT by itself repair the CoV integral over the whole IMAGE.  Sol's corrections to the earlier
  triple-mismatch framing (all three were NOT independent new structural gaps):
    • **N1 is genuine** and is what this adapter resolves for the ball-local subproblem.  Sol confirms the
      truncation is logically sound: on `ball 0 r` the indicator agrees with `q` (so the integrand is
      unchanged and `setIntegral_congr_fun` restores it), off it `= 0 ≤ M`, and `0 ∈ ball 0 r` (`r>0`)
      preserves the center value — hence global boundedness + center-Lipschitz both hold for the
      truncation.
    • **N2 was MISDIAGNOSED.**  `two_term_census_bound_uniform` accepts ANY measurable `Ω ⊇ ball 0 r`, so
      the non-ball shape of the CoV image `Wbv''(ball 0 ρ)` is NOT itself an obstruction.  The REAL
      remaining obligation is the **image-residue / localization** cost incurred by truncating to a ball:
      on `Wbv''(ball 0 ρ) \ ball 0 r` the truncated coefficient is `0` while the transported one is not,
      so that residue must be separately controlled (whole-image coefficient bounds, an integrand-vanishing
      argument, a preimage-localized CoV, or a coordinate-compatible envelope estimate).
    • **N3 is NOT a structural mismatch** — it is routine `simp_rw`/`congr`/`setIntegral_congr` plumbing on
      the banked weight-match `Wbv (V w) = w` (G1); no new assumption.
    • Also (Sol): the gate predicate is `z ∈ K ∧ 0 ∈ S z`; G2 supplies only the `0 ∈ S z` conjunct, so the
      `z ∈ K` half (from `K ∈ 𝓝 0`) must also be threaded.
  So the residual CoV-junction obligations are: the **image-residue localization** just described, the
  gate-split integral restriction (G2 + the `z ∈ K` half), the off-ball Gaussian envelope + integrability
  for the domain bridge, and the final rate absorption — NONE in this file.  `hDuhamel`/`hDConv` remain
  carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussTauTraceChartTransported

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.CensusTwoTermBallLocal

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the BALL-LOCAL two-term Gaussian census bound (resolves N1).
    ############################################################################### -/

/-- **★★ `two_term_census_bound_ballLocal` — the BALL-LOCAL flat two-term Gaussian census bound.**  For
    `0 < τ ≤ T`, `r > 0`, and weights `q₁, q₂` that are measurable and bounded (`|q₁|≤M₁`, `|q₂|≤M₂`) +
    (`q₁`) CENTER-Lipschitz (`L`) ONLY on the ball `ball 0 r` (exactly the ball-local regularity the
    common-witness transport / Levi F-factor deliver),
      `|∫_{ball 0 r}(∑ᵢ(zᵢ²/4τ²−1/2τ))·gaussDdim τ z·q₁ z  +  ∫_{ball 0 r} gaussDdim τ z·q₂ z|
         ≤ (L·(n²(16√2+1)) + (3n·M₁·√2ⁿ·(4(2n+1)/r²) + M₂)·√T)/√τ` .
    Proof: truncate `q₁, q₂` to `Set.indicator (ball 0 r) q` (globally bounded by `M`, agreeing with `q`
    on `ball 0 r`, center-value `q 0` preserved since `0 ∈ ball 0 r`), apply
    `two_term_census_bound_uniform_combined` with superset `Ω := ball 0 r`, then restore the
    un-truncated integrand on `ball 0 r` by `setIntegral_congr_fun`.  NOT `a₁ = R/6`. -/
theorem two_term_census_bound_ballLocal
    (τ r T : ℝ) (hτ : 0 < τ) (hτT : τ ≤ T) (hr : 0 < r)
    (q₁ q₂ : Point n → ℝ)
    (L M₁ M₂ : ℝ) (hL : 0 ≤ L) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hq₁meas : AEStronglyMeasurable q₁ volume) (hq₂meas : AEStronglyMeasurable q₂ volume)
    (hq₁bnd : ∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z| ≤ M₁)
    (hq₂bnd : ∀ z ∈ Metric.ball (0 : Point n) r, |q₂ z| ≤ M₂)
    (hcl : ∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖) :
    |(∫ z in Metric.ball (0 : Point n) r,
          (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z)
        + (∫ z in Metric.ball (0 : Point n) r, gaussDdim τ z * q₂ z)|
      ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1))
          + (3 * (n : ℝ) * M₁ * (Real.sqrt 2 ^ n * (4 * (2 * (n : ℝ) + 1) / r ^ 2)) + M₂)
              * Real.sqrt T) / Real.sqrt τ := by
  classical
  set B : Set (Point n) := Metric.ball (0 : Point n) r with hBdef
  have hBmeas : MeasurableSet B := measurableSet_ball
  have h0B : (0 : Point n) ∈ B := Metric.mem_ball_self hr
  -- Truncated weights: `0` off the ball, so GLOBALLY bounded.
  set qt1 : Point n → ℝ := Set.indicator B q₁ with hqt1def
  set qt2 : Point n → ℝ := Set.indicator B q₂ with hqt2def
  -- measurability.
  have hqt1meas : AEStronglyMeasurable qt1 volume := hq₁meas.indicator hBmeas
  have hqt2meas : AEStronglyMeasurable qt2 volume := hq₂meas.indicator hBmeas
  -- global boundedness of the truncations.
  have hqt1bnd : ∀ z, |qt1 z| ≤ M₁ := by
    intro z
    rw [hqt1def, Set.indicator_apply]
    by_cases hz : z ∈ B
    · simp only [if_pos hz]; exact hq₁bnd z hz
    · simp only [if_neg hz, abs_zero]; exact hM₁
  have hqt2bnd : ∀ z, |qt2 z| ≤ M₂ := by
    intro z
    rw [hqt2def, Set.indicator_apply]
    by_cases hz : z ∈ B
    · simp only [if_pos hz]; exact hq₂bnd z hz
    · simp only [if_neg hz, abs_zero]; exact hM₂
  -- center value preserved (`0 ∈ B`) ⟹ center-Lipschitz on `B` transfers to `qt1`.
  have hqt10 : qt1 (0 : Point n) = q₁ 0 := by rw [hqt1def]; exact Set.indicator_of_mem h0B q₁
  have hqtcl : ∀ z ∈ Metric.ball (0 : Point n) r, |qt1 z - qt1 0| ≤ L * ‖z‖ := by
    intro z hz
    have hzB : z ∈ B := hz
    rw [hqt1def, Set.indicator_of_mem hzB q₁]
    rw [hqt1def] at hqt10
    rw [hqt10]
    exact hcl z hz
  -- the flat two-term uniform bound at the truncated weights, over `Ω := B ⊇ ball 0 r`.
  have h := two_term_census_bound_uniform_combined τ r T hτ hτT hr qt1 qt2 L M₁ M₂ hL hM₁ hM₂
    hqt1meas hqt2meas hqt1bnd hqt2bnd hqtcl B hBmeas (le_of_eq hBdef.symm)
  -- restore the un-truncated integrand on `B` (indicator agrees with `q` there).
  have e1 : (∫ z in B, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * qt1 z)
      = ∫ z in Metric.ball (0 : Point n) r,
          (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q₁ z := by
    rw [← hBdef]
    refine setIntegral_congr_fun hBmeas (fun z hz => ?_)
    rw [hqt1def, Set.indicator_of_mem hz q₁]
  have e2 : (∫ z in B, gaussDdim τ z * qt2 z)
      = ∫ z in Metric.ball (0 : Point n) r, gaussDdim τ z * q₂ z := by
    rw [← hBdef]
    refine setIntegral_congr_fun hBmeas (fun z hz => ?_)
    rw [hqt2def, Set.indicator_of_mem hz q₂]
  rw [e1, e2] at h
  exact h

/-! ###############################################################################
    ### §B — non-vacuity (with TEETH: locally bounded but NOT globally bounded weights).
    ############################################################################### -/

/-- **Non-vacuity of `two_term_census_bound_ballLocal` — TEETH that exercise the ACTUAL N1 mismatch.**
    The point of the adapter is admitting weights that are bounded ONLY ball-locally, so the witness must
    be locally-bounded-but-NOT-globally-bounded (`sin`/`cos`, being globally bounded, would NOT exercise
    N1 — per gpt-5.6-sol audit).  Exhibited at `q₁ z := ‖z‖²` (on `ball 0 1`: `‖z‖²<1` so `M₁=1`;
    center-Lipschitz `L=1` via `‖z‖²≤‖z‖`; GLOBALLY UNBOUNDED) and `q₂ z := ‖z‖` (on `ball 0 1`:
    `‖z‖<1` so `M₂=1`; GLOBALLY UNBOUNDED), on a genuine ball (`r=1`, `0<τ=1≤T=1`).  So the ball-local
    bound fires precisely on weights the GLOBAL two-term core would REJECT.  NOT `a₁ = R/6`. -/
theorem two_term_census_bound_ballLocal_hyp_satisfiable :
    ∃ (τ r T : ℝ) (q₁ q₂ : Point n → ℝ) (L M₁ M₂ : ℝ),
      0 < τ ∧ τ ≤ T ∧ 0 < r ∧ 0 ≤ L ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
        AEStronglyMeasurable q₁ (volume : Measure (Point n)) ∧
        AEStronglyMeasurable q₂ (volume : Measure (Point n)) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z| ≤ M₁) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q₂ z| ≤ M₂) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q₁ z - q₁ 0| ≤ L * ‖z‖) := by
  refine ⟨1, 1, 1, fun z => ‖z‖ ^ 2, fun z => ‖z‖, 1, 1, 1,
    one_pos, le_refl 1, one_pos, zero_le_one, zero_le_one, zero_le_one,
    (continuous_norm.pow 2).aestronglyMeasurable,
    continuous_norm.aestronglyMeasurable, ?_, ?_, ?_⟩
  · intro z hz
    have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    rw [abs_of_nonneg (by positivity)]
    nlinarith [hz1, norm_nonneg z]
  · intro z hz
    have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    rw [abs_of_nonneg (norm_nonneg z)]; exact le_of_lt hz1
  · intro z hz
    have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    show |‖z‖ ^ 2 - ‖(0 : Point n)‖ ^ 2| ≤ 1 * ‖z‖
    have h0 : ‖(0 : Point n)‖ ^ 2 = 0 := by simp
    rw [h0, sub_zero, one_mul, abs_of_nonneg (by positivity)]
    nlinarith [hz1, norm_nonneg z]

end QIQTH.CensusTwoTermBallLocal

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusTwoTermBallLocal
#print axioms two_term_census_bound_ballLocal
#print axioms two_term_census_bound_ballLocal_hyp_satisfiable
end AxiomChecks
