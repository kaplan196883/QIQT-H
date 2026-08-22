/-
  ChartIFTPackageGeneralQ0 — J4-1011: the EVAL-SLOT (field-varying) local INVERSE-FUNCTION-THEOREM
  package for the concrete normal chart at a GENERAL interior base point `q₀ ∈ interior K`, generalizing
  `ChartIFTPackage.chartIFTPackage`/`chart_gaussian_change_variables_concrete` (J4-270, tied to `q₀ = 0`)
  to arbitrary `q₀`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `VanVleckGatedSpatialSymmetry.hcomp`'s NEAR carry `nb`'s STEP-4c residual (r6), per J4-1010's
  honesty firewall: the antisymmetrization producing the near-isometry DIFFERENCE `G_τ(T_x v) − G_τ(v)`
  that `HCompNearCarryFullyClosed`'s item (iv) machinery (`terminalVelAt_chartReplace_sliver_bound`)
  consumes needs a genuine EVAL-SLOT change of variables `v := uniformInverseChart g gi hC hK x z`
  (base `x` FIXED at the field point, field `z` VARYING) — NOT the BASE-slot CoV `w := uniformInverseChart
  g gi hC hK z x` (base `z` varying) that J4-1008/1010 built.  The evenness link (`HCompNearCarryFullyClosed
  .gaussDdim_reversal_link`, already banked) connects the BASE-slot Gaussian appearing in `kPrime`'s
  literal shape to `G_τ(T_x v)` with `v := uniformInverseChart g gi hC hK x z` EXACTLY (not merely
  approximately) — but only an EVAL-slot CoV, transporting the integration variable to that same `v`,
  can turn this into a literal integral over `v` that `terminalVelAt_chartReplace_sliver_bound`'s
  difference bound directly dominates.

  The ONLY banked eval-slot CoV package (`ChartIFTPackage.chartIFTPackage`/
  `chart_gaussian_change_variables_concrete`, J4-270) is tied to base point `q₀ = 0` — it does NOT apply
  at the field point `x` of `nb`'s cell, which is a GENERAL interior point.  `HCrossDerivEngineWired`
  (J4-929) independently flagged this exact "FIELD-slot chart ... base 0" specialization as a genuine
  slot/basepoint mismatch for its own (unrelated) `hCross` wall.

  THIS FILE removes the `q₀ = 0` restriction: `ChartIFTPackage.chartIFTPackage`'s ENTIRE proof transplants
  VERBATIM to a general interior `q₀ ∈ interior K` (SAME arbitrary fixed `hK`, no `K := closedBall q₀ 1`
  re-tying), because its three inputs — `ContDiffAt ℝ 2 W_{q₀} q₀`, `fderiv ℝ W_{q₀} q₀ = Id`, and
  `W_{q₀} q₀ = 0` — are ALL ALREADY BANKED at general interior `q₀` by the J4-884/1006 generalization
  campaign (`JointRNCRegularityInterfaceLocalGeneralK.uniformInverseChart_slice_contDiffAt_diag_generalK`
  / `..._slice_fderiv_id_diag_generalK` / `..._slice_value_diag_generalK`), a fact NOT exploited by any
  prior file (don't-undercredit finding, same pattern as J4-1006's own "F3/F4 already general-K" finding).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  routine TRANSPLANT of `ChartIFTPackage.chartIFTPackage`'s Mathlib-IFT argument
  (`ContDiffAt.toOpenPartialHomeomorph`) from the base point `0` to a general interior `q₀ ∈ interior K`,
  using the ALREADY-BANKED general-`q₀` center facts as the sole new input (no new geometric content).
  It supplies the EVAL-SLOT CoV package at general `q₀` — it does NOT itself compose this with the
  evenness link, with J4-1010's `kPrime` factorization, or with `terminalVelAt_chartReplace_sliver_bound`
  to produce a literal bound on `nb`; that composition (identifying `V`'s image set with `ball 0 R`,
  reconciling `ball x ρ` with the CoV's domain `ball q₀ ρ`, and threading the resulting difference
  integral through the rest of STEP-4c) is a SEPARATE, NOT-attempted next step.  `a₁ = R/6` remains
  STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file
  edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartIFTPackage
import QIQTH.JointRNCRegularityInterfaceLocalGeneralK

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.JointRNCRegularityLocalGeneralK
open scoped Topology

namespace QIQTH.ChartIFTPackageGeneralQ0

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `chartIFTPackage_generalQ0` — the uniform local IFT package (M1–M4), general interior `q₀`.**
    For the EVAL-slot chart `W_{q₀} = uniformInverseChart g gi hC hK q₀` (base `q₀ ∈ interior K`, SAME
    arbitrary fixed `hK`), there is a radius `ρ > 0`, a left inverse `V`, and a derivative field `f'`
    such that on the gate `S₀ = ball q₀ ρ`:
      (M1) `HasFDerivWithinAt W_{q₀} (f' z) S₀ z`,  (M2) `Set.InjOn W_{q₀} S₀`,
      (M3) `V (W_{q₀} z) = z`,                        (M4) `0 < |(f' z).det|`,
    and the chart image is a neighbourhood of `0`:  `W_{q₀} '' S₀ ∈ 𝓝 0`.  VERBATIM transplant of
    `ChartIFTPackage.chartIFTPackage`'s proof, substituting the general-`q₀` center facts
    (`uniformInverseChart_slice_contDiffAt_diag_generalK`, `..._slice_fderiv_id_diag_generalK`,
    `..._slice_value_diag_generalK`) for the `q₀ = 0`-specific ones.  NOT `a₁ = R/6`. -/
theorem chartIFTPackage_generalQ0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball q₀ ρ)
      ∧ (∀ z ∈ Metric.ball q₀ ρ,
          HasFDerivWithinAt (uniformInverseChart g gi hC hK q₀) (f' z)
            (Metric.ball q₀ ρ) z)
      ∧ Set.InjOn (uniformInverseChart g gi hC hK q₀) (Metric.ball q₀ ρ)
      ∧ (∀ z ∈ Metric.ball q₀ ρ, V (uniformInverseChart g gi hC hK q₀ z) = z)
      ∧ (∀ z ∈ Metric.ball q₀ ρ, 0 < |(f' z).det|)
      ∧ (uniformInverseChart g gi hC hK q₀) '' (Metric.ball q₀ ρ)
          ∈ 𝓝 (0 : Point n) := by
  classical
  set W₀ := uniformInverseChart g gi hC hK q₀ with hW₀def
  -- Banked centre facts, GENERAL `q₀`.
  have hW0 : ContDiffAt ℝ 2 W₀ q₀ :=
    uniformInverseChart_slice_contDiffAt_diag_generalK g gi hC hK q₀ hq₀
  have hfd_id : fderiv ℝ W₀ q₀ = ContinuousLinearMap.id ℝ (Point n) :=
    uniformInverseChart_slice_fderiv_id_diag_generalK g gi hC hK q₀ hq₀
  have hval0 : W₀ q₀ = 0 :=
    uniformInverseChart_slice_value_diag_generalK g gi hC hK q₀ hq₀
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hWdiff0 : DifferentiableAt ℝ W₀ q₀ := hW0.differentiableAt (by norm_num)
  -- The IFT input `HasFDerivAt W₀ ↑(refl) q₀`.
  have hW'0 : HasFDerivAt W₀
      ((ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)) q₀ := by
    have hcoe : fderiv ℝ W₀ q₀ = ((ContinuousLinearEquiv.refl ℝ (Point n)) : Point n →L[ℝ] Point n) := by
      rw [hfd_id, ContinuousLinearEquiv.coe_refl]
    rw [← hcoe]; exact hWdiff0.hasFDerivAt
  -- The IFT open partial homeomorph of `W₀` at `q₀`.
  set Φ := hW0.toOpenPartialHomeomorph W₀ hW'0 hn2 with hΦdef
  have hΦcoe : (⇑Φ : Point n → Point n) = W₀ := by
    rw [hΦdef]; exact hW0.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (q₀ : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hW0.mem_toOpenPartialHomeomorph_source hW'0 hn2
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp Φ.open_source q₀ h0src
  -- C² on a neighbourhood ⟹ differentiability field near `q₀`.
  have hevC2 : ∀ᶠ y in 𝓝 (q₀ : Point n), ContDiffAt ℝ 2 W₀ y := hW0.eventually (by norm_num)
  have hevdiff : ∀ᶠ y in 𝓝 (q₀ : Point n), DifferentiableAt ℝ W₀ y :=
    hevC2.mono (fun _ hy => hy.differentiableAt (by norm_num))
  -- Jacobian-determinant continuity at `q₀`, with value `det Id = 1`.
  have hfderiv_cont : ContinuousAt (fun y => fderiv ℝ W₀ y) q₀ :=
    (hW0.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hdet_cont : ContinuousAt (fun y => (fderiv ℝ W₀ y).det) q₀ :=
    (ContinuousLinearMap.continuous_det.continuousAt).comp hfderiv_cont
  have hdet0 : (fderiv ℝ W₀ q₀).det = 1 := by
    rw [hfd_id]; simp [ContinuousLinearMap.det]
  have hdet_gt0 : (1 : ℝ) / 2 < (fderiv ℝ W₀ q₀).det := by rw [hdet0]; norm_num
  have hevdet : ∀ᶠ y in 𝓝 (q₀ : Point n), (1 : ℝ) / 2 < (fderiv ℝ W₀ y).det :=
    hdet_cont.tendsto.eventually (eventually_gt_nhds hdet_gt0)
  -- Combine into a single small ball.
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hevdiff.and hevdet)
  refine ⟨min δ₁ ε, lt_min hδ₁ hε, (⇑Φ.symm : Point n → Point n),
    (fun z => fderiv ℝ W₀ z), measurableSet_ball, ?_, ?_, ?_, ?_, ?_⟩
  · -- M1: within-derivative field.
    intro z hz
    have hzε : dist z (q₀ : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    exact ((hεspec hzε).1.hasFDerivAt).hasFDerivWithinAt
  · -- M2: injectivity on the ball, from `Φ.injOn`.
    have hinjS : Set.InjOn (⇑Φ) Φ.source := Φ.injOn
    rw [hΦcoe] at hinjS
    exact hinjS.mono (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
  · -- M3: `Φ.symm` is a left inverse on the ball.
    intro z hz
    have hzsrc : z ∈ Φ.source :=
      hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz)
    have h := Φ.left_inv hzsrc
    have hcz : (⇑Φ : Point n → Point n) z = W₀ z := congrFun hΦcoe z
    rw [hcz] at h; exact h
  · -- M4: positive Jacobian.
    intro z hz
    have hzε : dist z (q₀ : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have hpos : (0 : ℝ) < (fderiv ℝ W₀ z).det := by linarith [(hεspec hzε).2]
    exact lt_of_lt_of_le hpos (le_abs_self _)
  · -- image neighbourhood glue.
    have hopen : IsOpen ((⇑Φ) '' Metric.ball (q₀ : Point n) (min δ₁ ε)) :=
      Φ.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
    rw [hΦcoe] at hopen
    have hmem : (0 : Point n) ∈ W₀ '' Metric.ball (q₀ : Point n) (min δ₁ ε) :=
      ⟨q₀, Metric.mem_ball_self (lt_min hδ₁ hε), hval0⟩
    exact hopen.mem_nhds hmem

/-- **`chartImage_mem_nhds_generalQ0`.**  The glue fact alone, general `q₀`.  NOT `a₁ = R/6`. -/
theorem chartImage_mem_nhds_generalQ0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K) :
    ∃ ρ > (0 : ℝ),
      (uniformInverseChart g gi hC hK q₀) '' (Metric.ball q₀ ρ) ∈ 𝓝 (0 : Point n) := by
  obtain ⟨ρ, hρ, _, _, _, _, _, _, _, himg⟩ := chartIFTPackage_generalQ0 g gi hC hK hq₀
  exact ⟨ρ, hρ, himg⟩

/-- **★★★ `chart_gaussian_change_variables_concrete_generalQ0` — the CONCRETE EVAL-SLOT change of
    variables at general `q₀`.**  Instantiates `ChartGaussianChangeVar.chart_gaussian_change_variables`
    at the real normal chart `W_{q₀} = uniformInverseChart g gi hC hK q₀` (base `q₀ ∈ interior K`) on the
    gate `S_{q₀} = ball q₀ ρ`, with the M1–M4 bundle discharged by `chartIFTPackage_generalQ0`.  For any
    `τ` and any weight `B`:
        `∫ z in ball q₀ ρ, gaussDdim τ (W_{q₀} z) · B z`
          = `∫ w in W_{q₀} '' (ball q₀ ρ), gaussDdim τ w · (B (V w) / |(D W_{q₀} (V w)).det|)`,
    with `V = Φ.symm` the IFT local inverse.  General-`q₀` analogue of `ChartIFTPackage.chart_gaussian_
    change_variables_concrete` (J4-270, there tied to `q₀ = 0`).  NOT `a₁ = R/6`. -/
theorem chart_gaussian_change_variables_concrete_generalQ0
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball q₀ ρ,
          gaussDdim τ (uniformInverseChart g gi hC hK q₀ z) * B z)
        = ∫ w in (uniformInverseChart g gi hC hK q₀) '' (Metric.ball q₀ ρ),
            gaussDdim τ w * (B (V w) / |(f' (V w)).det|) := by
  obtain ⟨ρ, hρ, V, f', hS, hfd, hinj, hV, hJpos, _⟩ := chartIFTPackage_generalQ0 g gi hC hK hq₀
  refine ⟨ρ, hρ, V, f', ?_⟩
  exact QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball q₀ ρ) (uniformInverseChart g gi hC hK q₀) V f'
    (fun z => |(f' z).det|) B hS hfd hinj hV (fun _ _ => rfl) hJpos

end QIQTH.ChartIFTPackageGeneralQ0

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.ChartIFTPackageGeneralQ0
#print axioms chartIFTPackage_generalQ0
#print axioms chartImage_mem_nhds_generalQ0
#print axioms chart_gaussian_change_variables_concrete_generalQ0
end AxiomChecks
