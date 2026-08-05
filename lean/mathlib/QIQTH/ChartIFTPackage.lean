/-
  ChartIFTPackage — J4-270: the uniform local INVERSE-FUNCTION-THEOREM package for the concrete
  normal chart `W₀ = uniformInverseChart g gi hC hK 0`, discharging the missing-fact bundle
  (M1–M4) that `ChartGaussianChangeVar` (Layer B) needs for its CONCRETE instantiation.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign, SOL#5 3-layer chart-image approximate-identity
  plan).  Layer C (`ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving`) and Layer B
  abstract (`ChartGaussianChangeVar.chart_gaussian_change_variables`) are landed.  Layer B consumes
  a change-of-variables DATA BUNDLE for a C¹ chart `W` on a gate `S`:
    (M1)  a within-derivative field `∀ z ∈ S, HasFDerivWithinAt W (f' z) S z`,
    (M2)  `Set.InjOn W S`,
    (M3)  a left inverse `V` with `∀ z ∈ S, V (W z) = z`,
    (M4)  a positive Jacobian `∀ z ∈ S, 0 < |(f' z).det|`.
  For the CONCRETE chart `W₀ = uniformInverseChart g gi hC hK 0` (base 0, field slot varying) this
  file PROVES M1–M4 on a genuine small ball `S₀ = ball 0 ρ` — none of M1–M4 is carried.

  ── WHAT IS PROVEN vs CARRIED.
    • PROVEN (from the banked centre facts, NOT hypotheses):
        `chartField_contDiffAt_center`  (W₀ ∈ C² at 0),
        `chartField_centerValue_base0`  (W₀ 0 = 0),
        `chartField_fderiv_center`      (D W₀(0) = Id).
      From `D W₀(0) = Id` (an invertible equiv) + C², Mathlib's IFT
      `ContDiffAt.toOpenPartialHomeomorph` exhibits `W₀` as an open partial homeomorph `Φ` near 0
      (⇑Φ = W₀, `0 ∈ Φ.source` open), giving M2 (`Φ.injOn`) and M3 (`Φ.symm` with `Φ.left_inv`)
      GRATIS on `Φ.source`.  C² on a NEIGHBOURHOOD (`ContDiffAt.eventually`) gives M1
      (differentiability field `f' z = fderiv ℝ W₀ z`), and continuity of `z ↦ (D W₀ z).det`
      with value `det Id = 1` gives M4 (`> 1/2 > 0` on a smaller ball).
    • CARRIED (exactly the geometry the bank already carries — NEVER the conclusion): the metric
      Christoffel-`C∞` field `hC`, the compact base `hK`, and `0 ∈ K`.  These are the inputs the
      chart's OWN regularity (`uniformInverseChart_huniformChart`) is built from; they are satisfiable
      and non-vacuous (any smooth metric on a compact set containing the origin).

  ── WHAT LANDS.
    • `chartIFTPackage`                       — ★ the M1–M4 bundle on `S₀ = ball 0 ρ`, plus the
       image-neighbourhood glue `W₀ '' (ball 0 ρ) ∈ 𝓝 0`.
    • `chartImage_mem_nhds`                    — the glue fact alone (Layer C needs `Ω ∈ 𝓝 0`).
    • `chart_gaussian_change_variables_concrete` — ★ the capstone: the concrete Layer-B change of
       variables for `W₀` at `S₀`, feeding `chart_gaussian_change_variables`.

  ⚠ HONEST FIREWALL.  This is NOT `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE analytic
  brick (the concrete IFT package for the Layer-B change of variables).  No `sorry` (prose only),
  no new axioms, no `:= True`, no vacuous / conclusion-in-disguise hypotheses:  M2/M3 are PROVEN
  from the IFT partial homeomorph, not assumed.  No existing file is edited.
-/
import Mathlib
import QIQTH.ChartJetBounds
import QIQTH.ChartGaussianChangeVar

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.ChartIFTPackage

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ `chartIFTPackage` — the uniform local IFT package (M1–M4) for the concrete normal chart.**
    For the field-slot chart `W₀ = uniformInverseChart g gi hC hK 0` (base `0 ∈ K`), there is a
    radius `ρ > 0`, a left inverse `V`, and a derivative field `f'` such that on the gate
    `S₀ = ball 0 ρ`:
      (M1) `HasFDerivWithinAt W₀ (f' z) S₀ z`,  (M2) `Set.InjOn W₀ S₀`,
      (M3) `V (W₀ z) = z`,                        (M4) `0 < |(f' z).det|`,
    and the chart image is a neighbourhood of `0`:  `W₀ '' S₀ ∈ 𝓝 0`.

    All four are DERIVED (not carried): the banked centre facts `chartField_contDiffAt_center`
    (C²), `chartField_fderiv_center` (`D W₀(0) = Id`) feed `ContDiffAt.toOpenPartialHomeomorph`
    (M2/M3), `ContDiffAt.eventually` gives M1, and continuity of `det ∘ D W₀` with `det Id = 1`
    gives M4.  NOT `a₁ = R/6`. -/
theorem chartIFTPackage (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt (uniformInverseChart g gi hC hK 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn (uniformInverseChart g gi hC hK 0) (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, V (uniformInverseChart g gi hC hK 0 z) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (uniformInverseChart g gi hC hK 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n) := by
  classical
  set W₀ := uniformInverseChart g gi hC hK 0 with hW₀def
  -- Banked centre facts.
  have hW0 : ContDiffAt ℝ 2 W₀ 0 := chartField_contDiffAt_center g gi hC hK h0K
  have hfd_id : fderiv ℝ W₀ 0 = ContinuousLinearMap.id ℝ (Point n) :=
    chartField_fderiv_center g gi hC hK h0K
  have hn2 : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hWdiff0 : DifferentiableAt ℝ W₀ 0 := hW0.differentiableAt (by norm_num)
  -- The IFT input `HasFDerivAt W₀ ↑(refl) 0`.
  have hW'0 : HasFDerivAt W₀
      ((ContinuousLinearEquiv.refl ℝ (Point n) : Point n →L[ℝ] Point n)) 0 := by
    have hcoe : fderiv ℝ W₀ 0 = ((ContinuousLinearEquiv.refl ℝ (Point n)) : Point n →L[ℝ] Point n) := by
      rw [hfd_id, ContinuousLinearEquiv.coe_refl]
    rw [← hcoe]; exact hWdiff0.hasFDerivAt
  -- The IFT open partial homeomorph of `W₀` at `0`.
  set Φ := hW0.toOpenPartialHomeomorph W₀ hW'0 hn2 with hΦdef
  have hΦcoe : (⇑Φ : Point n → Point n) = W₀ := by
    rw [hΦdef]; exact hW0.toOpenPartialHomeomorph_coe hW'0 hn2
  have h0src : (0 : Point n) ∈ Φ.source := by
    rw [hΦdef]; exact hW0.mem_toOpenPartialHomeomorph_source hW'0 hn2
  obtain ⟨δ₁, hδ₁, hδ₁sub⟩ := Metric.isOpen_iff.mp Φ.open_source 0 h0src
  -- C² on a neighbourhood ⟹ differentiability field near 0.
  have hevC2 : ∀ᶠ y in 𝓝 (0 : Point n), ContDiffAt ℝ 2 W₀ y := hW0.eventually (by norm_num)
  have hevdiff : ∀ᶠ y in 𝓝 (0 : Point n), DifferentiableAt ℝ W₀ y :=
    hevC2.mono (fun _ hy => hy.differentiableAt (by norm_num))
  -- Jacobian-determinant continuity at 0, with value `det Id = 1`.
  have hfderiv_cont : ContinuousAt (fun y => fderiv ℝ W₀ y) 0 :=
    (hW0.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hdet_cont : ContinuousAt (fun y => (fderiv ℝ W₀ y).det) 0 :=
    (ContinuousLinearMap.continuous_det.continuousAt).comp hfderiv_cont
  have hdet0 : (fderiv ℝ W₀ 0).det = 1 := by
    rw [hfd_id]; simp [ContinuousLinearMap.det]
  have hdet_gt0 : (1 : ℝ) / 2 < (fderiv ℝ W₀ 0).det := by rw [hdet0]; norm_num
  have hevdet : ∀ᶠ y in 𝓝 (0 : Point n), (1 : ℝ) / 2 < (fderiv ℝ W₀ y).det :=
    hdet_cont.tendsto.eventually (eventually_gt_nhds hdet_gt0)
  -- Combine into a single small ball.
  obtain ⟨ε, hε, hεspec⟩ := Metric.eventually_nhds_iff.mp (hevdiff.and hevdet)
  refine ⟨min δ₁ ε, lt_min hδ₁ hε, (⇑Φ.symm : Point n → Point n),
    (fun z => fderiv ℝ W₀ z), measurableSet_ball, ?_, ?_, ?_, ?_, ?_⟩
  -- ball ⊆ source (for M2/M3 and the image).
  · -- M1: within-derivative field.
    intro z hz
    have hzε : dist z (0 : Point n) < ε :=
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
    have hzε : dist z (0 : Point n) < ε :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have hpos : (0 : ℝ) < (fderiv ℝ W₀ z).det := by linarith [(hεspec hzε).2]
    exact lt_of_lt_of_le hpos (le_abs_self _)
  · -- image neighbourhood glue.
    have hopen : IsOpen ((⇑Φ) '' Metric.ball (0 : Point n) (min δ₁ ε)) :=
      Φ.isOpen_image_of_subset_source Metric.isOpen_ball
        (fun z hz => hδ₁sub (Metric.ball_subset_ball (min_le_left _ _) hz))
    rw [hΦcoe] at hopen
    have hmem : (0 : Point n) ∈ W₀ '' Metric.ball (0 : Point n) (min δ₁ ε) :=
      ⟨0, Metric.mem_ball_self (lt_min hδ₁ hε), chartField_centerValue_base0 g gi hC hK h0K⟩
    exact hopen.mem_nhds hmem

/-- **`chartImage_mem_nhds` — the chart image is a neighbourhood of `0`.**  The glue fact Layer C's
    moving approximate identity consumes (`Ω = W₀ '' (ball 0 ρ) ∈ 𝓝 0`).  Read off the package.
    NOT `a₁ = R/6`. -/
theorem chartImage_mem_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ∃ ρ > (0 : ℝ),
      (uniformInverseChart g gi hC hK 0) '' (Metric.ball (0 : Point n) ρ) ∈ 𝓝 (0 : Point n) := by
  obtain ⟨ρ, hρ, _, _, _, _, _, _, _, himg⟩ := chartIFTPackage g gi hC hK h0K
  exact ⟨ρ, hρ, himg⟩

/-- **★ `chart_gaussian_change_variables_concrete` — the CONCRETE Layer-B change of variables.**
    Instantiates the abstract `ChartGaussianChangeVar.chart_gaussian_change_variables` at the real
    normal chart `W₀ = uniformInverseChart g gi hC hK 0` on the gate `S₀ = ball 0 ρ`, with the
    M1–M4 bundle discharged by `chartIFTPackage`.  For any `τ` and any weight `B`:

        `∫ z in ball 0 ρ, gaussDdim τ (W₀ z) · B z`
          = `∫ w in W₀ '' (ball 0 ρ), gaussDdim τ w · (B (V w) / |(D W₀ (V w)).det|)`,

    with `V = Φ.symm` the IFT local inverse.  This is exactly the shape Layer C
    (`gaussDdim_set_approx_identity_moving`) consumes, with `Ω := W₀ '' (ball 0 ρ)`
    (a neighbourhood of `0` by `chartImage_mem_nhds`) and moving integrand
    `g τ w := B (V w) / |(D W₀ (V w)).det|`.  NOT `a₁ = R/6`. -/
theorem chart_gaussian_change_variables_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball (0 : Point n) ρ,
          gaussDdim τ (uniformInverseChart g gi hC hK 0 z) * B z)
        = ∫ w in (uniformInverseChart g gi hC hK 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w * (B (V w) / |(f' (V w)).det|) := by
  obtain ⟨ρ, hρ, V, f', hS, hfd, hinj, hV, hJpos, _⟩ := chartIFTPackage g gi hC hK h0K
  refine ⟨ρ, hρ, V, f', ?_⟩
  exact QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball (0 : Point n) ρ) (uniformInverseChart g gi hC hK 0) V f'
    (fun z => |(f' z).det|) B hS hfd hinj hV (fun _ _ => rfl) hJpos

end QIQTH.ChartIFTPackage

section AxiomChecks
open QIQTH.ChartIFTPackage
#print axioms chartIFTPackage
#print axioms chartImage_mem_nhds
#print axioms chart_gaussian_change_variables_concrete
end AxiomChecks
