/-
  WidthOneQuadResidual — J4-676: THE SURVIVING WIDTH WALL, EXTRACTED.

  The single width wall feeding the banked `hraw`/`hEdom` chain is the CURVED width-1 in-chart QUADRATIC
  parametrix residual — the input shape `HrawPreCollapse.chartTransfer_quad`/`chartTransfer_quad_from_
  nearIsometry` names but never receives:
      `A ≤ B·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v)`     (WIDTH 1, QUADRATIC in `r²_v/τ`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE EXTRACTION VERDICT (scoping finding, J4-676).

  The banked M2 engine `WidthMarginEngine.uniformResidual_gaussian_bound_tau_narrow` already decomposes
  the `N = 0` parametrix residual into the graded `T1 + T2 − T3` (via `parametrixResidual_N0_O1_isolated_
  C2`), and its OWN pre-absorption sub-bounds ARE the width-1 polynomial forms:
      |T1| = (1/τ)·G_τ·|totalRadialO1_coeff|         ≤ C_c·(r²_v/τ)·G_τ        [LINEAR — via `hCoeffU`],
      |T2| = (1/τ²)·G_τ·|(-1/4)·⟨(g⁻¹−δ)v⊗v⟩|·|w₀|   ≤ (n²MW/4)·(r²_v/τ)²·G_τ  [QUADRATIC — `|S|≤n²Mr⁴`],
      |T3| = G_τ·|Laplace–Beltrami w₀|               ≤ L·G_τ                    [CONSTANT — via `hLapU`].
  The engine then applies the M1 NARROW absorptions (`rncRadialSq_pow_mul_gaussDdim_le_narrow`, m=0,1,2)
  to COLLAPSE each into a constant × `gaussDdim (3/2·τ)`.  The width-1 QUADRATIC residual is EXACTLY that
  same grading WITHOUT the final absorption — keep the polynomial factors explicit, stay at width `τ`.

  Hence this is an EXTRACTION, not new analysis: re-run the engine's assembly with the RAW pointwise
  supplier bounds (`uniformFlowPullbackMetricInv_dev_uniform`, `uniformFlowLaplaceBeltrami_w0_near_
  uniform`, `hCoeffU`) in place of the three narrow-absorption applications.  The finer QUADRATIC form is
  a LABELLED CARRY even in the FLAT tower (the narrow producer collapses to 3/2-pure), so this extends the
  FLAT frontier too: it is proved here metric-agnostically for any `uniformFlow` pullback metric over `K`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  width-1 in-chart QUADRATIC residual brick — the input shape `chartTransfer_quad` consumes.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  `hCoeffU` is the genuine banked
  firewalled input (the `totalRadialO1_coeff` sub-bound), identical to the engine's; all suppliers are the
  same load-bearing uniform bounds.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthMarginEngine

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### W1 — the T2 QUADRATIC pointwise term, KEPT at width 1 (no absorption).

    The width-1 analogue of `WidthMarginEngine.residualQuadratic_pointwise_narrow`: the same
    `|S| ≤ n²·M·r⁴` deviation × quadratic-form bound, but the `(1/t²)·G_t` prefactor is KEPT explicit
    instead of being widened away.  The `(1/t²)·r⁴ = (r²/t)²` identity exposes the QUADRATIC power. -/
theorem residualQuadratic_pointwise_width1 (gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) {t : ℝ} (ht : 0 < t) (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (v : Point n)
    (hdev_v : ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw_v : |foldedCoeff Θ u 0 v| ≤ W) :
    |(1 / t ^ 2) * gaussDdim t v
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
        * foldedCoeff Θ u 0 v|
      ≤ (n : ℝ) ^ 2 * M * W / 4 * (rncRadialSq v / t) ^ 2 * gaussDdim t v := by
  have htne : t ≠ 0 := ht.ne'
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w : ℝ := foldedCoeff Θ u 0 v with hwdef
  have hG : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  -- `|S| ≤ n²·M·r⁴`  (identical to the engine's `hSabs`).
  have hSabs : |S| ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
    calc |S| ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * rncRadialSq v ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v := hdev_v i j
            have h2 : |v i * v j| ≤ rncRadialSq v := by
              rw [abs_mul]
              calc |v i| * |v j|
                  ≤ rncRadial v * rncRadial v :=
                    mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
                      (abs_nonneg _) (rncRadial_nonneg v)
                _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
            calc |gi v i j - (if i = j then (1 : ℝ) else 0)| * |v i * v j|
                ≤ (M * rncRadialSq v) * rncRadialSq v :=
                  mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM (rncRadialSq_nonneg v))
              _ = M * rncRadialSq v ^ 2 := by ring
      _ = (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  have hn2Mrr : 0 ≤ (n : ℝ) ^ 2 * M * rncRadialSq v ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM) (sq_nonneg _)
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  -- `(1/t²)·r⁴ = (r²/t)²` — the QUADRATIC-power exposure.
  have hquadid : (1 / t ^ 2) * rncRadialSq v ^ 2 = (rncRadialSq v / t) ^ 2 := by
    field_simp
  have hC0 : 0 ≤ (1 / t ^ 2) * (1 / 4) := by positivity
  calc |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * (1 / 4) * gaussDdim t v * (|S| * |w|) := by rw [habs2]; ring
    _ ≤ (1 / t ^ 2) * (1 / 4) * gaussDdim t v
          * (((n : ℝ) ^ 2 * M * rncRadialSq v ^ 2) * W) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hSabs hw_v (abs_nonneg _) hn2Mrr)
            (mul_nonneg hC0 hG)
    _ = (n : ℝ) ^ 2 * M * W / 4 * ((1 / t ^ 2) * rncRadialSq v ^ 2) * gaussDdim t v := by ring
    _ = (n : ℝ) ^ 2 * M * W / 4 * (rncRadialSq v / t) ^ 2 * gaussDdim t v := by rw [hquadid]

/-! ### W1 — THE WIDTH-1 IN-CHART QUADRATIC RESIDUAL (the surviving width wall, extracted). -/

/-- **★ W1 — `uniformResidual_quadPoly_bound_tau_width1`.**  THE SURVIVING WIDTH WALL.  The width-1
    in-chart QUADRATIC parametrix residual bound — the UNCOLLAPSED analogue of
    `WidthMarginEngine.uniformResidual_gaussian_bound_tau_narrow`.  Same firewalled `hCoeffU` input, same
    uniform suppliers, same `T1 + T2 − T3` grading; the three NARROW absorptions are DROPPED, keeping the
    polynomial factors explicit at width `τ`:
        `|parametrixResidualN 0 (metric) (metricInv) Θ u τ v|
            ≤ C·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v)`,   `C = C_c + n²MW/4 + L`,
    the EXACT `hchart` shape `HrawPreCollapse.chartTransfer_quad` (`B = C`, `A = |…|`) consumes.  Metric-
    agnostic (any `uniformFlow` pullback metric over `K`), so it extends the FLAT tower too.  Uniform in
    `τ > 0`; constant `τ`-free.  NOT `a₁ = R/6`. -/
theorem uniformResidual_quadPoly_bound_tau_width1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ C * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨rL, hrL0, L, hL0, hLapU⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u hw0smooth
  set ρ_u : ℝ := min rM (min rL ρ_c) with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hrM0 (lt_min hrL0 hρ_c)
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  have hq0 : 0 ≤ (n : ℝ) ^ 2 * M * W / 4 :=
    div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM0) hW0) (by norm_num)
  refine ⟨ρ_u, hρ_u0, C_c + (n : ℝ) ^ 2 * M * W / 4 + L, by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set X : ℝ := rncRadialSq v / τ with hXdef
  have hX0 : 0 ≤ X := div_nonneg (rncRadialSq_nonneg v) hτ.le
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  -- T1 — LINEAR in `X = r²/τ`.
  have hT1bd : |T1| ≤ C_c * X * gaussDdim τ v := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * X * gaussDdim τ v := by rw [hXdef]; field_simp
  -- T2 — QUADRATIC in `X`.
  have hT2bd : |T2| ≤ (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v := by
    rw [hT2def, hXdef]
    exact residualQuadratic_pointwise_width1 (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W
      hM0 hW0 v (hdevU q hq v hvM) (hWbd v hvball)
  -- T3 — CONSTANT term.
  have hT3bd : |T3| ≤ L * gaussDdim τ v := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ = L * gaussDdim τ v := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  -- assemble at width 1 — each monomial coefficient ≤ `C = C_c + n²MW/4 + L`.
  have hpoly : C_c * X + (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 + L
      ≤ (C_c + (n : ℝ) ^ 2 * M * W / 4 + L) * (X ^ 2 + X + 1) := by
    nlinarith [mul_nonneg hC_c0 (sq_nonneg X), mul_nonneg hq0 hX0,
      mul_nonneg hL0 (sq_nonneg X), mul_nonneg hL0 hX0, hC_c0, hq0, hL0, hX0]
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ C_c * X * gaussDdim τ v + (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 * gaussDdim τ v
          + L * gaussDdim τ v := add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (C_c * X + (n : ℝ) ^ 2 * M * W / 4 * X ^ 2 + L) * gaussDdim τ v := by ring
    _ ≤ ((C_c + (n : ℝ) ^ 2 * M * W / 4 + L) * (X ^ 2 + X + 1)) * gaussDdim τ v :=
        mul_le_mul_of_nonneg_right hpoly hGτ0
    _ = (C_c + (n : ℝ) ^ 2 * M * W / 4 + L) * ((X ^ 2 + X + 1) * gaussDdim τ v) := by ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.residualQuadratic_pointwise_width1
#print axioms QIQTH.HeatResidualBound.uniformResidual_quadPoly_bound_tau_width1
