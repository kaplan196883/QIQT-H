/-
  HrawChartTransfer — J4-360: the CHART→AMBIENT transfer step of the `hraw` labelled-input campaign
  (step 2 of the hraw campaign; ledger `docs/qg_roadmap/JET4_TOWER_PLAN.md` §§ J4-333/337/358/359).
  The width-1-with-polynomial two-sided radial comparison + the width-1-with-poly chart→ambient
  transfer + the width-parametric bridge re-run, advancing toward `hraw_concrete`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  TRANSFER + BRIDGE brick for the LABELLED input `hraw`.  No `sorry` (header prose excepted), no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  `hraw` remains a NAMED,
  SATISFIABLE labelled residue and `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-
  wiring stack AND on `hraw`/`hD2Hexpand`/`hPd2conv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE COORDINATE CONVENTION (T1 verdict).

  The banked in-chart bounds (`WidthMarginEngine.globalWitness_residual_bound_inChart_final_narrow`,
  `…chartGaussian`) are stated with the CHART coordinate `v` as the exp-map argument and the AMBIENT
  point `p = uniformFlowExp g gi hC hK q v`, so the ambient displacement is `p − q =
  uniformFlowExp g gi hC hK q v − q`.  Thus `r²_v = rncRadialSq v` (chart) and `r²_{p−q} =
  rncRadialSq (p − q)` (ambient), and the near-isometry compares THESE two.  Here we state the
  transfer ABSTRACTLY in two points `v` (chart) and `z` (ambient displacement `= p − q`), matching
  `gaussDdim_le_gaussDdim_chart`'s `(v, w)` convention (its `v` carries the narrow Gaussian, its `w`
  the wide one): we feed chart `v` = its `v` and ambient `z` = its `w`.

  ## THE WIDTH LANDING (T2 verdict).

  The width-1 in-chart Gaussian `e^{−r²_v/4τ}` transfers, under the LOWER near-isometry budget
  `r²_z ≤ (4/3)·r²_v` (i.e. `r²_v ≥ (3/4)·r²_z`), to the AMBIENT width-`4/3` Gaussian
  `√(4/3)ⁿ·gaussDdim ((4/3)·τ) z` (the `(4/3)^{n/2}` is the normalization bookkeeping between the
  widths — exactly `gaussDdim_le_gaussDdim_chart (c=1, d=4/3)`).  The exposed polynomial `r²_v/τ`
  transfers, under the UPPER budget `r²_v ≤ (5/4)·r²_z`, to `(5/4)·(r²_z/τ + 1)`.  Both budgets follow
  from the two-sided near-isometry `|r²_v − r²_z| ≤ (1/4)·r²_z` (`δ = 1/4`).  The result lands at
  AMBIENT width `4/3 < 3/2`, exactly where the polynomial-free width-3/2 route (which the chart
  transfer only delivers at width 2) does NOT close — the (Q1) verdict of J4-359.

  The banked bridge `DaLimHardTranche.hEdom_of_gaussPoly_residual` wants width `1` ambient; our
  transfer produces width `4/3` ambient-with-poly.  We deliver the WIDTH-PARAMETRIC bridge variant
  `hEdom_of_gaussPoly_residual_width` (the same absorption at any base width `0 < w₀ < 3/2`, driven by
  the width-generic `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width`), so the `4/3` width
  feeds the width-3/2 `hEdom` with slack.

  ## THE IN-CHART FORM (T3 extraction verdict).

  The M2 chain (`CoeffU1Fix` lineage, READ-ONLY) collapses to a POLYNOMIAL-FREE width-3/2 in-chart
  bound via the `√τ/τ` amplitude re-expression — the width-1-with-POLYNOMIAL intermediate `(r²_v/τ +
  1)·gaussDdim τ v` is NOT literally banked as a named theorem (it is the pre-absorption `N = 1`
  parametrix shape one step before the M1 lemmas `rncRadialSq_mul_gaussDdim_le_narrow` etc. consume
  it).  Hence T3/T4 carry it as an HONEST, SATISFIABLE named hypothesis with the EXACT width-1-with-
  poly shape (mirroring how `chartGaussian` carries `hdisp` as a load-bearing near-isometry input),
  and the capstone `hraw_variant_concrete` wires that carry (on-gate) through the gate assembly +
  the width-parametric bridge to the `hEdom` ∃-shape.

  ## DELIVERABLES.
  •  (T1) `nearIsometry_budgets_gen` / `nearIsometry_budgets` — the two-sided radial comparison: from
     `|r²_v − r²_z| ≤ δ·r²_z` (`δ = 1/4`) the two width budgets `r²_z ≤ (4/3)·r²_v` and `r²_v ≤
     (5/4)·r²_z`.
  •  (T2a) `chartTransfer_width1_poly` — the width-1-with-poly chart→ambient transfer under the two
     budgets: `A ≤ B·((r²_v/τ+1)·gaussDdim τ v)  ⟹  A ≤ B·(5/4)·√(4/3)ⁿ·((r²_z/τ+1)·gaussDdim ((4/3)τ) z)`.
  •  (T2a′) `chartTransfer_from_nearIsometry` — T1 ∘ T2a: the same transfer directly from the two-sided
     near-isometry.
  •  (T2b) `hEdom_of_gaussPoly_residual_width` — the WIDTH-PARAMETRIC bridge re-run: from a width-`w₀`
     (`0 < w₀ < 3/2`) exposed-polynomial ambient bound produce the width-3/2 `hEdom` ∃-shape.
  •  (T4) `GlobalGatedRawBoundWidth` / `gatedRawBoundWidth_of_onGate` / `hEdom_of_gatedRawBoundWidth` /
     `hraw_variant_concrete` — the width-parametric global gated predicate, its gate assembly (off-gate
     via the J4-359 support confinement), the bridge wrapper, and the capstone (on-gate width-4/3-with-
     poly ⟹ `hEdom`).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.WidthMarginEngine
import QIQTH.HrawCampaignOne

open Set Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.HrawChartTransfer

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### (T1) — the two-sided radial comparison (near-isometry width budgets).
    ############################################################################### -/

/-- **★ (T1) — `nearIsometry_budgets_gen`.**  THE TWO-SIDED RADIAL COMPARISON, parametric in the
    near-isometry tolerance `δ ∈ [0, 1)`.  From the symmetric near-isometry
        `hiso : |rncRadialSq v − rncRadialSq z| ≤ δ·rncRadialSq z`
    (`z` the ambient displacement, `v` the chart coordinate) the two width budgets follow:
        `rncRadialSq z ≤ (1/(1−δ))·rncRadialSq v`   (the LOWER budget, for the Gaussian leg),
        `rncRadialSq v ≤ (1+δ)·rncRadialSq z`       (the UPPER budget, for the polynomial leg).
    The lower budget is the `(1−δ)·r²_z ≤ r²_v` rearrangement (`1−δ > 0`); the upper is direct.  δ is
    "controllable by the gate radius": shrinking the flow-ball tightens the near-isometry.  NOT
    `a₁ = R/6`. -/
theorem nearIsometry_budgets_gen {v z : Point n} {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hiso : |rncRadialSq v - rncRadialSq z| ≤ δ * rncRadialSq z) :
    rncRadialSq z ≤ 1 / (1 - δ) * rncRadialSq v ∧ rncRadialSq v ≤ (1 + δ) * rncRadialSq z := by
  rw [abs_le] at hiso
  obtain ⟨hlo, hhi⟩ := hiso
  have hpos : 0 < 1 - δ := by linarith
  refine ⟨?_, by linarith⟩
  rw [show (1 : ℝ) / (1 - δ) * rncRadialSq v = rncRadialSq v / (1 - δ) by ring, le_div_iff₀ hpos]
  nlinarith [hlo]

/-- **★ (T1, δ = 1/4) — `nearIsometry_budgets`.**  The `δ = 1/4` specialization landing the exact
    budgets the width-4/3 transfer consumes: from `|rncRadialSq v − rncRadialSq z| ≤ (1/4)·rncRadialSq z`,
        `rncRadialSq z ≤ (4/3)·rncRadialSq v`   and   `rncRadialSq v ≤ (5/4)·rncRadialSq z`.
    (`1/(1−1/4) = 4/3`, `1+1/4 = 5/4`.)  NOT `a₁ = R/6`. -/
theorem nearIsometry_budgets {v z : Point n}
    (hiso : |rncRadialSq v - rncRadialSq z| ≤ 1 / 4 * rncRadialSq z) :
    rncRadialSq z ≤ 4 / 3 * rncRadialSq v ∧ rncRadialSq v ≤ 5 / 4 * rncRadialSq z := by
  obtain ⟨hlo, hhi⟩ :=
    nearIsometry_budgets_gen (v := v) (z := z) (δ := 1 / 4) (by norm_num) (by norm_num) hiso
  refine ⟨?_, ?_⟩
  · rwa [show (1 : ℝ) / (1 - 1 / 4) = 4 / 3 by norm_num] at hlo
  · rwa [show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num] at hhi

/-! ###############################################################################
    ### (T2a) — the width-1-with-polynomial chart→ambient transfer.
    ############################################################################### -/

/-- **★ (T2a) — `chartTransfer_width1_poly`.**  THE WIDTH-1-WITH-POLYNOMIAL CHART→AMBIENT TRANSFER.
    Given the two near-isometry budgets `rncRadialSq z ≤ (4/3)·rncRadialSq v` (lower) and
    `rncRadialSq v ≤ (5/4)·rncRadialSq z` (upper), a width-1 in-chart exposed-polynomial bound
        `hchart : A ≤ B·((rncRadialSq v/τ + 1)·gaussDdim τ v)`   (`B ≥ 0`, `τ > 0`)
    transfers to the AMBIENT width-4/3 exposed-polynomial bound
        `A ≤ B·(5/4)·√(4/3)ⁿ·((rncRadialSq z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Gaussian leg: `gaussDdim τ v ≤ √(4/3)ⁿ·gaussDdim ((4/3)τ) z` via
    `gaussDdim_le_gaussDdim_chart (c=1, d=4/3)` under the lower budget.  Polynomial leg:
    `rncRadialSq v/τ + 1 ≤ (5/4)·(rncRadialSq z/τ + 1)` under the upper budget.  NOT `a₁ = R/6`. -/
theorem chartTransfer_width1_poly {v z : Point n} {τ B A : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hlow : rncRadialSq z ≤ 4 / 3 * rncRadialSq v)
    (hup : rncRadialSq v ≤ 5 / 4 * rncRadialSq z)
    (hchart : A ≤ B * ((rncRadialSq v / τ + 1) * gaussDdim τ v)) :
    A ≤ B * (5 / 4) * Real.sqrt (4 / 3) ^ n
        * ((rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
  -- Gaussian leg: widen the chart Gaussian to the ambient width-4/3 Gaussian.
  have hgauss : gaussDdim τ v ≤ Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) z := by
    have h := QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart (c := (1 : ℝ)) (d := 4 / 3)
      one_pos (by norm_num) hτ (v := v) (w := z) (by rw [one_mul]; exact hlow)
    simpa using h
  -- polynomial leg: absorb the upper-budget factor 5/4.
  have hstep : rncRadialSq v / τ ≤ 5 / 4 * (rncRadialSq z / τ) := by
    have h := div_le_div_of_nonneg_right hup hτ.le
    rwa [mul_div_assoc] at h
  have hpoly : rncRadialSq v / τ + 1 ≤ 5 / 4 * (rncRadialSq z / τ + 1) := by linarith [hstep]
  -- nonnegativity facts
  have hGv0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  have hPz0 : 0 ≤ rncRadialSq z / τ + 1 :=
    add_nonneg (div_nonneg (rncRadialSq_nonneg z) hτ.le) zero_le_one
  have h54Pz0 : 0 ≤ 5 / 4 * (rncRadialSq z / τ + 1) := by positivity
  -- assemble
  calc A
      ≤ B * ((rncRadialSq v / τ + 1) * gaussDdim τ v) := hchart
    _ ≤ B * ((5 / 4 * (rncRadialSq z / τ + 1)) * gaussDdim τ v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly hGv0) hB
    _ ≤ B * ((5 / 4 * (rncRadialSq z / τ + 1))
          * (Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgauss h54Pz0) hB
    _ = B * (5 / 4) * Real.sqrt (4 / 3) ^ n
          * ((rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

/-- **★ (T2a′) — `chartTransfer_from_nearIsometry`.**  T1 ∘ T2a: the width-1-with-poly chart→ambient
    transfer taken DIRECTLY from the two-sided near-isometry `|rncRadialSq v − rncRadialSq z| ≤
    (1/4)·rncRadialSq z`.  NOT `a₁ = R/6`. -/
theorem chartTransfer_from_nearIsometry {v z : Point n} {τ B A : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hiso : |rncRadialSq v - rncRadialSq z| ≤ 1 / 4 * rncRadialSq z)
    (hchart : A ≤ B * ((rncRadialSq v / τ + 1) * gaussDdim τ v)) :
    A ≤ B * (5 / 4) * Real.sqrt (4 / 3) ^ n
        * ((rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
  obtain ⟨hlow, hup⟩ := nearIsometry_budgets hiso
  exact chartTransfer_width1_poly hτ hB hlow hup hchart

/-! ###############################################################################
    ### (T2b) — the width-parametric bridge re-run.
    ############################################################################### -/

/-- **★ (T2b) — `hEdom_of_gaussPoly_residual_width`.**  THE WIDTH-PARAMETRIC BRIDGE RE-RUN.  The banked
    `DaLimHardTranche.hEdom_of_gaussPoly_residual` is the `w₀ = 1` case; here we re-run the SAME
    absorption at ANY base width `0 < w₀ < 3/2`, using the width-generic
    `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width`.  From
        `hraw : ∀ τ>0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((r²/τ + 1)·gaussDdim (w₀·τ) (p−q))`   (`P ≥ 0`)
    the width-3/2 `hEdom` ∃-shape follows with `E₁ = 0`:
        `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ>0, ∀ p q,
            |heatOp g gi H τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`,
    `E₀ = P·√(3/2/w₀)ⁿ·(4·w₀·(3/2)/(3/2−w₀) + 1)` (`m = 0` widening `+` `m = 1` absorption, the
    `√(3/2)ⁿ ≥ 1` cofactor absorbed).  With `w₀ = 4/3` this consumes the T2a transfer output.  NOT
    `a₁ = R/6`. -/
theorem hEdom_of_gaussPoly_residual_width (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q|
          ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hden : 0 < 3 / 2 - w₀ := by linarith
  have hKm : 0 ≤ 4 * w₀ * (3 / 2) / (3 / 2 - w₀) := le_of_lt (div_pos (by positivity) hden)
  have hS0 : 0 ≤ Real.sqrt (3 / 2 / w₀) ^ n := by positivity
  have hE0 : 0 ≤ P * Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1) :=
    mul_nonneg (mul_nonneg hP hS0) (by linarith [hKm])
  refine ⟨P * Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1), 0, hE0, le_rfl,
    fun τ hτ p q => ?_⟩
  -- `m = 0` width widening
  have h0 : gaussDdim (w₀ * τ) (p - q)
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 0
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ (p - q)
    simpa using h
  -- `m = 1` polynomial absorption
  have h1 : rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q)
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) * τ
          * gaussDdim (3 / 2 * τ) (p - q) := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 1
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ (p - q)
    simpa using h
  have hG0 : 0 ≤ gaussDdim (3 / 2 * τ) (p - q) := gaussDdim_nonneg _ _
  -- divide the `m = 1` absorption by `τ`
  have hdiv : rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
          * gaussDdim (3 / 2 * τ) (p - q) := by
    rw [div_le_iff₀ hτ]
    calc rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q)
        ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) * τ
            * gaussDdim (3 / 2 * τ) (p - q) := h1
      _ = Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
            * gaussDdim (3 / 2 * τ) (p - q) * τ := by ring
  have hexpand : (rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q)
      = rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ + gaussDdim (w₀ * τ) (p - q) := by
    rw [add_mul, one_mul, div_mul_eq_mul_div]
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) ^ n := by
    have h1' : (1 : ℝ) ≤ Real.sqrt (3 / 2) := by
      have h2 := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rwa [Real.sqrt_one] at h2
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ ≤ Real.sqrt (3 / 2) ^ n := pow_le_pow_left₀ (by norm_num) h1' n
  calc |heatOp g gi H τ p q|
      ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q)) := hraw τ hτ p q
    _ = P * (rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ + gaussDdim (w₀ * τ) (p - q)) := by
        rw [hexpand]
    _ ≤ P * (Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
              * gaussDdim (3 / 2 * τ) (p - q)
            + Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (add_le_add hdiv h0) hP
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * gaussDdim (3 / 2 * τ) (p - q) := by ring
    _ ≤ (P * Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hG0 hsqrt1) hE0
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1) + 0 * τ)
          * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by ring

/-! ###############################################################################
    ### (T4) — the width-parametric global gated predicate, assembly, and capstone.
    ############################################################################### -/

/-- **★ (T4·pred) — `GlobalGatedRawBoundWidth`.**  The width-parametric analogue of
    `GlobalRawBoundFacade.GlobalGatedRawBound` (which is the `w₀ = 1` case): the exposed-polynomial
    residual predicate at base width `w₀`,
        `∀ τ > 0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((rncRadialSq (p−q)/τ + 1)·gaussDdim (w₀·τ) (p−q))`.
    The T2a transfer produces exactly this shape at `w₀ = 4/3`.  NOT `a₁ = R/6`. -/
def GlobalGatedRawBoundWidth (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (P w₀ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
    |heatOp g gi H τ p q|
      ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q))

/-- **★ (T4·assembly) — `gatedRawBoundWidth_of_onGate`.**  THE WIDTH-PARAMETRIC GATE ASSEMBLY (the
    (Q3) skeleton at base width `w₀`): the global `GlobalGatedRawBoundWidth g gi (gatedKernel K S H) P
    w₀` (`P ≥ 0`) follows from the ON-GATE bound alone,
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q| ≤ P·((r²/τ + 1)·gaussDdim (w₀·τ) (p−q))`,
    the off-gate region discharged by the J4-359 support confinement
    `HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport` (LHS `= 0 ≤` the nonneg RHS).  NOT
    `a₁ = R/6`. -/
theorem gatedRawBoundWidth_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P w₀ : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q))) :
    GlobalGatedRawBoundWidth g gi (gatedKernel K S H) P w₀ := by
  intro τ hτ p q
  have hRHS : 0 ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (w₀ * τ) (p - q)) :=
    mul_nonneg hP (mul_nonneg
      (add_nonneg (div_nonneg (rncRadialSq_nonneg _) hτ.le) zero_le_one)
      (gaussDdim_nonneg _ _))
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ closure (S q)
    · exact hgate τ hτ q hq p hp
    · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inr hp),
        abs_zero]
      exact hRHS
  · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inl hq),
      abs_zero]
    exact hRHS

/-- **★ (T4·bridge) — `hEdom_of_gatedRawBoundWidth`.**  The predicate wrapper of T2b: from the width-
    parametric labelled predicate `GlobalGatedRawBoundWidth g gi H P w₀` (`0 < w₀ < 3/2`, `P ≥ 0`)
    produce the width-3/2 `hEdom` ∃-shape.  NOT `a₁ = R/6`. -/
theorem hEdom_of_gatedRawBoundWidth (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    (P : ℝ) (hP : 0 ≤ P) (hraw : GlobalGatedRawBoundWidth g gi H P w₀) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  hEdom_of_gaussPoly_residual_width g gi H hw₀ hw₀lt P hP hraw

/-- **★★ (T4·capstone) — `hraw_variant_concrete`.**  THE ASSEMBLY.  From the ON-GATE ambient
    width-`4/3`-with-poly bound (the honest carry that the T3 in-chart form + the T2a per-base transfer
    would produce, on the near-diagonal gate),
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q| ≤ P·((r²/τ + 1)·gaussDdim ((4/3)·τ) (p−q))`,
    the width-3/2 `hEdom` ∃-shape follows: the gate assembly (`gatedRawBoundWidth_of_onGate`, off-gate
    via the support confinement) lifts to the global width-4/3 predicate, and the width-parametric
    bridge (`hEdom_of_gatedRawBoundWidth`, `4/3 < 3/2`) discharges it.  This is the `hraw`-route
    variant of the `hEdom` domination, with `4/3` the width where the design closes (Q1 verdict).
    `hgate` is the NAMED, SATISFIABLE labelled carry — NOT the conclusion (width-4/3-with-poly vs
    width-3/2 affine ∃-shape).  NOT `a₁ = R/6`. -/
theorem hraw_variant_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ P * ((rncRadialSq (p - q) / τ + 1) * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hglob : GlobalGatedRawBoundWidth g gi (gatedKernel K S H) P (4 / 3) :=
    gatedRawBoundWidth_of_onGate g gi K S H P (4 / 3) hP hgate
  exact hEdom_of_gatedRawBoundWidth g gi (gatedKernel K S H) (by norm_num) (by norm_num) P hP hglob

end QIQTH.HrawChartTransfer

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HrawChartTransfer.nearIsometry_budgets_gen
#print axioms QIQTH.HrawChartTransfer.nearIsometry_budgets
#print axioms QIQTH.HrawChartTransfer.chartTransfer_width1_poly
#print axioms QIQTH.HrawChartTransfer.chartTransfer_from_nearIsometry
#print axioms QIQTH.HrawChartTransfer.hEdom_of_gaussPoly_residual_width
#print axioms QIQTH.HrawChartTransfer.gatedRawBoundWidth_of_onGate
#print axioms QIQTH.HrawChartTransfer.hEdom_of_gatedRawBoundWidth
#print axioms QIQTH.HrawChartTransfer.hraw_variant_concrete
