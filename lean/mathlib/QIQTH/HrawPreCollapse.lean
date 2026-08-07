/-
  HrawPreCollapse — J4-362: THE `hraw` FINISH — the pre-collapse extraction (P1) + the wiring to the
  `hEdom` discharge (P2).  Ledger `docs/qg_roadmap/JET4_TOWER_PLAN.md` §§ J4-359 / J4-360 / J4-361;
  consumes `HrawCampaignOne` (the support confinement / gate assembly), `HrawChartTransfer` (the
  near-isometry budgets), `WidthMarginEngine` (the width-parametric absorptions), and the banked
  `GlobalRawBoundFacade` / `DaLimHardTranche` `hEdom` bridges.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  pre-collapse-extraction + wiring brick for the LABELLED input `hraw`.  No `sorry` (header prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed.  `a₁ = R/6` stays
  CONDITIONAL on the whole convergence / geometric-wiring stack AND on `hraw`/`hD2Hexpand`/`hPd2conv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE P1 GRADING-RECONCILIATION VERDICT (the genuine work).

  The banked M2 engine `WidthMarginEngine.uniformResidual_gaussian_bound_tau_narrow` decomposes the
  `N = 0` parametrix residual into THREE graded terms `T1 + T2 − T3` (proof body, pre-absorption):
      T1 = (1/τ)·G_τ(v)·totalRadialO1_coeff ,   |T1| ≤ C_c·(r²_v/τ)·G_τ(v)          [LINEAR in r²/τ],
      T2 = (1/τ²)·G_τ(v)·⟨(g⁻¹−δ)·v⊗v⟩·w₀ ,      |T2| ≤ (n²MW/4)·(r²_v/τ)²·G_τ(v)   [QUADRATIC],
      T3 = G_τ(v)·(Laplace–Beltrami w₀) ,          |T3| ≤ L·G_τ(v)                    [CONSTANT term].
  (The metric deviation `g⁻¹−δ = O(r²)` × the quadratic form `vᵢvⱼ = O(r²)` gives the `O(r⁴)/τ²`, i.e.
  the SQUARE `(r²/τ)²`.)  Hence the HONEST pre-collapse in-chart residual bound at WIDTH 1 is
      `|heatOp g gi H_G τ (φ_q v) q| ≤ B·((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v`,   `B = max(C_c, n²MW/4, L)`,
  a QUADRATIC polynomial in `r²_v/τ` — NOT the LINEAR `(r²_v/τ + 1)` shape of the idealized `N = 1`
  narrative baked into `GlobalRawBoundFacade.GlobalGatedRawBound`.  The banked engine's own T1/T2/T3
  sub-bounds are the M1-ABSORBED width-3/2 forms (`residualQuadratic_pointwise_narrow` eats `(r²/τ)²`
  ALL THE WAY to a constant × `G_{3/2}` via the `m = 2` absorption `rncRadialSq_sq_mul_gaussDdim_le_
  narrow`), so the pre-absorption quadratic shape is NOT separately banked — it is carried here as an
  HONEST, SATISFIABLE labelled hypothesis (mirroring how `HrawChartTransfer` carries the linear one).

  RECONCILIATION.  The genuine grading (extra `(r²/τ)²` power) reconciles with the width-3/2 `hEdom`
  target EXACTLY as the banked chain's own `m = 0,1,2` width absorptions do: the width jump `w₀ ↦ 3/2`
  absorbs BOTH exposed powers into constants (each `r^{2m}·G_{w₀} ≤ C·τ^m·G_{3/2}`,
  `rncRadialSq_pow_mul_gaussDdim_le_width`), so the QUADRATIC width-`w₀` form still lands at the same
  `(E₀ + E₁·τ)` affine width-3/2 domination with `E₁ = 0`.  This is the `hEdom_of_quadPoly_residual_
  width` bridge below — the honest quadratic analogue of `hEdom_of_gaussPoly_residual` (which handled
  only the linear form).  The single-widening degree reduction QUADRATIC → LINEAR (one power absorbed
  into the width) is `quadPoly_to_linearPoly_width`, the reconciliation verdict as a theorem.

  ## DELIVERABLES.

  •  (P1·bridge) `hEdom_of_quadPoly_residual_width` — from a width-`w₀` (`0 < w₀ < 3/2`) QUADRATIC
     exposed-polynomial ambient bound produce the width-3/2 `hEdom` ∃-shape (`E₁ = 0`).
  •  (P1·reconcile) `quadPoly_to_linearPoly_width` — the honest single-widening degree reduction
     QUADRATIC(width `w₀`) ⟹ LINEAR(width `w₁`) for `0 < w₀ < w₁`, absorbing ONE `(r²/τ)` power.
  •  (P1·transfer) `chartTransfer_quad` / `chartTransfer_quad_from_nearIsometry` — the QUADRATIC
     chart→ambient transfer under the near-isometry budgets (width 1 in chart → width 4/3 in ambient),
     the honest-grading analogue of `HrawChartTransfer.chartTransfer_width1_poly`.
  •  (P2·pred) `GlobalGatedRawBoundQuadWidth` — the width-parametric QUADRATIC global gated predicate.
  •  (P2·assembly) `gatedRawBoundQuadWidth_of_onGate` — the gate assembly (off-gate via the J4-359
     support confinement `HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport`).
  •  (P2·bridge) `hEdom_of_gatedRawBoundQuadWidth` — the predicate wrapper of the bridge.
  •  (P2·capstone) `hEdom_concrete_final` — from the ON-GATE ambient width-4/3 QUADRATIC carry produce
     the `hEdom` ∃-shape (the EXACT binder `GlobalRawBoundFacade.hEdom_of_globalRawBound` yields, i.e.
     the slot `hDaLimLU_from_labelled` consumes via its `hraw`→`hEdom` adapter).

  ## `hraw` FINAL STATUS.
  The `hEdom` ∃-shape — the object the `hraw`-labelled slot ultimately feeds — is now PRODUCIBLE from
  the HONEST reachable data (the width-4/3 QUADRATIC on-gate bound, the genuine grading), via
  `hEdom_concrete_final`.  The surviving labelled carry is the ON-GATE width-4/3 QUADRATIC bound
  (`hgate`) — the per-base M2 parametrix/amplitude sup-bound data glued along the gate = flow-ball; it
  is NAMED, SATISFIABLE, and NOT the conclusion.  `hraw` (the literal width-1 LINEAR `GlobalGatedRaw
  Bound` predicate) remains the idealized entry the banked `hDaLimLU_from_labelled` signature names; the
  honest reachable form is width-4/3 QUADRATIC, which this file discharges to the SAME `hEdom`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GlobalRawBoundFacade
import QIQTH.WidthMarginEngine
import QIQTH.HrawCampaignOne
import QIQTH.HrawChartTransfer

open Set Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.HrawPreCollapse

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### (P1·bridge) — the QUADRATIC exposed-polynomial → width-3/2 `hEdom` bridge.
    ############################################################################### -/

/-- **★ (P1·bridge) — `hEdom_of_quadPoly_residual_width`.**  THE HONEST QUADRATIC BRIDGE.  From the
    genuine PRE-COLLAPSE width-`w₀` (`0 < w₀ < 3/2`) QUADRATIC exposed-polynomial ambient residual bound
        `hraw : ∀ τ>0, ∀ p q, |heatOp g gi H τ p q|
                    ≤ P·(((r²/τ)² + r²/τ + 1)·gaussDdim (w₀·τ) (p−q))`   (`P ≥ 0`, `r² = rncRadialSq (p−q)`)
    the width-3/2 `hEdom` ∃-shape follows with `E₁ = 0`:
        `∃ E₀ E₁, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ>0, ∀ p q,
            |heatOp g gi H τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p−q)`,
    `E₀ = P·√(3/2/w₀)ⁿ·(2·k₁² + k₁ + 1)`, `k₁ = 4·w₀·(3/2)/(3/2−w₀)`.  Route: the `m = 0,1,2` width
    absorptions `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width` eat the `1`, `r²/τ`, `(r²/τ)²`
    terms into constants × `G_{3/2}` (dividing by `τ`, `τ²`); the `√(3/2)ⁿ ≥ 1` cofactor is absorbed.
    This is the honest QUADRATIC analogue of `DaLimHardTranche.hEdom_of_gaussPoly_residual` (linear).
    NOT `a₁ = R/6`. -/
theorem hEdom_of_quadPoly_residual_width (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    (P : ℝ) (hP : 0 ≤ P)
    (hraw : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi H τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (w₀ * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hden : 0 < 3 / 2 - w₀ := by linarith
  have hk1 : 0 ≤ 4 * w₀ * (3 / 2) / (3 / 2 - w₀) := le_of_lt (div_pos (by positivity) hden)
  have hS0 : 0 ≤ Real.sqrt (3 / 2 / w₀) ^ n := by positivity
  have hkfac : 0 ≤ 2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1 := by
    have : 0 ≤ 2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 := by positivity
    linarith [hk1]
  have hE0 : 0 ≤ P * Real.sqrt (3 / 2 / w₀) ^ n
      * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1) :=
    mul_nonneg (mul_nonneg hP hS0) hkfac
  refine ⟨P * Real.sqrt (3 / 2 / w₀) ^ n
      * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1), 0,
    hE0, le_rfl, fun τ hτ p q => ?_⟩
  have hτne : τ ≠ 0 := hτ.ne'
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
  -- `m = 2` polynomial absorption
  have h2 : rncRadialSq (p - q) ^ 2 * gaussDdim (w₀ * τ) (p - q)
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2) * τ ^ 2
          * gaussDdim (3 / 2 * τ) (p - q) := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 2
      (c := w₀) (d := 3 / 2) hw₀ hw₀lt hτ (p - q)
    simpa [Nat.factorial] using h
  have hG0 : 0 ≤ gaussDdim (3 / 2 * τ) (p - q) := gaussDdim_nonneg _ _
  -- divide the `m = 1` absorption by `τ`
  have hdiv1 : rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
          * gaussDdim (3 / 2 * τ) (p - q) := by
    rw [div_le_iff₀ hτ]
    calc rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q)
        ≤ Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) * τ
            * gaussDdim (3 / 2 * τ) (p - q) := h1
      _ = Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
            * gaussDdim (3 / 2 * τ) (p - q) * τ := by ring
  -- divide the `m = 2` absorption by `τ²`
  have hdiv2 : rncRadialSq (p - q) ^ 2 * gaussDdim (w₀ * τ) (p - q) / τ ^ 2
      ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
          * gaussDdim (3 / 2 * τ) (p - q) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < τ ^ 2)]
    calc rncRadialSq (p - q) ^ 2 * gaussDdim (w₀ * τ) (p - q)
        ≤ Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2) * τ ^ 2
            * gaussDdim (3 / 2 * τ) (p - q) := h2
      _ = Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
            * gaussDdim (3 / 2 * τ) (p - q) * τ ^ 2 := by ring
  -- expand the quadratic exposed polynomial
  have hexpand : ((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
        * gaussDdim (w₀ * τ) (p - q)
      = rncRadialSq (p - q) ^ 2 * gaussDdim (w₀ * τ) (p - q) / τ ^ 2
          + rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ
          + gaussDdim (w₀ * τ) (p - q) := by
    field_simp
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (3 / 2) ^ n := by
    have h1' : (1 : ℝ) ≤ Real.sqrt (3 / 2) := by
      have h2' := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 / 2 by norm_num)
      rwa [Real.sqrt_one] at h2'
    calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
      _ ≤ Real.sqrt (3 / 2) ^ n := pow_le_pow_left₀ (by norm_num) h1' n
  calc |heatOp g gi H τ p q|
      ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
              * gaussDdim (w₀ * τ) (p - q)) := hraw τ hτ p q
    _ = P * (rncRadialSq (p - q) ^ 2 * gaussDdim (w₀ * τ) (p - q) / τ ^ 2
              + rncRadialSq (p - q) * gaussDdim (w₀ * τ) (p - q) / τ
              + gaussDdim (w₀ * τ) (p - q)) := by rw [hexpand]
    _ ≤ P * (Real.sqrt (3 / 2 / w₀) ^ n * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2)
                * gaussDdim (3 / 2 * τ) (p - q)
              + Real.sqrt (3 / 2 / w₀) ^ n * (4 * w₀ * (3 / 2) / (3 / 2 - w₀))
                * gaussDdim (3 / 2 * τ) (p - q)
              + Real.sqrt (3 / 2 / w₀) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hdiv2 hdiv1) h0) hP
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n
            * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * gaussDdim (3 / 2 * τ) (p - q) := by ring
    _ ≤ (P * Real.sqrt (3 / 2 / w₀) ^ n
            * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1))
          * (Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hG0 hsqrt1) hE0
    _ = (P * Real.sqrt (3 / 2 / w₀) ^ n
            * (2 * (4 * w₀ * (3 / 2) / (3 / 2 - w₀)) ^ 2 + 4 * w₀ * (3 / 2) / (3 / 2 - w₀) + 1)
          + 0 * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by ring

/-! ###############################################################################
    ### (P1·reconcile) — the single-widening degree reduction QUADRATIC ⟹ LINEAR.
    ############################################################################### -/

/-- **★ (P1·reconcile) — `quadPoly_to_linearPoly_width`.**  THE GRADING-RECONCILIATION VERDICT AS A
    THEOREM.  A single Gaussian widening (`w₀ ↦ w₁`, `0 < w₀ < w₁`) absorbs ONE `(r²/τ)` power, turning
    the genuine QUADRATIC width-`w₀` bound into the idealized LINEAR width-`w₁` shape: from
        `hbound : A ≤ B·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim (w₀·τ) v)`   (`B ≥ 0`, `τ > 0`)
    follows
        `A ≤ B·(√(w₁/w₀)ⁿ·(k₁ + 2))·((r²_v/τ + 1)·gaussDdim (w₁·τ) v)`,   `k₁ = 4·w₀·w₁/(w₁−w₀)`.
    The `(r²/τ)²` term: `(r²/τ)²·G_{w₀} = (r²/τ)·(r²·G_{w₀}/τ) ≤ (r²/τ)·√·k₁·G_{w₁}` (the `m = 1`
    absorption `rncRadialSq_pow_mul_gaussDdim_le_width` divided by `τ`, then multiplied by `r²/τ ≥ 0`)
    `≤ √·k₁·(r²/τ + 1)·G_{w₁}`; the `r²/τ` and `1` terms widen with `m = 0`.  This is the honest reason
    the genuine QUADRATIC pre-collapse form and the idealized LINEAR `GlobalGatedRawBound` narrative land
    at the SAME `hEdom` — the extra power is a width, not a genuine obstruction.  NOT `a₁ = R/6`. -/
theorem quadPoly_to_linearPoly_width {v : Point n} {τ B A w₀ w₁ : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hw₀ : 0 < w₀) (hw : w₀ < w₁)
    (hbound : A ≤ B * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v)) :
    A ≤ B * (Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀) + 2))
        * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
  have hw₁ : 0 < w₁ := lt_trans hw₀ hw
  have hden : 0 < w₁ - w₀ := by linarith
  have hk1 : 0 ≤ 4 * w₀ * w₁ / (w₁ - w₀) := le_of_lt (div_pos (by positivity) hden)
  have hS0 : 0 ≤ Real.sqrt (w₁ / w₀) ^ n := by positivity
  have hX0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hG1 : 0 ≤ gaussDdim (w₁ * τ) v := gaussDdim_nonneg _ v
  have hXP0 : 0 ≤ rncRadialSq v / τ + 1 := by linarith
  -- `m = 0` widening
  have h0 : gaussDdim (w₀ * τ) v ≤ Real.sqrt (w₁ / w₀) ^ n * gaussDdim (w₁ * τ) v := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 0
      (c := w₀) (d := w₁) hw₀ hw hτ v
    simpa using h
  -- `m = 1` absorption, divided by `τ`
  have h1 : rncRadialSq v * gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀)) * τ * gaussDdim (w₁ * τ) v := by
    have h := QIQTH.HeatResidualBound.rncRadialSq_pow_mul_gaussDdim_le_width 1
      (c := w₀) (d := w₁) hw₀ hw hτ v
    simpa using h
  have hdiv1 : rncRadialSq v * gaussDdim (w₀ * τ) v / τ
      ≤ Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀)) * gaussDdim (w₁ * τ) v := by
    rw [div_le_iff₀ hτ]
    calc rncRadialSq v * gaussDdim (w₀ * τ) v
        ≤ Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀)) * τ * gaussDdim (w₁ * τ) v := h1
      _ = Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀)) * gaussDdim (w₁ * τ) v * τ := by ring
  -- `(r²/τ)²·G_{w₀} = (r²/τ)·(r²·G_{w₀}/τ)`
  have hsq_eq : (rncRadialSq v / τ) ^ 2 * gaussDdim (w₀ * τ) v
      = rncRadialSq v / τ * (rncRadialSq v * gaussDdim (w₀ * τ) v / τ) := by ring
  -- the quadratic term ⟹ linear width-`w₁`
  have hquad : (rncRadialSq v / τ) ^ 2 * gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀))
          * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
    rw [hsq_eq]
    calc rncRadialSq v / τ * (rncRadialSq v * gaussDdim (w₀ * τ) v / τ)
        ≤ rncRadialSq v / τ
            * (Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀)) * gaussDdim (w₁ * τ) v) :=
          mul_le_mul_of_nonneg_left hdiv1 hX0
      _ = Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀))
            * (rncRadialSq v / τ * gaussDdim (w₁ * τ) v) := by ring
      _ ≤ Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀))
            * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hS0 hk1)
          apply mul_le_mul_of_nonneg_right _ hG1
          linarith
  -- the linear term ⟹ linear width-`w₁`
  have hlin : rncRadialSq v / τ * gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (w₁ / w₀) ^ n * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
    calc rncRadialSq v / τ * gaussDdim (w₀ * τ) v
        ≤ rncRadialSq v / τ * (Real.sqrt (w₁ / w₀) ^ n * gaussDdim (w₁ * τ) v) :=
          mul_le_mul_of_nonneg_left h0 hX0
      _ = Real.sqrt (w₁ / w₀) ^ n * (rncRadialSq v / τ * gaussDdim (w₁ * τ) v) := by ring
      _ ≤ Real.sqrt (w₁ / w₀) ^ n * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
          apply mul_le_mul_of_nonneg_left _ hS0
          apply mul_le_mul_of_nonneg_right _ hG1
          linarith
  -- the constant term ⟹ linear width-`w₁`
  have hconst : gaussDdim (w₀ * τ) v
      ≤ Real.sqrt (w₁ / w₀) ^ n * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
    calc gaussDdim (w₀ * τ) v
        ≤ Real.sqrt (w₁ / w₀) ^ n * gaussDdim (w₁ * τ) v := h0
      _ ≤ Real.sqrt (w₁ / w₀) ^ n * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by
          apply mul_le_mul_of_nonneg_left _ hS0
          exact le_mul_of_one_le_left hG1 (by linarith)
  set L : ℝ := Real.sqrt (w₁ / w₀) ^ n * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) with hLdef
  have hLdist : Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀))
        * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v)
      = (4 * w₀ * w₁ / (w₁ - w₀)) * L := by rw [hLdef]; ring
  calc A
      ≤ B * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim (w₀ * τ) v) := hbound
    _ = B * ((rncRadialSq v / τ) ^ 2 * gaussDdim (w₀ * τ) v
            + rncRadialSq v / τ * gaussDdim (w₀ * τ) v + gaussDdim (w₀ * τ) v) := by ring
    _ ≤ B * ((4 * w₀ * w₁ / (w₁ - w₀)) * L + L + L) := by
          refine mul_le_mul_of_nonneg_left ?_ hB
          have h := add_le_add (add_le_add hquad hlin) hconst
          rw [hLdist] at h
          exact h
    _ = B * (Real.sqrt (w₁ / w₀) ^ n * (4 * w₀ * w₁ / (w₁ - w₀) + 2))
          * ((rncRadialSq v / τ + 1) * gaussDdim (w₁ * τ) v) := by rw [hLdef]; ring

/-! ###############################################################################
    ### (P1·transfer) — the QUADRATIC chart→ambient transfer.
    ############################################################################### -/

/-- **★ (P1·transfer) — `chartTransfer_quad`.**  THE QUADRATIC CHART→AMBIENT TRANSFER (the honest-grading
    analogue of `HrawChartTransfer.chartTransfer_width1_poly`).  Given the two near-isometry budgets
    `rncRadialSq z ≤ (4/3)·rncRadialSq v` (lower) and `rncRadialSq v ≤ (5/4)·rncRadialSq z` (upper), a
    width-1 in-chart QUADRATIC bound
        `hchart : A ≤ B·(((r²_v/τ)² + r²_v/τ + 1)·gaussDdim τ v)`   (`B ≥ 0`, `τ > 0`)
    transfers to the AMBIENT width-4/3 QUADRATIC bound
        `A ≤ B·(25/16)·√(4/3)ⁿ·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Gaussian leg: `gaussDdim τ v ≤ √(4/3)ⁿ·gaussDdim ((4/3)τ) z` (`gaussDdim_le_gaussDdim_chart`,
    `c=1,d=4/3`, lower budget).  Polynomial leg: `r²_v/τ ≤ (5/4)(r²_z/τ)` (upper budget) ⟹
    `(r²_v/τ)² + r²_v/τ + 1 ≤ (25/16)((r²_z/τ)² + r²_z/τ + 1)`.  NOT `a₁ = R/6`. -/
theorem chartTransfer_quad {v z : Point n} {τ B A : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hlow : rncRadialSq z ≤ 4 / 3 * rncRadialSq v)
    (hup : rncRadialSq v ≤ 5 / 4 * rncRadialSq z)
    (hchart : A ≤ B * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v)) :
    A ≤ B * (25 / 16) * Real.sqrt (4 / 3) ^ n
        * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
  -- Gaussian leg
  have hgauss : gaussDdim τ v ≤ Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) z := by
    have h := QIQTH.HeatResidualBound.gaussDdim_le_gaussDdim_chart (c := (1 : ℝ)) (d := 4 / 3)
      one_pos (by norm_num) hτ (v := v) (w := z) (by rw [one_mul]; exact hlow)
    simpa using h
  -- polynomial leg
  have hstep : rncRadialSq v / τ ≤ 5 / 4 * (rncRadialSq z / τ) := by
    have h := div_le_div_of_nonneg_right hup hτ.le
    rwa [mul_div_assoc] at h
  have hXv0 : 0 ≤ rncRadialSq v / τ := div_nonneg (rncRadialSq_nonneg v) hτ.le
  have hXz0 : 0 ≤ rncRadialSq z / τ := div_nonneg (rncRadialSq_nonneg z) hτ.le
  have hpoly : (rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1
      ≤ 25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) := by
    nlinarith [hstep, hXv0, hXz0, sq_nonneg (rncRadialSq z / τ),
      mul_nonneg hXz0 hXz0, sq_nonneg (5 / 4 * (rncRadialSq z / τ) - rncRadialSq v / τ)]
  -- nonnegativity facts
  have hGv0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  have hPz0 : 0 ≤ (rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1 := by positivity
  have h2516Pz0 : 0 ≤ 25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) := by positivity
  -- assemble
  calc A
      ≤ B * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v) := hchart
    _ ≤ B * ((25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1)) * gaussDdim τ v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly hGv0) hB
    _ ≤ B * ((25 / 16 * ((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1))
          * (Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgauss h2516Pz0) hB
    _ = B * (25 / 16) * Real.sqrt (4 / 3) ^ n
          * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by ring

/-- **★ (P1·transfer) — `chartTransfer_quad_from_nearIsometry`.**  The QUADRATIC chart→ambient transfer
    taken DIRECTLY from the two-sided near-isometry `|rncRadialSq v − rncRadialSq z| ≤ (1/4)·rncRadialSq z`
    (via `HrawChartTransfer.nearIsometry_budgets`).  NOT `a₁ = R/6`. -/
theorem chartTransfer_quad_from_nearIsometry {v z : Point n} {τ B A : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (hiso : |rncRadialSq v - rncRadialSq z| ≤ 1 / 4 * rncRadialSq z)
    (hchart : A ≤ B * (((rncRadialSq v / τ) ^ 2 + rncRadialSq v / τ + 1) * gaussDdim τ v)) :
    A ≤ B * (25 / 16) * Real.sqrt (4 / 3) ^ n
        * (((rncRadialSq z / τ) ^ 2 + rncRadialSq z / τ + 1) * gaussDdim (4 / 3 * τ) z) := by
  obtain ⟨hlow, hup⟩ := QIQTH.HrawChartTransfer.nearIsometry_budgets hiso
  exact chartTransfer_quad hτ hB hlow hup hchart

/-! ###############################################################################
    ### (P2) — the QUADRATIC global gated predicate, assembly, bridge, and capstone.
    ############################################################################### -/

/-- **★ (P2·pred) — `GlobalGatedRawBoundQuadWidth`.**  The width-parametric QUADRATIC exposed-polynomial
    residual predicate at base width `w₀` — the honest-grading analogue of
    `HrawChartTransfer.GlobalGatedRawBoundWidth`:
        `∀ τ>0, ∀ p q, |heatOp g gi H τ p q|
            ≤ P·(((rncRadialSq (p−q)/τ)² + rncRadialSq (p−q)/τ + 1)·gaussDdim (w₀·τ) (p−q))`.
    The QUADRATIC chart transfer produces exactly this shape at `w₀ = 4/3`.  NOT `a₁ = R/6`. -/
def GlobalGatedRawBoundQuadWidth (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (P w₀ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
    |heatOp g gi H τ p q|
      ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
              * gaussDdim (w₀ * τ) (p - q))

/-- **★ (P2·assembly) — `gatedRawBoundQuadWidth_of_onGate`.**  THE QUADRATIC GATE ASSEMBLY: the global
    `GlobalGatedRawBoundQuadWidth g gi (gatedKernel K S H) P w₀` (`P ≥ 0`) follows from the ON-GATE bound
    alone,
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q|
              ≤ P·(((r²/τ)² + r²/τ + 1)·gaussDdim (w₀·τ) (p−q))`,
    the off-gate region discharged by the J4-359 support confinement
    `HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport` (LHS `= 0 ≤` the nonneg RHS).  NOT
    `a₁ = R/6`. -/
theorem gatedRawBoundQuadWidth_of_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P w₀ : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (w₀ * τ) (p - q))) :
    GlobalGatedRawBoundQuadWidth g gi (gatedKernel K S H) P w₀ := by
  intro τ hτ p q
  have hRHS : 0 ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
      * gaussDdim (w₀ * τ) (p - q)) := by
    have hX0 : 0 ≤ rncRadialSq (p - q) / τ := div_nonneg (rncRadialSq_nonneg _) hτ.le
    have hpoly0 : 0 ≤ (rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1 := by positivity
    exact mul_nonneg hP (mul_nonneg hpoly0 (gaussDdim_nonneg _ _))
  by_cases hq : q ∈ K
  · by_cases hp : p ∈ closure (S q)
    · exact hgate τ hτ q hq p hp
    · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inr hp),
        abs_zero]
      exact hRHS
  · rw [QIQTH.HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport g gi K S H τ p q (Or.inl hq),
      abs_zero]
    exact hRHS

/-- **★ (P2·bridge) — `hEdom_of_gatedRawBoundQuadWidth`.**  The predicate wrapper of the QUADRATIC
    bridge: from the width-parametric QUADRATIC labelled predicate `GlobalGatedRawBoundQuadWidth g gi H P
    w₀` (`0 < w₀ < 3/2`, `P ≥ 0`) produce the width-3/2 `hEdom` ∃-shape.  NOT `a₁ = R/6`. -/
theorem hEdom_of_gatedRawBoundQuadWidth (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀lt : w₀ < 3 / 2)
    (P : ℝ) (hP : 0 ≤ P) (hraw : GlobalGatedRawBoundQuadWidth g gi H P w₀) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi H τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) :=
  hEdom_of_quadPoly_residual_width g gi H hw₀ hw₀lt P hP hraw

/-- **★★ (P2·capstone) — `hEdom_concrete_final`.**  THE `hraw` FINISH.  From the ON-GATE ambient
    width-`4/3` QUADRATIC carry (the honest reachable grading — the per-base M2 parametrix/amplitude
    sup-bound data glued along the gate = flow-ball, transferred to the ambient by the QUADRATIC chart
    transfer),
        `hgate : ∀ τ>0, ∀ q ∈ K, ∀ p ∈ closure (S q),
            |heatOp g gi (gatedKernel K S H) τ p q|
              ≤ P·(((r²/τ)² + r²/τ + 1)·gaussDdim ((4/3)·τ) (p−q))`,
    the width-3/2 `hEdom` ∃-shape follows — the EXACT binder `GlobalRawBoundFacade.hEdom_of_globalRaw
    Bound` yields (the slot `hDaLimLU_from_labelled` consumes via its `hraw`→`hEdom` adapter): the gate
    assembly (`gatedRawBoundQuadWidth_of_onGate`, off-gate via the J4-359 support confinement) lifts to
    the global width-4/3 QUADRATIC predicate, and the QUADRATIC bridge (`hEdom_of_gatedRawBoundQuadWidth`,
    `4/3 < 3/2`) discharges it.

    HONEST SURVIVING CARRY.  `hgate` is the NAMED, SATISFIABLE labelled input — the on-gate per-base
    parametrix bound at the genuine width-4/3 QUADRATIC grading; it is NOT the conclusion (width-4/3
    QUADRATIC on the gate vs the width-3/2 affine ∃-shape everywhere).  This is the `hraw`-route `hEdom`
    discharge at the CORRECT grading (the T2-quadratic honesty).  NOT `a₁ = R/6`. -/
theorem hEdom_concrete_final (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (P : ℝ) (hP : 0 ≤ P)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n, p ∈ closure (S q) →
        |heatOp g gi (gatedKernel K S H) τ p q|
          ≤ P * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q))) :
    ∃ E₀ E₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q) := by
  have hglob : GlobalGatedRawBoundQuadWidth g gi (gatedKernel K S H) P (4 / 3) :=
    gatedRawBoundQuadWidth_of_onGate g gi K S H P (4 / 3) hP hgate
  exact hEdom_of_gatedRawBoundQuadWidth g gi (gatedKernel K S H) (by norm_num) (by norm_num) P hP hglob

end QIQTH.HrawPreCollapse

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HrawPreCollapse.hEdom_of_quadPoly_residual_width
#print axioms QIQTH.HrawPreCollapse.quadPoly_to_linearPoly_width
#print axioms QIQTH.HrawPreCollapse.chartTransfer_quad
#print axioms QIQTH.HrawPreCollapse.chartTransfer_quad_from_nearIsometry
#print axioms QIQTH.HrawPreCollapse.gatedRawBoundQuadWidth_of_onGate
#print axioms QIQTH.HrawPreCollapse.hEdom_of_gatedRawBoundQuadWidth
#print axioms QIQTH.HrawPreCollapse.hEdom_concrete_final
