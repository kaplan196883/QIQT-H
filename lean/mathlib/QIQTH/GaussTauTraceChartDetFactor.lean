/-
  GaussTauTraceChartDetFactor — the DETERMINANT-FACTOR reduction bricks for the chart change-of-variables
  route toward the concrete `AmplitudeDerivativeData` (`hqLip`) / `two_term_census` (`hcl`) consumers.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick — the follow-on to J4-924's `GaussTauTraceChartTransported`.  It supplies
  the ALGEBRAIC REDUCTION for the ONE geometric factor J4-924 flagged as the remaining chart-CoV wall:
  the reciprocal Jacobian weight `1/|det f'|∘V`.

  ## WHAT LANDS (all pure real analysis; NO chart, NO `det`, NO `a₁ = R/6`).
    • `reciprocal_abs_lipschitzOn` — ★★ the PAIRWISE reciprocal glue.  For `D : Point n → ℝ` bounded
        BELOW (`c ≤ |D x|`, `c > 0`) and pairwise Lipschitz (`|D x − D y| ≤ L_D·dist x y`) on a set `S`,
        `w ↦ 1/|D w|` is bounded by `1/c` on `S` AND pairwise Lipschitz with constant `L_D/c²` on `S`.
        THIS is the exact shape the concrete `AmplitudeDerivativeData.hqLip` field consumes (pairwise, not
        center-Lipschitz — the correction gpt-5.6-sol flagged on the J4-924 report).
    • `ratio_abs_lipschitzOn` — ★★ the CONSUMER-FACING product-with-reciprocal.  For `P` bounded (`M_P`)
        + Lipschitz (`L_P`) and `D` bounded-below (`c`) + Lipschitz (`L_D`) on `S`, the ratio `P/|D|` is
        bounded by `M_P/c` and pairwise Lipschitz with constant `L_P/c + M_P·L_D/c²` on `S`.  This is the
        `A·F/|det|`-per-factor shape (with `P := A·F`) that feeds `hqLip` directly.
    • `reciprocal_abs_center_lipschitz` — ★ the CENTER-at-0 corollary (specialising `y := 0`), the shape
        `two_term_census_bound_uniform`'s `hcl` binder consumes.

  ## WHAT THIS DOES — AND DOES NOT — UNBLOCK (gpt-5.6-sol audit, verbatim honest).
  This REDUCES "`1/|det f'|∘V` bounded + Lipschitz" to exactly TWO geometric obligations it does NOT prove:
    (A) `det(f'∘V)` bounded BELOW by `c > 0` on the ball — EXTRACTABLE (the IFT packages
        `baseVaryingIFTPackage`/`chartIFTPackage` prove `1/2 < det` / `|det 0|/2 < |det y|` internally,
        from `chartW0_absdet_fderiv_zero : |det(fderiv W₀ 0)| = 1` + continuity of `y ↦ |det(fderiv W₀ y)|`);
    (B) `det(f'∘V)` pairwise LIPSCHITZ (the SLOPE) — the GENUINE remaining wall: needs a quantitative
        operator-determinant Lipschitz bound (`|det A − det B| ≤ C(n,‖·‖)·‖A−B‖`, ABSENT from Mathlib —
        no `hasFDerivAt_det`/`differentiable_det`/`LipschitzOnWith det`) composed with a Jacobian-Lipschitz
        `‖f'(x)−f'(y)‖≤L_J·dist x y` (chart C² Hessian) and `V`'s own Lipschitz `L_V`.
  It does NOT close `hqLip`/`hGpow`.  The `W₀∘V = id`-on-image obligation is NOT built here — it is
  literally Mathlib's `Set.LeftInvOn.rightInvOn_image` applied to the banked left inverse `V(W₀ z)=z`.

  ⚠  STILL NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none equal to
  the conclusion, no existing file edited.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.GaussTauTraceChartTransported

open MeasureTheory Finset
open QIQTH.Curvature
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the PAIRWISE reciprocal glue (the `hqLip`-shape).
    ############################################################################### -/

/-- **★★ `reciprocal_abs_lipschitzOn` — pairwise reciprocal glue.**  For `D : Point n → ℝ` bounded below
    (`c ≤ |D x|` on `S`, `c > 0`) and pairwise Lipschitz (`|D x − D y| ≤ L_D·dist x y` on `S`, `L_D ≥ 0`),
    `w ↦ 1/|D w|` is bounded by `1/c` on `S` and pairwise Lipschitz with constant `L_D/c²` on `S`.
    Pure real analysis (`||a|−|b|| ≤ |a−b|` + reciprocal difference).  NOT `a₁ = R/6`. -/
theorem reciprocal_abs_lipschitzOn (S : Set (Point n)) (D : Point n → ℝ)
    (c L_D : ℝ) (hc : 0 < c) (hLD : 0 ≤ L_D)
    (hlb : ∀ x ∈ S, c ≤ |D x|)
    (hDlip : ∀ x ∈ S, ∀ y ∈ S, |D x - D y| ≤ L_D * dist x y) :
    (∀ x ∈ S, abs ((1 : ℝ) / |D x|) ≤ 1 / c) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        abs ((1 : ℝ) / |D x| - 1 / |D y|) ≤ (L_D / c ^ 2) * dist x y) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · -- bound `1/|D x| ≤ 1/c`
    have hDx : c ≤ |D x| := hlb x hx
    have hDxpos : 0 < |D x| := lt_of_lt_of_le hc hDx
    rw [abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le hc hDx
  · -- pairwise Lipschitz
    have hDx : c ≤ |D x| := hlb x hx
    have hDy : c ≤ |D y| := hlb y hy
    have hDxpos : 0 < |D x| := lt_of_lt_of_le hc hDx
    have hDypos : 0 < |D y| := lt_of_lt_of_le hc hDy
    have hkey : (1 : ℝ) / |D x| - 1 / |D y| = (|D y| - |D x|) / (|D x| * |D y|) := by
      field_simp
    rw [hkey, abs_div]
    have hnum : |(|D y| - |D x|)| ≤ |D x - D y| := by
      rw [abs_sub_comm (|D y|)]
      exact abs_abs_sub_abs_le_abs_sub (D x) (D y)
    have hnum2 : |(|D y| - |D x|)| ≤ L_D * dist x y := le_trans hnum (hDlip x hx y hy)
    have hden : |(|D x| * |D y|)| = |D x| * |D y| := abs_of_nonneg (by positivity)
    have hdenlb : c ^ 2 ≤ |D x| * |D y| := by
      have hmul := mul_le_mul hDx hDy (le_of_lt hc) (le_of_lt hDxpos)
      calc c ^ 2 = c * c := by ring
        _ ≤ |D x| * |D y| := hmul
    rw [hden]
    have hdenpos : 0 < |D x| * |D y| := mul_pos hDxpos hDypos
    have hdistnn : 0 ≤ dist x y := dist_nonneg
    have hLdistnn : 0 ≤ L_D * dist x y := mul_nonneg hLD hdistnn
    have hc2 : 0 < c ^ 2 := by positivity
    calc |(|D y| - |D x|)| / (|D x| * |D y|)
        ≤ (L_D * dist x y) / (|D x| * |D y|) := by gcongr
      _ ≤ (L_D * dist x y) / c ^ 2 := by gcongr
      _ = (L_D / c ^ 2) * dist x y := by ring

/-! ###############################################################################
    ### §B — the consumer-facing product-with-reciprocal (`A·F/|det|` shape).
    ############################################################################### -/

/-- **★★ `ratio_abs_lipschitzOn` — the `A·F/|det|`-per-factor shape.**  For `P : Point n → ℝ` bounded
    (`|P x| ≤ M_P`, `M_P ≥ 0`) + pairwise Lipschitz (`L_P`) and `D` bounded below (`c > 0`) + pairwise
    Lipschitz (`L_D`) on `S`, the ratio `w ↦ P w / |D w|` is bounded by `M_P/c` and pairwise Lipschitz
    with constant `L_P/c + M_P·L_D/c²` on `S`.  (Take `P := A·F` for the concrete `hqLip`.)  NOT `a₁=R/6`. -/
theorem ratio_abs_lipschitzOn (S : Set (Point n)) (P D : Point n → ℝ)
    (M_P L_P c L_D : ℝ) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P) (hc : 0 < c) (hLD : 0 ≤ L_D)
    (hPbnd : ∀ x ∈ S, |P x| ≤ M_P) (hPlip : ∀ x ∈ S, ∀ y ∈ S, |P x - P y| ≤ L_P * dist x y)
    (hlb : ∀ x ∈ S, c ≤ |D x|)
    (hDlip : ∀ x ∈ S, ∀ y ∈ S, |D x - D y| ≤ L_D * dist x y) :
    (∀ x ∈ S, abs (P x / |D x|) ≤ M_P / c) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        abs (P x / |D x| - P y / |D y|) ≤ (L_P / c + M_P * L_D / c ^ 2) * dist x y) := by
  obtain ⟨hRbnd, hRlip⟩ := reciprocal_abs_lipschitzOn S D c L_D hc hLD hlb hDlip
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · -- bound `|P x|/|D x| ≤ M_P/c`
    have hDx : c ≤ |D x| := hlb x hx
    have hDxpos : 0 < |D x| := lt_of_lt_of_le hc hDx
    have hPx : |P x| ≤ M_P := hPbnd x hx
    rw [abs_div, abs_abs]
    gcongr
  · -- pairwise Lipschitz via `P·(1/|D|)` split
    have hDxpos : 0 < |D x| := lt_of_lt_of_le hc (hlb x hx)
    have hDypos : 0 < |D y| := lt_of_lt_of_le hc (hlb y hy)
    set Rx : ℝ := (1 : ℝ) / |D x| with hRxdef
    set Ry : ℝ := (1 : ℝ) / |D y| with hRydef
    -- rewrite each ratio as a product with the reciprocal
    have hRx : P x / |D x| = P x * Rx := by rw [hRxdef, mul_one_div]
    have hRy : P y / |D y| = P y * Ry := by rw [hRydef, mul_one_div]
    rw [hRx, hRy]
    have hsplit : P x * Rx - P y * Ry = P x * (Rx - Ry) + Ry * (P x - P y) := by ring
    rw [hsplit]
    have hdistnn : 0 ≤ dist x y := dist_nonneg
    have hRlipxy : abs (Rx - Ry) ≤ (L_D / c ^ 2) * dist x y := hRlip x hx y hy
    have hRyb : Ry ≤ 1 / c := by
      have := hRbnd y hy; rwa [abs_of_nonneg (by positivity)] at this
    have hRyb0 : 0 ≤ Ry := by positivity
    calc abs (P x * (Rx - Ry) + Ry * (P x - P y))
        ≤ abs (P x * (Rx - Ry)) + abs (Ry * (P x - P y)) := abs_add_le _ _
      _ = |P x| * abs (Rx - Ry) + Ry * |P x - P y| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hRyb0]
      _ ≤ M_P * ((L_D / c ^ 2) * dist x y) + (1 / c) * (L_P * dist x y) := by
            apply add_le_add
            · exact mul_le_mul (hPbnd x hx) hRlipxy (abs_nonneg _) hMP
            · exact mul_le_mul hRyb (hPlip x hx y hy) (abs_nonneg _) (by positivity)
      _ = (L_P / c + M_P * L_D / c ^ 2) * dist x y := by ring

/-! ###############################################################################
    ### §C — the CENTER-at-0 corollary (the `two_term_census` `hcl` shape).
    ############################################################################### -/

/-- **★ `reciprocal_abs_center_lipschitz` — CENTER-at-0 corollary.**  Specialising `reciprocal_abs_-
    lipschitzOn` to `S = ball 0 r`, `y := 0` (using `dist z 0 = ‖z‖`): `w ↦ 1/|D w|` is bounded by `1/c`
    and CENTER-Lipschitz at `0` with constant `L_D/c²` on `ball 0 r`.  This is the shape
    `two_term_census_bound_uniform`'s `hcl` binder consumes.  NOT `a₁ = R/6`. -/
theorem reciprocal_abs_center_lipschitz (r : ℝ) (D : Point n → ℝ)
    (c L_D : ℝ) (hc : 0 < c) (hLD : 0 ≤ L_D) (hr : 0 < r)
    (hlb : ∀ z ∈ Metric.ball (0 : Point n) r, c ≤ |D z|)
    (hDlip : ∀ x ∈ Metric.ball (0 : Point n) r, ∀ y ∈ Metric.ball (0 : Point n) r,
        |D x - D y| ≤ L_D * dist x y) :
    (∀ z ∈ Metric.ball (0 : Point n) r, abs ((1 : ℝ) / |D z|) ≤ 1 / c) ∧
      (∀ z ∈ Metric.ball (0 : Point n) r,
        abs ((1 : ℝ) / |D z| - 1 / |D 0|) ≤ (L_D / c ^ 2) * ‖z‖) := by
  obtain ⟨hb, hl⟩ := reciprocal_abs_lipschitzOn (Metric.ball (0 : Point n) r) D c L_D hc hLD hlb hDlip
  have h0mem : (0 : Point n) ∈ Metric.ball (0 : Point n) r := Metric.mem_ball_self hr
  refine ⟨hb, fun z hz => ?_⟩
  have := hl z hz 0 h0mem
  rwa [dist_zero_right] at this

/-! ###############################################################################
    ### §D — non-vacuity (jointly satisfiable, with TEETH: a genuinely-varying `D`).
    ############################################################################### -/

/-- **Non-vacuity of `reciprocal_abs_lipschitzOn` / `ratio_abs_lipschitzOn`.**  Exhibited on `S = univ`
    with the genuinely-VARYING bounded-below Lipschitz `D z := 2 + ‖z‖` (`|D z| ≥ 2`, pairwise Lipschitz
    `1` via `|‖x‖−‖y‖| ≤ ‖x−y‖`) and `P z := 1` (bounded `1`, Lipschitz `0`).  So `L_D = 1 ≠ 0` — the
    reciprocal Lipschitz slope is genuinely exercised.  NOT `a₁ = R/6`. -/
theorem reciprocal_abs_lipschitzOn_hyp_satisfiable :
    ∃ (S : Set (Point n)) (P D : Point n → ℝ) (M_P L_P c L_D : ℝ),
      0 ≤ M_P ∧ 0 ≤ L_P ∧ 0 < c ∧ 0 ≤ L_D ∧
        (∀ x ∈ S, |P x| ≤ M_P) ∧ (∀ x ∈ S, ∀ y ∈ S, |P x - P y| ≤ L_P * dist x y) ∧
        (∀ x ∈ S, c ≤ |D x|) ∧
        (∀ x ∈ S, ∀ y ∈ S, |D x - D y| ≤ L_D * dist x y) ∧ (0 : ℝ) < L_D := by
  refine ⟨Set.univ, fun _ => 1, fun z => 2 + ‖z‖, 1, 0, 2, 1,
    zero_le_one, le_refl 0, by norm_num, zero_le_one, ?_, ?_, ?_, ?_, one_pos⟩
  · intro x _; simp
  · intro x _ y _; simp
  · intro x _
    have : (2 : ℝ) ≤ 2 + ‖x‖ := by have := norm_nonneg x; linarith
    rw [abs_of_nonneg (by positivity)]; exact this
  · intro x _ y _
    have h : |(2 + ‖x‖) - (2 + ‖y‖)| = |‖x‖ - ‖y‖| := by ring_nf
    rw [h, one_mul, dist_eq_norm]
    exact abs_norm_sub_norm_le x y

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms reciprocal_abs_lipschitzOn
#print axioms ratio_abs_lipschitzOn
#print axioms reciprocal_abs_center_lipschitz
#print axioms reciprocal_abs_lipschitzOn_hyp_satisfiable
end AxiomChecks
