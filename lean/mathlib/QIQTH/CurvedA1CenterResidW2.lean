/-
  CurvedA1CenterResidW2 — J4-684: the WIDTH-2 branch of (hbound-fat) layer 4 — the CENTER-GAUGE
  variant of the τ-residual Gaussian bound retargeted to the tower's consumer WIDTH 2
  (`gaussDdim (2·τ)`, the `baseKernelW 2` shape the fat-`K` `hEdom`/`hBdom` slot consumes), pushing the
  layer-3 `ε₀` floor through the T1 slot, instantiated at the genuinely-curved witness
  `g^κ = curvedRNCMetric κ` on the fat base compact `K = Metric.closedBall 0 r`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes (hbound-fat) layer 5 (the producer re-assembly) + fat-`K` `hEmeas` + `hAdom` + `hcont` + the
  co-instantiated capstone application + the prior analytic piles / convergence trio / `hmassone`
  pre-ρ carriers / `hjets`.  This brick is the WIDTH-2 face of layer 4, not the wall's closure.

  ── ★★ WHY WIDTH 2 (the scoping finding).  The banked J4-607 center engines
  (`CurvedA1CenterResid.uniformResidual_gaussian_bound_tau_narrow_center`, etc.) produce the NARROW
  width-3/2 Gaussian `gaussDdim (3/2·τ)`.  But the (hbound-fat) target scoped in
  `CurvedA1ReBaseHBdom` is the width-2 `baseKernelW 2 0 τ` bound, and the fat-`K`
  `hEdom`/`hBdom`/`leviSeries` tower consumes `gaussDdim (2·τ)` (J4-674..680: suppliers hardcode a
  target width; the tower was width-widened to 3/2, but the D2/Levi consumer conclusion is at
  `gaussDdim (2·s)`).  This file re-runs the SAME `T1 + T2 − T3` grading with the width-parametric
  absorptions `WidthMarginEngine.rncRadialSq_pow_mul_gaussDdim_le_width` /
  `CoeffU1Fix.rncRadial_mul_gaussDdim_le_width` specialised to `(c, d) = (1, 2)` in place of the
  narrow `(1, 3/2)` ones — an EXTRACTION, not new analysis.

  ── ★★ THE `hframeK` USE-SITE VERIFICATION (T2/T3, per the task).  Exactly as in J4-607:
  `hframeK` enters the residual engine at TWO independent sites —
    (T1)  INDIRECTLY, via the coefficient hypothesis `hCoeffU`/`hCoeffLin` (the layer-3 center shape
          adds `+C_ε·ε₀`);
    (T2)  ★ DIRECTLY, via the inner call `uniformFlowPullbackMetricInv_dev_uniform` (which TAKES
          `hframeK`), feeding the deviation `|S| ≤ n²·M·r⁴` of the QUADRATIC residual term.  The
          center replacement `uniformFlowPullbackMetricInv_dev_uniform_center` (layer 1) degrades this
          to `|S| ≤ n²·M·(rncRadialSq v + ε₀)·rncRadialSq v` — CONFIRMING the task's caution that
          T2's `|S|`-bound also needs the per-`q` correction.
  The T3 Laplace–Beltrami block (`uniformFlowLaplaceBeltrami_w0_near_uniform`) NEVER took `hframeK`
  (frame-free), so it is UNCHANGED — verified: this file feeds it `hg hC hK hgnd Θ u hw0smooth`, no
  frame input.

  ── ★★ THE HONEST ε₀/τ PLACEMENT (width-2 weights, no suppression).  The bound degrades by a
  `(1/τ)`-weighted 0th-order Gaussian term:
      `|R₀| ≤ (C₀ + Cεu·ε₀·(1/τ)) · gaussDdim (2·τ) v`                    (O(r²) engine)
      `|R₀| ≤ (C₀ + C₁·(√τ/τ) + Cεu·ε₀·(1/τ)) · gaussDdim (2·τ) v`       (O(r)  engine)
  with the width-2 weights (from the `(1,2)` absorptions `r²·G ≤ √2ⁿ·8·τ·G₂`,
  `r⁴·G ≤ √2ⁿ·128·τ²·G₂`, `r·G ≤ √2ⁿ·2·√τ·G₂`, `G ≤ √2ⁿ·G₂`):
      C₀  = √2ⁿ·(8·C_c + 32·n²·M·W + L)      (O(r²); LITERALLY the banked constant at ε₀ = 0)
      C₀  = √2ⁿ·(32·n²·M·W + L),  C₁ = C_c·√2ⁿ·2                      (O(r); banked at ε₀ = 0)
      Cεu = √2ⁿ·(C_ε + 2·n²·M·W)                                     (BOTH engines — the NEW term)
  Provenance of `Cεu`: the `C_ε` share is the T1 constant coefficient (`(1/τ)·G·(C_ε·ε₀)` with the
  `m = 0` fold `G ≤ √2ⁿ·G₂` — a CONSTANT coefficient pays the raw `(1/τ)`, no width fold eats it);
  the `2·n²·M·W` share is the T2 cross term `(1/τ²)·ε₀·r²·G·(n²MW/4)`, where the `m = 1` absorption
  `r²·G ≤ √2ⁿ·8·τ·G₂` eats ONE power of `τ` and leaves `ε₀·(1/τ)` (weight `8/4 = 2`).
  DISCIPLINE (inherited from layers 1–4): `ρ_u`, `C₀`, `C₁`, `Cεu` are all produced BEFORE `ε₀` is
  quantified — no ε₀-inflation of the geometric/heat constants.  The `ε₀/τ` term is left EXPLICIT so
  layer 5 (the producer re-assembly + order-of-limits, per J4-608) cannot silently drop it.

  ── LANDED HERE:
    • `residualQuadratic_pointwise_width2_center` — the T2 quadratic pointwise bound at width 2 with
      the center deviation `M·(rncRadialSq v + ε₀)`.
    • `uniformResidual_gaussian_bound_tau_width2_center` — ★ THE BRICK (O(r²) engine, `gaussDdim(2τ)`).
    • `uniformResidualLinear_gaussian_bound_tau_width2_center` — the O(r) companion (NO `hw0flat`).
    • `curvedRNC_resid_width2_bound_center` / `curvedRNC_residLinear_width2_bound_center` — fat-`K`
      curved instantiations (`κ ≤ 0`, EVERY `r`, explicit `ε₀ = (|κ|/3)·n·r²`, coeff antecedent
      discharged from layer 3).
    • `curvedRNC_resid_width2_center_satisfiable` — non-vacuity gate (cp466 discipline).

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.CoeffU1Fix
import QIQTH.WidthMarginEngine
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedA1CenterChr
import QIQTH.CurvedA1CenterCoeff
import QIQTH.CurvedA1CenterResid
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.OuterCarryRecon

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.OuterCarryRecon
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterChr QIQTH.CurvedA1CenterCoeff
open QIQTH.HeatResidualBound
open Set Filter
open scoped Topology BigOperators ContDiff

namespace QIQTH.CurvedA1CenterResidW2

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### Width-2 absorption specializations `(c, d) = (1, 2)` of the width-parametric engine lemmas. -/

/-- `gaussDdim τ v ≤ √2ⁿ · gaussDdim (2·τ) v` — the `m = 0` width-2 absorption (T3 / T1-constant). -/
theorem gaussDdim_le_gaussDdim_width2 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim τ v ≤ Real.sqrt 2 ^ n * gaussDdim (2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 0 (c := 1) (d := 2) (by norm_num) (by norm_num)
    hτ v
  simpa using h

/-- `r²·gaussDdim τ v ≤ (√2ⁿ·8)·τ·gaussDdim (2·τ) v` — the `m = 1` width-2 absorption (T1 shape). -/
theorem rncRadialSq_mul_gaussDdim_le_width2 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadialSq v * gaussDdim τ v
      ≤ Real.sqrt 2 ^ n * 8 * τ * gaussDdim (2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 1 (c := 1) (d := 2) (by norm_num) (by norm_num)
    hτ v
  have e1 : (2 / 1 : ℝ) = 2 := by norm_num
  have e2 : ((1:ℕ).factorial : ℝ) * (4 * (1:ℝ) * 2 / (2 - 1)) ^ 1 = 8 := by
    norm_num [Nat.factorial]
  rw [e1, one_mul, e2] at h
  simpa using h

/-- `r⁴·gaussDdim τ v ≤ (√2ⁿ·128)·τ²·gaussDdim (2·τ) v` — the `m = 2` width-2 absorption (T2 shape). -/
theorem rncRadialSq_sq_mul_gaussDdim_le_width2 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadialSq v ^ 2 * gaussDdim τ v
      ≤ Real.sqrt 2 ^ n * 128 * τ ^ 2 * gaussDdim (2 * τ) v := by
  have h := rncRadialSq_pow_mul_gaussDdim_le_width 2 (c := 1) (d := 2) (by norm_num) (by norm_num)
    hτ v
  have e1 : (2 / 1 : ℝ) = 2 := by norm_num
  have e2 : ((2:ℕ).factorial : ℝ) * (4 * (1:ℝ) * 2 / (2 - 1)) ^ 2 = 128 := by
    norm_num [Nat.factorial]
  rw [e1, one_mul, e2] at h
  simpa using h

/-- `r·gaussDdim τ v ≤ (√2ⁿ·2)·√τ·gaussDdim (2·τ) v` — the `m = 1/2` (odd-power) width-2 absorption. -/
theorem rncRadial_mul_gaussDdim_le_width2 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    rncRadial v * gaussDdim τ v
      ≤ Real.sqrt 2 ^ n * 2 * Real.sqrt τ * gaussDdim (2 * τ) v := by
  have h := rncRadial_mul_gaussDdim_le_width (c := 1) (d := 2) (by norm_num) (by norm_num) hτ v
  have e1 : (2 / 1 : ℝ) = 2 := by norm_num
  have e2 : Real.sqrt (2 * (1:ℝ) * 2 / (2 - 1)) = 2 := by
    rw [show (2 * (1:ℝ) * 2 / (2 - 1)) = 4 by norm_num, show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [e1, e2, one_mul] at h
  exact h

/-! ### The T2 quadratic pointwise bound at width 2 with the CENTER deviation — the second ε₀ site. -/

/-- **J4-684 — THE T2 QUADRATIC POINTWISE BOUND, WIDTH 2, CENTER DEVIATION.**  The width-2 analogue of
    `CurvedA1CenterResid.residualQuadratic_pointwise_narrow_center`: the same `|S| ≤ n²·M·(r²+ε₀)·r²`
    center deviation, but the `(1/t²)·G_t` prefactor is folded against `gaussDdim (2·t)` via the
    `(1,2)` absorptions.  The `r⁴` share pays the `m = 2` absorption (`128/4 = 32`, τ-free); the NEW
    `ε₀·r²` cross share pays the `m = 1` absorption `r²·G ≤ √2ⁿ·8·t·G₂`, leaving the honest
    `(1/t)`-weighted term with weight `8/4 = 2`.  NOT `a₁ = R/6`. -/
theorem residualQuadratic_pointwise_width2_center (gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) {t : ℝ} (ht : 0 < t)
    (M W ε₀ : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W) (hε₀ : 0 ≤ ε₀) (v : Point n)
    (hdev_v : ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)|
      ≤ M * (rncRadialSq v + ε₀))
    (hw_v : |foldedCoeff Θ u 0 v| ≤ W) :
    |(1 / t ^ 2) * gaussDdim t v
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
        * foldedCoeff Θ u 0 v|
      ≤ Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * gaussDdim (2 * t) v
        + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / t)
            * gaussDdim (2 * t) v := by
  have htne : t ≠ 0 := ht.ne'
  set S : ℝ := ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j) with hSdef
  set w : ℝ := foldedCoeff Θ u 0 v with hwdef
  set r2 : ℝ := rncRadialSq v with hr2def
  have hr20 : 0 ≤ r2 := rncRadialSq_nonneg v
  have hSε0 : (0 : ℝ) ≤ r2 + ε₀ := add_nonneg hr20 hε₀
  have hSabs : |S| ≤ (n : ℝ) ^ 2 * M * ((r2 + ε₀) * r2) := by
    calc |S| ≤ ∑ i, ∑ j, |(gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, (M * (r2 + ε₀)) * r2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have h1 : |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * (r2 + ε₀) := hdev_v i j
          have h2 : |v i * v j| ≤ r2 := by
            rw [abs_mul]
            calc |v i| * |v j|
                ≤ rncRadial v * rncRadial v :=
                  mul_le_mul (abs_coord_le_rncRadial v i) (abs_coord_le_rncRadial v j)
                    (abs_nonneg _) (rncRadial_nonneg v)
              _ = r2 := by rw [hr2def, ← rncRadial_sq]; ring
          exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hM hSε0)
      _ = (n : ℝ) ^ 2 * M * ((r2 + ε₀) * r2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hG : 0 ≤ gaussDdim t v := gaussDdim_nonneg t v
  set Gn : ℝ := gaussDdim (2 * t) v with hGndef
  have hGn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  have hr4G : r2 ^ 2 * gaussDdim t v
      ≤ Real.sqrt 2 ^ n * 128 * t ^ 2 * Gn := by
    rw [hGndef, hr2def]; exact rncRadialSq_sq_mul_gaussDdim_le_width2 ht v
  have hr2G : r2 * gaussDdim t v ≤ Real.sqrt 2 ^ n * 8 * t * Gn := by
    rw [hGndef, hr2def]; exact rncRadialSq_mul_gaussDdim_le_width2 ht v
  have hK4 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) := by positivity
  have hK1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * M * W / 4 * ε₀ * (1 / t ^ 2) := by positivity
  calc |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * (1 / 4) * gaussDdim t v * (|S| * |w|) := by rw [habs2]; ring
    _ ≤ (1 / t ^ 2) * (1 / 4) * gaussDdim t v
          * (((n : ℝ) ^ 2 * M * ((r2 + ε₀) * r2)) * W) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul hSabs hw_v (abs_nonneg _) ?_) (by positivity)
        exact mul_nonneg (mul_nonneg (by positivity) hM) (mul_nonneg hSε0 hr20)
    _ = (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2) * (r2 ^ 2 * gaussDdim t v)
          + (n : ℝ) ^ 2 * M * W / 4 * ε₀ * (1 / t ^ 2) * (r2 * gaussDdim t v) := by ring
    _ ≤ (n : ℝ) ^ 2 * M * W / 4 * (1 / t ^ 2)
          * (Real.sqrt 2 ^ n * 128 * t ^ 2 * Gn)
          + (n : ℝ) ^ 2 * M * W / 4 * ε₀ * (1 / t ^ 2)
              * (Real.sqrt 2 ^ n * 8 * t * Gn) :=
        add_le_add (mul_le_mul_of_nonneg_left hr4G hK4)
          (mul_le_mul_of_nonneg_left hr2G hK1)
    _ = Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * Gn
          + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / t) * Gn := by
        field_simp
        ring

/-! ### ★ THE BRICK — center-gauge WIDTH-2 τ-residual engine (O(r²)): honest `+Cεu·ε₀·(1/τ)`. -/

/-- **★★ J4-684 — CENTER-GAUGE WIDTH-2 N = 0 RESIDUAL BOUND (O(r²) coefficient + ε₀ floor).**  The
    width-2 face of `CurvedA1CenterResid.uniformResidual_gaussian_bound_tau_narrow_center`: same
    `T1 + T2 − T3` grading, `hframeK` deleted at BOTH sites (T1 = center coefficient shape
    `≤ C_c·rncRadialSq v + C_ε·ε₀`; T2 = layer-1 center deviation), retargeted to `gaussDdim (2·τ)`:
        `|R₀| ≤ (C₀ + Cεu·ε₀·(1/τ)) · gaussDdim (2·τ) v`,   ∀ τ > 0,
    `C₀ = √2ⁿ·(8·C_c + 32·n²·M·W + L)` (LITERALLY the banked constant at ε₀ = 0),
    `Cεu = √2ⁿ·(C_ε + 2·n²·M·W)`.  `ρ_u`, `C₀`, `Cεu` produced BEFORE ε₀.  NOT `a₁ = R/6`. -/
theorem uniformResidual_gaussian_bound_tau_width2_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c C_ε : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c) (hC_ε0 : 0 ≤ C_ε) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ Cεu : ℝ, 0 ≤ C₀ ∧ 0 ≤ Cεu ∧
      ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
          ≤ C_c * rncRadialSq v + C_ε * ε₀) →
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (C₀ + Cεu * ε₀ * (1 / τ)) * gaussDdim (2 * τ) v := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform_center g gi hC hK hg hgnd hgsymm hinvF
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
  refine ⟨ρ_u, hρ_u0, Real.sqrt 2 ^ n * (8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L),
    Real.sqrt 2 ^ n * (C_ε + 2 * (n : ℝ) ^ 2 * M * W),
    by positivity, by positivity, ?_⟩
  intro ε₀ hε₀ hdevK hCoeffU τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  set Gn : ℝ := gaussDdim (2 * τ) v with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  -- (T1) — the coefficient site: `C_c·r²` pays the `m = 1` width-2 absorption (τ-free), the NEW
  -- `C_ε·ε₀` constant coefficient keeps the raw `(1/τ)` (only the `m = 0` fold applies).
  have hT1bd : |T1| ≤ Real.sqrt 2 ^ n * 8 * C_c * Gn
      + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hGle : gaussDdim τ v ≤ Real.sqrt 2 ^ n * Gn := by
      rw [hGndef]; exact gaussDdim_le_gaussDdim_width2 hτ v
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadialSq v + C_ε * ε₀) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadialSq v * gaussDdim τ v)
            + C_ε * ε₀ * (1 / τ) * gaussDdim τ v := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt 2 ^ n * 8 * τ * Gn)
            + C_ε * ε₀ * (1 / τ) * (Real.sqrt 2 ^ n * Gn) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (by rw [hGndef]; exact rncRadialSq_mul_gaussDdim_le_width2 hτ v)
              (by positivity))
            (mul_le_mul_of_nonneg_left hGle (by positivity))
      _ = Real.sqrt 2 ^ n * 8 * C_c * Gn
            + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
          field_simp
  -- (T2) — the DIRECT `hframeK` site, replaced by the layer-1 center deviation (second ε₀ share).
  have hT2bd : |T2| ≤ Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * Gn
      + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_width2_center
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W ε₀ hM0 hW0 hε₀ v
      (hdevU ε₀ hε₀ hdevK q hq v hvM) (hWbd v hvball)
  -- (T3) — frame-free, exactly as banked, `m = 0` width-2 fold.
  have hT3bd : |T3| ≤ Real.sqrt 2 ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt 2 ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_width2 hτ v) hL0
      _ = Real.sqrt 2 ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ (Real.sqrt 2 ^ n * 8 * C_c * Gn
          + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn)
          + (Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * Gn
            + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn)
          + Real.sqrt 2 ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (Real.sqrt 2 ^ n * (8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L)
          + Real.sqrt 2 ^ n * (C_ε + 2 * (n : ℝ) ^ 2 * M * W) * ε₀ * (1 / τ)) * Gn := by
        ring

/-! ### The O(r) companion — NO `hw0flat` (the shifted van-Vleck profile branch). -/

/-- **★ J4-684 — CENTER-GAUGE WIDTH-2 N = 0 RESIDUAL BOUND (O(r) coefficient + ε₀ floor).**  The
    width-2 face of `CurvedA1CenterResid.uniformResidualLinear_gaussian_bound_tau_narrow_center`
    (`hframeK` deleted at BOTH sites; linear center coeff shape `≤ C_c·rncRadial v + C_ε·ε₀`):
        `|R₀| ≤ (C₀ + C₁·(√τ/τ) + Cεu·ε₀·(1/τ)) · gaussDdim (2·τ) v`,   ∀ τ > 0,
    `C₀ = √2ⁿ·(32n²MW + L)`, `C₁ = C_c·√2ⁿ·2` (both LITERALLY banked at ε₀ = 0),
    `Cεu = √2ⁿ·(C_ε + 2n²MW)`.  NOT `a₁ = R/6`. -/
theorem uniformResidualLinear_gaussian_bound_tau_width2_center
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c C_ε : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c) (hC_ε0 : 0 ≤ C_ε) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ C₁ Cεu : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ Cεu ∧
      ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
          ≤ C_c * rncRadial v + C_ε * ε₀) →
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (C₀ + C₁ * (Real.sqrt τ / τ) + Cεu * ε₀ * (1 / τ))
              * gaussDdim (2 * τ) v := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform_center g gi hC hK hg hgnd hgsymm hinvF
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
  refine ⟨ρ_u, hρ_u0, Real.sqrt 2 ^ n * (32 * (n : ℝ) ^ 2 * M * W + L),
    C_c * (Real.sqrt 2 ^ n * 2),
    Real.sqrt 2 ^ n * (C_ε + 2 * (n : ℝ) ^ 2 * M * W),
    by positivity, by positivity, by positivity, ?_⟩
  intro ε₀ hε₀ hdevK hCoeffLin τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  set Gn : ℝ := gaussDdim (2 * τ) v with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have hGτ0 : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  -- (T1) — `C_c·r` pays the odd-power `√τ` width-2 absorption; the NEW `C_ε·ε₀` constant keeps `1/τ`.
  have hT1bd : |T1| ≤ (C_c * (Real.sqrt 2 ^ n * 2)) * (Real.sqrt τ / τ) * Gn
      + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hdivmul : (1 / τ) * Real.sqrt τ = Real.sqrt τ / τ := by rw [one_div, inv_mul_eq_div]
    have hGle : gaussDdim τ v ≤ Real.sqrt 2 ^ n * Gn := by
      rw [hGndef]; exact gaussDdim_le_gaussDdim_width2 hτ v
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadial v + C_ε * ε₀) :=
          mul_le_mul_of_nonneg_left (hCoeffLin q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadial v * gaussDdim τ v)
            + C_ε * ε₀ * (1 / τ) * gaussDdim τ v := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt 2 ^ n * 2 * Real.sqrt τ * Gn)
            + C_ε * ε₀ * (1 / τ) * (Real.sqrt 2 ^ n * Gn) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (by rw [hGndef]; exact rncRadial_mul_gaussDdim_le_width2 hτ v)
              (by positivity))
            (mul_le_mul_of_nonneg_left hGle (by positivity))
      _ = (C_c * (Real.sqrt 2 ^ n * 2)) * ((1 / τ) * Real.sqrt τ) * Gn
            + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn := by ring
      _ = (C_c * (Real.sqrt 2 ^ n * 2)) * (Real.sqrt τ / τ) * Gn
            + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn := by rw [hdivmul]
  -- (T2) — the DIRECT `hframeK` site, center-replaced (second ε₀ share).
  have hT2bd : |T2| ≤ Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * Gn
      + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_width2_center
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W ε₀ hM0 hW0 hε₀ v
      (hdevU ε₀ hε₀ hdevK q hq v hvM) (hWbd v hvball)
  -- (T3) — frame-free, exactly as banked.
  have hT3bd : |T3| ≤ Real.sqrt 2 ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt 2 ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_width2 hτ v) hL0
      _ = Real.sqrt 2 ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ ((C_c * (Real.sqrt 2 ^ n * 2)) * (Real.sqrt τ / τ) * Gn
          + Real.sqrt 2 ^ n * C_ε * ε₀ * (1 / τ) * Gn)
          + (Real.sqrt 2 ^ n * 32 * (n : ℝ) ^ 2 * M * W * Gn
            + Real.sqrt 2 ^ n * 2 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn)
          + Real.sqrt 2 ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (Real.sqrt 2 ^ n * (32 * (n : ℝ) ^ 2 * M * W + L)
          + (C_c * (Real.sqrt 2 ^ n * 2)) * (Real.sqrt τ / τ)
          + Real.sqrt 2 ^ n * (C_ε + 2 * (n : ℝ) ^ 2 * M * W) * ε₀ * (1 / τ)) * Gn := by
        ring

/-! ### The fat-`K` curved instantiations — all geometric carries discharged, explicit `ε₀`. -/

/-- **★★ THE CENTER-GAUGE WIDTH-2 τ-RESIDUAL BOUND AT THE FAT BASE COMPACT for the curved witness
    (O(r²) engine).**  For `κ ≤ 0` and EVERY radius `r`, on `K = Metric.closedBall 0 r`:
    `∃ ρ_u > 0, ∃ C₀ ≥ 0, ∃ Cεu ≥ 0, ∀ τ > 0, ∀ q ∈ K, ∀ ‖v‖ < ρ_u,
        |R₀(τ,v)| ≤ (C₀ + Cεu·((|κ|/3)·n·r²)·(1/τ))·gaussDdim (2·τ) v`
    — every geometric carry discharged from banked curved lemmas, the `hdevK` antecedent from
    `curvedRNC_frame_dev_on_ball`, the coefficient antecedent DISCHARGED from layer 3
    (`curvedRNC_coeff_bound_center`).  NOT `a₁ = R/6`. -/
theorem curvedRNC_resid_width2_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ Cεu : ℝ, 0 ≤ C₀ ∧ 0 ≤ Cεu ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0
            (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
            (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u τ v|
          ≤ (C₀ + Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ))
              * gaussDdim (2 * τ) v := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hcoeff⟩ :=
    curvedRNC_coeff_bound_center κ r hκ Θ u hw0smooth hw0flat
  obtain ⟨ρ_u, hρ_u0, C₀, Cεu, hC₀0, hCεu0, hmain⟩ :=
    uniformResidual_gaussian_bound_tau_width2_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
      Θ u hw0smooth ρ_c C_c C_ε hρ_c0 hC_c0 hC_ε0
  exact ⟨ρ_u, hρ_u0, C₀, Cεu, hC₀0, hCεu0,
    fun τ hτ q hq v hv =>
      hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity)
        (curvedRNC_frame_dev_on_ball κ r) hcoeff τ hτ q hq v hv⟩

/-- **★★ The fat-`K` curved instantiation of the WIDTH-2 O(r) engine** (no `hw0flat` — the shifted
    van-Vleck profile branch).  Same carries, same explicit `ε₀ = (|κ|/3)·n·r²`; the coefficient
    antecedent discharged from `curvedRNC_coeffLinear_bound_center`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_residLinear_width2_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0)) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ C₁ Cεu : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ Cεu ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0
            (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
            (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u τ v|
          ≤ (C₀ + C₁ * (Real.sqrt τ / τ) + Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ))
              * gaussDdim (2 * τ) v := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hcoeff⟩ :=
    curvedRNC_coeffLinear_bound_center κ r hκ Θ u hw0smooth
  obtain ⟨ρ_u, hρ_u0, C₀, C₁, Cεu, hC₀0, hC₁0, hCεu0, hmain⟩ :=
    uniformResidualLinear_gaussian_bound_tau_width2_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
      Θ u hw0smooth ρ_c C_c C_ε hρ_c0 hC_c0 hC_ε0
  exact ⟨ρ_u, hρ_u0, C₀, C₁, Cεu, hC₀0, hC₁0, hCεu0,
    fun τ hτ q hq v hv =>
      hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity)
        (curvedRNC_frame_dev_on_ball κ r) hcoeff τ hτ q hq v hv⟩

/-! ### Non-vacuity gate (cp466 discipline: ANTECEDENT inhabitance, not conclusion shape). -/

/-- **Non-vacuity of the center-gauge width-2 τ-residual bounds at fat `K`.**  At every `r > 0`,
    `κ ≤ 0`, `n ≥ 1`: (i) the base compact `closedBall 0 r` contains a NONZERO point (no
    `K ⊆ {0}` collapse); (ii) the heat-side antecedents are INHABITED (`Θ = 1`, `u = 1`:
    `foldedCoeff = 1`, smooth AND center-flat) AND at that witness the COEFFICIENT-BOUND antecedent
    of the width-2 engines is exhibited DISCHARGED (via layer 3's `curvedRNC_coeff_bound_center`);
    (iii) the `hdevK` antecedent HOLDS at the curved witness with the explicit
    `ε₀ = (|κ|/3)·n·r²`.  Every antecedent of `uniformResidual_gaussian_bound_tau_width2_center`
    (and its Linear companion) is exhibited satisfiable at the fat curved base compact.
    NOT `a₁ = R/6`. -/
theorem curvedRNC_resid_width2_center_satisfiable (κ r : ℝ) (hκ : κ ≤ 0) (hr : 0 < r) (hn : 1 ≤ n) :
    (∃ q ∈ Metric.closedBall (0 : Point n) r, q ≠ 0) ∧
      (∃ Θ : Point n → ℝ, ∃ u : ℕ → Point n → ℝ,
        ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0) ∧
        (∀ e : Fin n, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) ∧
        ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
          ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_c →
          |totalRadialO1_coeff
              (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
              (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u v|
            ≤ C_c * rncRadialSq v + C_ε * (|κ| / 3 * ((n : ℝ) * r ^ 2))) ∧
      (∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j : Fin n,
        |curvedRNCMetric κ q i j - (if i = j then (1 : ℝ) else 0)|
          ≤ |κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  obtain ⟨h1, ⟨Θ, u, hs, hf⟩, h3⟩ := curvedRNC_coeff_center_satisfiable (n := n) κ r hr hn
  exact ⟨h1, ⟨Θ, u, hs, hf, curvedRNC_coeff_bound_center κ r hκ Θ u hs hf⟩, h3⟩

end QIQTH.CurvedA1CenterResidW2

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1CenterResidW2

#print axioms residualQuadratic_pointwise_width2_center
#print axioms uniformResidual_gaussian_bound_tau_width2_center
#print axioms uniformResidualLinear_gaussian_bound_tau_width2_center
#print axioms curvedRNC_resid_width2_bound_center
#print axioms curvedRNC_residLinear_width2_bound_center
#print axioms curvedRNC_resid_width2_center_satisfiable

end AxiomChecks
