/-
  WidthParametricGoodGate — J4-673 (brick 2 of the curved width-3/2 near-diagonal domination campaign).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE (brick 2 = the two width-campaign primitives).

    • (b) `uniformFlowExp_hdisp_ball_delta` — the (1+δ) SHRUNK-RADIUS near-isometry displacement.  For any
      `δ > 0`, there is a radius `r > 0` such that on the ball `‖v‖ < r`, UNIFORMLY over `q ∈ K`,
          `rncRadialSq (φ_q v − q) ≤ (1 + δ)·rncRadialSq v`.
      This is `NearIsometryBudget.uniformFlowExp_hdisp_ball` (J4-96, which delivers the FIXED width-4/3
      instance `3/2·rncRadialSq(φ_q v − q) ≤ 2·rncRadialSq v` i.e. `≤ 4/3·rncRadialSq v`) generalised: the
      correction factor `(1 + 2n·C_D·r + n·C_D²·r²)` is a MODULUS-OF-CONTINUITY-at-0 estimate whose bracket
      `2n·C_D·r + n·C_D²·r²` is `≤ δ` once `r ≤ δ/D` (with `D = 2n·C_D + n·C_D² + 1`).  So the displacement
      ratio `→ 1` as the radius `→ 0`; the fixed `4/3` is one instance (`δ = 1/3`).  cp466: the radius stays
      STRICTLY positive (`0 < r`), so the gate remains inhabited — satisfiable at `κ = −1`, `n = 2`.

    • (a) `gatedWitnessN1_hEboundW_le_of_good_W` — the WIDTH-PARAMETRIC chart-transfer merge.  Verbatim
      `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_of_good_CONST`, but with the AMBIENT Gaussian width
      exposed as a parameter `W_a` (the CONST version pins it to `2`): the in-gate field bound is stated at
      `gaussDdim (W_a·τ)` and the produced `hEboundW` is at `baseKernelW W_a 0`.  The `GateSqControl` field
      keeps the fixed `3/2` ratio (that is a HARDCODED property of the `GateSqControl` def, independent of
      the ambient Gaussian width).  The width-`W_a` mixed-cover engine (`_mixed_of_cover_W`,
      `mixedAlpha_to_alpha0_le_W`, `_le_of_mixedCover_W`) is a mechanical `κ`-generalisation of the width-2
      tower (`OrderOneTower` / `RestrictedEboundW`): every `baseKernelW` plumbing lemma
      (`baseKernelW_zero_apply`, `baseKernelW_one_eq_tau_mul`) is already `κ`-parametric, and
      `gaussDdim_nonneg` is unconditional in the width, so no positivity constraint on `W_a` is needed.

  Composing (a) at intrinsic width `w_i = 3/2` with (b) at displacement `D = 1 + δ` gives the ambient width
  `w_i·D = (3/2)(1 + δ)`, tunable toward the intrinsic floor `3/2` — the `gaussDdim_le_gaussDdim_chart`
  prefactor becomes `√(1 + δ)ⁿ → 1`.  Whether that suffices for a downstream consumer depends on the
  consumer's demanded width; see the FIREWALL note.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It lands ONLY the two width-campaign primitives.
  It does NOT compose the ambient constGate width-3/2 `hEdom` (brick 3 = a `_lin`-style assembly at the
  parametric width, pulling in `CurvedIntrinsicWidth32.curvedRNC_intrinsic_width32_defect`).  SCOPING
  VERDICT recorded for the caller: the width-2 Levi/convolution/true-kernel tower AND the labelled
  restricted capstone `RestrictedEboundW.trueKernel_diagonal_a1_eq_R6_residual_restricted` demand
  `hEboundW_le` at the HARDCODED ambient width `baseKernelW (2:ℝ) (0:ℝ)`; the width-parametric primitives
  here reach `baseKernelW W_a 0` for ANY `W_a`, but the `(3/2)(1+δ)` composite is strictly above `3/2` for
  `δ > 0` (the pure-Gaussian route cannot reach the intrinsic floor exactly).  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no conclusion-in-disguise, no existing file edited.
-/
import Mathlib
import QIQTH.ConstRadiusGateExport

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.GateOpennessExport QIQTH.S1TripleHEmeasGate QIQTH.ConstRadiusGateExport
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.WidthParametricGoodGate

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (b) — the (1+δ) shrunk-radius near-isometry displacement. -/

/-- **★ J4-673 (b) — the `(1+δ)` shrunk-radius near-isometry displacement.**  For every `δ > 0` there is a
    radius `r > 0` such that for all `q ∈ K`, `‖v‖ < r`, the uniform-flow exponential displacement obeys
        `rncRadialSq (φ_q v − q) ≤ (1 + δ)·rncRadialSq v`.
    Generalises `NearIsometryBudget.uniformFlowExp_hdisp_ball` (which delivers the FIXED width-4/3 slice)
    to arbitrary `δ`: the ℓ² expansion `rncRadialSq (v + e) ≤ rncRadialSq v·(1 + 2n·C_D·r + n·C_D²·r²)`
    (with `e = φ_q v − q − v`, `‖e‖ ≤ C_D·‖v‖²` the quadratic displacement bound) has correction bracket
    `≤ D·r ≤ δ` once `r ≤ δ/D`, `D = 2n·C_D + n·C_D² + 1`.  The radius stays `> 0`, so the gate remains
    inhabited (cp466).  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_hdisp_ball_delta (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r →
      rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (1 + δ) * rncRadialSq v := by
  obtain ⟨ρ₀, hρ₀pos, C_D, hCD0, hdisp2⟩ := uniformFlowExp_displacement_bound g gi hC hK
  set D : ℝ := 2 * (n : ℝ) * C_D + (n : ℝ) * C_D ^ 2 + 1 with hD
  have hDpos : 0 < D := by
    have h1 : 0 ≤ 2 * (n : ℝ) * C_D := mul_nonneg (by positivity) hCD0
    have h2 : 0 ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
    rw [hD]; linarith
  set r : ℝ := min ρ₀ (min 1 (δ / D)) with hr
  have hrpos : 0 < r := lt_min hρ₀pos (lt_min one_pos (div_pos hδ hDpos))
  refine ⟨r, hrpos, ?_⟩
  intro q hq v hv
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (by rw [hr]; exact min_le_left _ _)
  have he : ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖ := hdisp2 q hq v hvρ₀
  set e : Point n := uniformFlowExp g gi hC hK q v - q - v with hedef
  have hxe : uniformFlowExp g gi hC hK q v - q = v + e := by rw [hedef]; abel
  rw [hxe]
  have hadd := rncRadialSq_add_le v e
  have hrv : (0 : ℝ) ≤ rncRadialSq v := rncRadialSq_nonneg v
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hne : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have hnvsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ hnv h 2
      _ = rncRadialSq v := rncRadial_sq v
  have he2 : ‖e‖ ≤ C_D * ‖v‖ ^ 2 := by rw [sq, ← mul_assoc]; exact he
  have hvr1 : ‖v‖ ≤ r := hv.le
  have hr_le1 : r ≤ 1 := by rw [hr]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_leD : r ≤ δ / D := by rw [hr]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hnvsq_r1 : ‖v‖ ^ 2 ≤ r ^ 2 := by nlinarith [hvr1, hnv, hrpos.le]
  have hT1 : ‖v‖ * ‖e‖ ≤ C_D * r * rncRadialSq v := by
    have h1 : ‖v‖ * ‖e‖ ≤ ‖v‖ * (C_D * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left he2 hnv
    have h2 : ‖v‖ ^ 2 * ‖v‖ ≤ rncRadialSq v * r := mul_le_mul hnvsq hvr1 hnv hrv
    nlinarith [h1, mul_le_mul_of_nonneg_left h2 hCD0]
  have hT2 : ‖e‖ ^ 2 ≤ C_D ^ 2 * r ^ 2 * rncRadialSq v := by
    have he2sq : ‖e‖ ^ 2 ≤ (C_D * ‖v‖ ^ 2) ^ 2 := pow_le_pow_left₀ hne he2 2
    have hv4 : ‖v‖ ^ 2 * ‖v‖ ^ 2 ≤ rncRadialSq v * r ^ 2 :=
      mul_le_mul hnvsq hnvsq_r1 (sq_nonneg _) hrv
    nlinarith [he2sq, mul_le_mul_of_nonneg_left hv4 (sq_nonneg C_D)]
  have hr1sq : r ^ 2 ≤ r := by nlinarith [hrpos.le, hr_le1]
  have hnC2 : (0 : ℝ) ≤ (n : ℝ) * C_D ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg C_D)
  have hbig : 2 * (n : ℝ) * C_D * r + (n : ℝ) * C_D ^ 2 * r ^ 2 ≤ D * r := by
    rw [hD]; nlinarith [mul_nonneg hnC2 (sub_nonneg.mpr hr1sq), hrpos.le]
  have hrD : D * r ≤ δ := by
    calc D * r ≤ D * (δ / D) := mul_le_mul_of_nonneg_left hr_leD hDpos.le
      _ = δ := by field_simp
  have hcoef : 2 * (n : ℝ) * C_D * r + (n : ℝ) * C_D ^ 2 * r ^ 2 ≤ δ := le_trans hbig hrD
  have hM : 2 * (n : ℝ) * (‖v‖ * ‖e‖) + (n : ℝ) * ‖e‖ ^ 2 ≤ δ * rncRadialSq v := by
    nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ)),
      mul_le_mul_of_nonneg_left hT2 (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_right hcoef hrv, hrv]
  linarith [hadd, hM]

/-! ### (a1) — the width-`κ` mixed-α gated cover (mechanical `κ`-generalisation of `OrderOneTower`). -/

/-- **★ J4-673 (a1) — width-`κ` mixed-α gated cover.**  The `κ`-parametric analogue of
    `HeatResidualBound.gatedKernel_hEboundW_mixed_of_cover` (which pins `κ = 2`): from the 3-leg mixed
    cover phrased against `baseKernelW κ`, the gated kernel obeys the same mixed bound for all `p q τ > 0`.
    Every `baseKernelW`/gate lemma used is already `κ`-independent (`baseKernelW_zero_apply`,
    `baseKernelW_one_eq_tau_mul`, `gaussDdim_nonneg` — unconditional in the width).  NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_mixed_of_cover_W (κ : ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q|
            ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q) := by
  intro τ p q hτ
  have hbase0 : 0 ≤ baseKernelW κ (0 : ℝ) τ p q := by
    rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _
  have hbase1 : 0 ≤ baseKernelW κ (1 : ℝ) τ p q := by
    rw [baseKernelW_one_eq_tau_mul]; exact mul_nonneg hτ.le hbase0
  have hrhs : 0 ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q) :=
    mul_nonneg hC (by linarith)
  by_cases hq : q ∈ K
  · rcases hcover q hq τ hτ p with ⟨hS, hbd⟩ | hoff | ⟨ht, hs⟩
    · rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S H τ p q hq hS]; exact hbd
    · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr hoff), abs_zero]
      exact hrhs
    · rw [gatedKernel_heatOp_eq_zero_of_kernel_locally_zero g gi K S H τ p q ht hs, abs_zero]
      exact hrhs
  · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hrhs

/-- **★ J4-673 (a1) — width-`κ` mixed-α → α=0 collapse.**  The `κ`-parametric analogue of
    `RestrictedEboundW.mixedAlpha_to_alpha0_le`: on `(0,T]`, a mixed-α bound
    `|E| ≤ C·(baseKernelW κ 0 + baseKernelW κ 1)` is a pure α=0 bound with constant `C·(1+T)`, because
    `baseKernelW κ 1 τ = τ·baseKernelW κ 0 τ` and `τ ≤ T`.  NOT `a₁ = R/6`. -/
theorem mixedAlpha_to_alpha0_le_W (κ : ℝ) (E : ℝ → Point n → Point n → ℝ) (C T : ℝ) (hC : 0 ≤ C)
    (hmix : ∀ τ p q, 0 < τ → τ ≤ T →
      |E τ p q| ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q)) :
    ∀ τ p q, 0 < τ → τ ≤ T →
      |E τ p q| ≤ (C * (1 + T)) * baseKernelW κ (0 : ℝ) τ p q := by
  intro τ p q hτ hτT
  have hb0 : 0 ≤ baseKernelW κ (0 : ℝ) τ p q := by
    rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _
  have h1 : baseKernelW κ (1 : ℝ) τ p q = τ * baseKernelW κ (0 : ℝ) τ p q :=
    baseKernelW_one_eq_tau_mul κ τ p q
  calc |E τ p q|
      ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q) := hmix τ p q hτ hτT
    _ = C * (1 + τ) * baseKernelW κ (0 : ℝ) τ p q := by rw [h1]; ring
    _ ≤ (C * (1 + T)) * baseKernelW κ (0 : ℝ) τ p q := by
        apply mul_le_mul_of_nonneg_right _ hb0
        apply mul_le_mul_of_nonneg_left _ hC
        linarith

/-- **★ J4-673 (a1) — width-`κ` restricted `hEboundW_le` from the mixed cover.**  Composes the width-`κ`
    mixed gated cover with the width-`κ` α-collapse: from the 3-leg mixed cover, the gated kernel obeys
    the `(0,t]`-restricted pure α=0 bound `≤ (C·(1+t))·baseKernelW κ 0`.  The `κ`-parametric analogue of
    `HeatResidualBound.gatedKernel_hEboundW_le_of_mixedCover`.  NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_le_of_mixedCover_W (κ : ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C t : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q|
            ≤ C * (baseKernelW κ (0 : ℝ) τ p q + baseKernelW κ (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun s => H s p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (C * (1 + t)) * baseKernelW κ (0 : ℝ) τ p q :=
  mixedAlpha_to_alpha0_le_W κ (heatOp g gi (gatedKernel K S H)) C t hC
    (fun τ p q hτ _ => gatedKernel_hEboundW_mixed_of_cover_W κ g gi K S H C hC hcover τ p q hτ)

/-! ### (a) — the width-parametric `_of_good` merge (ambient width `W_a` exposed). -/

/-- **★★ J4-673 (a) — the WIDTH-PARAMETRIC `_of_good` merge.**  Verbatim
    `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_of_good_CONST`, but with the ambient Gaussian width
    exposed as a parameter `W_a` (the CONST version pins `W_a = 2`).  The in-gate field bound reads
    `gaussDdim (W_a·τ)` and the produced `hEboundW` reads `baseKernelW W_a 0`.  The `GateSqControl` field
    keeps the FIXED `3/2` ratio (a hardcoded property of the `GateSqControl` def — the square-control ratio
    is INDEPENDENT of the ambient Gaussian width).  Fed the intrinsic width-`w_i` defect through a
    displacement `rncRadialSq (φ_q v − q) ≤ D·rncRadialSq v` (via `gaussDdim_le_gaussDdim_chart`, prefactor
    absorbed into `B₀ B₁`), this produces the ambient width `W_a = w_i·D`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_of_good_W (W_a : ℝ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b B₀ B₁ : ℝ) (ha : 0 < a) (hab : a < b) (hB0 : 0 ≤ B₀) (hB1 : 0 ≤ B₁)
    (W : Point n → Point n → Point n)
    (c : ℝ) (hbc : b < c)
    (hgoodC : ∀ q ∈ K,
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (W_a * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c ∧
      (∀ v : Point n, ‖v‖ < c →
        rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (3 / 2 : ℝ) * rncRadialSq v) ∧
      q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) :
    (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
            (globalCutoffParametrixWitnessN 1 Θ u a b (W))) τ p q|
          ≤ (max B₀ B₁ * (1 + t)) * baseKernelW W_a (0 : ℝ) τ p q)
      ∧ GateSqControl K (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) W
      ∧ (∀ q ∈ K, q ∈ (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q)
      ∧ (∀ q ∈ K, IsOpen ((fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q)) := by
  classical
  set H : ℝ → Point n → Point n → ℝ :=
    globalCutoffParametrixWitnessN 1 Θ u a b (W) with hHdef
  have hCmax0 : (0 : ℝ) ≤ max B₀ B₁ := le_trans hB0 (le_max_left _ _)
  have hb0 : 0 < b := lt_trans ha hab
  have hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
      ((fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q ∈ nhds p
          ∧ |heatOp g gi H τ p q|
            ≤ max B₀ B₁ * (baseKernelW W_a (0 : ℝ) τ p q + baseKernelW W_a (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q}
          ∈ nhds p)
      ∨ ((fun s => H s p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ))) := by
    intro q hq τ hτ p
    obtain ⟨hbnd, hinv, hcont, hopen, hclos, _, _⟩ := hgoodC q hq
    by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c
    · refine Or.inl ⟨hopen.mem_nhds hpS, ?_⟩
      obtain ⟨w, hw, hwp⟩ := hpS
      rw [mem_ball_zero_iff] at hw
      have hb := hbnd τ hτ w hw
      rw [hwp] at hb
      rw [baseKernelW_one_eq_tau_mul, baseKernelW_zero_apply]
      have hG : (0 : ℝ) ≤ gaussDdim (W_a * τ) (p - q) := gaussDdim_nonneg _ _
      have hle : B₀ + B₁ * τ ≤ max B₀ B₁ * (1 + τ) := by
        have h2 : B₁ ≤ max B₀ B₁ := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_right h2 hτ.le, le_max_left B₀ B₁]
      calc |heatOp g gi H τ p q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (W_a * τ) (p - q) := hb
        _ ≤ (max B₀ B₁ * (1 + τ)) * gaussDdim (W_a * τ) (p - q) :=
            mul_le_mul_of_nonneg_right hle hG
        _ = max B₀ B₁ * (gaussDdim (W_a * τ) (p - q) + τ * gaussDdim (W_a * τ) (p - q)) := by ring
    · by_cases hpcl : p ∈ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      · obtain ⟨w', hw', hw'p⟩ := hclos hpcl
        rw [mem_closedBall_zero_iff] at hw'
        have hnormeq : ‖w'‖ = c := by
          rcases lt_or_eq_of_le hw' with hlt | heq
          · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
              p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) hpS
          · exact heq
        have hWp : W q p = w' := by
          rw [← hw'p]; exact hinv w' hw'
        have hb2 : b ^ 2 < rncRadialSq (W q p) := by
          rw [hWp]
          have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
            have hle := norm_le_rncRadial w'
            have := rncRadial_sq w'
            nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, this]
          nlinarith [h1, hnormeq, hb0, hbc]
        have hcontp : ContinuousAt (W q) p := by
          rw [← hw'p]; exact hcont w' hw'
        have hNnhds :
            (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
          hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · refine Filter.Eventually.of_forall (fun s => ?_)
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hb2), zero_mul]
        · filter_upwards [hNnhds] with p' hp'
          have hp'2 : b ^ 2 < rncRadialSq (W q p') := hp'
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hp'2), zero_mul]
      · refine Or.inr (Or.inl ?_)
        have hsub : (closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c))ᶜ
            ⊆ {p' : Point n | p' ∉ uniformFlowExp g gi hC hK q '' Metric.ball 0 c} :=
          fun x hx hxS => hx (subset_closure hxS)
        exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hpcl) hsub
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact gatedKernel_hEboundW_le_of_mixedCover_W W_a g gi K
      (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) H (max B₀ B₁) t hCmax0 hcover
  · intro q hq p hp
    obtain ⟨_, hinv, _, _, _, hsqc, _⟩ := hgoodC q hq
    obtain ⟨v, hvmem, hvp⟩ := hp
    rw [mem_ball_zero_iff] at hvmem
    have hWp : W q p = v := by rw [← hvp]; exact hinv v (le_of_lt hvmem)
    calc rncRadialSq (p - q)
        = rncRadialSq (uniformFlowExp g gi hC hK q v - q) := by rw [hvp]
      _ ≤ (3 / 2 : ℝ) * rncRadialSq v := hsqc v hvmem
      _ = (3 / 2 : ℝ) * rncRadialSq (W q p) := by rw [hWp]
  · intro q hq
    obtain ⟨_, _, _, _, _, _, hmem⟩ := hgoodC q hq
    exact hmem
  · intro q hq
    obtain ⟨_, _, _, hopen, _, _, _⟩ := hgoodC q hq
    exact hopen

end QIQTH.WidthParametricGoodGate

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WidthParametricGoodGate
#print axioms uniformFlowExp_hdisp_ball_delta
#print axioms gatedKernel_hEboundW_mixed_of_cover_W
#print axioms mixedAlpha_to_alpha0_le_W
#print axioms gatedKernel_hEboundW_le_of_mixedCover_W
#print axioms gatedWitnessN1_hEboundW_le_of_good_W
end AxiomChecks
