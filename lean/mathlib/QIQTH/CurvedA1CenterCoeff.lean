/-
  CurvedA1CenterCoeff — J4-606: THIRD layer of the (hbound-fat) wall — the CENTER-GAUGE variant of
  the uniform van-Vleck coefficient bounds `uniformCoeff_bound` (O(r²), J4-87 R3) and
  `uniformCoeffLinear_bound` (O(r), J4-108 L2), on the fat base compact `K = Metric.closedBall 0 r`,
  instantiated at the genuinely-curved witness `g^κ = curvedRNCMetric κ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes (hbound-fat) layers 4–5 + fat-`K` `hEmeas` + `hAdom` + `hcont` + the co-instantiated capstone
  application + the prior analytic piles / convergence trio / `hmassone` pre-ρ carriers / `hjets`.
  This brick is the THIRD layer of the (hbound-fat) producer rework, not its closure.

  ── ★★ THE USE-SITE VERDICT (proved by construction, the point of this brick).
  In the banked `uniformCoeff_bound` / `uniformCoeffLinear_bound` the frame normalisation
  `hframeK : ∀ q ∈ K, g q = δ` enters through EXACTLY TWO inner calls:
    (i)  `uniformFlowPullbackMetricInv_dev_uniform` (the inverse-metric deviation `hdev`), consumed
         at TWO sites of the coefficient algebra: the (A1) diagonal trace `½Σ(g̃⁻¹ᵢᵢ−1)` inside
         `coeffAF`, and every entry of the `coeffDevF` double sum (TC);
    (ii) `uniformFlowChristoffel_linear_decay` (the Γ̃-decay `hChb`), consumed at the (A2)
         Christoffel contraction `½ΣΣΣ g̃⁻¹·Γ̃·v` inside `coeffAF`.
  The third geometric pillar, `uniformFlowPullbackMetricInv_entry_uniform_bound` (Kg), and the two
  heat-side EVT blocks (`W = sup|w₀|`, `Kw` the gradient sup / linear-decay constant) NEVER took
  `hframeK`.  Substituting the center-gauge layers:
    (i)  → layer 1 (`uniformFlowPullbackMetricInv_dev_uniform_center`, J4-604): each deviation entry
         costs `Md·(rncRadialSq v + ε₀)` — THE `ε₀` DEBT SURFACES HERE, at both sites;
    (ii) → layer 2 (`uniformFlowChristoffel_linear_decay_center`, J4-605): FREE — no `ε₀` at all.

  ── ★★ THE HONEST `ε₀` PLACEMENT (no suppression).  The bound genuinely DEGRADES to an affine form:
      `|totalRadialO1_coeff(v)| ≤ C_c · rncRadialSq v + C_ε · ε₀`      (O(r²) version)
      `|totalRadialO1_coeff(v)| ≤ C_c · rncRadial  v + C_ε · ε₀`      (O(r)  version)
  with a REAL 0th-order term `C_ε·ε₀` that does NOT vanish as `v → 0`: the (A1) trace picks up
  `½·n·Md·ε₀` per se (the pullback metric at flow time 0 is `g(q) ≠ δ`, so the trace of the inverse
  deviates from `n` by O(ε₀) even at the center), and the (TC) `coeffDevF` sum picks up
  `n²·Md·Kw·ρ_c²·ε₀` (resp. `n²·Md·Kw·Rmax·ε₀`).  Exact constants:
      C_c = (½n·Md + ½n³·Kg·KdΓ)·W + n·Kw₂ + n²·Md·Kw₂·ρ_c²          (IDENTICAL to the banked C_c)
      C_ε = ½n·Md·W + n²·Md·Kw₂·ρ_c²                                  (the new 0th-order weight)
  (Linear version: `ρ_c² → n·ρ_c²` in the TC slot, `Rmax = √n·ρ_c` in the C_ε TC slot, `Kw₂ → Kw`.)
  DISCIPLINE (inherited from layer 1): `ρ_c`, `C_c`, `C_ε` are all produced BEFORE `ε₀` is
  quantified — no ε₀-inflation of the geometric/heat constants; only the additive floor moves.
  Smallness of `C_ε·ε₀` is NOT claimed here; it is delivered downstream by
  `curvedRNC_center_eps_arbitrarily_small` (shrink the base-ball radius `r`, `K` stays fat).

  ── LANDED HERE:
    • `uniformCoeff_bound_center` — ★ THE BRICK (O(r²) + ε₀ version, `hw0flat` gauge as banked):
      `hframeK` → `hdevK`, conclusion `≤ C_c·rncRadialSq v + C_ε·ε₀`, constants before `ε₀`.
    • `uniformCoeffLinear_bound_center` — the O(r) + ε₀ companion (NO `hw0flat`, as banked L2 —
      this is the branch the shifted van-Vleck profile `u₁` consumes, where `∂w₁(0) ≠ 0`).
    • `curvedRNC_coeff_bound_center` / `curvedRNC_coeffLinear_bound_center` — ★★ fat-`K` curved
      instantiations: for `κ ≤ 0` and EVERY radius `r`, on `K = closedBall 0 r`, with the explicit
      `ε₀ = (|κ|/3)·n·r²` supplied by `curvedRNC_frame_dev_on_ball` and every geometric carry
      discharged from banked curved lemmas.
    • `curvedRNC_coeff_center_satisfiable` — non-vacuity gate (cp466 discipline): fat `K` contains a
      NONZERO point, the heat-side antecedents (`hw0smooth`/`hw0flat`) are INHABITED (`Θ = 1`,
      `u = 1`: `foldedCoeff = 1`), and the `hdevK` antecedent HOLDS at the curved witness with the
      explicit `ε₀` — every antecedent of the center theorems is exhibited satisfiable at fat `K`.

  ── CONSUMABILITY BY LAYER 4 (checked).  The τ-narrow residual engines
  (`uniformResidual_gaussian_bound_tau_narrow`, `uniformResidualLinear_gaussian_bound_tau_narrow`,
  `cutoffResidual_uniformFlow_of_coeffBound`) consume the coefficient bound as an EXPLICIT
  HYPOTHESIS `hCoeffU`/`hCoeffLin` of shape `≤ C_c·rncRadialSq v` (resp. `·rncRadial v`).  The
  center conclusions here expose the same interface extended by the additive `C_ε·ε₀`; layer 4 must
  thread that 0th-order term through the width-2 Gaussian bookkeeping, where a CONSTANT coefficient
  is exactly a `(1/τ)·G·(C_ε·ε₀)` contribution in the `T1` slot — i.e. layer 4's honest output shape
  gains a `(C_ε·ε₀/τ)`-weighted Gaussian term (NOT absorbed here; stated so layer 4 cannot silently
  drop it).

  ── REMAINING (hbound-fat) LAYERS (scoped, OPEN — in dependency order):
    4. center-gauge `uniformResidual(_Linear)_gaussian_bound_tau_narrow` (consumes this layer; the
       `C_ε·ε₀` term enters the `T1` slot as a `(1/τ)`-weighted constant coefficient),
    5. producer re-assembly (`cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` →
       `gatedWitnessN1_hEboundW_le_lin_CONST` → fat-`K` dom pkg) with `ε₀` tracked through the
       width-2 Gaussian bookkeeping.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.UniformFlowJetZero
import QIQTH.UniformFlowMetricInvProps
import QIQTH.UniformCoeffBound
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedA1CenterChr
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.OuterCarryRecon
import QIQTH.ChristoffelSmooth

open Finset
open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.ExpMap QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.OuterCarryRecon
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterChr
open QIQTH.HeatResidualBound QIQTH.ResidueBound
open Set Filter
open scoped Topology BigOperators ContDiff

namespace QIQTH.CurvedA1CenterCoeff

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### ★ THE BRICK — center-gauge `uniformCoeff_bound`: `hframeK → hdevK`, honest `+C_ε·ε₀`. -/

/-- **★★ J4-606 — CENTER-GAUGE UNIFORM COEFFICIENT BOUND (O(r²) + ε₀).**  The banked
    `uniformCoeff_bound` (J4-87 R3) with `hframeK` replaced by the frame deviation
    `hdevK : ∀ q ∈ K, |g(q) − δ| ≤ ε₀`, and the HONEST degraded conclusion
        `|totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadialSq v + C_ε · ε₀`.
    The `ε₀` debt of layer 1 surfaces at BOTH `hdev` sites of the coefficient algebra:
      (A1) the diagonal trace `½Σ(g̃⁻¹ᵢᵢ−1)` inside `coeffAF` pays `½·n·Md·ε₀` (times `W`),
      (TC) each `coeffDevF` entry pays its `Md·ε₀` share, absorbed into `n²·Md·Kw₂·ρ_c²·ε₀`;
    the (A2) Christoffel contraction is `ε₀`-FREE (layer 2 deleted `hframeK` there) and (TB)
    `radialDeriv(w₀)` is heat-side only.  `C_c` is LITERALLY the banked constant (at `ε₀ = 0` the
    banked bound's shape is recovered), and `ρ_c`, `C_c`, `C_ε` are produced BEFORE `ε₀` — no
    ε₀-inflation of the geometric/heat constants.  The 0th-order term `C_ε·ε₀` is REAL (it does not
    vanish as `v → 0`); its smallness comes only from shrinking the base ball
    (`curvedRNC_center_eps_arbitrarily_small`), downstream.  NOT `a₁ = R/6`. -/
theorem uniformCoeff_bound_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
      ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ C_c * rncRadialSq v + C_ε * ε₀ := by
  classical
  -- geometric ingredients: layer-1 center deviation (carries the ε₀), frame-free entry bound,
  -- layer-2 center Christoffel decay (ε₀-free).  All constants BEFORE ε₀.
  obtain ⟨r_d, hr_d0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform_center g gi hC hK hg hgnd hgsymm hinvF
  obtain ⟨r_e, hr_e0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r_Γ, hr_Γ0, KdΓ, hKdΓ0, hChb⟩ :=
    uniformFlowChristoffel_linear_decay_center g gi hg hC hK hgnd hgsymm hinvF
  set ρ_c : ℝ := min r_d (min r_e r_Γ) with hρ_c_def
  have hρ_c0 : 0 < ρ_c := lt_min hr_d0 (lt_min hr_e0 hr_Γ0)
  -- heat-side `q`-independent EVT data on the closed ball of radius `ρ_c` (as banked; ε₀-free).
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨Kw2, hKw20, hpdw⟩ : ∃ Kw2 : ℝ, 0 ≤ Kw2 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, ∀ i : Fin n,
        |pd (foldedCoeff Θ u 0) i v| ≤ Kw2 * ‖v‖ := by
    have hcont : Continuous
        (fun w => ∑ i, ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i y) w‖) :=
      continuous_finsetSum _
        (fun i _ => ((contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).continuous_fderiv (by simp)).norm)
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hvmem i => ?_⟩
    have hvle : ‖v‖ ≤ ρ_c := by rw [mem_closedBall_zero_iff] at hvmem; exact hvmem
    refine decay_order_one (fun y => pd (foldedCoeff Θ u 0) i y) (max C 0) ρ_c hρ_c0
      (hw0flat i) ?_ ?_ hvle
    · exact fun w _ =>
        ((contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).differentiable (by simp)).differentiableAt
    · intro w hw
      have hsum := hC' w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at hsum
      calc ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i y) w‖
          ≤ ∑ i', ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i' y) w‖ :=
            Finset.single_le_sum
              (f := fun i' => ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i' y) w‖)
              (fun i' _ => norm_nonneg _) (Finset.mem_univ i)
        _ ≤ C := hsum
        _ ≤ max C 0 := le_max_left _ _
  -- the assembled constants: C_c is the BANKED constant; C_ε is the honest new 0th-order weight.
  have hCA1nn : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) * Md :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hMd0
  have hCA2nn : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hKg0) hKdΓ0
  have hCTCnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw20) (by positivity)
  refine ⟨ρ_c, hρ_c0,
    ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W
      + (n : ℝ) * Kw2 + (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2,
    ?_,
    (1 / 2) * (n : ℝ) * Md * W + (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2,
    ?_, ?_⟩
  · -- `0 ≤ C_c`.
    have hCB0 : (0 : ℝ) ≤ (n : ℝ) * Kw2 := mul_nonneg (Nat.cast_nonneg n) hKw20
    have := mul_nonneg (add_nonneg hCA1nn hCA2nn) hW0
    positivity
  · -- `0 ≤ C_ε`.
    exact add_nonneg (mul_nonneg hCA1nn hW0) hCTCnn
  intro ε₀ hε₀ hdevK q hq v hv
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hve : ‖v‖ < r_e := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvΓ : ‖v‖ < r_Γ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_c := by
    rw [mem_closedBall_zero_iff]; exact hv.le
  unfold totalRadialO1_coeff radialDeriv
  set Gm : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hGmdef
  set Gi : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hGidef
  set w0 : Point n → ℝ := foldedCoeff Θ u 0 with hw0def
  -- pointwise data at `v` — the deviation now costs `Md·(rncRadialSq v + ε₀)` (layer 1).
  have hGI : ∀ i j : Fin n, |Gi v i j| ≤ Kg := fun i j => hGIb q hq v hve i j
  have hdevv : ∀ i j : Fin n, |Gi v i j - (if i = j then (1 : ℝ) else 0)|
      ≤ Md * (rncRadialSq v + ε₀) :=
    fun i j => hdev ε₀ hε₀ hdevK q hq v hvd i j
  have hΓv : ∀ k i j : Fin n, |christoffel Gm Gi k i j v| ≤ KdΓ * ‖v‖ :=
    fun k i j => hChb q hq v hvΓ k i j
  have hpdwv : ∀ i : Fin n, |pd w0 i v| ≤ Kw2 * ‖v‖ := hpdw v hvball
  have hWv : |w0 v| ≤ W := hWbd v hvball
  have hvi : ∀ i : Fin n, |v i| ≤ ‖v‖ := fun i => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  have hnv2 : ‖v‖ * ‖v‖ ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
          mul_le_mul h h (norm_nonneg _) (rncRadial_nonneg _)
      _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
  have hvρ2 : ‖v‖ * ‖v‖ ≤ ρ_c * ρ_c := mul_le_mul hv.le hv.le (norm_nonneg _) hρ_c0.le
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  have hSε0 : (0 : ℝ) ≤ rncRadialSq v + ε₀ := add_nonneg (rncRadialSq_nonneg v) hε₀
  -- (A1) diagonal-trace part — ε₀ SURFACES: `≤ ½·n·Md·(rncRadialSq v + ε₀)`.
  have hA1 : |(1 / 2) * (∑ i, (Gi v i i - 1))|
      ≤ (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀) := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, (Gi v i i - 1)| ≤ (n : ℝ) * (Md * (rncRadialSq v + ε₀)) := by
      calc |∑ i, (Gi v i i - 1)| ≤ ∑ i, |Gi v i i - 1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Md * (rncRadialSq v + ε₀) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := hdevv i i; simpa using h
        _ = (n : ℝ) * (Md * (rncRadialSq v + ε₀)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (1 / 2 : ℝ) * |∑ i, (Gi v i i - 1)|
        ≤ (1 / 2) * ((n : ℝ) * (Md * (rncRadialSq v + ε₀))) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀) := by ring
  -- (A2) Christoffel-contraction part — ε₀-FREE (layer 2), exactly as banked.
  have hA2 : |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
      ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
          ≤ ∑ i, ∑ j, ∑ k, |Gi v i j * christoffel Gm Gi k i j v * v k| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, Kg * (KdΓ * ‖v‖) * ‖v‖ := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hGI i j) (hΓv k i j) (abs_nonneg _) hKg0) (hvi k)
              (abs_nonneg _) (mul_nonneg hKg0 (mul_nonneg hKdΓ0 (norm_nonneg _)))
        _ = (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          exact mul_le_mul_of_nonneg_left hnv2
            (mul_nonneg (mul_nonneg (by positivity) hKg0) hKdΓ0)
      _ = (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by ring
  -- (TA) `coeffAF · w₀` — carries the (A1) ε₀ share `½·n·Md·W·ε₀`.
  have hCAcoeff : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ :=
    add_nonneg hCA1nn hCA2nn
  have hTA : |((1 / 2) * (∑ i, (Gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)) * w0 v|
      ≤ ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W * rncRadialSq v
        + (1 / 2) * (n : ℝ) * Md * W * ε₀ := by
    rw [abs_mul]
    have hAF : |(1 / 2) * (∑ i, (Gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
        ≤ ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v
          + (1 / 2) * (n : ℝ) * Md * ε₀ := by
      calc |(1 / 2) * (∑ i, (Gi v i i - 1))
              - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
          ≤ |(1 / 2) * (∑ i, (Gi v i i - 1))|
              + |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| :=
            habs_sub _ _
        _ ≤ (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀)
              + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := add_le_add hA1 hA2
        _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v
              + (1 / 2) * (n : ℝ) * Md * ε₀ := by ring
    have hAFnn : (0 : ℝ)
        ≤ ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v
          + (1 / 2) * (n : ℝ) * Md * ε₀ :=
      add_nonneg (mul_nonneg hCAcoeff (rncRadialSq_nonneg v)) (mul_nonneg hCA1nn hε₀)
    calc |(1 / 2) * (∑ i, (Gi v i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| * |w0 v|
        ≤ (((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v
            + (1 / 2) * (n : ℝ) * Md * ε₀) * W :=
          mul_le_mul hAF hWv (abs_nonneg _) hAFnn
      _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W * rncRadialSq v
            + (1 / 2) * (n : ℝ) * Md * W * ε₀ := by ring
  -- (TB) `radialDeriv(w₀)` — heat-side only, ε₀-FREE, exactly as banked.
  have hTB : |∑ i, v i * pd w0 i v| ≤ (n : ℝ) * Kw2 * rncRadialSq v := by
    calc |∑ i, v i * pd w0 i v| ≤ ∑ i, |v i * pd w0 i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ * (Kw2 * ‖v‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hvi i) (hpdwv i) (abs_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * Kw2 * (‖v‖ * ‖v‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (n : ℝ) * Kw2 * rncRadialSq v :=
          mul_le_mul_of_nonneg_left hnv2 (mul_nonneg (Nat.cast_nonneg n) hKw20)
  -- (TC) `coeffDevF` — the second ε₀ site: `≤ n²·Md·Kw₂·ρ_c²·(rncRadialSq v + ε₀)`.
  have hTC : |(1 / 2) * (∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd w0 j v + v j * pd w0 i v))|
      ≤ (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * rncRadialSq v
        + (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * ε₀ := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (n : ℝ) ^ 2 * Md * Kw2 * 2 * (rncRadialSq v + ε₀) * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd w0 j v + v j * pd w0 i v)|
          ≤ ∑ i, ∑ j, (Md * (rncRadialSq v + ε₀)) * (2 * (‖v‖ * (Kw2 * ‖v‖))) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            refine mul_le_mul (hdevv i j) ?_ (abs_nonneg _) (mul_nonneg hMd0 hSε0)
            calc |v i * pd w0 j v + v j * pd w0 i v|
                ≤ |v i * pd w0 j v| + |v j * pd w0 i v| := abs_add_le _ _
              _ ≤ ‖v‖ * (Kw2 * ‖v‖) + ‖v‖ * (Kw2 * ‖v‖) := by
                  refine add_le_add ?_ ?_
                  · rw [abs_mul]
                    exact mul_le_mul (hvi i) (hpdwv j) (abs_nonneg _) (norm_nonneg _)
                  · rw [abs_mul]
                    exact mul_le_mul (hvi j) (hpdwv i) (abs_nonneg _) (norm_nonneg _)
              _ = 2 * (‖v‖ * (Kw2 * ‖v‖)) := by ring
        _ = (n : ℝ) ^ 2 * Md * Kw2 * 2 * (rncRadialSq v + ε₀) * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (1 / 2) * ((n : ℝ) ^ 2 * Md * Kw2 * 2 * (rncRadialSq v + ε₀) * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = ((n : ℝ) ^ 2 * Md * Kw2 * (rncRadialSq v + ε₀)) * (‖v‖ * ‖v‖) := by ring
      _ ≤ ((n : ℝ) ^ 2 * Md * Kw2 * (rncRadialSq v + ε₀)) * (ρ_c * ρ_c) :=
          mul_le_mul_of_nonneg_left hvρ2
            (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw20) hSε0)
      _ = (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * rncRadialSq v
            + (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * ε₀ := by ring
  -- assemble the three summands by the triangle inequality.
  refine le_trans (abs_add_le _ _)
    (le_trans (add_le_add (abs_add_le _ _) (le_refl _))
      (le_trans (add_le_add (add_le_add hTA hTB) hTC) ?_))
  apply le_of_eq; ring

/-! ### The O(r) + ε₀ companion — NO `hw0flat` (the shifted van-Vleck profile branch). -/

/-- **★ J4-606 — CENTER-GAUGE UNIFORM `O(r)` COEFFICIENT BOUND (+ε₀), NO FLATNESS.**  The banked
    `uniformCoeffLinear_bound` (J4-108 L2) with `hframeK → hdevK`:
        `|totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadial v + C_ε · ε₀`.
    Same two `hdev` sites pay the `ε₀` ((A1) trace: `½·n·Md·W·ε₀`; (TC): `n²·Md·Kw·Rmax·ε₀` after
    `rncRadial v ≤ Rmax = √n·ρ_c`); the `radialDeriv` summand is bounded by the `C¹` sup directly
    (no `∂w₀(0) = 0` assumed — this is the branch the shifted van-Vleck profile `u₁` consumes, where
    the `O(r²)` bound is generically FALSE).  `C_c` is the banked constant; `ρ_c`, `C_c`, `C_ε`
    before `ε₀`.  NOT `a₁ = R/6`. -/
theorem uniformCoeffLinear_bound_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0)) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
      ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ C_c * rncRadial v + C_ε * ε₀ := by
  classical
  obtain ⟨r_d, hr_d0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform_center g gi hC hK hg hgnd hgsymm hinvF
  obtain ⟨r_e, hr_e0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r_Γ, hr_Γ0, KdΓ, hKdΓ0, hChb⟩ :=
    uniformFlowChristoffel_linear_decay_center g gi hg hC hK hgnd hgsymm hinvF
  set ρ_c : ℝ := min r_d (min r_e r_Γ) with hρ_c_def
  have hρ_c0 : 0 < ρ_c := lt_min hr_d0 (lt_min hr_e0 hr_Γ0)
  -- heat-side sups (NO flatness): `W = sup|w₀|`, `Kw = sup|∂w₀|` on the closed ball (as banked).
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨Kw, hKw0, hpdw⟩ : ∃ Kw : ℝ, 0 ≤ Kw ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, ∀ i : Fin n,
        |pd (foldedCoeff Θ u 0) i v| ≤ Kw := by
    have hcont : Continuous (fun w => ∑ i, |pd (foldedCoeff Θ u 0) i w|) :=
      continuous_finsetSum _
        (fun i _ => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).continuous.abs)
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hvmem i => ?_⟩
    have hsum := hC' v hvmem
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at hsum
    calc |pd (foldedCoeff Θ u 0) i v|
        ≤ ∑ i', |pd (foldedCoeff Θ u 0) i' v| :=
          Finset.single_le_sum (f := fun i' => |pd (foldedCoeff Θ u 0) i' v|)
            (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ C := hsum
      _ ≤ max C 0 := le_max_left _ _
  set Caf : ℝ := (1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ with hCaf_def
  have hCA1nn : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) * Md :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hMd0
  have hCaf0 : 0 ≤ Caf := by
    rw [hCaf_def]; positivity
  set Rmax : ℝ := Real.sqrt (n : ℝ) * ρ_c with hRmax_def
  have hRmax0 : 0 ≤ Rmax := by rw [hRmax_def]; positivity
  refine ⟨ρ_c, hρ_c0,
    Caf * W * Rmax + (n : ℝ) * Kw + (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2),
    ?_,
    (1 / 2) * (n : ℝ) * Md * W + (n : ℝ) ^ 2 * Md * Kw * Rmax,
    ?_, ?_⟩
  · positivity
  · exact add_nonneg (mul_nonneg hCA1nn hW0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw0) hRmax0)
  intro ε₀ hε₀ hdevK q hq v hv
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hve : ‖v‖ < r_e := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvΓ : ‖v‖ < r_Γ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_c := by
    rw [mem_closedBall_zero_iff]; exact hv.le
  have hvle : ‖v‖ ≤ ρ_c := hv.le
  unfold totalRadialO1_coeff radialDeriv
  set Gm : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hGmdef
  set Gi : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hGidef
  set w0 : Point n → ℝ := foldedCoeff Θ u 0 with hw0def
  have hGI : ∀ i j : Fin n, |Gi v i j| ≤ Kg := fun i j => hGIb q hq v hve i j
  have hdevv : ∀ i j : Fin n, |Gi v i j - (if i = j then (1 : ℝ) else 0)|
      ≤ Md * (rncRadialSq v + ε₀) :=
    fun i j => hdev ε₀ hε₀ hdevK q hq v hvd i j
  have hΓv : ∀ k i j : Fin n, |christoffel Gm Gi k i j v| ≤ KdΓ * ‖v‖ :=
    fun k i j => hChb q hq v hvΓ k i j
  have hpdwv : ∀ i : Fin n, |pd w0 i v| ≤ Kw := hpdw v hvball
  have hWv : |w0 v| ≤ W := hWbd v hvball
  have hvi : ∀ i : Fin n, |v i| ≤ rncRadial v := fun i => abs_coord_le_rncRadial v i
  have hSε0 : (0 : ℝ) ≤ rncRadialSq v + ε₀ := add_nonneg (rncRadialSq_nonneg v) hε₀
  -- `r² = rncRadialSq v` bounds (as banked).
  have hrsq_bnd : rncRadialSq v ≤ (n : ℝ) * ρ_c ^ 2 := by
    have hsq : ∀ i : Fin n, (v i) ^ 2 ≤ ρ_c ^ 2 := by
      intro i
      have h1 : |v i| ≤ ρ_c := le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i) hvle
      nlinarith [sq_abs (v i), abs_nonneg (v i)]
    calc rncRadialSq v = ∑ i, (v i) ^ 2 := rfl
      _ ≤ ∑ _i : Fin n, ρ_c ^ 2 := Finset.sum_le_sum fun i _ => hsq i
      _ = (n : ℝ) * ρ_c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hRle : rncRadial v ≤ Rmax := by
    rw [rncRadial, hRmax_def]
    calc Real.sqrt (rncRadialSq v) ≤ Real.sqrt ((n : ℝ) * ρ_c ^ 2) := Real.sqrt_le_sqrt hrsq_bnd
      _ = Real.sqrt (n : ℝ) * ρ_c := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hρ_c0.le]
  have hrsq_r : rncRadialSq v ≤ Rmax * rncRadial v := by
    calc rncRadialSq v = rncRadial v * rncRadial v := by rw [← rncRadial_sq]; ring
      _ ≤ Rmax * rncRadial v := mul_le_mul_of_nonneg_right hRle (rncRadial_nonneg v)
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  -- (A1) diagonal-trace part — ε₀ SURFACES.
  have hA1 : |(1 / 2) * (∑ i, (Gi v i i - 1))|
      ≤ (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀) := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, (Gi v i i - 1)| ≤ (n : ℝ) * (Md * (rncRadialSq v + ε₀)) := by
      calc |∑ i, (Gi v i i - 1)| ≤ ∑ i, |Gi v i i - 1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Md * (rncRadialSq v + ε₀) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := hdevv i i; simpa using h
        _ = (n : ℝ) * (Md * (rncRadialSq v + ε₀)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (1 / 2 : ℝ) * |∑ i, (Gi v i i - 1)|
        ≤ (1 / 2) * ((n : ℝ) * (Md * (rncRadialSq v + ε₀))) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀) := by ring
  -- (A2) Christoffel-contraction part — ε₀-FREE (layer 2).
  have hA2 : |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
      ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
          ≤ ∑ i, ∑ j, ∑ k, |Gi v i j * christoffel Gm Gi k i j v * v k| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, Kg * (KdΓ * ‖v‖) * ‖v‖ := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            refine mul_le_mul (mul_le_mul (hGI i j) (hΓv k i j) (abs_nonneg _) hKg0) ?_
              (abs_nonneg _) (mul_nonneg hKg0 (mul_nonneg hKdΓ0 (norm_nonneg _)))
            rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k
        _ = (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by positivity) hKg0) hKdΓ0)
          have h := norm_le_rncRadial v
          calc ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
                mul_le_mul h h (norm_nonneg _) (rncRadial_nonneg _)
            _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
      _ = (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by ring
  -- (TA) `coeffAF · w₀` — `≤ Caf·W·Rmax·rncRadial v + ½·n·Md·W·ε₀`.
  have hTA : |((1 / 2) * (∑ i, (Gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)) * w0 v|
      ≤ Caf * W * Rmax * rncRadial v + (1 / 2) * (n : ℝ) * Md * W * ε₀ := by
    rw [abs_mul]
    have hAF : |(1 / 2) * (∑ i, (Gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
        ≤ Caf * rncRadialSq v + (1 / 2) * (n : ℝ) * Md * ε₀ := by
      rw [hCaf_def]
      calc |(1 / 2) * (∑ i, (Gi v i i - 1))
              - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
          ≤ |(1 / 2) * (∑ i, (Gi v i i - 1))|
              + |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| :=
            habs_sub _ _
        _ ≤ (1 / 2) * (n : ℝ) * Md * (rncRadialSq v + ε₀)
              + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := add_le_add hA1 hA2
        _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v
              + (1 / 2) * (n : ℝ) * Md * ε₀ := by ring
    have hAFnn : (0 : ℝ) ≤ Caf * rncRadialSq v + (1 / 2) * (n : ℝ) * Md * ε₀ :=
      add_nonneg (mul_nonneg hCaf0 (rncRadialSq_nonneg v)) (mul_nonneg hCA1nn hε₀)
    calc |(1 / 2) * (∑ i, (Gi v i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| * |w0 v|
        ≤ (Caf * rncRadialSq v + (1 / 2) * (n : ℝ) * Md * ε₀) * W :=
          mul_le_mul hAF hWv (abs_nonneg _) hAFnn
      _ ≤ (Caf * (Rmax * rncRadial v) + (1 / 2) * (n : ℝ) * Md * ε₀) * W := by
          refine mul_le_mul_of_nonneg_right (add_le_add ?_ (le_refl _)) hW0
          exact mul_le_mul_of_nonneg_left hrsq_r hCaf0
      _ = Caf * W * Rmax * rncRadial v + (1 / 2) * (n : ℝ) * Md * W * ε₀ := by ring
  -- (TB) `radialDeriv(w₀)` — the honest `O(r)` linear part, ε₀-FREE.
  have hTB : |∑ i, v i * pd w0 i v| ≤ (n : ℝ) * Kw * rncRadial v := by
    calc |∑ i, v i * pd w0 i v| ≤ ∑ i, |v i * pd w0 i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, rncRadial v * Kw := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hvi i) (hpdwv i) (abs_nonneg _) (rncRadial_nonneg v)
      _ = (n : ℝ) * Kw * rncRadial v := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- (TC) `coeffDevF` — the second ε₀ site: `≤ n²·Md·Kw·(n·ρ_c²)·rncRadial v + n²·Md·Kw·Rmax·ε₀`.
  have hTC : |(1 / 2) * (∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd w0 j v + v j * pd w0 i v))|
      ≤ (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2) * rncRadial v
        + (n : ℝ) ^ 2 * Md * Kw * Rmax * ε₀ := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (n : ℝ) ^ 2 * Md * Kw * 2 * (rncRadialSq v + ε₀) * rncRadial v := by
      calc |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd w0 j v + v j * pd w0 i v)|
          ≤ ∑ i, ∑ j, (Md * (rncRadialSq v + ε₀)) * (2 * (rncRadial v * Kw)) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            refine mul_le_mul (hdevv i j) ?_ (abs_nonneg _) (mul_nonneg hMd0 hSε0)
            calc |v i * pd w0 j v + v j * pd w0 i v|
                ≤ |v i * pd w0 j v| + |v j * pd w0 i v| := abs_add_le _ _
              _ ≤ rncRadial v * Kw + rncRadial v * Kw := by
                  refine add_le_add ?_ ?_
                  · rw [abs_mul]
                    exact mul_le_mul (hvi i) (hpdwv j) (abs_nonneg _) (rncRadial_nonneg v)
                  · rw [abs_mul]
                    exact mul_le_mul (hvi j) (hpdwv i) (abs_nonneg _) (rncRadial_nonneg v)
              _ = 2 * (rncRadial v * Kw) := by ring
        _ = (n : ℝ) ^ 2 * Md * Kw * 2 * (rncRadialSq v + ε₀) * rncRadial v := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hMKnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 * Md * Kw :=
      mul_nonneg (mul_nonneg (by positivity) hMd0) hKw0
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (1 / 2) * ((n : ℝ) ^ 2 * Md * Kw * 2 * (rncRadialSq v + ε₀) * rncRadial v) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = ((n : ℝ) ^ 2 * Md * Kw) * (rncRadialSq v * rncRadial v)
            + ((n : ℝ) ^ 2 * Md * Kw) * (ε₀ * rncRadial v) := by ring
      _ ≤ ((n : ℝ) ^ 2 * Md * Kw) * (((n : ℝ) * ρ_c ^ 2) * rncRadial v)
            + ((n : ℝ) ^ 2 * Md * Kw) * (ε₀ * Rmax) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hrsq_bnd (rncRadial_nonneg v)) hMKnn
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hRle hε₀) hMKnn
      _ = (n : ℝ) ^ 2 * Md * Kw * ((n : ℝ) * ρ_c ^ 2) * rncRadial v
            + (n : ℝ) ^ 2 * Md * Kw * Rmax * ε₀ := by ring
  -- assemble.
  refine le_trans (abs_add_le _ _)
    (le_trans (add_le_add (abs_add_le _ _) (le_refl _))
      (le_trans (add_le_add (add_le_add hTA hTB) hTC) ?_))
  apply le_of_eq; ring

/-! ### The fat-`K` curved instantiations — all geometric carries discharged, explicit `ε₀`. -/

/-- **★★ THE CENTER-GAUGE COEFFICIENT BOUND AT THE FAT BASE COMPACT for the curved witness
    (O(r²) + ε₀ version).**  For `κ ≤ 0` and EVERY radius `r`, on `K = Metric.closedBall 0 r`, with
    ANY heat-side data satisfying the (banked) gauge hypotheses:
    `∃ ρ_c > 0, ∃ C_c ≥ 0, ∃ C_ε ≥ 0, ∀ q ∈ K, ∀ ‖v‖ < ρ_c,
        |totalRadialO1_coeff(v)| ≤ C_c·rncRadialSq v + C_ε·((|κ|/3)·n·r²)`
    — the THIRD member of the (hbound-fat) `hframeK` use-site list now HOLDS at the fat curved base
    compact, with every geometric carry discharged from banked curved lemmas and the explicit
    `ε₀ = (|κ|/3)·n·r²` supplied by `curvedRNC_frame_dev_on_ball`.  The `C_ε·ε₀` floor is REAL; its
    smallness is reachable only via `curvedRNC_center_eps_arbitrarily_small` (shrink `r`, `K` stays
    fat).  NOT `a₁ = R/6` — layers 4–5 remain OPEN. -/
theorem curvedRNC_coeff_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff
          (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
          (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u v|
        ≤ C_c * rncRadialSq v + C_ε * (|κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hmain⟩ :=
    uniformCoeff_bound_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
      Θ u hw0smooth hw0flat
  exact ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0,
    hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity) (curvedRNC_frame_dev_on_ball κ r)⟩

/-- **★★ The fat-`K` curved instantiation of the O(r) + ε₀ version** (no `hw0flat` — the shifted
    van-Vleck profile branch).  Same carries, same explicit `ε₀ = (|κ|/3)·n·r²`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_coeffLinear_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0)) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff
          (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
          (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u v|
        ≤ C_c * rncRadial v + C_ε * (|κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hmain⟩ :=
    uniformCoeffLinear_bound_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
      Θ u hw0smooth
  exact ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0,
    hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity) (curvedRNC_frame_dev_on_ball κ r)⟩

/-! ### Non-vacuity gate (cp466 discipline: ANTECEDENT inhabitance, not conclusion shape). -/

/-- **Non-vacuity of the center-gauge coefficient bounds at fat `K`.**  At every `r > 0`, `n ≥ 1`:
    (i) the base compact `closedBall 0 r` contains a NONZERO point (no `K ⊆ {0}` collapse — contrast
    `rebased_hframeK_unsat`, J4-603); (ii) the HEAT-SIDE antecedents are INHABITED: `Θ = 1`, `u = 1`
    give `foldedCoeff Θ u 0 = 1`, which is smooth AND center-flat (`hw0smooth` ∧ `hw0flat` both
    hold — the same satisfiability witness the banked `uniformCoeff_bound` cites); (iii) the `hdevK`
    antecedent of the center theorems HOLDS at the curved witness with the explicit
    `ε₀ = (|κ|/3)·n·r²`.  So EVERY antecedent of `uniformCoeff_bound_center` /
    `uniformCoeffLinear_bound_center` is exhibited satisfiable at the fat curved base compact —
    the conclusions are not vacuously quantified.  NOT `a₁ = R/6`. -/
theorem curvedRNC_coeff_center_satisfiable (κ r : ℝ) (hr : 0 < r) (hn : 1 ≤ n) :
    (∃ q ∈ Metric.closedBall (0 : Point n) r, q ≠ 0) ∧
      (∃ Θ : Point n → ℝ, ∃ u : ℕ → Point n → ℝ,
        ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0) ∧
        ∀ e : Fin n, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) ∧
      (∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j : Fin n,
        |curvedRNCMetric κ q i j - (if i = j then (1 : ℝ) else 0)|
          ≤ |κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  refine ⟨(curvedRNC_center_gauge_satisfiable κ r hr hn).1, ?_,
    (curvedRNC_center_gauge_satisfiable κ r hr hn).2⟩
  refine ⟨fun _ => (1 : ℝ), fun _ _ => (1 : ℝ), ?_, ?_⟩
  · have hfold : foldedCoeff (n := n) (fun _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) 0
        = fun _ => (1 : ℝ) := by
      funext y
      simp [foldedCoeff, Real.one_rpow]
    rw [hfold]
    exact contDiff_const
  · intro e
    have hfold : foldedCoeff (n := n) (fun _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) 0
        = fun _ => (1 : ℝ) := by
      funext y
      simp [foldedCoeff, Real.one_rpow]
    rw [hfold]
    exact pd_const 1 e 0

end QIQTH.CurvedA1CenterCoeff
