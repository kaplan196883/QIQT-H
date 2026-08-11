/-
  CurvedA1CenterResid — J4-607: FOURTH layer of the (hbound-fat) wall — the CENTER-GAUGE variants of
  the τ-narrow residual Gaussian bounds (`uniformResidual_gaussian_bound_tau_narrow`, J4-97 M2, and
  `uniformResidualLinear_gaussian_bound_tau_narrow`, J4-108 L3a), pushing the layer-3 ε₀ floor
  through the T1 algebra, instantiated at the genuinely-curved witness `g^κ = curvedRNCMetric κ` on
  the fat base compact `K = Metric.closedBall 0 r`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes (hbound-fat) layer 5 + fat-`K` `hEmeas` + `hAdom` + `hcont` + the co-instantiated capstone
  application + the prior analytic piles / convergence trio / `hmassone` pre-ρ carriers / `hjets`.
  This brick is the FOURTH layer of the (hbound-fat) producer rework, not its closure.

  ── ★★ THE USE-SITE VERDICT (the point of this brick).  In the banked τ-narrow residual engines,
  `hframeK : ∀ q ∈ K, g q = δ` enters at **TWO INDEPENDENT SITES** — NOT only through the
  coefficient hypothesis:
    (T1)  INDIRECTLY, via `hCoeffU`/`hCoeffLin` (an explicit hypothesis; the center layer-3 shape
          adds `+C_ε·ε₀`);
    (T2)  ★ DIRECTLY, via the inner call `uniformFlowPullbackMetricInv_dev_uniform` (which TAKES
          `hframeK`), feeding the deviation `M·rncRadialSq v` of the QUADRATIC residual term
          `(1/τ²)·G·(−¼Σ dev·vᵢvⱼ)·w₀` (`residualQuadratic_pointwise_narrow`).
  The T3 Laplace–Beltrami block (`uniformFlowLaplaceBeltrami_w0_near_uniform`) never took `hframeK`.
  Substituting the center-gauge layer 1 (`uniformFlowPullbackMetricInv_dev_uniform_center`,
  J4-604) at BOTH sites, the ε₀ debt surfaces TWICE.

  ── ★★ THE HONEST ε₀/τ PLACEMENT (no suppression, no silent absorption).  The banked bounds
  genuinely DEGRADE by a `(1/τ)`-weighted 0th-order Gaussian term:
      `|R₀| ≤ (C₀ + Cεu·ε₀·(1/τ)) · gaussDdim (3/2·τ) v`                    (O(r²) engine)
      `|R₀| ≤ (C₀ + C₁·(√τ/τ) + Cεu·ε₀·(1/τ)) · gaussDdim (3/2·τ) v`       (O(r)  engine)
  with the EXACT weights
      C₀  = √(3/2)ⁿ·(12·C_c + 72·n²·M·W + L)     (O(r²); LITERALLY the banked constant at ε₀ = 0)
      C₀  = √(3/2)ⁿ·(72·n²·M·W + L),  C₁ = C_c·√(3/2)ⁿ·√6            (O(r); banked at ε₀ = 0)
      Cεu = √(3/2)ⁿ·(C_ε + 3·n²·M·W)                                 (BOTH engines — the NEW term)
  Provenance of `Cεu`: the `C_ε` share is the T1 constant coefficient (`(1/τ)·G·(C_ε·ε₀)` with
  `G ≤ √(3/2)ⁿ·G_{3/2}` — the width fold pays NO τ-power for a CONSTANT coefficient, so the raw
  `(1/τ)` weight is irreducible there); the `3·n²·M·W` share is the T2 cross term
  `(1/τ²)·ε₀·r²·G·(n²MW/4)`, where the `m = 1` absorption `r²·G ≤ √(3/2)ⁿ·12·τ·G_{3/2}` eats ONE
  power of `τ` and leaves `ε₀·(1/τ)` (weight `12/4 = 3`).  The Gaussian-absorption steps CANNOT eat
  a constant (`v`-independent) coefficient at any width price: at `v = 0` every `gaussDdim` width
  equals `1` while `(1/τ) → ∞` as `τ → 0` — so the `ε₀/τ` term is stated where the algebra puts it.
  DISCIPLINE (inherited from layers 1–3): `ρ_u`, `C₀`, `C₁`, `Cεu` are all produced BEFORE `ε₀` is
  quantified — no ε₀-inflation of the geometric/heat constants.

  ── ★ THE ε₀-vs-τ TENSION (layer 5, SCOPED here — not resolved).  In the N = 1 mixed split
  `R₁ = R₀[u] + H₀[u'] + τ·R₀[u']` (J4-103), the `τ·R₀[u']` branch through the LINEAR center engine
  is BENIGN: `τ·(Cεu·ε₀/τ) = Cεu·ε₀` — a plain additive constant, folding into `B₀` exactly like
  the banked `√τ ≤ 1+τ` fold.  The `R₀[u]` branch through the O(r²) center engine is NOT: it keeps
  the raw `Cεu·ε₀·(1/τ)`, so the honest N = 1 center output is `(B₀ + B₁·τ + Bε·ε₀·(1/τ))·G_{3/2}`,
  and any `∫₀ᵗ (1/τ) dτ`-type fold in the producer chain DIVERGES logarithmically at fixed ε₀.
  Layer 5 must therefore either (a) restrict to `τ ≥ τ₀` with an ε₀-dependent threshold (width-2
  fold can absorb `ε₀/τ ≤ ε₀/τ₀` only above it), or (b) run the ε₀ → 0 limit (shrink `r`,
  `curvedRNC_center_eps_arbitrarily_small`) BEFORE the τ-integration — the ORDER of limits is the
  layer-5 crux.  Nothing here forecloses either route; the term is left explicit so layer 5 cannot
  silently drop it.

  ── LANDED HERE:
    • `residualQuadratic_pointwise_narrow_center` — the T2 quadratic pointwise bound with the
      center deviation `M·(rncRadialSq v + ε₀)`: `≤ √(3/2)ⁿ·72·n²·M·W·G_{3/2}
      + √(3/2)ⁿ·3·n²·M·W·ε₀·(1/t)·G_{3/2}` (the `m = 2` and `m = 1` narrow absorptions).
    • `uniformResidual_gaussian_bound_tau_narrow_center` — ★ THE BRICK (O(r²) engine): `hframeK`
      deleted at BOTH sites (`hdevK` + center coeff shape), conclusion
      `(C₀ + Cεu·ε₀·(1/τ))·G_{3/2}`, constants before ε₀.
    • `uniformResidualLinear_gaussian_bound_tau_narrow_center` — ★ the O(r) companion (NO
      `hw0flat`; the shifted van-Vleck profile branch): `(C₀ + C₁·(√τ/τ) + Cεu·ε₀·(1/τ))·G_{3/2}`.
    • `curvedRNC_resid_bound_center` / `curvedRNC_residLinear_bound_center` — ★★ fat-`K` curved
      instantiations: for `κ ≤ 0` and EVERY radius `r`, on `K = closedBall 0 r`, with the explicit
      `ε₀ = (|κ|/3)·n·r²` and the coeff hypothesis DISCHARGED from layer 3
      (`curvedRNC_coeff_bound_center` / `curvedRNC_coeffLinear_bound_center`).
    • `curvedRNC_resid_center_satisfiable` — non-vacuity gate (cp466 discipline): fat `K` contains
      a NONZERO point, the heat-side antecedents are INHABITED (`Θ = 1`, `u = 1`), the `hdevK`
      antecedent HOLDS at the curved witness with the explicit ε₀, AND the coefficient-bound
      antecedent of the center engines is exhibited DISCHARGED (not merely assumed) at that data.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.CoeffU1Fix
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedA1CenterChr
import QIQTH.CurvedA1CenterCoeff
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

namespace QIQTH.CurvedA1CenterResid

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### The T2 quadratic pointwise bound with the CENTER deviation — the second ε₀ site. -/

/-- **J4-607 — THE T2 QUADRATIC POINTWISE BOUND, CENTER DEVIATION.**  The exact analogue of
    `residualQuadratic_pointwise_narrow` (M2) with the deviation hypothesis degraded to the
    layer-1 center shape `|g̃⁻¹ᵢⱼ − δᵢⱼ| ≤ M·(rncRadialSq v + ε₀)`.  The `r⁴` share pays the banked
    `m = 2` narrow absorption (`288/4 = 72`, τ-free); the NEW `ε₀·r²` cross share pays the `m = 1`
    absorption `r²·G ≤ √(3/2)ⁿ·12·t·G_{3/2}`, which eats only ONE of the two `(1/t)` powers —
    leaving the honest `(1/t)`-weighted term with weight `12/4 = 3`.  NOT `a₁ = R/6`. -/
theorem residualQuadratic_pointwise_narrow_center (gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) {t : ℝ} (ht : 0 < t)
    (M W ε₀ : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W) (hε₀ : 0 ≤ ε₀) (v : Point n)
    (hdev_v : ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)|
      ≤ M * (rncRadialSq v + ε₀))
    (hw_v : |foldedCoeff Θ u 0 v| ≤ W) :
    |(1 / t ^ 2) * gaussDdim t v
        * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
        * foldedCoeff Θ u 0 v|
      ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * gaussDdim (3 / 2 * t) v
        + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / t)
            * gaussDdim (3 / 2 * t) v := by
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
  set Gn : ℝ := gaussDdim (3 / 2 * t) v with hGndef
  have hGn0 : 0 ≤ Gn := gaussDdim_nonneg _ v
  have habs2 : |(1 / t ^ 2) * gaussDdim t v * ((-1 / 4) * S) * w|
      = (1 / t ^ 2) * gaussDdim t v * (1 / 4) * |S| * |w| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 / t ^ 2 by positivity),
        abs_of_nonneg hG, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
    ring
  have hr4G : r2 ^ 2 * gaussDdim t v
      ≤ Real.sqrt (3 / 2) ^ n * 288 * t ^ 2 * Gn := by
    rw [hGndef, hr2def]; exact rncRadialSq_sq_mul_gaussDdim_le_narrow ht v
  have hr2G : r2 * gaussDdim t v ≤ Real.sqrt (3 / 2) ^ n * 12 * t * Gn := by
    rw [hGndef, hr2def]; exact rncRadialSq_mul_gaussDdim_le_narrow ht v
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
          * (Real.sqrt (3 / 2) ^ n * 288 * t ^ 2 * Gn)
          + (n : ℝ) ^ 2 * M * W / 4 * ε₀ * (1 / t ^ 2)
              * (Real.sqrt (3 / 2) ^ n * 12 * t * Gn) :=
        add_le_add (mul_le_mul_of_nonneg_left hr4G hK4)
          (mul_le_mul_of_nonneg_left hr2G hK1)
    _ = Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
          + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / t) * Gn := by
        field_simp
        ring

/-! ### ★ THE BRICK — center-gauge O(r²) τ-narrow residual engine: honest `+Cεu·ε₀·(1/τ)`. -/

/-- **★★ J4-607 — CENTER-GAUGE τ-NARROW N = 0 RESIDUAL BOUND (O(r²) coefficient + ε₀ floor).**
    The banked `uniformResidual_gaussian_bound_tau_narrow` (M2) with `hframeK` deleted at BOTH of
    its use sites: (T1) the coefficient hypothesis takes the layer-3 center shape
    `≤ C_c·rncRadialSq v + C_ε·ε₀`, and (T2) the quadratic deviation is supplied by the layer-1
    center lemma (`hdevK` antecedent) instead of the `hframeK`-consuming banked one.  The HONEST
    degraded conclusion is
        `|R₀| ≤ (C₀ + Cεu·ε₀·(1/τ)) · gaussDdim (3/2·τ) v`,   ∀ τ > 0,
    with `C₀ = √(3/2)ⁿ·(12·C_c + 72·n²·M·W + L)` (LITERALLY the banked constant at ε₀ = 0) and
    `Cεu = √(3/2)ⁿ·(C_ε + 3·n²·M·W)` — the `C_ε` share from T1 (a CONSTANT coefficient pays the
    raw `(1/τ)`; no width fold can eat it), the `3n²MW` share from T2's `ε₀·r²` cross term (the
    `m = 1` absorption eats one of the two `(1/τ)` powers).  `ρ_u`, `C₀`, `Cεu` are produced
    BEFORE ε₀ — no ε₀-inflation.  NOT `a₁ = R/6`. -/
theorem uniformResidual_gaussian_bound_tau_narrow_center (g gi : Point n → Fin n → Fin n → ℝ)
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
          ≤ (C₀ + Cεu * ε₀ * (1 / τ)) * gaussDdim (3 / 2 * τ) v := by
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
  refine ⟨ρ_u, hρ_u0, Real.sqrt (3 / 2) ^ n * (12 * C_c + 72 * (n : ℝ) ^ 2 * M * W + L),
    Real.sqrt (3 / 2) ^ n * (C_ε + 3 * (n : ℝ) ^ 2 * M * W),
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
  set Gn : ℝ := gaussDdim (3 / 2 * τ) v with hGndef
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
  -- (T1) — the coefficient site: `C_c·r²` pays the banked `m = 1` absorption (τ-free), the NEW
  -- `C_ε·ε₀` constant coefficient keeps the raw `(1/τ)` (no width fold can eat it).
  have hT1bd : |T1| ≤ Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn
      + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hGle : gaussDdim τ v ≤ Real.sqrt (3 / 2) ^ n * Gn := by
      rw [hGndef]; exact gaussDdim_le_gaussDdim_narrow hτ v
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadialSq v + C_ε * ε₀) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadialSq v * gaussDdim τ v)
            + C_ε * ε₀ * (1 / τ) * gaussDdim τ v := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt (3 / 2) ^ n * 12 * τ * Gn)
            + C_ε * ε₀ * (1 / τ) * (Real.sqrt (3 / 2) ^ n * Gn) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (by rw [hGndef]; exact rncRadialSq_mul_gaussDdim_le_narrow hτ v)
              (by positivity))
            (mul_le_mul_of_nonneg_left hGle (by positivity))
      _ = Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn
            + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
          field_simp
  -- (T2) — the DIRECT `hframeK` site, replaced by the layer-1 center deviation: the second ε₀
  -- share, `3·n²·M·W·ε₀·(1/τ)`.
  have hT2bd : |T2| ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
      + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_narrow_center
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W ε₀ hM0 hW0 hε₀ v
      (hdevU ε₀ hε₀ hdevK q hq v hvM) (hWbd v hvball)
  -- (T3) — frame-free, exactly as banked.
  have hT3bd : |T3| ≤ Real.sqrt (3 / 2) ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt (3 / 2) ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_narrow hτ v) hL0
      _ = Real.sqrt (3 / 2) ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ (Real.sqrt (3 / 2) ^ n * 12 * C_c * Gn
          + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn)
          + (Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
            + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn)
          + Real.sqrt (3 / 2) ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (Real.sqrt (3 / 2) ^ n * (12 * C_c + 72 * (n : ℝ) ^ 2 * M * W + L)
          + Real.sqrt (3 / 2) ^ n * (C_ε + 3 * (n : ℝ) ^ 2 * M * W) * ε₀ * (1 / τ)) * Gn := by
        ring

/-! ### The O(r) companion — NO `hw0flat` (the shifted van-Vleck profile branch). -/

/-- **★ J4-607 — CENTER-GAUGE τ-NARROW N = 0 RESIDUAL BOUND (O(r) coefficient + ε₀ floor).**  The
    banked `uniformResidualLinear_gaussian_bound_tau_narrow` (L3a) with `hframeK` deleted at BOTH
    sites (`hdevK` + linear center coeff shape `≤ C_c·rncRadial v + C_ε·ε₀`):
        `|R₀| ≤ (C₀ + C₁·(√τ/τ) + Cεu·ε₀·(1/τ)) · gaussDdim (3/2·τ) v`,   ∀ τ > 0,
    `C₀ = √(3/2)ⁿ·(72n²MW + L)`, `C₁ = C_c·√(3/2)ⁿ·√6` (both LITERALLY banked at ε₀ = 0),
    `Cεu = √(3/2)ⁿ·(C_ε + 3n²MW)` — same ε₀ weight as the O(r²) engine (the T1 constant share and
    the T2 cross share are coefficient-shape-independent).  This is the branch the shifted
    van-Vleck profile `u₁` consumes; in the N = 1 split its output is multiplied by τ, so the
    `Cεu·ε₀·(1/τ)` term folds to the BENIGN additive constant `Cεu·ε₀` there — the raw `(1/τ)`
    survives only through the `R₀[u]` (O(r²)) branch.  NOT `a₁ = R/6`. -/
theorem uniformResidualLinear_gaussian_bound_tau_narrow_center
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
              * gaussDdim (3 / 2 * τ) v := by
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
  refine ⟨ρ_u, hρ_u0, Real.sqrt (3 / 2) ^ n * (72 * (n : ℝ) ^ 2 * M * W + L),
    C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6),
    Real.sqrt (3 / 2) ^ n * (C_ε + 3 * (n : ℝ) ^ 2 * M * W),
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
  set Gn : ℝ := gaussDdim (3 / 2 * τ) v with hGndef
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
  -- (T1) — `C_c·r` pays the odd-power `√τ` absorption (L1); the NEW `C_ε·ε₀` constant keeps `1/τ`.
  have hT1bd : |T1| ≤ (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn
      + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)]
    have hdivmul : (1 / τ) * Real.sqrt τ = Real.sqrt τ / τ := by rw [one_div, inv_mul_eq_div]
    have hGle : gaussDdim τ v ≤ Real.sqrt (3 / 2) ^ n * Gn := by
      rw [hGndef]; exact gaussDdim_le_gaussDdim_narrow hτ v
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadial v + C_ε * ε₀) :=
          mul_le_mul_of_nonneg_left (hCoeffLin q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGτ0)
      _ = C_c * (1 / τ) * (rncRadial v * gaussDdim τ v)
            + C_ε * ε₀ * (1 / τ) * gaussDdim τ v := by ring
      _ ≤ C_c * (1 / τ) * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6 * Real.sqrt τ * Gn)
            + C_ε * ε₀ * (1 / τ) * (Real.sqrt (3 / 2) ^ n * Gn) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (by rw [hGndef]; exact rncRadial_mul_gaussDdim_le_narrow hτ v)
              (by positivity))
            (mul_le_mul_of_nonneg_left hGle (by positivity))
      _ = (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * ((1 / τ) * Real.sqrt τ) * Gn
            + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn := by ring
      _ = (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn
            + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn := by rw [hdivmul]
  -- (T2) — the DIRECT `hframeK` site, center-replaced (second ε₀ share).
  have hT2bd : |T2| ≤ Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
      + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn := by
    rw [hT2def, hGndef]
    exact residualQuadratic_pointwise_narrow_center
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W ε₀ hM0 hW0 hε₀ v
      (hdevU ε₀ hε₀ hdevK q hq v hvM) (hWbd v hvball)
  -- (T3) — frame-free, exactly as banked.
  have hT3bd : |T3| ≤ Real.sqrt (3 / 2) ^ n * L * Gn := by
    rw [hT3def, abs_mul, abs_of_nonneg hGτ0]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGτ0
      _ ≤ (Real.sqrt (3 / 2) ^ n * Gn) * L := by
          rw [hGndef]
          exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdim_narrow hτ v) hL0
      _ = Real.sqrt (3 / 2) ^ n * L * Gn := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ ((C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ) * Gn
          + Real.sqrt (3 / 2) ^ n * C_ε * ε₀ * (1 / τ) * Gn)
          + (Real.sqrt (3 / 2) ^ n * 72 * (n : ℝ) ^ 2 * M * W * Gn
            + Real.sqrt (3 / 2) ^ n * 3 * (n : ℝ) ^ 2 * M * W * ε₀ * (1 / τ) * Gn)
          + Real.sqrt (3 / 2) ^ n * L * Gn :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (Real.sqrt (3 / 2) ^ n * (72 * (n : ℝ) ^ 2 * M * W + L)
          + (C_c * (Real.sqrt (3 / 2) ^ n * Real.sqrt 6)) * (Real.sqrt τ / τ)
          + Real.sqrt (3 / 2) ^ n * (C_ε + 3 * (n : ℝ) ^ 2 * M * W) * ε₀ * (1 / τ)) * Gn := by
        ring

/-! ### The fat-`K` curved instantiations — all geometric carries discharged, explicit `ε₀`. -/

/-- **★★ THE CENTER-GAUGE τ-NARROW RESIDUAL BOUND AT THE FAT BASE COMPACT for the curved witness
    (O(r²) engine).**  For `κ ≤ 0` and EVERY radius `r`, on `K = Metric.closedBall 0 r`:
    `∃ ρ_u > 0, ∃ C₀ ≥ 0, ∃ Cεu ≥ 0, ∀ τ > 0, ∀ q ∈ K, ∀ ‖v‖ < ρ_u,
        |R₀(τ,v)| ≤ (C₀ + Cεu·((|κ|/3)·n·r²)·(1/τ))·gaussDdim (3/2·τ) v`
    — every geometric carry discharged from banked curved lemmas, the `hdevK` antecedent from
    `curvedRNC_frame_dev_on_ball`, and the coefficient antecedent DISCHARGED from layer 3
    (`curvedRNC_coeff_bound_center`).  The `ε₀/τ` term is REAL; its smallness at fixed τ comes
    only from shrinking `r` (`curvedRNC_center_eps_arbitrarily_small`) — the τ → 0 behaviour at
    fixed `r` is the layer-5 tension, NOT resolved here.  NOT `a₁ = R/6`. -/
theorem curvedRNC_resid_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
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
              * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hcoeff⟩ :=
    curvedRNC_coeff_bound_center κ r hκ Θ u hw0smooth hw0flat
  obtain ⟨ρ_u, hρ_u0, C₀, Cεu, hC₀0, hCεu0, hmain⟩ :=
    uniformResidual_gaussian_bound_tau_narrow_center (curvedRNCMetric κ) (curvedRNCInv κ)
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

/-- **★★ The fat-`K` curved instantiation of the O(r) engine** (no `hw0flat` — the shifted
    van-Vleck profile branch).  Same carries, same explicit `ε₀ = (|κ|/3)·n·r²`; the coefficient
    antecedent discharged from `curvedRNC_coeffLinear_bound_center`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_residLinear_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
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
              * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ_c, hρ_c0, C_c, hC_c0, C_ε, hC_ε0, hcoeff⟩ :=
    curvedRNC_coeffLinear_bound_center κ r hκ Θ u hw0smooth
  obtain ⟨ρ_u, hρ_u0, C₀, C₁, Cεu, hC₀0, hC₁0, hCεu0, hmain⟩ :=
    uniformResidualLinear_gaussian_bound_tau_narrow_center (curvedRNCMetric κ) (curvedRNCInv κ)
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

/-- **Non-vacuity of the center-gauge τ-narrow residual bounds at fat `K`.**  At every `r > 0`,
    `κ ≤ 0`, `n ≥ 1`: (i) the base compact `closedBall 0 r` contains a NONZERO point (no
    `K ⊆ {0}` collapse — contrast `rebased_hframeK_unsat`, J4-603); (ii) the heat-side antecedents
    are INHABITED (`Θ = 1`, `u = 1`: `foldedCoeff = 1`, smooth AND center-flat) AND at that
    witness the COEFFICIENT-BOUND antecedent of the center engines is exhibited DISCHARGED (via
    layer 3's `curvedRNC_coeff_bound_center` — not merely assumed); (iii) the `hdevK` antecedent
    HOLDS at the curved witness with the explicit `ε₀ = (|κ|/3)·n·r²`.  So EVERY antecedent of
    `uniformResidual_gaussian_bound_tau_narrow_center` (and its Linear companion, whose
    antecedents are a subset) is exhibited satisfiable at the fat curved base compact — the
    conclusions are not vacuously quantified.  NOT `a₁ = R/6`. -/
theorem curvedRNC_resid_center_satisfiable (κ r : ℝ) (hκ : κ ≤ 0) (hr : 0 < r) (hn : 1 ≤ n) :
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

end QIQTH.CurvedA1CenterResid
