/-
  CurvedA1CenterN1 — J4-608: FIFTH-layer FIRST INCREMENT of the (hbound-fat) wall — the CENTER-GAUGE
  `N = 1` mixed residual engine (the honest `(B₀ + B₁·τ + (Bc + Bδ/τ)·ε₀)·G_{3/2}` shape), its fat-`K`
  curved instantiation, and the ORDER-OF-LIMITS ROUTE DECISION for the ε₀/τ crux — settled by proof
  and by two formal no-majorant gates, adversarially confirmed by external review (Sol, 2026-08-11).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes the REST of layer 5 (the producer re-assembly toward (hbound-fat)) + fat-`K` `hEmeas` +
  `hAdom` + `hcont` + the co-instantiated capstone application + the prior analytic piles /
  convergence trio / `hmassone` pre-ρ carriers / `hjets`.

  ── ★★★ THE ROUTE DECISION (the layer-5 crux of J4-607, RESOLVED here — route (c)).
  The J4-607 scoping left two candidate routes for the `Bδ·ε₀·(1/τ)` term of the N = 1 center shape:
  (a) an ε₀-dependent τ-threshold `τ ≥ τ₀(ε₀)` consumed through the interior `hContDom` window, or
  (b) the ε₀ → 0 (shrink `r`) limit BEFORE τ-integration.  VERDICT: **BOTH FAIL; the crux does not
  dissolve by an order of limits.  The genuine resolution is (c): eliminate the ε₀ floor at leading
  order by a PER-`q` re-basing of the principal Gaussian (frozen-metric Gaussian at the pole /
  vielbein normalization) — the standard Levi frozen-coefficient structure.**  In detail:
    (a) FAILS: the interior window of the J4-596 builder (`s₀ ∈ Ioo 0 u`, window inf ≥ s₀/2 > 0)
        restricts only the OUTER Duhamel variable.  The `hBdom` consumer
        (`leviSeries_dominatedW_le`) bounds `leviSeries` at `s` through `iterE`, whose time
        convolutions (`heatConvK`; `IterConvIntegrableW` is quantified over ALL `s ∈ (0,t)`)
        integrate the defect over simplices whose INDIVIDUAL increments reach down to 0 even when
        their sum is interior.  A `τ ≥ τ₀`-restricted defect bound therefore CANNOT feed the
        existing Volterra chain at any positive τ₀.
    (b) FAILS: for ANY fixed `r > 0` (i.e. any fixed `ε₀ = (|κ|/3)·n·r² > 0`),
        `sup_{τ∈(0,T]} ε₀/τ = ∞` AND `∫₀^T ε₀/τ dτ = ∞`; shrinking `r` shrinks the coefficient but
        never restores τ-uniformity at a fixed fat base.  The limit is SINGULAR: `ε₀ = 0` first
        changes the problem (collapses `K` to `{0}` — the J4-603 vacuity).  Formal gates below:
        `centerShape_no_uniform_majorant` (the shape cannot fill the α = 0 slot) and
        `centerShape_no_width2_kernel_majorant` (nor after multiplying by the width-3/2 Gaussian
        against the width-2 target: at `v = 0` ALL widths share the same `τ^{-n/2}` diagonal
        scaling — `gaussDdim_zero` — so no width absorption exists at any constant price).
    (c) THE FORWARD ROUTE (layer 6+, NOT built here): per-`q` frozen-metric Gaussian
        `Γ_q(τ,v) = (4πτ)^{-n/2}(det g(q))^{-1/2}·exp(−g(q)⁻¹v·v/4τ)` (or per-`q` normal
        coordinates / geodesic phase).  A per-`q` LINEAR normalization kills the order-0 symbol
        mismatch (the ε₀ floor) and leaves an `O(|v|)` deviation → defect `~ τ^{-1/2}·G` — the
        classical Levi singularity, INTEGRABLE (the α-generic `baseKernelW`/`modelCoeff` machinery
        tolerates α = −1/2; α = −1 is the borderline non-integrable case we are stuck at now).
        Full α = 0 τ-uniformity (the literal (hbound-fat) shape) additionally needs per-`q`
        first-jet cancellation (q-normal coordinates / geodesic phase + van Vleck transport); the
        alternative is to α-generalize the D2 consumer to −1/2.  ⚠ Honesty note: the no-majorant
        gates below are about the DERIVED BOUND SHAPE, not about the defect kernel `E` itself; the
        external review confirms the `ε₀/τ` term is also GENUINELY present in the defect of the
        center-frozen flat Gaussian at `q ≠ 0` (diagonal witness `tr(g⁻¹(q)) − n ≠ 0` at parabolic
        scale for the space form), but THAT lower-bound statement is not formalized here.

  ── LANDED HERE (all std-3, no sorry):
    • `uniformResidualN1_narrow_mixed_lin_center` — ★★ THE BRICK: the N = 1 mixed residual engine
      in center gauge (`hframeK` deleted; layer-4 center engines at both branches of the J4-103
      split `R₁ = R₀[u] + H₀[u′] + τ·R₀[u′]`).  Honest conclusion
          `|R₁| ≤ (B₀ + B₁·τ + (Bc + Bδ·(1/τ))·ε₀) · gaussDdim (3/2·τ) v`,   ∀ τ > 0,
      with `B₀ = Cu + W₁·√(3/2)ⁿ + Cs₁`, `B₁ = Cs₀ + Cs₁` (LITERALLY the banked N = 1 constants at
      ε₀ = 0), `Bc = Cεs` (the BENIGN fold `τ·(Cεs·ε₀/τ) = Cεs·ε₀` of the linear branch — kept as
      an EXPLICIT ε₀-term, NOT hidden inside B₀: constants-before-ε₀ discipline), `Bδ = Cεu` (the
      raw `1/τ` surviving through the `R₀[u]` branch ONLY).  Nothing dropped, nothing absorbed.
    • `curvedRNC_residN1_bound_center` — ★★ fat-`K` curved instantiation (`κ ≤ 0`, EVERY `r`, on
      `K = closedBall 0 r`, explicit `ε₀ = (|κ|/3)·n·r²`), BOTH coefficient antecedents DISCHARGED
      from layer 3 (`curvedRNC_coeff_bound_center` at `u`; `curvedRNC_coeffLinear_bound_center` at
      the shifted profile `u′`).
    • `curvedRNC_residN1_bound_center_thresholded` — the route-(a) artifact, stated TRANSPARENTLY:
      on `τ ∈ [τ₀,∞)` the clean mixed shape `((B₀ + (Bc + Bδ/τ₀)·ε₀) + B₁·τ)·G_{3/2}` holds — with
      the FULL constant `B₀ + Bc·ε₀ + Bδ·ε₀/τ₀` exposed (no silent re-baptism of `B₀`).  ⚠ This
      does NOT feed the D2 Volterra engine (see the route decision: the engine needs (0,T]); it is
      recorded as the honest content of route (a), not as a discharge of (hbound-fat).
    • `centerShape_no_uniform_majorant` / `centerShape_no_width2_kernel_majorant` — ★ the formal
      route-decision gates: the `Bδ·ε₀·(1/τ)` SHAPE admits NO τ-uniform majorant on (0,T] (for any
      ε₀ > 0), scalar-level AND against the width-2 kernel target of (hbound-fat).
    • `curvedRNC_residN1_center_satisfiable` — non-vacuity gate (cp466 discipline): fat `K` has a
      nonzero point; the heat-side antecedents are INHABITED (`Θ = 1`, `u ≡ 1`: ALL-`k` smoothness
      + center-flatness) AND both coefficient-bound antecedents are exhibited DISCHARGED at that
      data; the `hdevK` antecedent HOLDS at the curved witness with the explicit ε₀.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.CoeffU1Fix
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedA1CenterChr
import QIQTH.CurvedA1CenterCoeff
import QIQTH.CurvedA1CenterResid
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.CConvV2GaussianPairing
import QIQTH.OuterCarryRecon

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.OuterCarryRecon
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterChr QIQTH.CurvedA1CenterCoeff
open QIQTH.CurvedA1CenterResid QIQTH.CConvV2GaussianPairing
open QIQTH.HeatResidualBound
open Set Filter
open scoped Topology BigOperators ContDiff

namespace QIQTH.CurvedA1CenterN1

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### ★★ THE BRICK — the center-gauge N = 1 mixed residual engine (honest 4-constant shape). -/

/-- **★★ J4-608 — THE CENTER-GAUGE `N = 1` MIXED RESIDUAL BOUND.**  The exact analogue of
    `uniformResidualN1_narrow_mixed_lin` (J4-108 L3) with `hframeK` DELETED: the J4-103 split
    `R₁ = R₀[u] + H₀[u′] + τ·R₀[u′]` fed by the layer-4 CENTER engines (`hdevK` + center
    coefficient shapes at BOTH profiles).  The honest degraded conclusion is
        `|R₁| ≤ (B₀ + B₁·τ + (Bc + Bδ·(1/τ))·ε₀) · gaussDdim (3/2·τ) v`,   ∀ τ > 0:
    the `R₀[u]` branch (O(r²) center engine) contributes the RAW `Bδ·ε₀·(1/τ)` (`Bδ = Cεu`); the
    `τ·R₀[u′]` branch through the linear center engine is benign — `τ·(Cεs·ε₀·(1/τ)) = Cεs·ε₀`
    folds to the τ-FREE ε₀-term `Bc·ε₀` (kept explicit, NOT hidden inside `B₀`), and its `√τ` tail
    folds by `√τ ≤ 1+τ` exactly as banked.  All four constants are produced BEFORE `ε₀` is
    quantified — no ε₀-inflation of the geometric/heat constants.  At `ε₀ = 0` the conclusion is
    LITERALLY the banked `(B₀ + B₁·τ)·G` mixed shape.  ⚠ The `Bδ·ε₀·(1/τ)` term is genuinely fatal
    for the α = 0 Volterra consumer at fixed `ε₀ > 0` (see the header route decision and the
    no-majorant gates below) — it is stated where the algebra puts it so layer 6 cannot silently
    drop it.  NOT `a₁ = R/6`. -/
theorem uniformResidualN1_narrow_mixed_lin_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 C_ε0 C_ε1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hC_ε00 : 0 ≤ C_ε0) (hC_ε10 : 0 ≤ C_ε1) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ Bc Bδ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ Bc ∧ 0 ≤ Bδ ∧
      ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
          ≤ C_c0 * rncRadialSq v + C_ε0 * ε₀) →
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
        |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
          ≤ C_c1 * rncRadial v + C_ε1 * ε₀) →
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (B₀ + B₁ * τ + (Bc + Bδ * (1 / τ)) * ε₀) * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ₀, hρ₀0, Cu, Cεu, hCu0, hCεu0, hbnd0⟩ :=
    uniformResidual_gaussian_bound_tau_narrow_center g gi hg hC hK hgnd hgsymm hinvF
      Θ u (hw 0) ρ_c C_c0 C_ε0 hρ_c hC_c0 hC_ε00
  obtain ⟨ρ₁, hρ₁0, Cs₀, Cs₁, Cεs, hCs00, hCs10, hCεs0, hbnd1⟩ :=
    uniformResidualLinear_gaussian_bound_tau_narrow_center g gi hg hC hK hgnd hgsymm hinvF
      Θ (fun j => u (j + 1)) (hw 1) ρ_c C_c1 C_ε1 hρ_c hC_c1 hC_ε10
  set ρ_u : ℝ := min ρ₀ ρ₁ with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hρ₀0 hρ₁0
  obtain ⟨W₁, hW₁0, hW₁bd⟩ : ∃ W₁ : ℝ, 0 ≤ W₁ ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 1 v| ≤ W₁ := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, Cu + W₁ * Real.sqrt (3 / 2) ^ n + Cs₁, Cs₀ + Cs₁, Cεs, Cεu,
    by positivity, by positivity, hCεs0, hCεu0, ?_⟩
  intro ε₀ hε₀ hdevK hU0 hL1 τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hv0 : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_right _ _)
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  rw [parametrixResidual_one_split (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw]
  set G : ℝ := gaussDdim (3 / 2 * τ) v with hGdef
  have hG0 : 0 ≤ G := gaussDdim_nonneg _ v
  set R0 : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v with hR0def
  set Mid : ℝ := heatParametrix 0 Θ (fun j => u (j + 1)) τ v with hMiddef
  set R0' : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) τ v with hR0'def
  have hb0 : |R0| ≤ (Cu + Cεu * ε₀ * (1 / τ)) * G :=
    hbnd0 ε₀ hε₀ hdevK hU0 τ hτ q hq v hv0
  have hb1 : |R0'| ≤ (Cs₀ + Cs₁ * (Real.sqrt τ / τ) + Cεs * ε₀ * (1 / τ)) * G :=
    hbnd1 ε₀ hε₀ hdevK hL1 τ hτ q hq v hv1
  have hmid : |Mid| ≤ (W₁ * Real.sqrt (3 / 2) ^ n) * G := by
    have hfold : Mid = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
      rw [hMiddef, heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
    rw [hfold, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    have hv' : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W₁ := hW₁bd v hvball
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W₁ := mul_le_mul_of_nonneg_left hv' (gaussDdim_nonneg τ v)
      _ = W₁ * gaussDdim τ v := by ring
      _ ≤ W₁ * (Real.sqrt (3 / 2) ^ n * G) := by
          rw [hGdef]; exact mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow hτ v) hW₁0
      _ = (W₁ * Real.sqrt (3 / 2) ^ n) * G := by ring
  -- `τ·R₀[u′]` branch: the `√τ` tail folds by `√τ ≤ 1+τ`; the ε₀ tail folds BENIGNLY,
  -- `τ·(Cεs·ε₀·(1/τ)) = Cεs·ε₀` — the τ-free ε₀ constant (kept explicit as `Bc·ε₀`).
  have hττ : τ * (Real.sqrt τ / τ) = Real.sqrt τ := by field_simp
  have hτε : τ * (Cεs * ε₀ * (1 / τ)) = Cεs * ε₀ := by field_simp
  have hsqle : Real.sqrt τ ≤ 1 + τ := by
    rw [show (1 : ℝ) + τ = Real.sqrt ((1 + τ) ^ 2) from (Real.sqrt_sq (by linarith [hτ.le])).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hτ.le])
  have hb1τ : τ * |R0'| ≤ (Cs₀ * τ + Cs₁ * (1 + τ) + Cεs * ε₀) * G := by
    calc τ * |R0'|
        ≤ τ * ((Cs₀ + Cs₁ * (Real.sqrt τ / τ) + Cεs * ε₀ * (1 / τ)) * G) :=
          mul_le_mul_of_nonneg_left hb1 hτ.le
      _ = (Cs₀ * τ + Cs₁ * (τ * (Real.sqrt τ / τ)) + τ * (Cεs * ε₀ * (1 / τ))) * G := by ring
      _ = (Cs₀ * τ + Cs₁ * Real.sqrt τ + Cεs * ε₀) * G := by rw [hττ, hτε]
      _ ≤ (Cs₀ * τ + Cs₁ * (1 + τ) + Cεs * ε₀) * G := by
          apply mul_le_mul_of_nonneg_right _ hG0
          have := mul_le_mul_of_nonneg_left hsqle hCs10
          linarith
  calc |R0 + Mid + τ * R0'|
      ≤ |R0 + Mid| + |τ * R0'| := abs_add_le _ _
    _ ≤ (|R0| + |Mid|) + |τ * R0'| := add_le_add (abs_add_le _ _) le_rfl
    _ = (|R0| + |Mid|) + τ * |R0'| := by rw [abs_mul, abs_of_pos hτ]
    _ ≤ ((Cu + Cεu * ε₀ * (1 / τ)) * G + (W₁ * Real.sqrt (3 / 2) ^ n) * G)
          + (Cs₀ * τ + Cs₁ * (1 + τ) + Cεs * ε₀) * G :=
        add_le_add (add_le_add hb0 hmid) hb1τ
    _ = ((Cu + W₁ * Real.sqrt (3 / 2) ^ n + Cs₁) + (Cs₀ + Cs₁) * τ
          + (Cεs + Cεu * (1 / τ)) * ε₀) * G := by ring

/-! ### The fat-`K` curved instantiation — both coefficient antecedents discharged from layer 3. -/

/-- **★★ J4-608 — THE CENTER-GAUGE `N = 1` MIXED RESIDUAL BOUND AT THE FAT BASE COMPACT.**  For
    `κ ≤ 0` and EVERY radius `r`, on `K = Metric.closedBall 0 r`, with the explicit
    `ε₀ = (|κ|/3)·n·r²`:
        `|R₁(τ,v)| ≤ (B₀ + B₁·τ + (Bc + Bδ·(1/τ))·ε₀)·gaussDdim (3/2·τ) v`,   ∀ τ > 0 —
    every geometric carry discharged from banked curved lemmas, the `hdevK` antecedent from
    `curvedRNC_frame_dev_on_ball`, and BOTH coefficient antecedents DISCHARGED from layer 3:
    `curvedRNC_coeff_bound_center` at the profile `u` (O(r²) + ε₀) and
    `curvedRNC_coeffLinear_bound_center` at the SHIFTED profile `u′ = (fun j => u (j+1))`
    (O(r) + ε₀; smoothness of `foldedCoeff Θ u′ 0` is `hw 1` via the definitional
    `foldedCoeff_shift`).  The `Bδ·ε₀·(1/τ)` term is REAL and, at fixed `r`, NOT τ-uniformly
    majorizable (gates below) — the (hbound-fat) producer must go through the per-`q` re-based
    Gaussian (route (c)), not through this engine as-is.  NOT `a₁ = R/6`. -/
theorem curvedRNC_residN1_bound_center (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ Bc Bδ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ Bc ∧ 0 ≤ Bδ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1
            (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
            (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u τ v|
          ≤ (B₀ + B₁ * τ + (Bc + Bδ * (1 / τ)) * (|κ| / 3 * ((n : ℝ) * r ^ 2)))
              * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ₀c, hρ₀c0, Cc0, hCc00, Cε0, hCε00, hU0⟩ :=
    curvedRNC_coeff_bound_center κ r hκ Θ u (hw 0) hw0flat
  obtain ⟨ρ₁c, hρ₁c0, Cc1, hCc10, Cε1, hCε10, hL1⟩ :=
    curvedRNC_coeffLinear_bound_center κ r hκ Θ (fun j => u (j + 1)) (hw 1)
  obtain ⟨ρ_u, hρ_u0, B₀, B₁, Bc, Bδ, hB₀, hB₁, hBc, hBδ, hmain⟩ :=
    uniformResidualN1_narrow_mixed_lin_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
      Θ u hw (min ρ₀c ρ₁c) Cc0 Cc1 Cε0 Cε1 (lt_min hρ₀c0 hρ₁c0) hCc00 hCc10 hCε00 hCε10
  exact ⟨ρ_u, hρ_u0, B₀, B₁, Bc, Bδ, hB₀, hB₁, hBc, hBδ,
    fun τ hτ q hq v hv =>
      hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity)
        (curvedRNC_frame_dev_on_ball κ r)
        (fun q' hq' v' hv' => hU0 q' hq' v' (lt_of_lt_of_le hv' (min_le_left _ _)))
        (fun q' hq' v' hv' => hL1 q' hq' v' (lt_of_lt_of_le hv' (min_le_right _ _)))
        τ hτ q hq v hv⟩

/-! ### The route-(a) artifact — the τ-thresholded clean mixed shape, stated transparently. -/

/-- **★ J4-608 — the τ-THRESHOLDED clean mixed shape (route (a), honest content).**  On the
    restricted range `τ₀ ≤ τ`, the fat-`K` N = 1 center bound becomes the CLEAN mixed shape
        `|R₁| ≤ ((B₀ + (Bc + Bδ·(1/τ₀))·ε₀) + B₁·τ)·G_{3/2}` ,
    with the FULL threshold constant `B₀ + Bc·ε₀ + Bδ·ε₀/τ₀` exposed (nothing silently re-folded).
    ⚠ HONESTY (the route decision): this does **NOT** feed the D2 Volterra engine
    (`leviSeries_dominatedW_le` and `IterConvIntegrableW` require the bound on ALL of `(0,T]`; the
    `iterE` time-convolutions integrate down to 0 even at interior evaluation times, so the J4-596
    interior window does not rescue a thresholded bound), and its constant blows up as `τ₀ → 0`.
    It is the honest content of route (a), recorded so layer 6 can see exactly what a threshold
    buys — and what it cannot.  NOT `a₁ = R/6`. -/
theorem curvedRNC_residN1_bound_center_thresholded (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ Bc Bδ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ Bc ∧ 0 ≤ Bδ ∧
      ∀ (τ₀ : ℝ), 0 < τ₀ → ∀ (τ : ℝ), τ₀ ≤ τ →
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1
            (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
            (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u τ v|
          ≤ ((B₀ + (Bc + Bδ * (1 / τ₀)) * (|κ| / 3 * ((n : ℝ) * r ^ 2))) + B₁ * τ)
              * gaussDdim (3 / 2 * τ) v := by
  obtain ⟨ρ_u, hρ_u0, B₀, B₁, Bc, Bδ, hB₀, hB₁, hBc, hBδ, hmain⟩ :=
    curvedRNC_residN1_bound_center κ r hκ Θ u hw hw0flat
  refine ⟨ρ_u, hρ_u0, B₀, B₁, Bc, Bδ, hB₀, hB₁, hBc, hBδ, ?_⟩
  intro τ₀ hτ₀ τ hττ₀ q hq v hv
  have hτ : 0 < τ := lt_of_lt_of_le hτ₀ hττ₀
  refine (hmain τ hτ q hq v hv).trans
    (mul_le_mul_of_nonneg_right ?_ (gaussDdim_nonneg _ v))
  have hinv : 1 / τ ≤ 1 / τ₀ := one_div_le_one_div_of_le hτ₀ hττ₀
  have hε : (0 : ℝ) ≤ |κ| / 3 * ((n : ℝ) * r ^ 2) := by positivity
  have h2 : Bδ * (1 / τ) ≤ Bδ * (1 / τ₀) := mul_le_mul_of_nonneg_left hinv hBδ
  nlinarith [mul_le_mul_of_nonneg_right h2 hε]

/-! ### ★ The route-decision gates — the `ε₀/τ` shape has NO τ-uniform majorant on `(0,T]`. -/

/-- **★ J4-608 (ROUTE GATE, scalar level) — `centerShape_no_uniform_majorant`.**  For ANY `ε₀ > 0`
    (i.e. any fixed fat radius `r > 0` at `κ ≠ 0`), the `Bδ·ε₀·(1/τ)` term of the N = 1 center
    shape admits NO uniform majorant on `(0,T]`: route (b) — shrinking `r` BEFORE τ-integration —
    cannot produce the τ-uniform (α = 0) (hbound-fat) slot at any FIXED fat base, because for
    every fixed `ε₀ > 0` the sup over `(0,T]` is infinite.  ⚠ Scope: this is a statement about the
    derived BOUND SHAPE (it does not, by itself, prove the defect kernel `E` admits no better
    bound — the genuine `ε₀/τ` lower bound on `E` for the center-frozen Gaussian is the external
    reviewer's diagonal-witness argument, not formalized here).  NOT `a₁ = R/6`. -/
theorem centerShape_no_uniform_majorant (Bδ ε₀ T : ℝ)
    (hBδ : 0 < Bδ) (hε₀ : 0 < ε₀) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T → Bδ * ε₀ * (1 / τ) ≤ C := by
  rintro ⟨C, hC⟩
  set A : ℝ := Bδ * ε₀ with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set τ : ℝ := min T (A / (|C| + 1)) with hτdef
  have hτ0 : 0 < τ := lt_min hT (by positivity)
  have hτT : τ ≤ T := min_le_left _ _
  have h1 : τ ≤ A / (|C| + 1) := min_le_right _ _
  have h2 : τ * (|C| + 1) ≤ A := by
    calc τ * (|C| + 1) ≤ (A / (|C| + 1)) * (|C| + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = A := div_mul_cancel₀ _ (by positivity)
  have h3 : |C| + 1 ≤ A * (1 / τ) := by
    have hcalc : ((|C| + 1) * τ) * (1 / τ) = |C| + 1 := by
      rw [mul_one_div, mul_div_assoc, div_self hτ0.ne', mul_one]
    calc |C| + 1 = ((|C| + 1) * τ) * (1 / τ) := hcalc.symm
      _ ≤ A * (1 / τ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h4 : A * (1 / τ) ≤ C := hC τ hτ0 hτT
  linarith [le_abs_self C]

/-- **★ J4-608 (ROUTE GATE, kernel level) — `centerShape_no_width2_kernel_majorant`.**  The same
    obstruction AGAINST THE ACTUAL (hbound-fat) TARGET: the `Bδ·ε₀·(1/τ)`-weighted width-3/2
    Gaussian cannot be majorized by `C·gaussDdim(2τ)` uniformly on `(0,T]` — no width absorption
    exists, because at `v = 0` every width shares the same `τ^{-n/2}` diagonal scaling
    (`gaussDdim_zero`), and the narrower width-3/2 peak DOMINATES the width-2 peak
    (`gaussDdim_zero_antitone`), so the hypothetical majorant would force a uniform scalar
    majorant of `Bδ·ε₀·(1/τ)` — contradicting the scalar gate.  Together the two gates settle the
    route decision: the center-gauge N = 1 shape CANNOT fill (hbound-fat) at any fixed fat
    `ε₀ > 0`; the producer must re-base the principal Gaussian per-`q` (route (c)).
    NOT `a₁ = R/6`. -/
theorem centerShape_no_width2_kernel_majorant (Bδ ε₀ T : ℝ)
    (hBδ : 0 < Bδ) (hε₀ : 0 < ε₀) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T →
        Bδ * ε₀ * (1 / τ) * gaussDdim (3 / 2 * τ) (0 : Point n)
          ≤ C * gaussDdim (2 * τ) (0 : Point n) := by
  rintro ⟨C, hC⟩
  refine centerShape_no_uniform_majorant Bδ ε₀ T hBδ hε₀ hT ⟨C, fun τ hτ hτT => ?_⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pos : 0 < gaussDdim (2 * τ) (0 : Point n) := by
    rw [gaussDdim_zero]
    have hs : (0 : ℝ) < Real.sqrt (4 * Real.pi * (2 * τ)) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  have hmono : gaussDdim (2 * τ) (0 : Point n) ≤ gaussDdim (3 / 2 * τ) (0 : Point n) :=
    gaussDdim_zero_antitone (3 / 2 * τ) (2 * τ) (by linarith) (by linarith)
  have hstep : Bδ * ε₀ * (1 / τ) * gaussDdim (2 * τ) (0 : Point n)
      ≤ C * gaussDdim (2 * τ) (0 : Point n) :=
    le_trans (mul_le_mul_of_nonneg_left hmono (by positivity)) (hC τ hτ hτT)
  exact le_of_mul_le_mul_right hstep h2pos

/-! ### Non-vacuity gate (cp466 discipline: ANTECEDENT inhabitance, not conclusion shape). -/

/-- **Non-vacuity of the center-gauge N = 1 engine at fat `K`.**  At every `r > 0`, `κ ≤ 0`,
    `n ≥ 1`: (i) the base compact `closedBall 0 r` contains a NONZERO point (no `K ⊆ {0}`
    collapse — contrast `rebased_hframeK_unsat`, J4-603); (ii) the heat-side antecedents are
    INHABITED (`Θ = 1`, `u ≡ 1`: `foldedCoeff Θ u k = 1` for EVERY `k`, so the ALL-`k` smoothness
    `hw` and center-flatness `hw0flat` both hold) AND at that witness BOTH coefficient-bound
    antecedents of the N = 1 center engine are exhibited DISCHARGED (via layer 3's
    `curvedRNC_coeff_bound_center` at `u` and `curvedRNC_coeffLinear_bound_center` at the shifted
    profile — not merely assumed); (iii) the `hdevK` antecedent HOLDS at the curved witness with
    the explicit `ε₀ = (|κ|/3)·n·r²`.  So EVERY antecedent of
    `uniformResidualN1_narrow_mixed_lin_center` is exhibited satisfiable at the fat curved base
    compact — the conclusions are not vacuously quantified.  NOT `a₁ = R/6`. -/
theorem curvedRNC_residN1_center_satisfiable (κ r : ℝ) (hκ : κ ≤ 0) (hr : 0 < r) (hn : 1 ≤ n) :
    (∃ q ∈ Metric.closedBall (0 : Point n) r, q ≠ 0) ∧
      (∃ Θ : Point n → ℝ, ∃ u : ℕ → Point n → ℝ,
        (∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k)) ∧
        (∀ e : Fin n, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) ∧
        (∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
          ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_c →
          |totalRadialO1_coeff
              (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
              (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u v|
            ≤ C_c * rncRadialSq v + C_ε * (|κ| / 3 * ((n : ℝ) * r ^ 2))) ∧
        (∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∃ C_ε : ℝ, 0 ≤ C_ε ∧
          ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_c →
          |totalRadialO1_coeff
              (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
              (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
              Θ (fun j => u (j + 1)) v|
            ≤ C_c * rncRadial v + C_ε * (|κ| / 3 * ((n : ℝ) * r ^ 2)))) ∧
      (∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j : Fin n,
        |curvedRNCMetric κ q i j - (if i = j then (1 : ℝ) else 0)|
          ≤ |κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  obtain ⟨h1, -, h3⟩ := curvedRNC_coeff_center_satisfiable (n := n) κ r hr hn
  refine ⟨h1, ?_, h3⟩
  refine ⟨fun _ => (1 : ℝ), fun _ _ => (1 : ℝ), ?_, ?_, ?_, ?_⟩
  · intro k
    have hfold : foldedCoeff (n := n) (fun _ => (1 : ℝ)) (fun _ _ => (1 : ℝ)) k
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
  · -- the O(r²)+ε₀ coefficient antecedent at the profile `u`, exhibited DISCHARGED from layer 3.
    refine curvedRNC_coeff_bound_center κ r hκ _ _ ?_ ?_
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
  · -- the O(r)+ε₀ coefficient antecedent at the SHIFTED profile, exhibited DISCHARGED from layer 3.
    refine curvedRNC_coeffLinear_bound_center κ r hκ _ _ ?_
    have hfold : foldedCoeff (n := n) (fun _ => (1 : ℝ))
        (fun j => (fun _ _ => (1 : ℝ)) (j + 1)) 0 = fun _ => (1 : ℝ) := by
      funext y
      simp [foldedCoeff, Real.one_rpow]
    rw [hfold]
    exact contDiff_const

end QIQTH.CurvedA1CenterN1
