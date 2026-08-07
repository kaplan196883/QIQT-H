/-
  AnnulusAmbientTransfer — J4-376: the ANNULUS AMBIENT transfer (Sol brick map, annulus counterpart
  of the ball-leg transport J4-374).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / TRANSPORT-WIRING brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It is
  the OFF-PLATEAU (annulus) sibling of the near-diagonal ball-leg transport
  `QIQTH.PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau` (J4-374): it carries the
  chart-frame annulus cutoff-residual envelope (`QIQTH.AnnulusAffineLeg.cutoffResidual_annulus43_bound`,
  J4-375, re-instantiated at chart width `5/4`) to the AMBIENT displacement `z := uniformFlowExp q v − q`
  at width `4/3` via the banked near-isometry QUAD transfer
  (`QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry`, J4-372), and wires it onto the gated
  witness's `heatOp` on the annulus via the banked on-gate transport identity
  (`QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport`, J4-370) and the gate layer
  (`QIQTH.HeatResidualBound.gatedKernel_heatOp_eq_of_mem_nhds`).  NO `sorry` (header prose excepted), NO
  new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding)
  the conclusion, NO existing file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on the whole
  convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WIDTH BOOKKEEPING VERDICT.

  The banked QUAD transfer `chartTransfer43_quad_from_nearIsometry` consumes a CHART-frame envelope at
  Gaussian width `5/4` (`gaussDdim ((5/4)τ) v`) and produces the AMBIENT-frame envelope at width `4/3`
  (`gaussDdim ((4/3)τ) z`).  The banked J4-375 annulus cutoff-residual bound
  `cutoffResidual_annulus43_bound` is stated AT chart width `4/3`, which the transfer canNOT consume (a
  chart-`4/3` Gaussian is not comparable to an ambient-`4/3` Gaussian without slack).  So we RE-RUN the
  J4-375 assembly at chart width `5/4` (its proof is width-AGNOSTIC — every step is `abs_add`/`mul_le_mul`
  bookkeeping plus the `Q ≥ 1` absorption, with NO `4/3`-specific lemma; the only `4/3` occurrences are
  the literal Gaussian widths).  The width-`5/4` tail-trade constant is `(4·1·(5/4)/((5/4−1)a²))^k·k!
  = (20/a²)^k·k!` (vs `(16/a²)^k·k!` at `4/3`), and the free pure-Gaussian upgrade normalizer is
  `√(5/4)ⁿ` (vs `√(4/3)ⁿ`).

  ## THE SHAPE-MATCH VERDICT.  The transport RHS of `heatOp_globalCutoffWitness_transport`,
      `radialCutoff a b v · ∂_τ(heatParametrix 1 · v) − Δ_{g̃_q}(radialCutoff · heatParametrix 1 τ ·) v`,
  is DEFINITIONALLY the LHS of `cutoffResidual_annulus54_bound` at the PULLBACK metric pair `(g̃_q,g̃i_q)`
  with `H := heatParametrix 1 Θ u τ` and `dtH := ∂_τ(heatParametrix 1 · v)` — same expression (the
  pullback frame is instantiated exactly as J4-374 did for the ball leg).  On the annulus there is NO
  plateau collapse: the `∂χ`/`Δχ` terms are exactly what the annulus bound bounds.

  ## DELIVERABLES.
  •  (W1) `invTpow_gaussDdim_le_narrow54` — the width-`5/4` annulus tail-trade helper (`c=1,d=5/4`
     specialization of the banked general `invTpow_gaussDdim_le_width_annulus`; constant `(20/a²)^k·k!`);
     `gaussDdim_le_gaussDdim_narrow54` — the free `1 → 5/4` pure-Gaussian upgrade;
     `parametrixCofactor_value_annulus54` / `parametrixCofactor_deriv_annulus54` — the annulus VALUE /
     DERIVATIVE per-term at width `5/4` (J4-375's P1/P2, re-run at `5/4`);
     `cutoffResidual_annulus54_bound` — ★ the J4-375 assembly re-run at chart width `5/4`.
  •  (W2) `cutoffResidual_annulusAmbient43_bound` — ★ the AMBIENT annulus bound: composes the width-`5/4`
     annulus bound with the QUAD transfer on the annulus ∩ near-isometry ball (`b < r₁`).
  •  (W3) `gatedHeatOp_affine_onAnnulus` — ★★ the heatOp wiring: via the transport identity + the gate
     layer, the gated witness's `heatOp` at the exp point is bounded by the ambient width-`4/3` affine
     envelope on the annulus, with all carries threaded honestly.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AnnulusAffineLeg
import QIQTH.Transfer43Quad
import QIQTH.OnGateGlue

open Finset Set Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.AnnulusAmbientTransfer

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (W1) — the width-`5/4` annulus tail-trade helpers and per-term bounds.
    ############################################################################### -/

/-- **★ (W1) — `invTpow_gaussDdim_le_narrow54`.**  THE WIDTH-`5/4` ANNULUS TAIL TRADE.  The `d = 5/4`
    specialization of the banked GENERAL `QIQTH.HeatResidualBound.invTpow_gaussDdim_le_width_annulus`
    (`c = 1 < d = 5/4`), the width-`5/4` sibling of J4-375's `invTpow_gaussDdim_le_narrow43`.  On the
    annulus `a² ≤ rncRadialSq v` (`a > 0`), for every `k`,
        `(1/τ)^k·gaussDdim τ v ≤ √(5/4)ⁿ·((20/a²)^k·k!)·gaussDdim ((5/4)·τ) v`.
    The `τ`-free constant `(20/a²)^k·k!` is the `exp(−a²/…τ)`-beats-`τ^{−k}` factor.  NOT `a₁ = R/6`. -/
theorem invTpow_gaussDdim_le_narrow54 (k : ℕ) (a : ℝ) (ha : 0 < a) {τ : ℝ} (hτ : 0 < τ)
    {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / τ) ^ k * gaussDdim τ v
      ≤ Real.sqrt (5 / 4) ^ n * ((20 / a ^ 2) ^ k * (k.factorial : ℝ)) * gaussDdim (5 / 4 * τ) v := by
  have h := invTpow_gaussDdim_le_width_annulus k a ha (c := 1) (d := 5 / 4)
    (by norm_num) (by norm_num) hτ hv
  have e1 : (5 / 4 / 1 : ℝ) = 5 / 4 := by norm_num
  have e3 : (4 * (1 : ℝ) * (5 / 4) / ((5 / 4 - 1) * a ^ 2)) = 20 / a ^ 2 := by
    rw [show ((5 / 4 : ℝ) - 1) = 1 / 4 by norm_num]; ring
  rw [e1, one_mul, e3] at h
  exact h

/-- **★ (W1) — `gaussDdim_le_gaussDdim_narrow54`.**  THE FREE `1 → 5/4` PURE-GAUSSIAN WIDTH UPGRADE.
    The `k = 0` case of `invTpow_gaussDdim_le_narrow54` — narrowing (`1 < 5/4`) is FREE up to the
    normalizer `√(5/4)ⁿ ≥ 1` (`gaussDdim_le_gaussDdim_chart` at `c = 1 < d = 5/4`, `v = w`).  NOT
    `a₁ = R/6`. -/
theorem gaussDdim_le_gaussDdim_narrow54 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim τ v ≤ Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) v := by
  have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 5 / 4)
    (by norm_num) (by norm_num) hτ (v := v) (w := v)
    (by have := rncRadialSq_nonneg v; linarith)
  simpa using h

/-- **★ (W1) — `parametrixCofactor_value_annulus54`.**  THE ANNULUS VALUE PER-TERM AT WIDTH `5/4`.  The
    width-`5/4` sibling of J4-375's `parametrixCofactor_value_annulus43`: the banked width-`1` value
    bound `parametrixCofactor_value_annulus_tauUniform` composed with the free upgrade
    `gaussDdim_le_gaussDdim_narrow54`.  NOT `a₁ = R/6`. -/
theorem parametrixCofactor_value_annulus54
    (a b : ℝ) (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor) :
    ∃ Kcof : ℝ, 0 ≤ Kcof ∧ ∀ (τ : ℝ), 0 < τ → ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |gaussDdim τ w * cofactor w| ≤ Kcof * gaussDdim (5 / 4 * τ) w := by
  obtain ⟨Kcof, hKcof0, hval⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b cofactor hcof_cont
  refine ⟨Kcof * Real.sqrt (5 / 4) ^ n, by positivity, ?_⟩
  intro τ hτ w h1 h2
  have hv1 : |gaussDdim τ w * cofactor w| ≤ Kcof * gaussDdim τ w := hval τ hτ w h1 h2
  calc |gaussDdim τ w * cofactor w|
      ≤ Kcof * gaussDdim τ w := hv1
    _ ≤ Kcof * (Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) w) :=
        mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow54 hτ w) hKcof0
    _ = Kcof * Real.sqrt (5 / 4) ^ n * gaussDdim (5 / 4 * τ) w := by ring

/-- **★★ (W1) — `parametrixCofactor_deriv_annulus54`.**  THE ANNULUS DERIVATIVE PER-TERM AT WIDTH `5/4`
    (the crux `k = 1` tail trade).  The width-`5/4` sibling of J4-375's
    `parametrixCofactor_deriv_annulus43`: Leibniz `∂ⱼ(G·cof) = (−wʲ/2τ)·G·cof + G·∂ⱼcof`, then the
    `k=1` tail trade `invTpow_gaussDdim_le_narrow54` `(1/τ)·G ≤ √(5/4)ⁿ·(20/a²)·G_{5/4}` and the free
    upgrade `gaussDdim_le_gaussDdim_narrow54`.  `Kd = √(5/4)ⁿ·(b·Kcof/2·(20/a²)+Kdcof)`.  NOT
    `a₁ = R/6`. -/
theorem parametrixCofactor_deriv_annulus54
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => gaussDdim τ y * cofactor y) j w| ≤ Kd * gaussDdim (5 / 4 * τ) w := by
  classical
  obtain ⟨Kcof, hKcof0, hKcof⟩ := exists_bound_on_annulus cofactor hcof_cont a b
  have hbd : ∀ j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ K :=
    fun j => exists_bound_on_annulus (fun w => pd cofactor j w) (hdcof_cont j) a b
  choose Kd' hKd'0 hKdbd using hbd
  set Kdcof : ℝ := ∑ j, Kd' j with hKdcof_def
  have hKdcof0 : 0 ≤ Kdcof := Finset.sum_nonneg fun j _ => hKd'0 j
  have hKdcof : ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ Kdcof := by
    intro w j h1 h2
    refine (hKdbd j w h1 h2).trans ?_
    exact Finset.single_le_sum (f := fun j' => Kd' j') (fun j' _ => hKd'0 j') (Finset.mem_univ j)
  refine ⟨Real.sqrt (5 / 4) ^ n * (b * Kcof / 2 * (20 / a ^ 2) + Kdcof), by positivity, ?_⟩
  intro τ hτ w j h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  set Gn : ℝ := gaussDdim (5 / 4 * τ) w with hGndef
  have hGnn0 : 0 ≤ Gn := gaussDdim_nonneg _ w
  have h2tpos : (0 : ℝ) < 2 * τ := by linarith
  have hwj : |w j| ≤ b := by
    have hle : (w j) ^ 2 ≤ b ^ 2 :=
      calc (w j) ^ 2 ≤ ∑ i, (w i) ^ 2 :=
            Finset.single_le_sum (f := fun i => (w i) ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ j)
        _ = rncRadialSq w := rfl
        _ ≤ b ^ 2 := h2
    calc |w j| = Real.sqrt ((w j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
      _ = |b| := Real.sqrt_sq_eq_abs _
      _ = b := abs_of_pos hb
  have hpg : PdiffAt (fun y => gaussDdim τ y) j w :=
    PdiffAt_of_contDiff (fun y => gaussDdim τ y) (gaussDdim_contDiff τ) j w
  have hpc : PdiffAt cofactor j w := hcof_pdiff j w
  rw [pd_mul (fun y => gaussDdim τ y) cofactor j w hpg hpc, gaussDdim_pd_eq τ hτ w j]
  have hinvT : (1 / τ) * gaussDdim τ w ≤ Real.sqrt (5 / 4) ^ n * (20 / a ^ 2) * Gn := by
    have h := invTpow_gaussDdim_le_narrow54 1 a ha hτ h1
    rw [hGndef]
    simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
  have hGle : gaussDdim τ w ≤ Real.sqrt (5 / 4) ^ n * Gn := by
    rw [hGndef]; exact gaussDdim_le_gaussDdim_narrow54 hτ w
  have hT1 : |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w|
      ≤ b / (2 * τ) * gaussDdim τ w * Kcof := by
    rw [abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2tpos]
    have hGA : 0 ≤ |w j| / (2 * τ) * gaussDdim τ w :=
      mul_nonneg (div_nonneg (abs_nonneg _) (le_of_lt h2tpos)) hG0
    calc |w j| / (2 * τ) * gaussDdim τ w * |cofactor w|
        ≤ |w j| / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_left (hKcof w h1 h2) hGA
      _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right h2tpos).mpr hwj) hG0)
            hKcof0
  have hT2 : |gaussDdim τ w * pd cofactor j w| ≤ gaussDdim τ w * Kdcof := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul_of_nonneg_left (hKdcof w j h1 h2) hG0
  have hT1abs : b / (2 * τ) * gaussDdim τ w * Kcof
      ≤ b * Kcof / 2 * (Real.sqrt (5 / 4) ^ n * (20 / a ^ 2)) * Gn := by
    have hcoef : (0 : ℝ) ≤ b * Kcof / 2 := by positivity
    calc b / (2 * τ) * gaussDdim τ w * Kcof
        = (b * Kcof / 2) * ((1 / τ) * gaussDdim τ w) := by ring
      _ ≤ (b * Kcof / 2) * (Real.sqrt (5 / 4) ^ n * (20 / a ^ 2) * Gn) :=
          mul_le_mul_of_nonneg_left hinvT hcoef
      _ = b * Kcof / 2 * (Real.sqrt (5 / 4) ^ n * (20 / a ^ 2)) * Gn := by ring
  have hT2abs : gaussDdim τ w * Kdcof ≤ Kdcof * (Real.sqrt (5 / 4) ^ n * Gn) := by
    calc gaussDdim τ w * Kdcof = Kdcof * gaussDdim τ w := by ring
      _ ≤ Kdcof * (Real.sqrt (5 / 4) ^ n * Gn) := mul_le_mul_of_nonneg_left hGle hKdcof0
  calc |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w + gaussDdim τ w * pd cofactor j w|
      ≤ |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w| + |gaussDdim τ w * pd cofactor j w| :=
        abs_add_le _ _
    _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof + gaussDdim τ w * Kdcof := add_le_add hT1 hT2
    _ ≤ b * Kcof / 2 * (Real.sqrt (5 / 4) ^ n * (20 / a ^ 2)) * Gn
          + Kdcof * (Real.sqrt (5 / 4) ^ n * Gn) := add_le_add hT1abs hT2abs
    _ = Real.sqrt (5 / 4) ^ n * (b * Kcof / 2 * (20 / a ^ 2) + Kdcof) * Gn := by ring

/-! ###############################################################################
    ### (W1) — the annulus cutoff-residual bound at chart width `5/4` (AffineGateBound inner shape).
    ############################################################################### -/

/-- **★★ (W1) — `cutoffResidual_annulus54_bound`.**  THE ANNULUS CUTOFF-RESIDUAL BOUND AT CHART WIDTH
    `5/4`.  VERBATIM re-run of J4-375's `QIQTH.AnnulusAffineLeg.cutoffResidual_annulus43_bound` at chart
    width `5/4` (its proof is width-agnostic — the `Δ_g(χ·H) = χ·Δ_gH + H·Δ_gχ + 2·Σ g⁻¹·∂χ·∂H` split,
    the `Q ≥ 1` absorption, and the `abs_add`/`mul_le_mul` bookkeeping carry NO `4/3`-specific lemma; the
    only change is the literal Gaussian width).  Bounds, on the annulus `a² ≤ rncRadialSq v ≤ b²`,
        `|χ·∂_τH − Δ_g(χ·H)|(v) ≤ (P₀ + P₁·t)·(((r²/t)²+r²/t+1)·gaussDdim ((5/4)·t) v)`,
    `P₀ = C₀ + Kcof·Kc2 + 2n²·Kg·Kc1·Kder`, `P₁ = C₁`.  This is the width the QUAD transfer
    `chartTransfer43_quad_from_nearIsometry` consumes.  Every hypothesis is SATISFIABLE
    (`hHann`/`hDHann` by `parametrixCofactor_value_annulus54`/`_deriv_annulus54`, the near carry
    `hEnear` by the affine residual estimate, the cutoff/metric carries by the concrete witness), none
    equals the conclusion.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_annulus54_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hEnear : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w|
          ≤ (C₀ + C₁ * t) * (((rncRadialSq w / t) ^ 2 + rncRadialSq w / t + 1)
              * gaussDdim (5 / 4 * t) w))
    (Kcof : ℝ) (hKcof : 0 ≤ Kcof)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ Kcof * gaussDdim (5 / 4 * t) w)
    (Kder : ℝ) (hKder : 0 ≤ Kder)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ Kder * gaussDdim (5 / 4 * t) w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    ∀ v : Point n, a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t)
            * (((rncRadialSq v / t) ^ 2 + rncRadialSq v / t + 1) * gaussDdim (5 / 4 * t) v) := by
  intro v ha2 hb2
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  set G54 : ℝ := gaussDdim (5 / 4 * t) v with hG54def
  have hG54nn : 0 ≤ G54 := gaussDdim_nonneg _ v
  set Q : ℝ := (rncRadialSq v / t) ^ 2 + rncRadialSq v / t + 1 with hQdef
  have hX0 : 0 ≤ rncRadialSq v / t := div_nonneg (rncRadialSq_nonneg _) ht.le
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef]; nlinarith [sq_nonneg (rncRadialSq v / t), hX0]
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
  have hQG0 : 0 ≤ Q * G54 := mul_nonneg hQ0 hG54nn
  have hGQ : G54 ≤ Q * G54 := by
    calc G54 = 1 * G54 := (one_mul _).symm
      _ ≤ Q * G54 := mul_le_mul_of_nonneg_right hQ1 hG54nn
  have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
  have hRcut : radialCutoff a b v * dtH v
      - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
        = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
          - H v * laplaceBeltrami g gi (radialCutoff a b) v
          - 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v := by
    rw [hlbmul]; ring
  rw [hRcut]
  set A := radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v) with hA
  set B' := H v * laplaceBeltrami g gi (radialCutoff a b) v with hB'
  set Cc := 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v with hCc
  have hsub2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
  have htri : |A - B' - Cc| ≤ |A| + |B'| + |Cc| :=
    (hsub2 (A - B') Cc).trans (by have := hsub2 A B'; linarith)
  have hAbd : |A| ≤ (C₀ + C₁ * t) * (Q * G54) := by
    rw [hA, abs_mul]
    have hχle : |radialCutoff a b v| ≤ 1 := by
      rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
    calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
        ≤ 1 * ((C₀ + C₁ * t) * (Q * G54)) :=
          mul_le_mul hχle (hEnear v ha2 hb2) (abs_nonneg _)
            (by positivity)
      _ = (C₀ + C₁ * t) * (Q * G54) := by ring
  have hBbd : |B'| ≤ (Kcof * Kc2) * (Q * G54) := by
    rw [hB', abs_mul]
    calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
        ≤ (Kcof * G54) * Kc2 :=
          mul_le_mul (hHann v ha2 hb2) (hLapChi v ha2 hb2) (abs_nonneg _)
            (mul_nonneg hKcof hG54nn)
      _ = (Kcof * Kc2) * G54 := by ring
      _ ≤ (Kcof * Kc2) * (Q * G54) := mul_le_mul_of_nonneg_left hGQ (mul_nonneg hKcof hKc2)
  have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ Kg * Kc1 * (Kder * G54) := by
    intro i j
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul (hgibd v i j ha2 hb2) (hDchi v i ha2 hb2) (abs_nonneg _) hKg)
      (hDHann v j ha2 hb2) (abs_nonneg _) (mul_nonneg hKg hKc1)
  have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * G54)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * G54)))
      = (n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * G54)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * (Q * G54) := by
    rw [hCc]
    have hstep : |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
        ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * G54 := by
      calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
            mul_le_mul_of_nonneg_left hSabs (by norm_num)
        _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * G54))) :=
            mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
        _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * G54 := by ring
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_left hGQ (by positivity)
  calc |A - B' - Cc|
      ≤ |A| + |B'| + |Cc| := htri
    _ ≤ (C₀ + C₁ * t) * (Q * G54) + (Kcof * Kc2) * (Q * G54)
          + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * (Q * G54) :=
        add_le_add (add_le_add hAbd hBbd) hCcbd
    _ = (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t) * (Q * G54) := by ring

/-! ###############################################################################
    ### (W2) — the AMBIENT annulus bound (width-`5/4` chart → width-`4/3` ambient transfer).  ★
    ############################################################################### -/

/-- **★★ (W2) — `cutoffResidual_annulusAmbient43_bound`.**  THE AMBIENT ANNULUS BOUND.  Composes the
    width-`5/4` chart annulus bound `cutoffResidual_annulus54_bound` (for a GENERIC annulus-Laplacian
    metric pair `(gM, giM)` and generic `H, dtH`) with the banked QUAD transfer
    `QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry` (for the ORIGINAL metric `g gi`), on
    the annulus contained in the near-isometry ball (`b < r₁`, whence
    `‖v‖ ≤ rncRadial v ≤ b < r₁` by `norm_le_rncRadial`).  With `z := uniformFlowExp g gi hC hK q v − q`
    the ambient displacement,
        `|χ·dtH − Δ_{gM}(χ·H)|(v)
            ≤ (B·P₀ + B·C₁·t)·(((r²_z/t)² + r²_z/t + 1)·gaussDdim ((4/3)·t) z)`,
    `B = (25/16)·√((4/3)/(5/4))ⁿ`, `P₀ = C₀ + Kcof·Kc2 + 2n²·Kg·Kc1·Kder`.  The transfer legs are
    metric-INDEPENDENT (they only involve `v`, `z`, the widths), so `(gM, giM)` will be instantiated at
    the PULLBACK pair in (W3).  Every carry is the SAME satisfiable input as the width-`5/4` annulus
    bound; none equals the conclusion.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_annulusAmbient43_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K,
      ∀ (gM giM : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ) (a b t : ℝ),
        0 < a → a < b → b < r₁ → 0 < t →
        (∀ w : Point n, ContDiffAt ℝ 2 H w) →
        (∀ w i j, giM w i j = giM w j i) →
      ∀ C₀ C₁ : ℝ, 0 ≤ C₀ → 0 ≤ C₁ →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |dtH w - laplaceBeltrami gM giM H w|
            ≤ (C₀ + C₁ * t) * (((rncRadialSq w / t) ^ 2 + rncRadialSq w / t + 1)
                * gaussDdim (5 / 4 * t) w)) →
      ∀ Kcof : ℝ, 0 ≤ Kcof →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |H w| ≤ Kcof * gaussDdim (5 / 4 * t) w) →
      ∀ Kder : ℝ, 0 ≤ Kder →
        (∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |pd H j w| ≤ Kder * gaussDdim (5 / 4 * t) w) →
      ∀ Kg Kc1 Kc2 : ℝ, 0 ≤ Kg → 0 ≤ Kc1 → 0 ≤ Kc2 →
        (∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |giM w i j| ≤ Kg) →
        (∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |pd (radialCutoff a b) i w| ≤ Kc1) →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |laplaceBeltrami gM giM (radialCutoff a b) w| ≤ Kc2) →
      ∀ v : Point n, a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
        |radialCutoff a b v * dtH v
            - laplaceBeltrami gM giM (fun y => radialCutoff a b y * H y) v|
          ≤ (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
                * (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder)
              + 25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n * C₁ * t)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / t) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / t + 1)
                  * gaussDdim (4 / 3 * t) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨r₁, hr₁pos, htrans⟩ :=
    QIQTH.Transfer43Quad.chartTransfer43_quad_from_nearIsometry g gi hC hK
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq gM giM H dtH a b t ha hab hbr ht hH2 hgisymm
    C₀ C₁ hC₀ hC₁ hEnear Kcof hKcof hHann Kder hKder hDHann
    Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi v ha2 hb2
  -- the width-`5/4` chart annulus bound at this metric / `H` / `dtH` / `t`.
  have hann := cutoffResidual_annulus54_bound gM giM H dtH a b t ha hab ht hH2 hgisymm
    C₀ C₁ hC₀ hC₁ hEnear Kcof hKcof hHann Kder hKder hDHann Kg Kc1 Kc2 hKg hKc1 hKc2
    hgibd hDchi hLapChi v ha2 hb2
  -- `‖v‖ < r₁` from the annulus membership (`b < r₁`).
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ha hab)
  have hvnorm : ‖v‖ < r₁ := by
    have h2 : rncRadial v ≤ b := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq v) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hb2
        _ = b := Real.sqrt_sq hb0
    calc ‖v‖ ≤ rncRadial v := norm_le_rncRadial v
      _ ≤ b := h2
      _ < r₁ := hbr
  -- the QUAD transfer at `(q, v, t)`.
  have htr := htrans q hq v hvnorm t ht
  set z : Point n := uniformFlowExp g gi hC hK q v - q with hz
  -- `P₀ + C₁·t ≥ 0`.
  have hM0 : 0 ≤ C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t := by
    have h1 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof hKc2
    have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
      have hn2 : 0 ≤ 2 * (n : ℝ) ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hn2 hKg) hKc1) hKder
    have h3 : 0 ≤ C₁ * t := mul_nonneg hC₁ ht.le
    linarith
  calc |radialCutoff a b v * dtH v
          - laplaceBeltrami gM giM (fun y => radialCutoff a b y * H y) v|
      ≤ (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t)
          * (((rncRadialSq v / t) ^ 2 + rncRadialSq v / t + 1) * gaussDdim (5 / 4 * t) v) := hann
    _ ≤ (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t)
          * (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
              * (((rncRadialSq z / t) ^ 2 + rncRadialSq z / t + 1) * gaussDdim (4 / 3 * t) z)) :=
        mul_le_mul_of_nonneg_left htr hM0
    _ = (25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
              * (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder)
            + 25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n * C₁ * t)
            * (((rncRadialSq z / t) ^ 2 + rncRadialSq z / t + 1) * gaussDdim (4 / 3 * t) z) := by
        ring

/-! ###############################################################################
    ### (W3) — the gated heatOp on the annulus.  ★★
    ############################################################################### -/

/-- **★★ (W3) — `gatedHeatOp_affine_onAnnulus`.**  THE GATED HEATOP ANNULUS LEG.  The off-plateau
    sibling of `QIQTH.PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau`.  On the annulus
    `a² ≤ rncRadialSq v ≤ b²` contained in the near-isometry ball (`b < r₁`), the GATED witness's
    `heatOp` at the exp point is bounded by the ambient width-`4/3` affine envelope on
    `z := uniformFlowExp g gi hC hK q v − q`:
        `|heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 …)) τ (exp q v) q|
            ≤ (P₀ + P₁·τ)·(((r²_z/τ)² + r²_z/τ + 1)·gaussDdim ((4/3)·τ) z)`.
    Route (mirroring the ball-leg P3): the gate layer
    `QIQTH.HeatResidualBound.gatedKernel_heatOp_eq_of_mem_nhds` (carry `hS`, `hq`) makes the hard set-gate
    transparent; the on-gate transport identity
    `QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport` (carries `hpt`, `hlap`) rewrites the
    ungated `heatOp` to the CHART-frame transport RHS in the PULLBACK metric
    `g̃_q = uniformFlowPullbackMetric g gi hC hK q`; the AMBIENT annulus bound (W2), instantiated at the
    pullback pair with `H := heatParametrix 1 Θ u τ` and `dtH := ∂_τ(heatParametrix 1 · ·)`, bounds it.
    Unlike the ball leg there is NO plateau collapse: the transport RHS with its `∂χ`/`Δχ` terms is
    exactly what the annulus bound bounds.  The transport carries (`hpt`, `hlap`) are dischargeable via
    the banked `OnGateGlue` G2 lemmas (`uniformInverseChart_leftInverse_of_lt`,
    `laplaceBeltrami_globalCutoffWitness_naturality`); the annulus carries (`hEnear`, `hHann`, `hDHann`,
    `hgibd`, `hDchi`, `hLapChi`) are the SAME satisfiable pointwise inputs the width-`5/4` annulus bound
    takes — threaded honestly here, discharged downstream; NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem gatedHeatOp_affine_onAnnulus
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ q ∈ K, ∀ v : Point n,
      ∀ (a b τ : ℝ), 0 < a → a < b → b < r₁ → 0 < τ →
        S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
        uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v →
        laplaceBeltrami g gi
            (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ p q)
            (uniformFlowExp g gi hC hK q v)
          = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v →
        (∀ w : Point n, ContDiffAt ℝ 2 (fun y => heatParametrix 1 Θ u τ y) w) →
        (∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
            = uniformFlowPullbackMetricInv g gi hC hK q w j i) →
      ∀ C₀ C₁ : ℝ, 0 ≤ C₀ → 0 ≤ C₁ →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |deriv (fun s => heatParametrix 1 Θ u s w) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => heatParametrix 1 Θ u τ y) w|
            ≤ (C₀ + C₁ * τ) * (((rncRadialSq w / τ) ^ 2 + rncRadialSq w / τ + 1)
                * gaussDdim (5 / 4 * τ) w)) →
      ∀ Kcof : ℝ, 0 ≤ Kcof →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |heatParametrix 1 Θ u τ w| ≤ Kcof * gaussDdim (5 / 4 * τ) w) →
      ∀ Kder : ℝ, 0 ≤ Kder →
        (∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |pd (fun y => heatParametrix 1 Θ u τ y) j w| ≤ Kder * gaussDdim (5 / 4 * τ) w) →
      ∀ Kg Kc1 Kc2 : ℝ, 0 ≤ Kg → 0 ≤ Kc1 → 0 ≤ Kc2 →
        (∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg) →
        (∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |pd (radialCutoff a b) i w| ≤ Kc1) →
        (∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
          |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (radialCutoff a b) w| ≤ Kc2) →
      a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
      ∃ P₀ P₁ : ℝ, 0 ≤ P₀ ∧ 0 ≤ P₁ ∧
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (P₀ + P₁ * τ)
              * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                    + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
  obtain ⟨r₁, hr₁pos, hW2⟩ := cutoffResidual_annulusAmbient43_bound g gi hC hK
  refine ⟨r₁, hr₁pos, ?_⟩
  intro q hq v a b τ ha hab hbr hτ hS hpt hlap hH2 hgisymm
    C₀ C₁ hC₀ hC₁ hEnear Kcof hKcof hHann Kder hKder hDHann
    Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi ha2 hb2
  refine ⟨25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n
            * (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder),
          25 / 16 * Real.sqrt ((4 / 3) / (5 / 4)) ^ n * C₁, ?_, ?_, ?_⟩
  · have hM0 : 0 ≤ C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
      have h1 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof hKc2
      have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
        have hn2 : 0 ≤ 2 * (n : ℝ) ^ 2 := by positivity
        exact mul_nonneg (mul_nonneg (mul_nonneg hn2 hKg) hKc1) hKder
      linarith
    positivity
  · positivity
  · -- rewrite the gated heatOp to the transport RHS, then apply (W2).
    rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S
          (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)) τ
          (uniformFlowExp g gi hC hK q v) q hq hS,
        QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport g gi hC hK Θ u a b
          (uniformInverseChart g gi hC hK) q v hpt hlap]
    exact hW2 q hq (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q)
      (fun y => heatParametrix 1 Θ u τ y) (fun w => deriv (fun s => heatParametrix 1 Θ u s w) τ)
      a b τ ha hab hbr hτ hH2 hgisymm C₀ C₁ hC₀ hC₁ hEnear Kcof hKcof hHann Kder hKder hDHann
      Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi v ha2 hb2

end QIQTH.AnnulusAmbientTransfer

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AnnulusAmbientTransfer.invTpow_gaussDdim_le_narrow54
#print axioms QIQTH.AnnulusAmbientTransfer.gaussDdim_le_gaussDdim_narrow54
#print axioms QIQTH.AnnulusAmbientTransfer.parametrixCofactor_value_annulus54
#print axioms QIQTH.AnnulusAmbientTransfer.parametrixCofactor_deriv_annulus54
#print axioms QIQTH.AnnulusAmbientTransfer.cutoffResidual_annulus54_bound
#print axioms QIQTH.AnnulusAmbientTransfer.cutoffResidual_annulusAmbient43_bound
#print axioms QIQTH.AnnulusAmbientTransfer.gatedHeatOp_affine_onAnnulus
