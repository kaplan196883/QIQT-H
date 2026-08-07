/-
  AnnulusAffineLeg — J4-375: the ANNULUS (2b) LEG of `AffineGateBound`, at width `4/3`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / WIDTH-TRADE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It supplies
  the OFF-PLATEAU (annulus) counterpart of the banked near-diagonal plateau leg
  `QIQTH.PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau` (J4-374), at the target width
  `4/3` of `QIQTH.HgateAffineRepair.AffineGateBound`.  No `sorry` (header prose excepted), no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on the whole
  convergence / geometric-wiring stack AND on the surviving LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE ANNULUS WIDTH-TRADE VERDICT (Phase-1 map).

  •  The banked cutoff-residual engine `QIQTH.HeatResidualBound.cutoffResidual_narrow_tauUniform_engine`
     (WidthMarginEngine.lean) is WIDTH-AGNOSTIC in its PROOF: it combines its `hEnear`, `hHann`,
     `hDHann`, `hgibd`, `hDchi`, `hLapChi` hypotheses by pure `abs_add` + `mul_le_mul` bookkeeping with
     NO width-`3/2`-specific lemma.  The `3/2` that appears in every hypothesis and its conclusion is
     merely the width CHOSEN by the consumers (`CoeffU1Fix.cutoffResidualN1_uniformFlow_narrow_mixed_below_lin`).

  •  The `3/2` is IRREVERSIBLE ONLY in the NEAR (plateau) region: there the parametrix residual carries a
     genuine quadratic polynomial `((r²/τ)²+r²/τ+1)` that can be absorbed into a PURE Gaussian only by
     WIDENING (`HgateAffineRepair.quadPoly_width_absorb`, `w₀ < 3/2`).  It is NOT irreversible on the
     ANNULUS: there every `∂χ`/`Δχ` term is a PURE Gaussian times a nonneg power of `1/τ`, and the tail
     trade `QIQTH.HeatResidualBound.invTpow_gaussDdim_le_width_annulus` (WidthMarginEngine.lean) is
     GENERAL in `(c,d)`:
         `(1/τ)^k · gaussDdim (c·τ) v ≤ √(d/c)ⁿ·((4cd/((d−c)a²))^k·k!)·gaussDdim (d·τ) v`   (`a²≤r²_v`),
     valid for ANY `c < d`.  The `√(d/c)ⁿ` prefactor and the `(4cd/((d−c)a²))^k·k!` constant are
     `τ`-FREE (this IS the `exp(−a²/…τ)` beats `τ^{−k}` mechanism — `invT_pow_exp_le`), so the annulus
     terms trade DOWN to ANY width `d ∈ (1, 3/2)`, in particular `d = 4/3`, with NO `(1+t)` cap and NO
     surviving `τ`-power.  The `AffineGateBound` target already CARRIES the quadratic factor `≥ 1`, so
     the pure-Gaussian annulus bound fits under it for free.

  •  τ-BEHAVIOUR on the annulus is τ-UNIFORM: the value term `|G_τ·cof|` is `k=0` (free `1→4/3` upgrade,
     `gaussDdim_le_gaussDdim_chart`), the derivative term `|∂ⱼ(G_τ·cof)|` deposits its `−wʲ/(2τ)` into
     the `k=1` tail trade, giving a `τ`-FREE constant.  The ONLY affine-in-`τ` growth (`P₁·τ`) is the
     NEAR residual's `τ·(Δu₁)·G` term, which enters the annulus split through the `χ·(∂_τH−Δ_GH)`
     leg (`hEnear`) — carried honestly here as the affine near coefficient `C₁`.

  ## DELIVERABLES (all in the chart / `v` coordinate; the ambient `v → (p−q)` chart transfer and the
     `∃`-capstone wiring through `AffineGateTransport.heatOp_globalCutoffWitness_transport` are the
     documented remaining distance — see the module note at the file end).
  •  (T1) `invTpow_gaussDdim_le_narrow43` — the width-`4/3` tail-trade helper (`c=1, d=4/3`
     specialization of the banked general `invTpow_gaussDdim_le_width_annulus`; constant `(16/a²)^k·k!`).
  •  (T2) `gaussDdim_le_gaussDdim_narrow43` — the free `1 → 4/3` pure-Gaussian width upgrade.
  •  (P1) `parametrixCofactor_value_annulus43` — the annulus VALUE per-term at width `4/3`.
  •  (P2) `parametrixCofactor_deriv_annulus43` — ★ the annulus DERIVATIVE per-term at width `4/3` (the
     `k=1` tail trade in action; mirror of `parametrixCofactor_deriv_annulus_narrow_tauUniform`).
  •  (A)  `cutoffResidual_annulus43_bound` — ★ the annulus cutoff-residual bound at width `4/3` in the
     `AffineGateBound` inner shape `(P₀+P₁τ)·(quadPoly·gaussDdim (4/3·τ))`, from the abstract annulus
     value / derivative / metric / cutoff carries plus the affine near carry `hEnear`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthMarginEngine

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open scoped BigOperators ContDiff Topology

namespace QIQTH.AnnulusAffineLeg

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T1)/(T2) — the width-`4/3` tail-trade helpers.
    ############################################################################### -/

/-- **★ (T1) — `invTpow_gaussDdim_le_narrow43`.**  THE WIDTH-`4/3` ANNULUS TAIL TRADE.  The `d = 4/3`
    specialization of the banked GENERAL `QIQTH.HeatResidualBound.invTpow_gaussDdim_le_width_annulus`
    (`c = 1 < d = 4/3`), the exact width-`4/3` sibling of the banked `invTpow_gaussDdim_le_narrow`
    (`d = 3/2`).  On the annulus `a² ≤ rncRadialSq v` (`a > 0`), for every `k`, a `(1/τ)^k`-weighted
    width-`1` Gaussian is bounded `τ`-UNIFORMLY by a width-`4/3` Gaussian:
        `(1/τ)^k·gaussDdim τ v ≤ √(4/3)ⁿ·((16/a²)^k·k!)·gaussDdim ((4/3)·τ) v`.
    The `τ`-free constant `(16/a²)^k·k!` is the `exp(−a²/…τ)`-beats-`τ^{−k}` factor.  NOT `a₁ = R/6`. -/
theorem invTpow_gaussDdim_le_narrow43 (k : ℕ) (a : ℝ) (ha : 0 < a) {τ : ℝ} (hτ : 0 < τ)
    {v : Point n} (hv : a ^ 2 ≤ rncRadialSq v) :
    (1 / τ) ^ k * gaussDdim τ v
      ≤ Real.sqrt (4 / 3) ^ n * ((16 / a ^ 2) ^ k * (k.factorial : ℝ)) * gaussDdim (4 / 3 * τ) v := by
  have h := invTpow_gaussDdim_le_width_annulus k a ha (c := 1) (d := 4 / 3)
    (by norm_num) (by norm_num) hτ hv
  have e1 : (4 / 3 / 1 : ℝ) = 4 / 3 := by norm_num
  have e3 : (4 * (1 : ℝ) * (4 / 3) / ((4 / 3 - 1) * a ^ 2)) = 16 / a ^ 2 := by
    rw [show ((4 / 3 : ℝ) - 1) = 1 / 3 by norm_num]; ring
  rw [e1, one_mul, e3] at h
  exact h

/-- **★ (T2) — `gaussDdim_le_gaussDdim_narrow43`.**  THE FREE `1 → 4/3` PURE-GAUSSIAN WIDTH UPGRADE.
    The `k = 0` case of (T1) — narrowing (`1 < 4/3`) is FREE up to the normalizer `√(4/3)ⁿ ≥ 1` (the
    banked `gaussDdim_le_gaussDdim_chart` at `c = 1 < d = 4/3`, `v = w`).  NOT `a₁ = R/6`. -/
theorem gaussDdim_le_gaussDdim_narrow43 {τ : ℝ} (hτ : 0 < τ) (v : Point n) :
    gaussDdim τ v ≤ Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) v := by
  have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 1) (d := 4 / 3)
    (by norm_num) (by norm_num) hτ (v := v) (w := v)
    (by have := rncRadialSq_nonneg v; linarith)
  simpa using h

/-! ###############################################################################
    ### (P1)/(P2) — the annulus VALUE and DERIVATIVE per-term bounds at width `4/3`.
    ############################################################################### -/

/-- **★ (P1) — `parametrixCofactor_value_annulus43`.**  THE ANNULUS VALUE PER-TERM AT WIDTH `4/3`.  For
    `H_τ = gaussDdim τ · cofactor`, on the annulus `a² ≤ rncRadialSq w ≤ b²` the value is dominated by a
    `τ`-FREE constant times the width-`4/3` Gaussian.  The banked width-`1` value bound
    `parametrixCofactor_value_annulus_tauUniform` composed with the free upgrade (T2).  NOT `a₁ = R/6`. -/
theorem parametrixCofactor_value_annulus43
    (a b : ℝ) (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor) :
    ∃ Kcof : ℝ, 0 ≤ Kcof ∧ ∀ (τ : ℝ), 0 < τ → ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |gaussDdim τ w * cofactor w| ≤ Kcof * gaussDdim (4 / 3 * τ) w := by
  obtain ⟨Kcof, hKcof0, hval⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b cofactor hcof_cont
  refine ⟨Kcof * Real.sqrt (4 / 3) ^ n, by positivity, ?_⟩
  intro τ hτ w h1 h2
  have hv1 : |gaussDdim τ w * cofactor w| ≤ Kcof * gaussDdim τ w := hval τ hτ w h1 h2
  calc |gaussDdim τ w * cofactor w|
      ≤ Kcof * gaussDdim τ w := hv1
    _ ≤ Kcof * (Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) w) :=
        mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow43 hτ w) hKcof0
    _ = Kcof * Real.sqrt (4 / 3) ^ n * gaussDdim (4 / 3 * τ) w := by ring

/-- **★★ (P2) — `parametrixCofactor_deriv_annulus43`.**  THE ANNULUS DERIVATIVE PER-TERM AT WIDTH `4/3`
    (the crux tail trade `k = 1`).  For `H_τ = gaussDdim τ · cofactor`, on the annulus
    `a² ≤ rncRadialSq w ≤ b²` (`0 < a`), EACH partial `∂ⱼH_τ` is dominated by a `τ`-FREE constant times
    the width-`4/3` Gaussian.  The exact width-`4/3` sibling of the banked
    `parametrixCofactor_deriv_annulus_narrow_tauUniform` (`3/2`): Leibniz
    `∂ⱼ(G·cof) = (−wʲ/2τ)·G·cof + G·∂ⱼcof`, then the `k=1` tail trade (T1) `(1/τ)·G ≤ √(4/3)ⁿ·(16/a²)·G_{4/3}`
    and the free upgrade (T2) `G ≤ √(4/3)ⁿ·G_{4/3}` deposit the `wʲ`- and `(1/τ)`-factors into the
    width-`4/3` Gaussian, so no `τ`-growth survives.  `Kd = √(4/3)ⁿ·(b·Kcof/2·(16/a²)+Kdcof)`.  NOT
    `a₁ = R/6`. -/
theorem parametrixCofactor_deriv_annulus43
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => gaussDdim τ y * cofactor y) j w| ≤ Kd * gaussDdim (4 / 3 * τ) w := by
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
  refine ⟨Real.sqrt (4 / 3) ^ n * (b * Kcof / 2 * (16 / a ^ 2) + Kdcof), by positivity, ?_⟩
  intro τ hτ w j h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  set Gn : ℝ := gaussDdim (4 / 3 * τ) w with hGndef
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
  have hinvT : (1 / τ) * gaussDdim τ w ≤ Real.sqrt (4 / 3) ^ n * (16 / a ^ 2) * Gn := by
    have h := invTpow_gaussDdim_le_narrow43 1 a ha hτ h1
    rw [hGndef]
    simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
  have hGle : gaussDdim τ w ≤ Real.sqrt (4 / 3) ^ n * Gn := by
    rw [hGndef]; exact gaussDdim_le_gaussDdim_narrow43 hτ w
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
      ≤ b * Kcof / 2 * (Real.sqrt (4 / 3) ^ n * (16 / a ^ 2)) * Gn := by
    have hcoef : (0 : ℝ) ≤ b * Kcof / 2 := by positivity
    calc b / (2 * τ) * gaussDdim τ w * Kcof
        = (b * Kcof / 2) * ((1 / τ) * gaussDdim τ w) := by ring
      _ ≤ (b * Kcof / 2) * (Real.sqrt (4 / 3) ^ n * (16 / a ^ 2) * Gn) :=
          mul_le_mul_of_nonneg_left hinvT hcoef
      _ = b * Kcof / 2 * (Real.sqrt (4 / 3) ^ n * (16 / a ^ 2)) * Gn := by ring
  have hT2abs : gaussDdim τ w * Kdcof ≤ Kdcof * (Real.sqrt (4 / 3) ^ n * Gn) := by
    calc gaussDdim τ w * Kdcof = Kdcof * gaussDdim τ w := by ring
      _ ≤ Kdcof * (Real.sqrt (4 / 3) ^ n * Gn) := mul_le_mul_of_nonneg_left hGle hKdcof0
  calc |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w + gaussDdim τ w * pd cofactor j w|
      ≤ |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w| + |gaussDdim τ w * pd cofactor j w| :=
        abs_add_le _ _
    _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof + gaussDdim τ w * Kdcof := add_le_add hT1 hT2
    _ ≤ b * Kcof / 2 * (Real.sqrt (4 / 3) ^ n * (16 / a ^ 2)) * Gn
          + Kdcof * (Real.sqrt (4 / 3) ^ n * Gn) := add_le_add hT1abs hT2abs
    _ = Real.sqrt (4 / 3) ^ n * (b * Kcof / 2 * (16 / a ^ 2) + Kdcof) * Gn := by ring

/-! ###############################################################################
    ### (A) — the annulus cutoff-residual bound at width `4/3` (AffineGateBound inner shape).
    ############################################################################### -/

/-- **★★ (A) — `cutoffResidual_annulus43_bound`.**  THE ANNULUS CUTOFF-RESIDUAL BOUND AT WIDTH `4/3`, in
    the `AffineGateBound` INNER SHAPE.  The width-`4/3` clone of the ANNULUS (middle) region of the
    banked `QIQTH.HeatResidualBound.cutoffResidual_narrow_tauUniform_engine`: the same
    `Δ_g(χ·H) = χ·Δ_gH + H·Δ_gχ + 2·Σ g⁻¹·∂χ·∂H` split (`laplaceBeltrami_mul_C2`), so
        `χ·∂_τH − Δ_g(χ·H) = χ·(∂_τH − Δ_gH) − H·Δ_gχ − 2·Σ g⁻¹·∂χ·∂H`   (`A − B' − C`),
    bounded on the annulus `a² ≤ rncRadialSq v ≤ b²` by
        `(P₀ + P₁·τ)·(((r²/τ)²+r²/τ+1)·gaussDdim ((4/3)·τ) v)`,
    `P₀ = C₀ + Kcof·Kc2 + 2n²·Kg·Kc1·Kder`, `P₁ = C₁`.  The `A`-leg consumes the AFFINE near carry
    `hEnear` (the quadPoly·`G_{4/3}` residual bound with the genuine `C₁·τ` from the `τ·Δu₁` term — the
    only affine growth), `|χ| ≤ 1`; the `B'`/`C`-legs consume the width-`4/3` value carry `hHann`
    (satisfiable by (P1)), derivative carry `hDHann` (by (P2)), inverse-metric `hgibd`, and cutoff
    `hDchi`/`hLapChi` carries — all pure width-`4/3` Gaussians, absorbed under the quadratic factor
    `≥ 1`.  Every hypothesis is SATISFIABLE (the concrete van-Vleck witness / banked annulus uniforms),
    non-vacuous, and NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_annulus43_bound
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hEnear : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w|
          ≤ (C₀ + C₁ * t) * (((rncRadialSq w / t) ^ 2 + rncRadialSq w / t + 1)
              * gaussDdim (4 / 3 * t) w))
    (Kcof : ℝ) (hKcof : 0 ≤ Kcof)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ Kcof * gaussDdim (4 / 3 * t) w)
    (Kder : ℝ) (hKder : 0 ≤ Kder)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ Kder * gaussDdim (4 / 3 * t) w)
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
            * (((rncRadialSq v / t) ^ 2 + rncRadialSq v / t + 1) * gaussDdim (4 / 3 * t) v) := by
  intro v ha2 hb2
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  set G43 : ℝ := gaussDdim (4 / 3 * t) v with hG43def
  have hG43nn : 0 ≤ G43 := gaussDdim_nonneg _ v
  set Q : ℝ := (rncRadialSq v / t) ^ 2 + rncRadialSq v / t + 1 with hQdef
  have hX0 : 0 ≤ rncRadialSq v / t := div_nonneg (rncRadialSq_nonneg _) ht.le
  have hQ1 : (1 : ℝ) ≤ Q := by rw [hQdef]; nlinarith [sq_nonneg (rncRadialSq v / t), hX0]
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
  have hQG0 : 0 ≤ Q * G43 := mul_nonneg hQ0 hG43nn
  -- `G_{4/3} ≤ Q·G_{4/3}` (the quadratic factor `≥ 1` absorbs each pure-Gaussian annulus term).
  have hGQ : G43 ≤ Q * G43 := by
    calc G43 = 1 * G43 := (one_mul _).symm
      _ ≤ Q * G43 := mul_le_mul_of_nonneg_right hQ1 hG43nn
  -- the Leibniz cutoff split (verbatim to the engine's annulus region).
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
  -- (A) the χ-scaled near residual, at width `4/3`, quadPoly-carrying.
  have hAbd : |A| ≤ (C₀ + C₁ * t) * (Q * G43) := by
    rw [hA, abs_mul]
    have hχle : |radialCutoff a b v| ≤ 1 := by
      rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
    calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
        ≤ 1 * ((C₀ + C₁ * t) * (Q * G43)) :=
          mul_le_mul hχle (hEnear v ha2 hb2) (abs_nonneg _)
            (by positivity)
      _ = (C₀ + C₁ * t) * (Q * G43) := by ring
  -- (B') the `H·Δ_gχ` term, pure width-`4/3`, absorbed under `Q ≥ 1`.
  have hBbd : |B'| ≤ (Kcof * Kc2) * (Q * G43) := by
    rw [hB', abs_mul]
    calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
        ≤ (Kcof * G43) * Kc2 :=
          mul_le_mul (hHann v ha2 hb2) (hLapChi v ha2 hb2) (abs_nonneg _)
            (mul_nonneg hKcof hG43nn)
      _ = (Kcof * Kc2) * G43 := by ring
      _ ≤ (Kcof * Kc2) * (Q * G43) := mul_le_mul_of_nonneg_left hGQ (mul_nonneg hKcof hKc2)
  -- (C) the `2·Σ g⁻¹·∂χ·∂H` term, pure width-`4/3`, absorbed under `Q ≥ 1`.
  have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
  have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ Kg * Kc1 * (Kder * G43) := by
    intro i j
    rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul (hgibd v i j ha2 hb2) (hDchi v i ha2 hb2) (abs_nonneg _) hKg)
      (hDHann v j ha2 hb2) (abs_nonneg _) (mul_nonneg hKg hKc1)
  have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * G43)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * G43)))
      = (n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * G43)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * (Q * G43) := by
    rw [hCc]
    have hstep : |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
        ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * G43 := by
      calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
            mul_le_mul_of_nonneg_left hSabs (by norm_num)
        _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * G43))) :=
            mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
        _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * G43 := by ring
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_left hGQ (by positivity)
  -- assemble.
  calc |A - B' - Cc|
      ≤ |A| + |B'| + |Cc| := htri
    _ ≤ (C₀ + C₁ * t) * (Q * G43) + (Kcof * Kc2) * (Q * G43)
          + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * (Q * G43) :=
        add_le_add (add_le_add hAbd hBbd) hCcbd
    _ = (C₀ + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder + C₁ * t) * (Q * G43) := by ring

end QIQTH.AnnulusAffineLeg

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AnnulusAffineLeg.invTpow_gaussDdim_le_narrow43
#print axioms QIQTH.AnnulusAffineLeg.gaussDdim_le_gaussDdim_narrow43
#print axioms QIQTH.AnnulusAffineLeg.parametrixCofactor_value_annulus43
#print axioms QIQTH.AnnulusAffineLeg.parametrixCofactor_deriv_annulus43
#print axioms QIQTH.AnnulusAffineLeg.cutoffResidual_annulus43_bound
