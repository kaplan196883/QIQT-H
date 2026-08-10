/-
  CurvedA1FintHFirstEnvSource — J4-573: SOURCING `hcrude`'s ON-GATE chart-image first-jet two-term
  envelope `hFirstEnv` (the LAST analytic carrier on `hcrude`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  J4-571 (`CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`)
  reduced the whole-space crude first-derivative envelope `hcrude` (consumed by
  `CurvedA1FintAdomSource.curved_hFint_hAdom_at_gate`) to three glued regions:

      • `z ∉ K`               — BANKED off-gate vanishing `witnessFieldDeriv_offGate_eq_zero`;
      • `z ∈ K`, `‖z‖ < r`    — the on-gate first-derivative wide transfer from `hFirstEnv`;
      • `z ∈ K`, `‖z‖ ≥ r`    — the far-field annulus envelope `hFar`  (SOURCED by J4-572).

  THIS file turns `hFirstEnv` — the ON-GATE (`z ∈ K`, `‖z‖ < r`) CHART-IMAGE first-jet TWO-TERM envelope

      `∀ i τ, 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < r →
          |witnessFieldDeriv g^K … (constGate … c) a b i τ 0 z|
            ≤ (A₀ + A₁·(rncRadialSq z / τ))·(√τ)⁻¹·gaussDdim τ (W₀ z)`,  `W₀ z := uniformInverseChart … z 0`

  from a WHOLE-CARRY into a THEOREM, discharged from the PROVED banked EXACT product-rule (Leibniz)
  decomposition `CConvV2WitnessStar.witnessFieldDeriv_productRule` plus the Cauchy–Schwarz numerator
  bound `CConvV2ChartComparison.numerator_le_radial_mul`, and a single genuinely-new SCALAR
  (per-point) near-isometry residual.

  ── THE SATISFIABILITY CORE (why the two-term envelope is TRUE for `g^K`).  The exact product rule
  gives `wfd = G·sc·A + G·∂A` at the field point `0`, `G = gaussDdim τ (W₀ z)`,
  `sc = −(∑ₖ (W₀ z)ₖ·Pvalₖ)/(2τ)`, `A = chartFieldAmp … 0`, `∂A = ∂ᵢ(chartFieldAmp …) 0`.
    •  AMPLITUDE leg  `G·|∂A| ≤ Bd·G`; supply the missing `(√τ)⁻¹` from `τ ≤ T`
       (`Bd ≤ Bd·√T·(√τ)⁻¹`) — the `A₀`-constant piece.
    •  GRADIENT leg  `G·|sc|·|A| ≤ (√n·L·Ba/2)·√(rncRadialSq(W₀ z))·τ⁻¹·G`.  The genuine Gaussian
       gradient factor is `√(rncRadialSq(W₀ z))/τ = √(rncRadialSq(W₀ z)/τ)·(√τ)⁻¹` — a `(√τ)⁻¹`
       prefactor times a `√(·/τ)` factor.  The pure `√x ≤ 1 + x` dominates the honest `√` by the
       INTEGER two-term shape `(1 + rncRadialSq(W₀ z)/τ)`; the two-sided near-isometry
       `rncRadialSq(W₀ z) ≤ 2·rncRadialSq z` (the UPPER companion of the banked LOWER coercivity
       `½·rncRadialSq z ≤ rncRadialSq(W₀ z)` carried by J4-572) bridges chart-image → base radius,
       giving the `A₁·(rncRadialSq z/τ)` term.
  Constants `A₀ := √n·L·Ba/2 + Bd·√T`, `A₁ := √n·L·Ba`.  The `(√τ)⁻¹` prefactor is kept VERBATIM
  (dropping it, or replacing `√(·/τ)` by a clean constant, is the FALSE bound — it blows up as `τ→0`).
  For `κ < 0 ⊂ κ ≠ 0`, `n ≥ 2` the witness is genuinely curved
  (`curvedRNCMetric_ricci_trace_diag_ne`), so this is NOT secretly flat.

  ── WHAT IS PROVED (axiom-free, no `sorry`).
    •  `curved_hFint_hFirstEnv_at_gate` — THE EXACT `hFirstEnv` binder consumed by
       `curved_hFint_hcrude_at_gate`, produced (existentially in `A₀`, `A₁`) from the banked product
       rule + numerator bound + the pure `√x ≤ 1+x`.
    •  `curved_hFint_hcrude_via_hFirstEnv_hFar_at_gate` — the demonstrator: the sourced `hFirstEnv`
       (+ the J4-572-sourced `hFar`) chained into `curved_hFint_hcrude_at_gate`, so the whole-space
       crude `hcrude` is now FULLY SOURCED modulo `{hlam4, the hdata-family carries}`.
    •  `curved_hFint_hFirstEnv_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── THE CARRIED RESIDUAL (scoped precisely).  Each satisfiable, none the conclusion:
    •  `hSopen`/`hgate0` — gate openness + the shared-centre activation `0 ∈ constGate … c z` (the SAME
       on-gate carries as J4-572 / `chartImage_approx_identity_final`).
    •  `hdata` — the per-`(i,τ,z)` inverse-chart Jacobian column bound `L`, amplitude value/derivative
       bounds `Ba`/`Bd`, AND the UPPER near-isometry `rncRadialSq(W₀ z) ≤ 2·rncRadialSq z` (the sibling
       of J4-572's LOWER coercivity `½·rncRadialSq z ≤ rncRadialSq(W₀ z)`; the two-sided
       `½·r ≤ r ≤ 2·r` near-isometry contemplated in `CConvV2Contracts`).  NOT provably false: at `z=0`
       both sides `0`; for the flat inverse chart `W₀ = id` it is `r ≤ 2r`.

  It does NOT make `a₁ = R/6` unconditional: `hlam4`, the `hdata`-family carries, `hsrc`,
  `hOffCollarTail`, the convergence trio, and `hInnerCont` all remain owed.  NOT `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintHFarSource

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCHeatOpDom2 QIQTH.WidthAdapters QIQTH.CurvedA1FintAdomSource
open QIQTH.CConvV2WitnessStar QIQTH.CConvV2ChartComparison
open QIQTH.CurvedA1FintHcrudeSource QIQTH.CurvedA1FintHFarSource
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintHFirstEnvSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (A) — THE ON-GATE CHART-IMAGE FIRST-JET TWO-TERM `hFirstEnv` BINDER FOR `g^K`.
    ############################################################################### -/

/-- **★★★ J4-573 — `curved_hFint_hFirstEnv_at_gate`.**  THE EXACT on-gate chart-image first-jet
    two-term envelope `hFirstEnv` consumed by `CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`,
    at the genuinely-curved witness `g^K = curvedRNCMetric κ`, SOURCED from the PROVED banked EXACT
    product-rule (Leibniz) decomposition `witnessFieldDeriv_productRule` + the Cauchy–Schwarz
    numerator bound `numerator_le_radial_mul`, with the honest Gaussian gradient factor
    `√(rncRadialSq(W₀ z)/τ)` dominated by the integer two-term shape via `√x ≤ 1 + x`, and the
    UPPER near-isometry `rncRadialSq(W₀ z) ≤ 2·rncRadialSq z` bridging chart-image → base radius.

    For the produced `A₀ := √n·L·Ba/2 + Bd·√T ≥ 0`, `A₁ := √n·L·Ba ≥ 0`,

    `∀ i τ, 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < r →
        |witnessFieldDeriv g^K … (constGate … c) a b i τ 0 z|
          ≤ (A₀ + A₁·(rncRadialSq z/τ))·(√τ)⁻¹·gaussDdim τ (W₀ z)`.

    ⚠ The `(√τ)⁻¹` prefactor is kept VERBATIM (dropping it — or replacing `√(·/τ)` by a clean
    constant — is the FALSE bound).  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFirstEnv_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            ≤ 2 * rncRadialSq z) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) := by
  refine ⟨Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T, Real.sqrt (n : ℝ) * L * Ba, ?_, ?_, ?_⟩
  · -- 0 ≤ A₀
    have h1 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * Ba :=
      mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)) hBa0
    have h2 : 0 ≤ Bd * Real.sqrt T := mul_nonneg hBd0 (Real.sqrt_nonneg _)
    linarith
  · -- 0 ≤ A₁
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hBa0
  · intro i τ hτ hτT z hzK hzr
    obtain ⟨Pval, hJetV, hJac, hAmp1, hBa, hBd, hUpper⟩ := hdata i τ hτ hτT z hzK hzr
    rw [witnessFieldDeriv_productRule (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ hτ z hzK
          (hSopen z hzK) (0 : Point n) (hgate0 z hzK) Pval hJetV hAmp1]
    set W := uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 with hWdef
    set G := gaussDdim τ W with hGdef
    set A := chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n) with hAdef
    set dA := pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
      with hdAdef
    set st := (Real.sqrt τ)⁻¹ with hstdef
    -- basic nonnegativities.
    have hτpos : (0 : ℝ) < 2 * τ := by linarith
    have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
    have hst : 0 ≤ st := inv_nonneg.mpr (Real.sqrt_nonneg τ)
    have hBa' : 0 ≤ Ba := le_trans (abs_nonneg _) hBa
    have hBd' : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
    -- the banked Cauchy–Schwarz numerator bound.
    have hnum : |∑ k, W k * Pval k| ≤ Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L) :=
      numerator_le_radial_mul W Pval L hL hJac
    -- the singular-factor absolute value.
    have habs_sc : |(-(∑ k, W k * Pval k) / (2 * τ))| = |∑ k, W k * Pval k| / (2 * τ) := by
      rw [abs_div, abs_neg, abs_of_pos hτpos]
    -- the gradient key: `√(rW)·τ⁻¹ ≤ (1 + rW/τ)·st`  (via `√x ≤ 1+x`).
    have hkey : Real.sqrt (rncRadialSq W) * τ⁻¹ ≤ (1 + rncRadialSq W / τ) * st := by
      have hy : (0 : ℝ) ≤ rncRadialSq W / τ := div_nonneg (rncRadialSq_nonneg W) hτ.le
      have hsq : Real.sqrt (rncRadialSq W / τ) ≤ 1 + rncRadialSq W / τ := by
        have h := Real.sqrt_le_sqrt
          (show rncRadialSq W / τ ≤ (1 + rncRadialSq W / τ) ^ 2 by
            nlinarith [sq_nonneg (rncRadialSq W / τ), hy])
        rwa [Real.sqrt_sq (by linarith)] at h
      have heq : Real.sqrt (rncRadialSq W / τ) = Real.sqrt (rncRadialSq W) * st := by
        rw [hstdef, div_eq_mul_inv, Real.sqrt_mul (rncRadialSq_nonneg W), Real.sqrt_inv]
      have hst2 : st * st = τ⁻¹ := by rw [hstdef, ← mul_inv, Real.mul_self_sqrt hτ.le]
      calc Real.sqrt (rncRadialSq W) * τ⁻¹
          = Real.sqrt (rncRadialSq W) * (st * st) := by rw [hst2]
        _ = (Real.sqrt (rncRadialSq W) * st) * st := by ring
        _ = Real.sqrt (rncRadialSq W / τ) * st := by rw [heq]
        _ ≤ (1 + rncRadialSq W / τ) * st := mul_le_mul_of_nonneg_right hsq hst
    -- the window normalizer `1 ≤ √T·st`.
    have hone : (1 : ℝ) ≤ Real.sqrt T * st := by
      rw [hstdef, ← div_eq_mul_inv, one_le_div (Real.sqrt_pos.mpr hτ)]
      exact Real.sqrt_le_sqrt hτT
    -- === GRADIENT leg (scalar) ===
    have h1 : |∑ k, W k * Pval k| / (2 * τ) * |A|
        ≤ (Real.sqrt (n : ℝ) * L / 2 * Ba) * st
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st := by
      have hinv0 : 0 ≤ (2 * τ)⁻¹ := inv_nonneg.mpr hτpos.le
      have hMnn : 0 ≤ Real.sqrt (n : ℝ) * L * Ba / 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hBa0) (by norm_num)
      calc |∑ k, W k * Pval k| / (2 * τ) * |A|
          = |∑ k, W k * Pval k| * (2 * τ)⁻¹ * |A| := by rw [div_eq_mul_inv]
        _ ≤ (Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L)) * (2 * τ)⁻¹ * Ba := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hnum hinv0) hBa (abs_nonneg _) ?_
            exact mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hL)) hinv0
        _ = (Real.sqrt (n : ℝ) * L * Ba / 2) * (Real.sqrt (rncRadialSq W) * τ⁻¹) := by
            rw [mul_inv]; ring
        _ ≤ (Real.sqrt (n : ℝ) * L * Ba / 2) * ((1 + rncRadialSq W / τ) * st) :=
            mul_le_mul_of_nonneg_left hkey hMnn
        _ ≤ (Real.sqrt (n : ℝ) * L * Ba / 2) * ((1 + 2 * rncRadialSq z / τ) * st) := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            refine mul_le_mul_of_nonneg_right ?_ hst
            have hbridge : rncRadialSq W / τ ≤ 2 * rncRadialSq z / τ := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hUpper (inv_nonneg.mpr hτ.le)
            linarith
        _ = (Real.sqrt (n : ℝ) * L / 2 * Ba) * st
              + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st := by ring
    -- === AMPLITUDE leg (scalar) ===
    have hd : |dA| ≤ Bd * Real.sqrt T * st := by
      calc |dA| ≤ Bd := hBd
        _ ≤ Bd * (Real.sqrt T * st) := le_mul_of_one_le_right hBd' hone
        _ = Bd * Real.sqrt T * st := by ring
    -- === the scalar prefactor bound ===
    have hpre : |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + |dA|
        ≤ ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st := by
      rw [habs_sc]
      calc |∑ k, W k * Pval k| / (2 * τ) * |A| + |dA|
          ≤ ((Real.sqrt (n : ℝ) * L / 2 * Ba) * st
                + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st)
              + Bd * Real.sqrt T * st := add_le_add h1 hd
        _ = ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
              + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st := by ring
    -- === combine (factor `G`) ===
    have eqL : |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A|
        = G * |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hGnn]
    have eqR : |G * dA| = G * |dA| := by rw [abs_mul, abs_of_nonneg hGnn]
    calc |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A + G * dA|
        ≤ |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A| + |G * dA| := abs_add_le _ _
      _ = G * |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + G * |dA| := by rw [eqL, eqR]
      _ = G * (|(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + |dA|) := by ring
      _ ≤ G * (((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st) :=
          mul_le_mul_of_nonneg_left hpre hGnn
      _ = ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st * G := by ring

/-! ###############################################################################
    ### (B) — DEMONSTRATOR: sourced `hFirstEnv` (+ sourced `hFar`) ⟹ whole-space `hcrude`.
    ############################################################################### -/

/-- **★★ J4-573 (demonstrator) — `curved_hFint_hcrude_via_hFirstEnv_hFar_at_gate`.**  The sourced
    on-gate `hFirstEnv` (§A) AND the J4-572-sourced far-field `hFar` chained into
    `CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`, producing the exact WHOLE-SPACE crude
    first-derivative `hcrude` census binder — proving `hcrude` is now FULLY SOURCED modulo
    `{hlam4, the hdata-family carries}` (both the off-gate vanishing and the on-gate width transfer
    are already PROVED inside `curved_hFint_hcrude_at_gate`; the on-gate first-jet envelope and the
    far-field annulus envelope are now BOTH theorems).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_hcrude_via_hFirstEnv_hFar_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hlam4 : 4 ≤ (curvedGate κ hChr hK).lam)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdataFar : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (hdataFirst : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            ≤ 2 * rncRadialSq z) :
    ∃ Ccrude wA : ℝ, 0 ≤ Ccrude ∧ 0 < wA ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wA * τ) (0 - z) := by
  obtain ⟨A₀, A₁, hA₀, hA₁, hFirstEnv⟩ :=
    curved_hFint_hFirstEnv_at_gate κ hChr hK a b c T L Ba Bd hL hBa0 hBd0 hSopen hgate0 hdataFirst
  obtain ⟨Cfar, hCfar, hFar⟩ :=
    curved_hFint_hFar_at_gate κ hChr hK a b c T L Ba Bd hL hBa0 hBd0 hlam4 hSopen hgate0 hdataFar
  exact curved_hFint_hcrude_at_gate κ hChr hK a b c T A₀ A₁ Cfar hA₀ hA₁ hCfar hFirstEnv hFar

/-! ###############################################################################
    ### (C) — the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-573 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the sourced `hFirstEnv`
    binder is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`; and the
    `(√τ)⁻¹` prefactor is what makes the two-term envelope TRUE (dropping it gives the FALSE clean
    bound).  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFirstEnv_at_gate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHFirstEnvSource

section AxiomChecks
open QIQTH.CurvedA1FintHFirstEnvSource
#print axioms curved_hFint_hFirstEnv_at_gate
#print axioms curved_hFint_hcrude_via_hFirstEnv_hFar_at_gate
#print axioms curved_hFint_hFirstEnv_at_gate_curved_satisfiable
end AxiomChecks
