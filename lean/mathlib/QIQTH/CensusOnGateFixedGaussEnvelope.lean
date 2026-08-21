/-
  CensusOnGateFixedGaussEnvelope — the τ-CAP FIXED-WIDTH Gaussian collapse (the genuine analytic core of
  carry **C3** of `censusBound_of_onGate_and_ballRate`, J4-947), plus the on-gate envelope assembly it
  feeds.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  REAL-ANALYSIS brick.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis,
  none equal to the conclusion, no existing banked file edited.

  ## THE PROBLEM (C3, precisely).  The J4-947 headline `censusBound_of_onGate_and_ballRate` is assembled
  modulo three carries; the genuine remaining analytic one is `honGate` (C3): on the census gate, off the
  ball `ρ ≤ ‖z‖`, the concrete integrand `|deriv(fun r ↦ vanVleckGatedWitness … r 0 z)(a−s) · F s z 0|`
  must be dominated by a SINGLE FIXED-WIDTH Gaussian `Cenv · gaussDdim lam z` — with `Cenv`, `lam` UNIFORM
  in `(s,a)`, i.e. uniform as `τ := a − s ↓ 0`.

  ## THE SUBTLE POINT (sympy-verified, discipline).  The banked crude time-derivative envelope
  (`WitnessTimeDerivEnvelope.witnessTimeDeriv_domination_global`) gives
      `|deriv(τ)| ≤ C · τ⁻¹ · gaussDdim (4·D.lam·τ) z` ,
  a `τ`-DEPENDENT Gaussian whose WIDTH shrinks with `τ`.  Its `sup` over `τ ∈ (0,τ₀]` does NOT decay like
  a fixed Gaussian: at the interior maximiser `τ* = r²/(2w(n+2))` the value `~ r^{−(n+2)}` is only
  POLYNOMIAL in `r = ‖z‖`.  A single fixed-width Gaussian could therefore NOT dominate the τ-family — WERE
  `τ` unbounded.  It IS rescued, cleanly and GLOBALLY in `z`, by the **τ-cap** `τ ≤ τ₀`: the interior
  maximiser exceeds `τ₀` once `r² > 2 w (n+2) τ₀`, so beyond a FIXED radius the sup reverts to the boundary
  `τ = τ₀`, where the decay is genuinely Gaussian `exp(−r²/(4 w τ₀))`.  The single clean inequality below
  captures both regimes at once via the exponent split `exp(−r²/4wτ) = exp(−r²/8wτ)·exp(−r²/8wτ)`:
  one half is bounded by the fixed Gaussian `exp(−r²/(4·lam))` (any `lam ≥ 2 w τ₀`, using `τ ≤ τ₀`), the
  other absorbs the `τ⁻¹·τ^{−n/2}` prefactor growth via the elementary sup `yᵏ·e^{−by²} ≤ 1 + k!/bᵏ`
  (`b = ρ²/8w`, `y = τ^{−1/2}`, `k = n+2`).  So NO compactness of `K` is needed — the τ-cap does all the
  work.

  ## WHAT LANDS.
    • `pow_mul_exp_negSq_le` — ★ the elementary Gaussian-moment sup `yᵏ·exp(−(b·y²)) ≤ 1 + k!/bᵏ`
        (`b > 0`, `y ≥ 0`), from the banked linear sup `pow_mul_exp_neg_le_factorial_div` + the `y²≥y`
        trick on `y ≥ 1` and the trivial `y ≤ 1` bound.
    • `tauInv_gaussWidth_le_fixedGauss` — ★★★ THE τ-CAP FIXED-WIDTH COLLAPSE: for `w,τ₀,ρ > 0` and any
        `lam ≥ 2·w·τ₀`, an EXPLICIT `Cenv > 0` with, uniformly over `0 < τ ≤ τ₀` and every `z` with
        `ρ ≤ ‖z‖`,  `τ⁻¹ · gaussDdim (w·τ) z ≤ Cenv · gaussDdim lam z`.
    • `censusOnGate_fixedGauss_of_crudeEnv` — ★★ the C3 SHAPE: composing a crude time-derivative envelope
        hypothesis (`|deriv(τ)| ≤ C·τ⁻¹·gaussDdim(w·τ)z`, the banked `witnessTimeDeriv_domination_global`
        conclusion) and a uniform F-factor bound (`|F s z 0| ≤ M_F`) with the collapse yields EXACTLY the
        `honGate` type `|deriv(τ)·F s z 0| ≤ Cenv·gaussDdim lam z`.
    • non-vacuity witnesses for both headline theorems (genuine `w,τ₀,ρ > 0`, `lam = 2wτ₀`; a genuine
        nonzero crude envelope and F-factor).

  ## HONEST STATUS.  This DISCHARGES the uniform-in-τ single-fixed-Gaussian domination sub-item of C3 — the
  piece J4-947 flagged as "dominating the two-term closed form by a single Gaussian in the ORIGINAL
  coordinate `z`, uniform as τ↓0".  The chart-coercivity `‖W z 0‖ ≳ ‖z‖` worry is ALREADY discharged
  upstream: the banked crude envelope is already a Gaussian in the BASE coordinate `z` (via the
  `FixedFlowGateData.poly_absorb` base transfer inside `witnessTimeDeriv_domination`).  So C3 reduces to
  {the crude time-derivative envelope (banked, ITSELF modulo the amplitude carries
  `hAmp0`/`hgate`/`hCfield`), a uniform F-factor bound}.  It is NOT reduced to `{G2, G3}` alone: the
  amplitude sup-bounds are a separate class.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussianWidthTransfer
import QIQTH.InverseChartDisplacement

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.GaussianWidthTransfer QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.CensusOnGateFixedGaussEnvelope

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the elementary Gaussian-moment sup `yᵏ·exp(−b·y²) ≤ 1 + k!/bᵏ`.
    ############################################################################### -/

/-- **★ `pow_mul_exp_negSq_le`.**  For `b > 0`, `y ≥ 0`, `k : ℕ`,
        `yᵏ · exp(−(b·y²)) ≤ 1 + k!/bᵏ` .
    On `y ≤ 1` the LHS is `≤ 1`; on `y ≥ 1` we have `y² ≥ y`, so `exp(−b·y²) ≤ exp(−b·y)` and the banked
    linear sup `pow_mul_exp_neg_le_factorial_div` gives `yᵏ·exp(−b·y) ≤ k!/bᵏ`.  NOT `a₁ = R/6`. -/
theorem pow_mul_exp_negSq_le {b : ℝ} (hb : 0 < b) (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ k * Real.exp (-(b * y ^ 2)) ≤ 1 + (Nat.factorial k : ℝ) / b ^ k := by
  have hfac : (0 : ℝ) ≤ (Nat.factorial k : ℝ) / b ^ k :=
    div_nonneg (by exact_mod_cast (Nat.factorial_pos k).le) (pow_pos hb k).le
  rcases le_total y 1 with hy1 | hy1
  · -- `y ≤ 1`: `yᵏ ≤ 1`, `exp(−·) ≤ 1`.
    have hyk : y ^ k ≤ 1 := pow_le_one₀ hy hy1
    have hexp : Real.exp (-(b * y ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
    calc y ^ k * Real.exp (-(b * y ^ 2))
        ≤ 1 * 1 := mul_le_mul hyk hexp (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
      _ ≤ 1 + (Nat.factorial k : ℝ) / b ^ k := by linarith
  · -- `y ≥ 1`: `y² ≥ y`, so `exp(−b·y²) ≤ exp(−b·y)`; then the linear sup.
    have hyy : y ≤ y ^ 2 := by nlinarith
    have hexp_le : Real.exp (-(b * y ^ 2)) ≤ Real.exp (-(b * y)) := by
      apply Real.exp_le_exp.mpr
      have : b * y ≤ b * y ^ 2 := mul_le_mul_of_nonneg_left hyy hb.le
      linarith
    have hlin := pow_mul_exp_neg_le_factorial_div hb k hy
    calc y ^ k * Real.exp (-(b * y ^ 2))
        ≤ y ^ k * Real.exp (-(b * y)) :=
          mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hy k)
      _ ≤ (Nat.factorial k : ℝ) / b ^ k := hlin
      _ ≤ 1 + (Nat.factorial k : ℝ) / b ^ k := by linarith

/-! ###############################################################################
    ### §B — THE τ-CAP FIXED-WIDTH COLLAPSE.
    ############################################################################### -/

/-- **★★★ `tauInv_gaussWidth_le_fixedGauss` — the τ-cap fixed-width Gaussian collapse.**  For `w, τ₀, ρ > 0`
    and any `lam ≥ 2·w·τ₀`, there is an EXPLICIT `Cenv > 0` such that, uniformly over `0 < τ ≤ τ₀` and
    every `z : Point n` with `ρ ≤ ‖z‖`,
        `τ⁻¹ · gaussDdim (w·τ) z ≤ Cenv · gaussDdim lam z` .
    The dominating Gaussian has FIXED width `lam` (independent of `τ`), collapsing the `τ`-scaled-width
    family `gaussDdim (w·τ)` uniformly across `τ ↓ 0`.  Route: split `exp(−r²/4wτ)` in two; the `τ ≤ τ₀`
    cap sends one half under the fixed `exp(−r²/4lam)` (`lam ≥ 2wτ₀`), the other absorbs the
    `τ⁻¹·τ^{−n/2} = ((√τ)⁻¹)^{n+2}` prefactor growth against `exp(−ρ²/8wτ)` via `pow_mul_exp_negSq_le`
    (`b = ρ²/8w`, `y = (√τ)⁻¹`, `k = n+2`), using `ρ² ≤ ‖z‖² ≤ r²`.  NOT `a₁ = R/6`. -/
theorem tauInv_gaussWidth_le_fixedGauss
    (w τ₀ ρ lam : ℝ) (hw : 0 < w) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ)
    (hlamge : 2 * w * τ₀ ≤ lam) :
    ∃ Cenv : ℝ, 0 < Cenv ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, ρ ≤ ‖z‖ →
      τ⁻¹ * gaussDdim (w * τ) z ≤ Cenv * gaussDdim lam z := by
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hlamge
  set b : ℝ := ρ ^ 2 / (8 * w) with hbdef
  have hb : 0 < b := by rw [hbdef]; positivity
  -- the elementary moment sup constant.
  set M : ℝ := 1 + (Nat.factorial (n + 2) : ℝ) / b ^ (n + 2) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; positivity
  -- the assembled uniform constant.
  set Cenv : ℝ := (Real.sqrt (4 * Real.pi * w))⁻¹ ^ n * M * (Real.sqrt (4 * Real.pi * lam)) ^ n
    with hCenvdef
  have hCpos : 0 < Cenv := by
    rw [hCenvdef]
    apply mul_pos (mul_pos (pow_pos (by positivity) n) hMpos)
    exact pow_pos (Real.sqrt_pos.mpr (by positivity)) n
  refine ⟨Cenv, hCpos, ?_⟩
  intro τ hτ hττ₀ z hznorm
  have hwτ : 0 < w * τ := mul_pos hw hτ
  set r2 : ℝ := rncRadialSq z with hr2def
  have hr2nn : 0 ≤ r2 := rncRadialSq_nonneg z
  -- `ρ² ≤ ‖z‖² ≤ r²`.
  have hρr2 : ρ ^ 2 ≤ r2 := by
    have h1 : ρ ^ 2 ≤ ‖z‖ ^ 2 := by
      apply pow_le_pow_left₀ hρ.le hznorm
    exact le_trans h1 (QIQTH.HeatResidualBound.norm_sq_le_rncRadialSq z)
  -- closed forms.
  rw [gaussDdim_closed (w * τ) z, gaussDdim_closed lam z, ← hr2def]
  -- split the source exponent in half.
  have hsplit : Real.exp (-r2 / (4 * (w * τ)))
      = Real.exp (-r2 / (8 * (w * τ))) * Real.exp (-r2 / (8 * (w * τ))) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  -- the τ-cap half: `exp(−r²/8wτ) ≤ exp(−r²/4lam)`.
  have h8wτ : 8 * (w * τ) ≤ 4 * lam := by
    nlinarith [hlamge, hw.le, hττ₀, mul_le_mul_of_nonneg_left hττ₀ hw.le]
  have hcaphalf : Real.exp (-r2 / (8 * (w * τ))) ≤ Real.exp (-r2 / (4 * lam)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  -- rewrite the prefactor `(√(4πwτ))⁻¹^n = (√(4πw))⁻¹^n·(√τ)⁻¹^n`.
  have hpre : (Real.sqrt (4 * Real.pi * (w * τ)))⁻¹ ^ n
      = (Real.sqrt (4 * Real.pi * w))⁻¹ ^ n * (Real.sqrt τ)⁻¹ ^ n := by
    rw [show 4 * Real.pi * (w * τ) = (4 * Real.pi * w) * τ by ring,
        Real.sqrt_mul (by positivity), mul_inv, mul_pow]
  -- the prefactor·τ⁻¹ collapses to `((√τ)⁻¹)^{n+2}` up to the `(√(4πw))⁻¹^n` constant.
  set y : ℝ := (Real.sqrt τ)⁻¹ with hydef
  have hynn : 0 ≤ y := by rw [hydef]; positivity
  have hτsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
  have hy2 : y ^ 2 = τ⁻¹ := by
    rw [hydef, inv_pow, hτsq]
  -- `τ⁻¹ · (√τ)⁻¹^n = y^(n+2)`.
  have hcollapse : τ⁻¹ * (Real.sqrt τ)⁻¹ ^ n = y ^ (n + 2) := by
    rw [← hy2, ← hydef, pow_add]; ring
  -- the moment sup applied at `k = n+2`, `b`, `y`.
  have hmom := pow_mul_exp_negSq_le (b := b) hb (n + 2) hynn
  -- express `exp(−r²/8wτ) ≤ exp(−ρ²/8wτ) = exp(−(b·y²))`.
  have hexp_rho : Real.exp (-r2 / (8 * (w * τ))) ≤ Real.exp (-(b * y ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have e : b * y ^ 2 = ρ ^ 2 / (8 * (w * τ)) := by
      rw [hy2, hbdef]; field_simp
    rw [e, neg_div, neg_le_neg_iff]
    gcongr
  -- the moment factor is `≤ M`.
  have hXM : y ^ (n + 2) * Real.exp (-r2 / (8 * (w * τ))) ≤ M :=
    le_trans (mul_le_mul_of_nonneg_left hexp_rho (pow_nonneg hynn _)) hmom
  -- abbreviations for the constant prefactors.
  set A : ℝ := (Real.sqrt (4 * Real.pi * w))⁻¹ ^ n with hAdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hcancel : (Real.sqrt (4 * Real.pi * lam)) ^ n * (Real.sqrt (4 * Real.pi * lam))⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (Real.sqrt_pos.mpr (by positivity)).ne', one_pow]
  -- the assembly.
  calc τ⁻¹ * ((Real.sqrt (4 * Real.pi * (w * τ)))⁻¹ ^ n * Real.exp (-r2 / (4 * (w * τ))))
      = A * (y ^ (n + 2) * Real.exp (-r2 / (8 * (w * τ)))) * Real.exp (-r2 / (8 * (w * τ))) := by
        rw [hpre, hsplit, ← hcollapse]; ring
    _ ≤ A * M * Real.exp (-r2 / (4 * lam)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hXM hAnn) hcaphalf (Real.exp_pos _).le
          (mul_nonneg hAnn hMpos.le)
    _ = Cenv * ((Real.sqrt (4 * Real.pi * lam))⁻¹ ^ n * Real.exp (-r2 / (4 * lam))) := by
        rw [hCenvdef]
        calc A * M * Real.exp (-r2 / (4 * lam))
            = A * M
                * ((Real.sqrt (4 * Real.pi * lam)) ^ n * (Real.sqrt (4 * Real.pi * lam))⁻¹ ^ n)
                * Real.exp (-r2 / (4 * lam)) := by rw [hcancel]; ring
          _ = A * M * (Real.sqrt (4 * Real.pi * lam)) ^ n
                * ((Real.sqrt (4 * Real.pi * lam))⁻¹ ^ n * Real.exp (-r2 / (4 * lam))) := by ring

/-! ###############################################################################
    ### §C — the C3 SHAPE: crude time-derivative envelope × F-factor bound ⟹ fixed-Gaussian domination.
    ############################################################################### -/

/-- **★★ `onGate_gauss_of_crude_and_bound` — the `honGate` (C3) shape.**  Abstract in the derivative
    factor `Dz` (the role of `deriv(fun r ↦ vanVleckGatedWitness … r 0 z)(a−s)`) and the Levi factor
    `Ffac` (the role of `F s z 0`).  Given the CRUDE `τ`-scaled Gaussian envelope
    `|Dz z| ≤ C·τ⁻¹·gaussDdim (w·τ) z` (exactly the banked `witnessTimeDeriv_domination_global`
    conclusion, `w = 4·D.lam`) and a UNIFORM off-ball F-factor bound `|Ffac z| ≤ MF`, and `lam ≥ 2·w·τ₀`,
    the product is dominated by a SINGLE FIXED-WIDTH Gaussian `Cenv·gaussDdim lam z`, uniformly for
    `ρ ≤ ‖z‖` — EXACTLY the `honGate` shape `censusBound_of_onGate_and_ballRate` (J4-947) consumes.  The
    `τ`-cap collapse `tauInv_gaussWidth_le_fixedGauss` supplies the uniform-in-`τ` fixed Gaussian.  NOT
    `a₁ = R/6`. -/
theorem onGate_gauss_of_crude_and_bound
    (w τ₀ ρ lam : ℝ) (hw : 0 < w) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ) (hlamge : 2 * w * τ₀ ≤ lam)
    (Dz Ffac : Point n → ℝ) (C MF : ℝ) (hC : 0 ≤ C) (hMF : 0 ≤ MF)
    (τ : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (hcrude : ∀ z : Point n, |Dz z| ≤ C * τ⁻¹ * gaussDdim (w * τ) z)
    (hF : ∀ z : Point n, ρ ≤ ‖z‖ → |Ffac z| ≤ MF) :
    ∃ Cenv : ℝ, 0 ≤ Cenv ∧ ∀ z : Point n, ρ ≤ ‖z‖ →
      |Dz z * Ffac z| ≤ Cenv * gaussDdim lam z := by
  obtain ⟨Ce, hCe, hb⟩ := tauInv_gaussWidth_le_fixedGauss (n := n) w τ₀ ρ lam hw hτ₀ hρ hlamge
  refine ⟨C * MF * Ce, mul_nonneg (mul_nonneg hC hMF) hCe.le, ?_⟩
  intro z hz
  have hgw : 0 ≤ gaussDdim (w * τ) z := gaussDdim_nonneg _ _
  have hcnn : 0 ≤ C * τ⁻¹ * gaussDdim (w * τ) z :=
    mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hτ.le)) hgw
  calc |Dz z * Ffac z|
      = |Dz z| * |Ffac z| := abs_mul _ _
    _ ≤ (C * τ⁻¹ * gaussDdim (w * τ) z) * MF :=
        mul_le_mul (hcrude z) (hF z hz) (abs_nonneg _) hcnn
    _ = C * MF * (τ⁻¹ * gaussDdim (w * τ) z) := by ring
    _ ≤ C * MF * (Ce * gaussDdim lam z) :=
        mul_le_mul_of_nonneg_left (hb τ hτ hττ₀ z hz) (mul_nonneg hC hMF)
    _ = (C * MF * Ce) * gaussDdim lam z := by ring

/-! ###############################################################################
    ### §D — non-vacuity (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of `tauInv_gaussWidth_le_fixedGauss`.**  Genuine strictly-positive data
    `w = τ₀ = 1`, `ρ = 1`, `lam = 2 = 2·w·τ₀` and a witness point `z` with `1 ≤ ‖z‖` at which BOTH sides
    are strictly positive (the bound is non-trivially exercised, not a `0 ≤ 0`).  NOT `a₁ = R/6`. -/
theorem tauInv_gaussWidth_le_fixedGauss_teeth (hn : 0 < n) :
    ∃ (w τ₀ ρ lam : ℝ) (z : Point n),
      0 < w ∧ 0 < τ₀ ∧ 0 < ρ ∧ 2 * w * τ₀ ≤ lam ∧ ρ ≤ ‖z‖ ∧
      0 < (1 : ℝ)⁻¹ * gaussDdim (w * 1) z ∧ 0 < gaussDdim lam z := by
  refine ⟨1, 1, 1, 2, (fun _ => (1 : ℝ)), one_pos, one_pos, one_pos, by norm_num,
    ?_, ?_, ?_⟩
  · -- `‖(fun _ ↦ 1)‖ = 1 ≥ ρ = 1` (sup norm on `Point n`, `n > 0`).
    have hle : (1 : ℝ) ≤ ‖(fun _ => (1 : ℝ) : Point n)‖ := by
      have := norm_le_pi_norm (fun _ => (1 : ℝ) : Point n) ⟨0, hn⟩
      simpa using this
    exact hle
  · simpa using QIQTH.LeviSeries.gaussDdim_pos (1 * 1) (by norm_num) (fun _ => (1 : ℝ))
  · exact QIQTH.LeviSeries.gaussDdim_pos 2 (by norm_num) (fun _ => (1 : ℝ))

/-- **Non-vacuity of `onGate_gauss_of_crude_and_bound` — TEETH.**  A GENUINE nonzero integrand:
    `Dz := gaussDdim 1` (nonzero), `Ffac ≡ 1`, `C = MF = 1`, `w = τ₀ = ρ = 1`, `lam = 2`, `τ = 1`.  The
    crude envelope holds with EQUALITY (`|gaussDdim 1 z| = 1·1⁻¹·gaussDdim 1 z`) and the F-bound with
    equality, so the hypotheses are genuinely met while the product `Dz z · Ffac z = gaussDdim 1 z` is
    strictly positive — the domination is non-trivially exercised.  NOT `a₁ = R/6`. -/
theorem onGate_gauss_of_crude_and_bound_teeth (hn : 0 < n) :
    ∃ (w τ₀ ρ lam : ℝ) (Dz Ffac : Point n → ℝ) (C MF τ : ℝ),
      0 < w ∧ 0 < τ₀ ∧ 0 < ρ ∧ 2 * w * τ₀ ≤ lam ∧ 0 ≤ C ∧ 0 ≤ MF ∧ 0 < τ ∧ τ ≤ τ₀ ∧
      (∀ z : Point n, |Dz z| ≤ C * τ⁻¹ * gaussDdim (w * τ) z) ∧
      (∀ z : Point n, ρ ≤ ‖z‖ → |Ffac z| ≤ MF) ∧
      (∃ z : Point n, ρ ≤ ‖z‖ ∧ 0 < |Dz z * Ffac z|) := by
  refine ⟨1, 1, 1, 2, gaussDdim (1 : ℝ), (fun _ => (1 : ℝ)), 1, 1, 1,
    one_pos, one_pos, one_pos, by norm_num, zero_le_one, zero_le_one, one_pos, le_refl _,
    ?_, ?_, ?_⟩
  · intro z
    rw [abs_of_nonneg (gaussDdim_nonneg _ _)]
    simp
  · intro z _; simp
  · refine ⟨(fun _ => (1 : ℝ)), ?_, ?_⟩
    · have := norm_le_pi_norm (fun _ => (1 : ℝ) : Point n) ⟨0, hn⟩
      simpa using this
    · rw [mul_one, abs_of_nonneg (gaussDdim_nonneg _ _)]
      exact QIQTH.LeviSeries.gaussDdim_pos 1 one_pos _

end QIQTH.CensusOnGateFixedGaussEnvelope

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.CensusOnGateFixedGaussEnvelope
#print axioms pow_mul_exp_negSq_le
#print axioms tauInv_gaussWidth_le_fixedGauss
#print axioms onGate_gauss_of_crude_and_bound
#print axioms tauInv_gaussWidth_le_fixedGauss_teeth
#print axioms onGate_gauss_of_crude_and_bound_teeth
end AxiomChecks
