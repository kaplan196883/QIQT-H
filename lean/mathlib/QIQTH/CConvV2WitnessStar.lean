/-
  CConvV2WitnessStar — J4-326 (facade-v2 bricks 8+9 of 14): THE ANALYTIC HEART.  The product-rule
  decomposition of the van-Vleck gated witness field-derivative (brick 8) + the concrete `(⋆)`
  Gaussian-gradient domination (brick 9), landing at the HONEST width `4(t−s)`.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It packages
  the chart geometry (banked in `CConvV2ChartComparison`) + the raw witness product-rule (banked in
  `EngineInstantiation`) into the concrete `(⋆)` witness-gradient bound the v2 facade consumes.  NO
  `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis
  in this file's OWN theorems.  No existing file is edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (S0) THE TWO VERDICTS (recon per feedback_dont_undercredit_repo — grepped HARD).

  ### VERDICT 1 — the banked decomposition.  `witnessFieldDeriv` (`EngineInstantiation.lean`, in
  `QIQTH.HeatResidualBound`) is `def … := pd (fun x' ↦ vanVleckGatedWitness … τ x' z) i p`.  The bank
  ALREADY carries its on-gate PRODUCT-RULE decomposition — `witnessFieldDeriv_gate_eq`:
      witnessFieldDeriv … i τ p z
        = G · (−(∑ₖ Wₖ·Pvalₖ)/(2τ)) · A   +   G · ∂ᵢA,
      G := gaussDdim τ (W z p),  W := uniformInverseChart,  Pvalₖ = ∂ᵢ Wₖ,  A := chartFieldAmp,
  valid on the field gate (`z ∈ K`, `p ∈ S z`, `0 < τ`).  Brick 8 is thereby a RE-EXPORT
  (`witnessFieldDeriv_productRule`), NOT a re-derivation.  The bank's `witnessFieldDeriv_gate_abs_le`
  / `…_gate_envelope_coercive` bound this by `G·(Bs·Ba+Bd)` with a CONSTANT `Bs` bounding the FULL
  quotient `|(∑ₖWₖPvalₖ)/(2τ)|` — that constant `Bs` IS the adjudicated-false conjunct (it bakes the
  `1/(2τ)→∞` blow-up into a constant).  Brick 9 keeps the log-gradient factor EXPLICIT and routes it
  through the C4 transfer (`CConvV2ChartComparison`) to expose the TRUE `(t−s)^{−1/2}` cost.

  ### VERDICT 2 — THE WIDTH (resolved: the HONEST WIDE route `4(t−s)`).
  The banked transfer `chart_gradient_gaussDdim_transfer_half` lands at `gaussDdim (4τ) z` (the field-
  centre near-isometry gives only the coercivity `c₀ = ½`, `½·r²_z ≤ r²_{W z p}`, whose transfer width
  is `2τ/c₀ = 4τ`).  The banked contract `CConvWitnessEnvelopeDataV2.hStar` pins `gaussDdim (2(t−s)) z`
  (would need `c₀ = 1`, i.e. an EXACT isometry — unobtainable off-centre; the near-isometry degrades).
  So the CONCRETE witness satisfies the strictly-wider form
      `|witnessFieldDeriv| ≤ C · (t−s)^{−1/2} · gaussDdim (4(t−s)) z`  ( `(⋆)`-WIDE, width `4(t−s)` ).
  The v2 CONTRACT (`CConvV2Contracts.hStar`) stays BANKED at `2(t−s)`; the downstream consumers
  (bricks 12/13/14) will consume the WIDE legs proved here (all their arguments are width-uniform —
  `gaussDdim (4·)` is still `z`-integrable, `(t−s)^{−1/2}` still `s`-integrable, and the pairing lower
  bound `a+b ≥ (min 4 cF)·t` on `Ioc 0 t` still holds).  `gaussDdim (4τ)` has WEAKER decay than
  `gaussDdim (2τ)` — this is an HONEST widening, not a strengthening.  (The `ε`-shrink alternative from
  `chartW0_rncRadialSq_error` gives width `2(1+ε)(t−s) ≠ 2` exactly, so the wide route stands
  regardless; not chased.)

  ## WHAT THIS FILE LANDS.
    • (S1, brick 8) `witnessFieldDeriv_productRule` — the RE-EXPORT of the banked on-gate product-rule.
    • (S2)         `gaussDdim_ampWiden4` — `½·r²_z ≤ r²_w ⟹ gaussDdim τ w ≤ 2ⁿ·gaussDdim (4τ) z`
                   (the amplitude-leg widening, via banked `Gk_anti`+`Gk_scaled` at `s = ¼`);
                   `sqrtInv_eq_rpow` — `(√τ)⁻¹ = τ^{−1/2}` (the rpow bookkeeping).
    • (S3, brick 9) `witnessFieldDeriv_starWide_onGate` — ★ THE `(⋆)`-WIDE per-point on-gate bound
                   (product-rule + numerator Cauchy–Schwarz + β1 transfer + amplitude widening);
                   `hStarWide_concrete` — the `(⋆)`-WIDE existential over the interior window `Ioo 0 t`
                   (off-gate `z ∉ K` branch vanishes; on-gate branch = the per-point bound).
    • (S4)         `sourcePairWide_of_gaussian_bound` / `hFpairWide` , `envelope_integrable_v2Wide` ,
                   `pointwise_domWide` — the width-`4(t−s)` analogs of the J4-323/324 downstream legs.

  The honest carried hypotheses of brick 9 (each SATISFIABLE, none the conclusion): the general-field-
  point coercivity `hmin` (`= hmin` of `witnessFieldDeriv_gate_envelope_coercive`), the inverse-chart
  Jacobian column bound `L` (`hJac`), and the amplitude value/derivative bounds `Ba`/`Bd` (the
  SATISFIABLE survivors of the old `hGateData` — continuity of `chartFieldAmp` on the on-gate compact).

  NOT `a₁ = R/6`.
-/
import QIQTH.CConvV2ChartComparison
import QIQTH.CConvV2EnvelopeFromStar
import QIQTH.CConvV2GaussianPairing
import QIQTH.EngineInstantiation

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.ExpMap
open QIQTH.CConvV2ChartComparison QIQTH.CConvV2Contracts
open scoped Topology BigOperators ContDiff

namespace QIQTH.CConvV2WitnessStar

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §S2a — the rpow bookkeeping `(√τ)⁻¹ = τ^{−1/2}`.
    ############################################################################### -/

/-- **`sqrtInv_eq_rpow`.**  `(√τ)⁻¹ = τ^{−1/2}` for `τ ≥ 0`.  Converts the `(√τ)⁻¹` form of the banked
    transfer (`chart_gradient_gaussDdim_transfer_half`) into the `(t−s)^{−1/2}` rpow the v2 facade's
    `hStar` shape is written in.  NOT `a₁ = R/6`. -/
theorem sqrtInv_eq_rpow (τ : ℝ) (hτ : 0 ≤ τ) : (Real.sqrt τ)⁻¹ = τ ^ (-(1 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ]
  norm_num

/-! ###############################################################################
    ### §S2b — the amplitude-leg widening `gaussDdim τ w ≤ 2ⁿ·gaussDdim (4τ) z`.
    ############################################################################### -/

/-- **`gaussDdim_ampWiden4`.**  From the field-centre coercivity `½·r²_z ≤ r²_w` (hence also
    `¼·r²_z ≤ r²_w`), the amplitude-leg (NO `τ⁻¹` factor) Gaussian widens to width `4τ` with the clean
    constant `2ⁿ`:
        `gaussDdim τ w ≤ 2ⁿ · gaussDdim (4τ) z`.
    Route (banked): `gaussDdim_eq_Gk` + `Gk_anti` (radial antitonicity `r²_w ≥ ¼·r²_z`) +
    `Gk_scaled` at `s = ¼` (`(√¼)⁻ⁿ = 2ⁿ`, width `τ/¼ = 4τ`).  The amplitude leg has no intrinsic
    `τ^{−1/2}` singularity; brick 9 supplies the missing `τ^{−1/2}` from the window bound `τ ≤ t`
    (`gaussDdim (4τ) z ≤ √t · τ^{−1/2} · gaussDdim (4τ) z`).  NOT `a₁ = R/6`. -/
theorem gaussDdim_ampWiden4 (τ : ℝ) (hτ : 0 < τ) (w z : Point n)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq w) :
    gaussDdim τ w ≤ (2 : ℝ) ^ n * gaussDdim (4 * τ) z := by
  have hmin4 : (1 / 4 : ℝ) * rncRadialSq z ≤ rncRadialSq w := by
    nlinarith [rncRadialSq_nonneg z, hmin]
  rw [gaussDdim_eq_Gk]
  have hanti : Gk n τ (rncRadialSq w) ≤ Gk n τ ((1 / 4 : ℝ) * rncRadialSq z) :=
    Gk_anti τ hτ hmin4
  have hscaled : Gk n τ ((1 / 4 : ℝ) * rncRadialSq z)
      = (Real.sqrt (1 / 4))⁻¹ ^ n * gaussDdim (τ / (1 / 4)) z :=
    Gk_scaled (1 / 4) τ (by norm_num) hτ z
  have hpref : (Real.sqrt (1 / 4 : ℝ))⁻¹ ^ n = (2 : ℝ) ^ n := by
    rw [show (1 / 4 : ℝ) = (2⁻¹) ^ 2 by norm_num, Real.sqrt_sq (by norm_num), inv_inv]
  have hw : (τ / (1 / 4 : ℝ)) = 4 * τ := by ring
  rw [hscaled, hpref, hw] at hanti
  exact hanti

/-! ###############################################################################
    ### §S1 (brick 8) — the RE-EXPORT of the banked on-gate product rule.
    ############################################################################### -/

/-- **★ (S1, brick 8) `witnessFieldDeriv_productRule`.**  The RE-EXPORT of the banked on-gate product-
    rule decomposition (`EngineInstantiation.witnessFieldDeriv_gate_eq`).  On the field gate
    (`z ∈ K`, `p ∈ S z`, `0 < τ`), with the chart Jacobian column `Pval` (`hJetV`) and amplitude field-
    differentiability (`hAmp1`),
        `witnessFieldDeriv … i τ p z
           = gaussDdim τ (W z p) · (−(∑ₖ (W z p)ₖ·Pvalₖ)/(2τ)) · chartFieldAmp … p
             + gaussDdim τ (W z p) · ∂ᵢ(chartFieldAmp …) p`,
    `W := uniformInverseChart`.  The Leibniz split `∂(G∘chart · A) = (∂ log G)·G·A + G·∂A` with the
    `Pval` column feeding `∂ log G = −(∑ₖ Wₖ Pvalₖ)/(2τ)`.  This is the exact decomposition brick 9
    dominates factor-by-factor.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_productRule (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update p i r) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p) :
    witnessFieldDeriv g gi hC hK S a b i τ p z
      = gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * (-(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ))
          * chartFieldAmp g gi hC hK a b τ z p
        + gaussDdim τ (uniformInverseChart g gi hC hK z p)
          * pd (chartFieldAmp g gi hC hK a b τ z) i p :=
  witnessFieldDeriv_gate_eq g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1

/-! ###############################################################################
    ### §S3 (brick 9) — the `(⋆)`-WIDE per-point on-gate bound (THE ANALYTIC HEART).
    ############################################################################### -/

/-- **★★★ (S3, brick 9) `witnessFieldDeriv_starWide_onGate`.**  THE concrete `(⋆)`-WIDE Gaussian-
    gradient domination of the witness field-derivative, on the field gate, at width `4τ`:
        `|witnessFieldDeriv … i τ p z|
           ≤ (½·√n·L·(√2·2ⁿ)·Ba + 2ⁿ·Bd·√t) · τ^{−1/2} · gaussDdim (4τ) z`,
    for `0 < τ ≤ t`.  Assembly (S0 verdict 1 + the banked C-layer):
      (1) product rule (S1)  →  `|·| ≤ G·|sc|·|A| + G·|∂A|`, `sc = −(∑ₖWₖPvalₖ)/(2τ)`;
      (2) GRADIENT leg  `G·|sc|·|A| = ½·|∑ₖWₖPvalₖ|·τ⁻¹·G·|A|` — bound `|∑ₖWₖPvalₖ| ≤ √(r²_W)·√n·L`
          (`numerator_le_radial_mul`, needs the Jacobian column bound `hJac`), then
          `√(r²_W)·τ⁻¹·G ≤ (√2·2ⁿ)·τ^{−1/2}·gaussDdim (4τ) z` (`chart_gradient_gaussDdim_transfer_half`,
          the β1 heat-kernel gradient estimate at the banked coercivity `c₀ = ½`), then `|A| ≤ Ba`;
      (3) AMPLITUDE leg  `G·|∂A| ≤ Bd·G ≤ Bd·2ⁿ·gaussDdim (4τ) z` (`gaussDdim_ampWiden4`), then supply
          the missing `τ^{−1/2}` from `τ ≤ t` (`gaussDdim (4τ) z ≤ √t·τ^{−1/2}·gaussDdim (4τ) z`).
    The constant `C` is `s`-UNIFORM (uses `√t`, not `√τ`).  HONEST CARRIES: `hmin` (general-field-point
    coercivity — the `hmin` of `witnessFieldDeriv_gate_envelope_coercive`), `hJac` (inverse-chart
    Jacobian column bound `L`), `hBa`/`hBd` (amplitude value/derivative bounds — the SATISFIABLE
    survivors of the falsified `hGateData`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_starWide_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t τ : ℝ) (hτ : 0 < τ) (hτt : τ ≤ t)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update p i r) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (L Ba Bd : ℝ) (hL : 0 ≤ L)
    (hJac : ∀ k, |Pval k| ≤ L)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z p)) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ (Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba + (2 : ℝ) ^ n * Bd * Real.sqrt t)
          * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
  have hBa' : 0 ≤ Ba := le_trans (abs_nonneg _) hBa
  have hBd' : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
  -- the banked factor inequalities (derived BEFORE the abbreviations so `set` folds them).
  have hnum := numerator_le_radial_mul (uniformInverseChart g gi hC hK z p) Pval L hL hJac
  have htrans := chart_gradient_gaussDdim_transfer_half τ hτ
    (uniformInverseChart g gi hC hK z p) z hmin
  have hampw := gaussDdim_ampWiden4 τ hτ (uniformInverseChart g gi hC hK z p) z hmin
  rw [sqrtInv_eq_rpow τ hτ.le] at htrans
  -- the product-rule decomposition (S1).
  rw [witnessFieldDeriv_productRule g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1]
  set W := uniformInverseChart g gi hC hK z p with hWdef
  set G := gaussDdim τ W with hGdef
  set A := chartFieldAmp g gi hC hK a b τ z p with hAdef
  set dA := pd (chartFieldAmp g gi hC hK a b τ z) i p with hdAdef
  have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
  have hQnn : 0 ≤ gaussDdim (4 * τ) z := gaussDdim_nonneg _ _
  have hPnn : 0 ≤ τ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hτ.le _
  -- window: `1 ≤ √t · τ^{−1/2}`.
  have hsqrtτpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsqrtle : Real.sqrt τ ≤ Real.sqrt t := Real.sqrt_le_sqrt hτt
  have honeP : (1 : ℝ) ≤ Real.sqrt t * τ ^ (-(1 : ℝ) / 2) := by
    rw [← sqrtInv_eq_rpow τ hτ.le, ← div_eq_mul_inv, one_le_div hsqrtτpos]
    exact hsqrtle
  -- triangle inequality on the product-rule form.
  refine le_trans (abs_add_le _ _) ?_
  -- === GRADIENT leg ===
  have hgrad : |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A|
      ≤ (Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba)
          * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
    have e1 : |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A|
        = G * (|∑ k, W k * Pval k| / (2 * τ)) * |A| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hGnn, abs_div, abs_neg,
          abs_of_pos (show (0 : ℝ) < 2 * τ by positivity)]
    rw [e1]
    -- reassociate the singular factor.
    have keyeq : G * (|∑ k, W k * Pval k| / (2 * τ))
        = (1 / 2 : ℝ) * (|∑ k, W k * Pval k| * (τ⁻¹ * G)) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    -- the gradient core bound (no amplitude yet).
    have hτG : 0 ≤ τ⁻¹ * G := mul_nonneg (by positivity) hGnn
    have hnLnn : 0 ≤ Real.sqrt (n : ℝ) * L := mul_nonneg (Real.sqrt_nonneg _) hL
    have hcore : |∑ k, W k * Pval k| * (τ⁻¹ * G)
        ≤ (Real.sqrt (n : ℝ) * L)
            * ((Real.sqrt 2 * (2 : ℝ) ^ n) * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z) := by
      calc |∑ k, W k * Pval k| * (τ⁻¹ * G)
          ≤ (Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L)) * (τ⁻¹ * G) :=
            mul_le_mul_of_nonneg_right hnum hτG
        _ = (Real.sqrt (n : ℝ) * L) * (Real.sqrt (rncRadialSq W) * τ⁻¹ * G) := by ring
        _ ≤ (Real.sqrt (n : ℝ) * L)
              * ((Real.sqrt 2 * (2 : ℝ) ^ n) * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z) :=
            mul_le_mul_of_nonneg_left htrans hnLnn
    have hB1 : G * (|∑ k, W k * Pval k| / (2 * τ))
        ≤ (Real.sqrt (n : ℝ) * L / 2) * (Real.sqrt 2 * (2 : ℝ) ^ n)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
      rw [keyeq]
      calc (1 / 2 : ℝ) * (|∑ k, W k * Pval k| * (τ⁻¹ * G))
          ≤ (1 / 2 : ℝ)
              * ((Real.sqrt (n : ℝ) * L)
                  * ((Real.sqrt 2 * (2 : ℝ) ^ n) * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z)) :=
            mul_le_mul_of_nonneg_left hcore (by norm_num)
        _ = (Real.sqrt (n : ℝ) * L / 2) * (Real.sqrt 2 * (2 : ℝ) ^ n)
              * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by ring
    have hB1nn : 0 ≤ (Real.sqrt (n : ℝ) * L / 2) * (Real.sqrt 2 * (2 : ℝ) ^ n)
        * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
      have h0 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 :=
        div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)
      have h1 : 0 ≤ Real.sqrt 2 * (2 : ℝ) ^ n := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg h0 h1) hPnn) hQnn
    calc G * (|∑ k, W k * Pval k| / (2 * τ)) * |A|
        ≤ ((Real.sqrt (n : ℝ) * L / 2) * (Real.sqrt 2 * (2 : ℝ) ^ n)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z) * |A| :=
          mul_le_mul_of_nonneg_right hB1 (abs_nonneg _)
      _ ≤ ((Real.sqrt (n : ℝ) * L / 2) * (Real.sqrt 2 * (2 : ℝ) ^ n)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z) * Ba :=
          mul_le_mul_of_nonneg_left hBa hB1nn
      _ = (Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by ring
  -- === AMPLITUDE leg ===
  have hamp : |G * dA|
      ≤ ((2 : ℝ) ^ n * Bd * Real.sqrt t)
          * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
    have e2 : |G * dA| = G * |dA| := by rw [abs_mul, abs_of_nonneg hGnn]
    rw [e2]
    have h1 : G * |dA| ≤ G * Bd := mul_le_mul_of_nonneg_left hBd hGnn
    have h2 : G * Bd ≤ ((2 : ℝ) ^ n * gaussDdim (4 * τ) z) * Bd :=
      mul_le_mul_of_nonneg_right hampw hBd'
    -- supply the missing `τ^{−1/2}` from the window.
    have h3 : ((2 : ℝ) ^ n * gaussDdim (4 * τ) z) * Bd
        ≤ ((2 : ℝ) ^ n * Bd * Real.sqrt t) * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by
      have hq : gaussDdim (4 * τ) z
          ≤ (Real.sqrt t * τ ^ (-(1 : ℝ) / 2)) * gaussDdim (4 * τ) z :=
        le_mul_of_one_le_left hQnn honeP
      calc ((2 : ℝ) ^ n * gaussDdim (4 * τ) z) * Bd
          = ((2 : ℝ) ^ n * Bd) * gaussDdim (4 * τ) z := by ring
        _ ≤ ((2 : ℝ) ^ n * Bd) * ((Real.sqrt t * τ ^ (-(1 : ℝ) / 2)) * gaussDdim (4 * τ) z) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = ((2 : ℝ) ^ n * Bd * Real.sqrt t) * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by ring
    exact le_trans (le_trans h1 h2) h3
  -- === combine ===
  calc |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A| + |G * dA|
      ≤ (Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z
          + ((2 : ℝ) ^ n * Bd * Real.sqrt t)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := add_le_add hgrad hamp
    _ = (Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba
          + (2 : ℝ) ^ n * Bd * Real.sqrt t)
            * τ ^ (-(1 : ℝ) / 2) * gaussDdim (4 * τ) z := by ring

/-! ###############################################################################
    ### §S3b (brick 9) — the `(⋆)`-WIDE existential over the interior window `Ioo 0 t`.
    ############################################################################### -/

/-- **★★ (S3, brick 9) `hStarWide_concrete`.**  The concrete discharge of the `(⋆)`-WIDE envelope
    existential over the INTERIOR window `s ∈ Ioo 0 t` (so `τ = t−s > 0`; the single endpoint `s = t`,
    `τ = 0`, is `volume`-null and irrelevant to the downstream `Ioc`-integrability consumers — the
    degenerate-width witness is excluded here, honestly documented, NOT silently capped):
        `∃ C ≥ 0, ∀ x ∈ u, ∀ i, ∀ s ∈ Ioo 0 t, ∀ z,
           |witnessFieldDeriv … i (t−s) x z| ≤ C · (t−s)^{−1/2} · gaussDdim (4(t−s)) z`.
    Two branches over `z`: OFF-GATE (`z ∉ K`) — the witness vanishes
    (`witnessFieldDeriv_offGate_eq_zero`), `0 ≤ RHS`; ON-GATE (`z ∈ K`) — the per-point
    `witnessFieldDeriv_starWide_onGate`, applicable because `hgate` supplies `x ∈ S z` for every
    `z ∈ K`.  HONEST CARRIES (each SATISFIABLE, none the conclusion): `hL/hBa0/hBd0` (nonneg
    constants), `hSopen` (gate openness — a property of `S`), `hgate` (the field points `u` lie in
    every base-gate `S z`, `z ∈ K` — satisfiable for `u ⊆ ⋂_{z∈K} S z`, e.g. a small ball at the
    shared centre `0`), and `hdata` (the per-`(x,i,s,z)` chart-Jacobian + amplitude + coercivity
    package — the survivors of the `hGateData` falsification).  NOT `a₁ = R/6`. -/
theorem hStarWide_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (u : Set (Point n)) (L Ba Bd : ℝ) (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hSopen : ∀ z ∈ K, IsOpen (S z))
    (hgate : ∀ x ∈ u, ∀ z ∈ K, x ∈ S z)
    (hdata : ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k) (x i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x
        ∧ |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba
        ∧ |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart g gi hC hK z x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
        ≤ C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z := by
  have hCnn : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba
      + (2 : ℝ) ^ n * Bd * Real.sqrt t := by
    have h0 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba :=
      mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)) (by positivity)) hBa0
    have h1 : 0 ≤ (2 : ℝ) ^ n * Bd * Real.sqrt t :=
      mul_nonneg (mul_nonneg (by positivity) hBd0) (Real.sqrt_nonneg _)
    linarith
  refine ⟨_, hCnn, fun x hx i s hs z => ?_⟩
  obtain ⟨hs0, hst⟩ := hs
  have hτ : 0 < t - s := by linarith
  have hτt : t - s ≤ t := by linarith [hs0.le]
  by_cases hzK : z ∈ K
  · obtain ⟨Pval, hJetV, hJac, hAmp1, hBa, hBd, hmin⟩ := hdata x hx i s ⟨hs0, hst⟩ z hzK
    exact witnessFieldDeriv_starWide_onGate g gi hC hK S a b i t (t - s) hτ hτt z hzK
      (hSopen z hzK) x (hgate x hx z hzK) Pval hJetV hAmp1 L Ba Bd hL hJac hBa hBd hmin
  · rw [witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i (t - s) x z hzK, abs_zero]
    exact mul_nonneg (mul_nonneg hCnn (Real.rpow_nonneg hτ.le _)) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### §S4 — the WIDE downstream legs (width-`4(t−s)` analogs of the J4-323/324 bricks).
    ############################################################################### -/

/-- **`abLowerW` (width-generic P3).**  On `0 ≤ s ≤ t`, the combined Gaussian width is bounded below
    `s`-uniformly for ANY width multiplier `w`: `min w cF · t ≤ w·(t − s) + cF·s`.  The width-generic
    replacement for the banked `abLower` (which fixes `w = 2`); at `w = 4` this feeds the WIDE pairing.
    NOT `a₁ = R/6`. -/
theorem abLowerW (w t cF s : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t) :
    min w cF * t ≤ w * (t - s) + cF * s := by
  have h2 : min w cF ≤ w := min_le_left _ _
  have hc : min w cF ≤ cF := min_le_right _ _
  have hts : 0 ≤ t - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hts, mul_le_mul_of_nonneg_right hc hs0]

/-- **★ `sourcePairWidth_of_gaussian_bound` (width-generic P5).**  The WIDTH-GENERIC pairing discharge:
    for any width multiplier `w > 0`, from a source Gaussian bound `|F s z| ≤ CF·s^γ·gaussDdim (cF·s) z`
    (`γ > −1`, `cF > 0`) and the (satisfiable) parametric-integral measurability `hgMeas`,
        `fun s ↦ (t−s)^{−1/2} · ∫ z, gaussDdim (w(t−s)) z · |F s z| dz`   is `IntegrableOn (Ioc 0 t)`.
    A near-verbatim generalization of the banked `sourcePair_of_gaussian_bound` (`w = 2`); the pairing
    lower bound `a + b ≥ (min w cF)·t` still holds (`abLowerW`).  Brick 9's consumers use `w = 4`
    (`hFpairWide`).  ⚠ NOT `a₁ = R/6`. -/
theorem sourcePairWidth_of_gaussian_bound (w : ℝ) (hw : 0 < w)
    (F : ℝ → Point n → ℝ) (t CF cF γ : ℝ)
    (ht : 0 < t) (hCF : 0 ≤ CF) (hcF : 0 < cF) (hγ : -1 < γ)
    (hgMeas : AEStronglyMeasurable
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 t)))
    (hF : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z, |F s z| ≤ CF * s ^ γ * gaussDdim (cF * s) z) :
    IntegrableOn
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      (Set.Ioc 0 t) (volume : Measure ℝ) := by
  set c₀ := min w cF with hc0def
  have hc0pos : 0 < c₀ := lt_min hw hcF
  set K := gaussDdim (c₀ * t) (0 : Point n) with hKdef
  have hdom_int : IntegrableOn
      (fun s : ℝ => CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2))) (Set.Ioc 0 t) volume :=
    (QIQTH.CConvV2GaussianPairing.betaPow_integrableOn t γ ht hγ).const_mul (CF * K)
  have hIoo : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ‖(t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n))‖
        ≤ CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by
    intro s hs
    obtain ⟨hs0, hst⟩ := hs
    have hts : 0 < t - s := by linarith
    have ha : 0 < w * (t - s) := mul_pos hw hts
    have hb : 0 < cF * s := mul_pos hcF hs0
    have hgauss_nonneg : ∀ z : Point n, 0 ≤ gaussDdim (w * (t - s)) z :=
      fun z => gaussDdim_nonneg _ _
    have htsrpow : 0 ≤ (t - s) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hts.le _
    have hinner_nonneg :
        0 ≤ ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n)) :=
      integral_nonneg (fun z => mul_nonneg (hgauss_nonneg z) (abs_nonneg _))
    have hdomz_int : Integrable
        (fun z => (CF * s ^ γ) * (gaussDdim (w * (t - s)) z * gaussDdim (cF * s) z))
        (volume : Measure (Point n)) :=
      (QIQTH.CConvV2GaussianPairing.gaussDdim_pair_integrable
        (w * (t - s)) (cF * s)).const_mul (CF * s ^ γ)
    have hle_z : ∀ z : Point n, gaussDdim (w * (t - s)) z * |F s z|
        ≤ (CF * s ^ γ) * (gaussDdim (w * (t - s)) z * gaussDdim (cF * s) z) := by
      intro z
      calc gaussDdim (w * (t - s)) z * |F s z|
          ≤ gaussDdim (w * (t - s)) z * (CF * s ^ γ * gaussDdim (cF * s) z) :=
            mul_le_mul_of_nonneg_left (hF s ⟨hs0, hst.le⟩ z) (hgauss_nonneg z)
        _ = (CF * s ^ γ) * (gaussDdim (w * (t - s)) z * gaussDdim (cF * s) z) := by ring
    have hCFsγ_nonneg : 0 ≤ CF * s ^ γ := mul_nonneg hCF (Real.rpow_nonneg hs0.le _)
    have hinner_le :
        (∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
          ≤ CF * s ^ γ * K := by
      calc (∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
          ≤ ∫ z, (CF * s ^ γ) * (gaussDdim (w * (t - s)) z * gaussDdim (cF * s) z)
              ∂(volume : Measure (Point n)) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun z => mul_nonneg (hgauss_nonneg z) (abs_nonneg _)))
              hdomz_int (Filter.Eventually.of_forall hle_z)
        _ = (CF * s ^ γ)
              * ∫ z, gaussDdim (w * (t - s)) z * gaussDdim (cF * s) z
                  ∂(volume : Measure (Point n)) := by
            rw [integral_const_mul]
        _ = (CF * s ^ γ) * gaussDdim (w * (t - s) + cF * s) (0 : Point n) := by
            rw [QIQTH.CConvV2GaussianPairing.gaussDdim_pairing_integral
              (w * (t - s)) (cF * s) ha hb]
        _ ≤ (CF * s ^ γ) * K := by
            refine mul_le_mul_of_nonneg_left ?_ hCFsγ_nonneg
            exact QIQTH.CConvV2GaussianPairing.gaussDdim_zero_antitone (c₀ * t)
              (w * (t - s) + cF * s) (mul_pos hc0pos ht)
              (by rw [hc0def]; exact abLowerW w t cF s hs0.le hst.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htsrpow hinner_nonneg)]
    calc (t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n))
        ≤ (t - s) ^ (-(1 : ℝ) / 2) * (CF * s ^ γ * K) :=
          mul_le_mul_of_nonneg_left hinner_le htsrpow
      _ = CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by ring
  have hvol_t : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton t
  have hdom_ae : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ioc 0 t)),
      ‖(t - s) ^ (-(1 : ℝ) / 2)
          * ∫ z, gaussDdim (w * (t - s)) z * |F s z| ∂(volume : Measure (Point n))‖
        ≤ CF * K * (s ^ γ * (t - s) ^ (-(1 : ℝ) / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hvol_t]
      with s hsIoc hsne
    exact hIoo s ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hsne⟩
  exact Integrable.mono' hdom_int hgMeas hdom_ae

/-- **`hFpairWide`.**  The width-`4(t−s)` `hFpair` — `sourcePairWidth_of_gaussian_bound` at `w = 4`.
    This is the WIDE source-integrability leg the brick-12/13/14 consumers pair against the
    `(⋆)`-WIDE witness bound.  ⚠ NOT `a₁ = R/6`. -/
theorem hFpairWide (F : ℝ → Point n → ℝ) (t CF cF γ : ℝ)
    (ht : 0 < t) (hCF : 0 ≤ CF) (hcF : 0 < cF) (hγ : -1 < γ)
    (hgMeas : AEStronglyMeasurable
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (4 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      ((volume : Measure ℝ).restrict (Set.Ioc 0 t)))
    (hF : ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ z, |F s z| ≤ CF * s ^ γ * gaussDdim (cF * s) z) :
    IntegrableOn
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (4 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      (Set.Ioc 0 t) (volume : Measure ℝ) :=
  sourcePairWidth_of_gaussian_bound 4 (by norm_num) F t CF cF γ ht hCF hcF hγ hgMeas hF

/-- **`envelope_integrable_v2Wide`.**  The WIDE `s`-envelope `φ s := C·(t−s)^{−1/2}·∫ gaussDdim (4(t−s))
    z·|F s z|` is `IntegrableOn (Ioc 0 t)` — `hFpairWide` scaled by `C` (`IntegrableOn.const_mul`).  The
    width-`4(t−s)` analog of `CConvV2EnvelopeFromStar.envelope_integrable_v2`.  ⚠ NOT `a₁ = R/6`. -/
theorem envelope_integrable_v2Wide (F : ℝ → Point n → ℝ) (t C : ℝ)
    (hpair : IntegrableOn
      (fun s : ℝ => (t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (4 * (t - s)) z * |F s z| ∂(volume : Measure (Point n)))
      (Set.Ioc 0 t) (volume : Measure ℝ)) :
    IntegrableOn
      (fun s : ℝ => C * ((t - s) ^ (-(1 : ℝ) / 2)
        * ∫ z, gaussDdim (4 * (t - s)) z * |F s z| ∂(volume : Measure (Point n))))
      (Set.Ioc 0 t) (volume : Measure ℝ) :=
  hpair.const_mul C

/-- **`pointwise_domWide`.**  The WIDE pointwise `hStar`-driven domination `|wfd·F| ≤ C·((t−s)^{−1/2}·
    gaussDdim (4(t−s)) z·|F s z|)` on the interior window `Ioo 0 t`, from the `(⋆)`-WIDE witness bound
    (e.g. the output of `hStarWide_concrete`).  The width-`4(t−s)` analog of
    `CConvV2EnvelopeFromStar.pointwise_dom_v2`; the `s`-window is `Ioo 0 t` (the `hStarWide` scope).
    ⚠ NOT `a₁ = R/6`. -/
theorem pointwise_domWide (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ) (C : ℝ) (_hC0 : 0 ≤ C)
    (hStarW : ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
        ≤ C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) :
    ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z|
        ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by
  intro x hx i s hs z
  rw [abs_mul]
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) * |F s z| :=
        mul_le_mul_of_nonneg_right (hStarW x hx i s hs z) (abs_nonneg _)
    _ = C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by ring

/-- **`hdomS_v2Wide`.**  The WIDE `hdomS` output slot (`∀ᶠ x → ∀ᵐ s → ∀ᵐ z`, width `4(t−s)`), from the
    `(⋆)`-WIDE witness bound over `Ioo 0 t` and the neighbourhood carry `hu`.  The single endpoint
    `s = t` is handled by the `volume`-null `{t}` (a.e. `s ∈ Ioc ⟹ s ∈ Ioo`), matching the
    `sourcePair` endpoint pattern.  The width-`4(t−s)` analog of
    `CConvV2EnvelopeFromStar.hdomS_v2`.  ⚠ NOT `a₁ = R/6`. -/
theorem hdomS_v2Wide (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 ≤ t) (u : Set (Point n)) (F : ℝ → Point n → ℝ) (C : ℝ) (_hC0 : 0 ≤ C)
    (hu : ∀ x₀ ∈ u, u ∈ 𝓝 x₀)
    (hStarW : ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
        ≤ C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by
  intro x₀ hx₀ i
  filter_upwards [hu x₀ hx₀] with x hxu
  have hvol_t : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton t
  filter_upwards [hvol_t] with s hsne hmem
  rw [Set.uIoc_of_le ht] at hmem
  have hsIoo : s ∈ Set.Ioo (0 : ℝ) t := ⟨hmem.1, lt_of_le_of_ne hmem.2 hsne⟩
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) * |F s z| :=
        mul_le_mul_of_nonneg_right (hStarW x hxu i s hsIoo z) (abs_nonneg _)
    _ = C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by ring

end QIQTH.CConvV2WitnessStar

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2WitnessStar
#print axioms sqrtInv_eq_rpow
#print axioms gaussDdim_ampWiden4
#print axioms witnessFieldDeriv_productRule
#print axioms witnessFieldDeriv_starWide_onGate
#print axioms hStarWide_concrete
#print axioms abLowerW
#print axioms sourcePairWidth_of_gaussian_bound
#print axioms hFpairWide
#print axioms envelope_integrable_v2Wide
#print axioms pointwise_domWide
#print axioms hdomS_v2Wide
end AxiomChecks
