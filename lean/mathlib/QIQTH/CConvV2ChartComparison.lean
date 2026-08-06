/-
  CConvV2ChartComparison — J4-325 (facade-v2 bricks 6+7 of 14): the CHART-COMPARISON layer
  (α₁ per-point identities + α₂ two-sided radial comparison + Jacobian bound + the β1 Gaussian
  transfer) feeding brick 9's concrete `(⋆)` / `hStar` proof.  ONE brick of the `a₁ = R/6`
  heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It packages
  chart geometry + the scalar heat-kernel gradient estimate into the shapes brick 9 consumes.  NO
  `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypotheses
  in this file's OWN theorems.  No existing file is edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (C0) THE RECON — what brick 9 needs and what the bank already supplies.

  ### The consumer (`CConvWitnessEnvelopeDataV2.hStar`, `CConvV2Contracts.lean`).
      `∃ C ≥ 0, ∀ x ∈ u, ∀ i, ∀ s ∈ Ioc 0 t, ∀ z,
         |witnessFieldDeriv g gi hC hK S a b i (t−s) x z| ≤ C·(t−s)^{−1/2}·gaussDdim (2(t−s)) z`.
  The witness field derivative factorises (`EngineInstantiation`/`G2CarryDischarge`) as
      witnessFieldDeriv = (∂ᵢ log G)·G·amp + G·∂ᵢamp,   G := gaussDdim (t−s) (W z x),
  with `W z x := uniformInverseChart g gi hC hK z x` the inverse-chart (`z`=base, `x`=field point) and
      ∂ᵢ log G = −(∑ₖ Wₖ·Pvalₖ)/(2(t−s)),   Pvalₖ = ∂ᵢ Wₖ  (the chart Jacobian column, `s`-INDEP).
  The RHS Gaussian `gaussDdim (2(t−s)) z` is the flat Gaussian in the BASE variable `z`.

  ### gaussDdim's exponent convention (`FlatHeatEquation`/`ChartGaussAdapter`).
      `gaussDdim τ v = (√(4πτ))⁻ⁿ · exp(−rncRadialSq v /(4τ))`,   `rncRadialSq v = ∑ₖ (vₖ)²`,  so
      `gaussDdim τ v = Gk n τ (rncRadialSq v)` (`gaussDdim_eq_Gk`); `Gk n τ (s·r²) = (√s)⁻ⁿ·gaussDdim
      (τ/s) v` (`Gk_scaled`); `gaussDdim (2τ) z` carries prefactor `(8πτ)^{−n/2}` and exponent
      `−rncRadialSq z /(8τ)`.

  ### THE BANKED INVENTORY (verdicts — grepped per feedback_dont_undercredit_repo).
    • THE `½`-CONJUNCT DISCHARGER (α₂-lower).  `HeatResidualBound.chartW0_nearIsometry` /
      `chartW0_rncRadialSq_error` (`InverseChartDisplacement.lean`) prove the two-sided near-isometry
      `|rncRadialSq(W z 0) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z` on `z ∈ K`, `‖z‖` small — hence, on a
      shrunk radius (`L·‖z‖ ≤ ½`), BOTH `½·rncRadialSq z ≤ rncRadialSq(W z 0)` AND
      `rncRadialSq(W z 0) ≤ 2·rncRadialSq z`.  ⚠ THIS IS AT THE FIELD CENTRE `x = 0` ONLY (`W₀ z = W z 0
      ≈ −z`).  The general-field-point `x ∈ S z` version is a genuine near-isometry NOT banked; §C2 gives
      the honest re-export at `x = 0` and states the general shape as the coercivity CARRY that
      `G2CarryDischarge.witnessFieldDeriv_gate_envelope_coercive` already takes as an input hypothesis.
    • HgateSatAudit's verdict concerns the S-MEMBERSHIP conclusion carrier (`hcarTau`/`hcarField`),
      NOT the radial conjunct — the radial `½`-comparison was ALWAYS a satisfiable survivor (see
      `GaussianJetTheorem` (G0): only the constant-`Bs` numerator conjunct (‡) is false).
    • THE CHART JACOBIAN (α₁ Pval).  `HeatResidualBound.chartField_firstJet_nhds_of_contDiffAt`
      (`GeneralBaseJets.lean`) proves `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt (r ↦ W z (update x i r) k)
      (fderiv(W z) x eᵢ k) (x i)` from the honest field-centre carry `ContDiffAt ℝ 2 (W z) 0` — itself
      provided by `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general`.  A DIRECT re-export.
    • THE GERM LEFT-INVERSE (α₁).  `HeatResidualBound.uniformInverseChart_huniformChart`
      (`UniformChartRadius.lean`) supplies the germ `W z (φ_z v) =ᶠ[𝓝 v] id`, giving `W z (φ_z v) = v`.
    • β1 (the scalar gradient estimate).  `GaussianJetTheorem.gaussian_beats_linear`:
      `r·s⁻¹·exp(−a r²/s) ≤ (1/(2√(a−a′)))·(√s)⁻¹·exp(−a′ r²/s)`  (`a′ < a`, `s > 0`).
    • THE GAUSSIAN-WIDTH TRANSFER (assembly).  `ChartGaussAdapter.Gk_scaled`/`Gk_anti` +
      `G2CarryDischarge.gaussDdim_coercivity_envelope` (`½·r²_base ≤ r²_w ⟹ G_τ(w) ≤ (√2)ⁿ·G_{2τ}(base)`).

  ### THE EXACT TRANSFER BRICK 9 NEEDS (with the real exponent convention).
      From the coercive radial lower comparison `c₀·rncRadialSq z ≤ rncRadialSq (W z x)` and the numerator
      bound `|∑ₖ Wₖ Pvalₖ| ≤ √(rncRadialSq(W z x))·√(∑ₖ Pvalₖ²)`, the gradient factor
        `(|∑ₖ Wₖ Pvalₖ|/(2τ))·gaussDdim τ (W z x)`
      is `≤ (½√(∑Pvalₖ²))·[√(rncRadialSq(W z x))·τ⁻¹·gaussDdim τ (W z x)]`, and (β1 + `Gk_scaled`)
        `√(r²_W)·τ⁻¹·gaussDdim τ (W z x)  ≤  √2·(√(c₀/2))⁻ⁿ·τ^{−1/2}·gaussDdim (2τ/c₀) z`
      — the exact `τ^{−1/2}` cost the facade's dropped conjunct (‡) illegitimately omitted.  (At `c₀ = 1`
      the width is `2τ` and the constant `√2·(√2)ⁿ` = the `hStar` shape; at the banked `c₀ = ½` the honest
      width is `4τ`.)  §C4 delivers this at the exp-level (normalizations factored out) AND at gaussDdim.

  NOT `a₁ = R/6`.
-/
import QIQTH.G2CarryDischarge
import QIQTH.GaussianJetTheorem
import QIQTH.GeneralBaseJets
import QIQTH.InverseChartNormalJets
import QIQTH.CConvV2Contracts

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.GaussianJetTheorem QIQTH.ResidueBound QIQTH.ExpMap
open scoped Topology BigOperators ContDiff

namespace QIQTH.CConvV2ChartComparison

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### §C1 (α₁) — THE PER-POINT IDENTITIES (re-exports; no heat asymptotics).
    ############################################################################### -/

/-- **α₁ radial identity — `sqrt_rncRadialSq`.**  `√(rncRadialSq v) = rncRadial v` (definitional:
    `rncRadial = √∘rncRadialSq`).  The `√(r²)` object the β1 transfer (§C4) and the Cauchy–Schwarz
    numerator bound are stated in.  NOT `a₁ = R/6`. -/
theorem sqrt_rncRadialSq (v : Point n) : Real.sqrt (rncRadialSq v) = rncRadial v := rfl

/-- **α₁ germ left-inverse — `chart_leftInverse_gate`.**  A re-export of the banked germ
    (`uniformInverseChart_huniformChart`): there is a single radius `δ₀ > 0` over `K` on which, for every
    base `z ∈ K` and every velocity `v` with `‖v‖ < δ₀`, the inverse chart is a genuine left inverse of
    the flow:
        `uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v`.
    (Goes through the banked germ PROPERTY lemma — never unfolds the `.choose`-built chart.)
    NOT `a₁ = R/6`. -/
theorem chart_leftInverse_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n, ‖v‖ < δ₀ →
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀, fun z hz v hv => ?_⟩
  exact ((hspec z hz).1 v hv).1.eq_of_nhds

/-- **α₁ chart Jacobian existence — `chart_firstJet_column_center`.**  A re-export of
    `chartField_firstJet_nhds_of_contDiffAt` fed by the banked field-centre carry
    `chartField_contDiffAt_center_general`: there is a single radius `δ₀ > 0` over `K` such that whenever
    the field centre `0` is a small exp-image (`φ_z v = 0`, `‖v‖ < δ₀`), the FIRST field line-jet of the
    inverse chart `W z` (the `Pval` column) EXISTS at every field point `x` near `0`:
        `∀ᶠ x in 𝓝 0, ∀ k, HasDerivAt (r ↦ W z (update x i r) k) (Pvalₖ) (x i)`,
    `Pvalₖ = fderiv ℝ (W z) x eᵢ k`.  This is the `hDeriv` slot of `SliceChartData` at the concrete
    chart, near the field centre (the honest scope of the banked `C²`).  NOT `a₁ = R/6`. -/
theorem chart_firstJet_column_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n, uniformFlowExp g gi hC hK z v = 0 → ‖v‖ < δ₀ →
      ∀ᶠ x in 𝓝 (0 : Point n), ∀ k : Fin n,
        HasDerivAt (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k)
          (fderiv ℝ (uniformInverseChart g gi hC hK z) x (Pi.single i (1 : ℝ)) k) (x i) := by
  obtain ⟨δ₀, hδ₀, hreg⟩ := chartField_contDiffAt_center_general g gi hC hK
  refine ⟨δ₀, hδ₀, fun z hz v hexp hv => ?_⟩
  exact chartField_firstJet_nhds_of_contDiffAt g gi hC hK z i (hreg z hz v hexp hv)

/-! ###############################################################################
    ### §C2 (α₂-lower) + §C3 (α₂-upper) — THE TWO-SIDED RADIAL COMPARISON at the field centre.
    ############################################################################### -/

/-- **α₂ two-sided center — `chart_radial_twosided_center`.**  From the banked near-isometry error
    `chartW0_rncRadialSq_error` (`|rncRadialSq(W z 0) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`), shrinking
    the radius so `L·‖z‖ ≤ ½`, both sides of the comparison at the field centre `x = 0`:
        `½·rncRadialSq z ≤ rncRadialSq (W z 0)`  (α₂-lower, `c₀ = ½`)  and
        `rncRadialSq (W z 0) ≤ 2·rncRadialSq z`  (α₂-upper).
    ⚠ FIELD CENTRE ONLY (`W z 0 ≈ −z`); the general `x ∈ S z` version is the carried coercivity input of
    `witnessFieldDeriv_gate_envelope_coercive` (see header C0).  NOT `a₁ = R/6`. -/
theorem chart_radial_twosided_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)
      ∧ rncRadialSq (uniformInverseChart g gi hC hK z 0) ≤ 2 * rncRadialSq z := by
  obtain ⟨r₀, hr₀, L, hL0, hraw⟩ := chartW0_rncRadialSq_error g gi hC hK
  refine ⟨min r₀ (1 / (2 * (L + 1))), lt_min hr₀ (by positivity), fun z hz hzr => ?_⟩
  have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hzrL : ‖z‖ < 1 / (2 * (L + 1)) := lt_of_lt_of_le hzr (min_le_right _ _)
  obtain ⟨hlow, hup⟩ := hraw z hz hzr₀
  have hLz : L * ‖z‖ ≤ 1 / 2 := by
    have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
      mul_le_mul_of_nonneg_left hzrL.le hL0
    have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
    linarith
  have hznn : 0 ≤ rncRadialSq z := rncRadialSq_nonneg z
  refine ⟨?_, ?_⟩
  · nlinarith [hlow, hLz, hznn]
  · nlinarith [hup, hLz, hznn]

/-- **α₂-lower center — `chart_radialLower_center`.**  The lower half of `chart_radial_twosided_center`
    isolated in the exactly `SliceChartData.hRadialLower`-consumable shape at `x = 0`
    (`c₀ = ½`).  NOT `a₁ = R/6`. -/
theorem chart_radialLower_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0) := by
  obtain ⟨r, hr, h⟩ := chart_radial_twosided_center g gi hC hK
  exact ⟨r, hr, fun z hz hzr => (h z hz hzr).1⟩

/-! ###############################################################################
    ### §C3 (α₂-upper on the compact + the Jacobian bound).
    ############################################################################### -/

/-- **`rncRadialSq_le_card_normSq`.**  `rncRadialSq v ≤ n·‖v‖²` (each coordinate `|vₖ| ≤ ‖v‖` in the
    sup norm on `Point n = Fin n → ℝ`).  The elementary companion of `norm_sq_le_rncRadialSq`, used to
    turn a chart sup-norm bound into a radial-square bound.  NOT `a₁ = R/6`. -/
theorem rncRadialSq_le_card_normSq (v : Point n) : rncRadialSq v ≤ (n : ℝ) * ‖v‖ ^ 2 := by
  rw [rncRadialSq]
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi : |v i| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
        nlinarith [hi, abs_nonneg (v i), sq_abs (v i), norm_nonneg v]
    _ = (n : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **α₂-upper (bounded form) — `chart_radialUpper_of_normBound`.**  From the banked on-gate uniform
    chart norm bound `‖W z p‖ ≤ R` (`ChartGeneralPContinuity`/`ConcreteGateAssembly`'s `hnorm`, valid at
    the `uniformFlowRadius` for `z ∈ K` and every field point `p`), the radial-square upper bound
        `rncRadialSq (W z p) ≤ n·R²`
    on the compact.  The honest bounded-form α₂-upper for general field points (the two-sided `≤ 2·r²`
    center form is the `x = 0` `chart_radial_twosided_center`).  NOT `a₁ = R/6`. -/
theorem chart_radialUpper_of_normBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z p : Point n) (R : ℝ)
    (hnorm : ‖uniformInverseChart g gi hC hK z p‖ ≤ R) :
    rncRadialSq (uniformInverseChart g gi hC hK z p) ≤ (n : ℝ) * R ^ 2 := by
  set W := uniformInverseChart g gi hC hK z p with hWdef
  have hRnn : 0 ≤ R := le_trans (norm_nonneg W) hnorm
  have hstep : (n : ℝ) * ‖W‖ ^ 2 ≤ (n : ℝ) * R ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg W, hnorm, hRnn]) (by positivity)
  exact le_trans (rncRadialSq_le_card_normSq W) hstep

/-- **The Cauchy–Schwarz numerator bound — `numerator_cauchy_schwarz`.**  The chart log-gradient
    numerator `∑ₖ Wₖ·Pvalₖ` is bounded by the product of radial lengths:
        `|∑ₖ W k · P k| ≤ √(rncRadialSq W)·√(∑ₖ (P k)²)`.
    (Discrete Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` + `√` monotonicity; `rncRadialSq W =
    ∑ₖ (W k)²`.)  The step (i) of brick 9's plan (`|∑ chart Pval| ≤ L·‖chart‖`).  NOT `a₁ = R/6`. -/
theorem numerator_cauchy_schwarz (W P : Point n) :
    |∑ k, W k * P k| ≤ Real.sqrt (rncRadialSq W) * Real.sqrt (∑ k, (P k) ^ 2) := by
  have hcs : (∑ k, W k * P k) ^ 2 ≤ (∑ k, (W k) ^ 2) * ∑ k, (P k) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ W P
  have h1 : 0 ≤ ∑ k, (W k) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc |∑ k, W k * P k| = Real.sqrt ((∑ k, W k * P k) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ k, (W k) ^ 2) * ∑ k, (P k) ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (rncRadialSq W) * Real.sqrt (∑ k, (P k) ^ 2) := by
        rw [Real.sqrt_mul h1]; rfl

/-- **The Jacobian bound — `jacobian_sumSq_le`.**  From a uniform column bound `∀ k, |P k| ≤ L`
    (`0 ≤ L`), `∑ₖ (P k)² ≤ n·L²`, hence `√(∑ₖ (P k)²) ≤ √n·L`.  Combined with `numerator_cauchy_schwarz`
    this is `|∑ₖ Wₖ Pvalₖ| ≤ √(rncRadialSq W)·(√n·L)` — step (i) with the explicit column bound.
    (The uniform `L` over the compact is the honest CARRY: the tower has the chart velocity 2-jet modulus
    but no banked inverse-chart Jacobian sup-bound; `L` is supplied where the chart is instantiated.)
    NOT `a₁ = R/6`. -/
theorem jacobian_sumSq_le (P : Point n) (L : ℝ) (hL : 0 ≤ L) (hP : ∀ k, |P k| ≤ L) :
    ∑ k, (P k) ^ 2 ≤ (n : ℝ) * L ^ 2 := by
  calc ∑ k, (P k) ^ 2 ≤ ∑ _k : Fin n, L ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        nlinarith [hP k, abs_nonneg (P k), sq_abs (P k)]
    _ = (n : ℝ) * L ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The assembled numerator bound — `numerator_le_radial_mul`.**  Combining Cauchy–Schwarz with the
    Jacobian column bound: `|∑ₖ W k · P k| ≤ √(rncRadialSq W)·(√n·L)` when `∀ k, |P k| ≤ L`.  This is the
    exact numerator control (step (i)) that multiplies the β1 gradient transfer (§C4).  NOT `a₁ = R/6`. -/
theorem numerator_le_radial_mul (W P : Point n) (L : ℝ) (hL : 0 ≤ L) (hP : ∀ k, |P k| ≤ L) :
    |∑ k, W k * P k| ≤ Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L) := by
  refine le_trans (numerator_cauchy_schwarz W P) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hsq : Real.sqrt (∑ k, (P k) ^ 2) ≤ Real.sqrt ((n : ℝ) * L ^ 2) :=
    Real.sqrt_le_sqrt (jacobian_sumSq_le P L hL hP)
  refine le_trans hsq ?_
  rw [Real.sqrt_mul (by positivity) (L ^ 2), Real.sqrt_sq hL]

/-! ###############################################################################
    ### §C4 (THE TRANSFER) — β1 + the radial comparison, at the exp-level and at gaussDdim.
    ############################################################################### -/

/-- **★★ C4a scalar transfer — `gradient_scalar_transfer`.**  THE heat-kernel gradient estimate in the
    exact scalar shape brick 9 multiplies by the numerator/amplitude factors, with normalizations
    factored out.  For `τ > 0`, `c₀ > 0`, radii `rc2` (chart, `= rncRadialSq (W z x)`) and `rz2` (base,
    `≥ 0`) with the coercive lower comparison `c₀·rz2 ≤ rc2`:
        `√(rc2)·τ⁻¹·exp(−rc2/(4τ))  ≤  √2·(√τ)⁻¹·exp(−c₀·rz2/(8τ))`.
    Route: `gaussian_beats_linear` (β1) at `a = ¼`, `a′ = ⅛`, `s = τ`, `r = √rc2` (so `r² = rc2`) gives
    the `τ^{−1/2}` and weakens the exponent to `−rc2/(8τ)`; then `rc2 ≥ c₀·rz2` weakens it to
    `−c₀·rz2/(8τ)`.  The `√2` is the β1 constant `1/(2√(¼−⅛))`.  NOT `a₁ = R/6`. -/
theorem gradient_scalar_transfer (τ : ℝ) (hτ : 0 < τ) (c₀ rc2 rz2 : ℝ) (hc₀ : 0 < c₀)
    (hrz2 : 0 ≤ rz2) (hmin : c₀ * rz2 ≤ rc2) :
    Real.sqrt rc2 * τ⁻¹ * Real.exp (-rc2 / (4 * τ))
      ≤ Real.sqrt 2 * (Real.sqrt τ)⁻¹ * Real.exp (-(c₀ * rz2) / (8 * τ)) := by
  have hrc2 : 0 ≤ rc2 := le_trans (by positivity) hmin
  set r := Real.sqrt rc2 with hrdef
  have hrsq : r ^ 2 = rc2 := Real.sq_sqrt hrc2
  -- β1 at a = 1/4, a' = 1/8.
  have hβ := gaussian_beats_linear (1 / 4) (1 / 8) (by norm_num) hτ r
  -- the β1 constant `1/(2√(1/4-1/8)) = √2`.
  have hconst : (1 : ℝ) / (2 * Real.sqrt (1 / 4 - 1 / 8)) = Real.sqrt 2 := by
    have he : (1 : ℝ) / 4 - 1 / 8 = 1 / 8 := by norm_num
    rw [he]
    have hprod : Real.sqrt 2 * Real.sqrt ((1 : ℝ) / 8) = 1 / 2 := by
      rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * (1 / 8) = (1 / 2) ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
    have hpos : (0 : ℝ) < Real.sqrt ((1 : ℝ) / 8) := Real.sqrt_pos.mpr (by norm_num)
    rw [eq_comm, eq_div_iff (by positivity)]
    linear_combination 2 * hprod
  -- rewrite β1's exponents into the `-rc2/(4τ)` / `-rc2/(8τ)` shapes.
  have hLexp : -(1 / 4 * r ^ 2 / τ) = -rc2 / (4 * τ) := by rw [hrsq]; ring
  have hRexp : -(1 / 8 * r ^ 2 / τ) = -rc2 / (8 * τ) := by rw [hrsq]; ring
  rw [hconst, hLexp, hRexp] at hβ
  refine le_trans hβ ?_
  -- weaken exponent `-rc2/(8τ) ≤ -(c₀·rz2)/(8τ)`.
  have hexp_le : Real.exp (-rc2 / (8 * τ)) ≤ Real.exp (-(c₀ * rz2) / (8 * τ)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 8 * τ)]
    linarith [hmin]
  have hcnn : 0 ≤ Real.sqrt 2 * (Real.sqrt τ)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hexp_le hcnn

/-- **★★★ C4b gaussDdim transfer — `chart_gradient_gaussDdim_transfer`.**  The `gaussDdim`-level assembly:
    for `τ > 0`, `c₀ > 0`, and the coercive lower comparison `c₀·rncRadialSq z ≤ rncRadialSq W`,
        `√(rncRadialSq W)·τ⁻¹·gaussDdim τ W
           ≤ (√2·(√(c₀/2))⁻ⁿ)·(√τ)⁻¹·gaussDdim (2τ/c₀) z`.
    Route: `gaussDdim τ W = (√(4πτ))⁻ⁿ·exp(−r²_W/(4τ))` (`gaussDdim_eq_Gk`), multiply the scalar transfer
    C4a by the nonnegative prefactor, then recognise `(√(4πτ))⁻ⁿ·exp(−c₀·r²_z/(8τ)) = Gk n τ ((c₀/2)·
    rncRadialSq z) = (√(c₀/2))⁻ⁿ·gaussDdim (2τ/c₀) z` (`Gk_scaled` at `s = c₀/2`).  The `τ^{−1/2}` cost is
    the honest heat-kernel gradient factor.  Brick 9 multiplies this core by `½·√n·L` (numerator, §C3)
    and `Ba` (amplitude), then normalizes the width `2τ/c₀` (at `c₀ = 1`, `= gaussDdim (2τ) z`; at the
    banked `c₀ = ½`, `= gaussDdim (4τ) z`).  NOT `a₁ = R/6`. -/
theorem chart_gradient_gaussDdim_transfer (τ : ℝ) (hτ : 0 < τ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (W z : Point n) (hmin : c₀ * rncRadialSq z ≤ rncRadialSq W) :
    Real.sqrt (rncRadialSq W) * τ⁻¹ * gaussDdim τ W
      ≤ (Real.sqrt 2 * (Real.sqrt (c₀ / 2))⁻¹ ^ n) * (Real.sqrt τ)⁻¹ * gaussDdim (2 * τ / c₀) z := by
  have hc2nn : 0 ≤ rncRadialSq W := rncRadialSq_nonneg W
  have hznn : 0 ≤ rncRadialSq z := rncRadialSq_nonneg z
  -- prefactor `(√(4πτ))⁻ⁿ ≥ 0`.
  set pref : ℝ := (Real.sqrt (4 * Real.pi * τ))⁻¹ ^ n with hprefdef
  have hprefnn : 0 ≤ pref := by rw [hprefdef]; positivity
  -- LHS = pref · [scalar LHS].
  have hLHS : Real.sqrt (rncRadialSq W) * τ⁻¹ * gaussDdim τ W
      = pref * (Real.sqrt (rncRadialSq W) * τ⁻¹ * Real.exp (-rncRadialSq W / (4 * τ))) := by
    rw [gaussDdim_eq_Gk τ W, Gk, hprefdef]; ring
  rw [hLHS]
  -- apply the scalar transfer C4a.
  have hscalar := gradient_scalar_transfer τ hτ c₀ (rncRadialSq W) (rncRadialSq z) hc₀ hznn hmin
  have hstep1 : pref * (Real.sqrt (rncRadialSq W) * τ⁻¹ * Real.exp (-rncRadialSq W / (4 * τ)))
      ≤ pref * (Real.sqrt 2 * (Real.sqrt τ)⁻¹ * Real.exp (-(c₀ * rncRadialSq z) / (8 * τ))) :=
    mul_le_mul_of_nonneg_left hscalar hprefnn
  refine le_trans hstep1 ?_
  -- recognise `pref · exp(-(c₀·r²_z)/(8τ)) = Gk n τ ((c₀/2)·rncRadialSq z)`.
  have hc2pos : 0 < c₀ / 2 := by positivity
  have harg : -(c₀ * rncRadialSq z) / (8 * τ) = -((c₀ / 2) * rncRadialSq z) / (4 * τ) := by
    rw [neg_div, neg_div,
        show (c₀ / 2) * rncRadialSq z = (c₀ * rncRadialSq z) / 2 by ring, div_div,
        show (2 : ℝ) * (4 * τ) = 8 * τ by ring]
  have hGkval : pref * Real.exp (-(c₀ * rncRadialSq z) / (8 * τ))
      = Gk n τ ((c₀ / 2) * rncRadialSq z) := by
    rw [Gk, hprefdef, harg]
  have hGkscaled : Gk n τ ((c₀ / 2) * rncRadialSq z)
      = (Real.sqrt (c₀ / 2))⁻¹ ^ n * gaussDdim (τ / (c₀ / 2)) z :=
    Gk_scaled (c₀ / 2) τ hc2pos hτ z
  have hwidth : τ / (c₀ / 2) = 2 * τ / c₀ := by rw [div_div_eq_mul_div]; ring
  rw [hwidth] at hGkscaled
  -- assemble: rearrange the RHS to expose `pref · exp` factor.
  have hRHSeq : pref * (Real.sqrt 2 * (Real.sqrt τ)⁻¹ * Real.exp (-(c₀ * rncRadialSq z) / (8 * τ)))
      = Real.sqrt 2 * (Real.sqrt τ)⁻¹ * (pref * Real.exp (-(c₀ * rncRadialSq z) / (8 * τ))) := by
    ring
  rw [hRHSeq, hGkval, hGkscaled]
  apply le_of_eq
  ring

/-! ###############################################################################
    ### §C4' — the `c₀ = ½` specialization landing on `gaussDdim (4τ) z` (the banked lower constant).
    ############################################################################### -/

/-- **`chart_gradient_gaussDdim_transfer_half`.**  The `c₀ = ½` instance of the transfer (the banked
    `chart_radialLower_center` lower comparison): with `½·rncRadialSq z ≤ rncRadialSq W`,
        `√(rncRadialSq W)·τ⁻¹·gaussDdim τ W ≤ (√2·2ⁿ)·(√τ)⁻¹·gaussDdim (4τ) z`.
    (`(√(¼))⁻ⁿ = 2ⁿ`, width `2τ/(½) = 4τ`.)  The honest width the banked field-centre lower comparison
    forces; brick 9 carries `gaussDdim (4τ) z` (still `z`-integrable, `(t−s)^{−1/2}` `s`-integrable).
    NOT `a₁ = R/6`. -/
theorem chart_gradient_gaussDdim_transfer_half (τ : ℝ) (hτ : 0 < τ) (W z : Point n)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq W) :
    Real.sqrt (rncRadialSq W) * τ⁻¹ * gaussDdim τ W
      ≤ (Real.sqrt 2 * (2 : ℝ) ^ n) * (Real.sqrt τ)⁻¹ * gaussDdim (4 * τ) z := by
  have h := chart_gradient_gaussDdim_transfer τ hτ (1 / 2) (by norm_num) W z hmin
  have hpref : (Real.sqrt ((1 / 2 : ℝ) / 2))⁻¹ ^ n = (2 : ℝ) ^ n := by
    rw [show ((1 / 2 : ℝ) / 2) = (2⁻¹) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [inv_inv]
  have hwidth : (2 * τ / (1 / 2 : ℝ)) = 4 * τ := by ring
  rw [hpref, hwidth] at h
  exact h

end QIQTH.CConvV2ChartComparison

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2ChartComparison
#print axioms sqrt_rncRadialSq
#print axioms chart_leftInverse_gate
#print axioms chart_firstJet_column_center
#print axioms chart_radial_twosided_center
#print axioms chart_radialLower_center
#print axioms rncRadialSq_le_card_normSq
#print axioms chart_radialUpper_of_normBound
#print axioms numerator_cauchy_schwarz
#print axioms jacobian_sumSq_le
#print axioms numerator_le_radial_mul
#print axioms gradient_scalar_transfer
#print axioms chart_gradient_gaussDdim_transfer
#print axioms chart_gradient_gaussDdim_transfer_half
end AxiomChecks
