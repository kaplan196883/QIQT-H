/-
  SlotInstantiationVII — J4-424 (Part B, tranche (a) phase 7): the R1–R5 RESIDUE CARRIES.  Continues
  `SlotInstantiationI..VI`.  This brick discharges the analytic HEART of the group-(1) residue — the
  pointwise ρ-deviation bound `|ρ − 1| ≤ Cρ·‖z‖³/τ` on the gate/collar-confined region (R1) — and the
  hf2/hf3 integrand INTEGRABILITIES from the bundle's banked measurabilities (R5).  R2/R3/R4 outcomes
  are documented in the PHASE 7 COVERAGE block.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  R1 — THE ρ-DEVIATION POWER/EXPONENT BUDGET (written BEFORE the proof, per spec).
    `rhoRatio τ z = G^chart/G_τ = exp(θ)`,  `θ = (r²_z − r²_{W z 0})/(4τ)`  (`W = uniformInverseChart`).
    Linearise the exponential with the ELEMENTARY MVT-FREE bound
        `|e^θ − 1| ≤ |θ|·e^{|θ|}`     (`abs_exp_sub_one_le`, from `Real.add_one_le_exp` twice — the
                                        same `1 − e^{−x} ≤ x` route as S5a, no MVT).
    NUMERATOR (near-isometry, CUBIC).  The two-sided chart near-isometry error
    `|r²_z − r²_{W z 0}| ≤ L·‖z‖·r²_z` (banked `chartW0_rncRadialSq_error`) + `r²_z ≤ n·‖z‖²`
    (`rncRadialSq_le_nsq`) gives `|num| ≤ L·n·‖z‖³`, hence `|θ| ≤ L·n·‖z‖³/(4τ)`.
    THE e^{|θ|} FACTOR — WHERE r₀/τ₀/COLLAR ENTER.  On the confined region `collarRegime` (`‖z‖ ≤ c√τ`,
    `τ ≤ τ₀`, `z ∈ K`, `‖z‖ < r₀`): `‖z‖³ ≤ c³·τ·√τ` so `|θ| ≤ L·n·c³·√τ/4 ≤ L·n·c³·√τ₀/4`, whence
    `e^{|θ|} ≤ exp(L·n·c³·√τ₀/4) = collarK L c τ₀` — a τ-INDEPENDENT constant.  This is EXACTLY the gate
    confinement bounding the exponential; the `‖z‖ < r₀`/`z ∈ K` conjuncts feed the near-isometry, the
    collar `‖z‖ ≤ c√τ` + window `τ ≤ τ₀` bound the exponent.  Assembling:
        `|ρ − 1| ≤ |θ|·e^{|θ|} ≤ (L·n·‖z‖³/(4τ))·collarK = (L·n·collarK/4)·(‖z‖³/τ)`,
    i.e. `Cρ = L·n·collarK L c τ₀ / 4` — τ-independent.

    ⚠ EXPONENT-BUDGET FAILURE OFF COLLAR (recorded for Sol, per spec).  This bound is HONEST ONLY on the
    confined region.  On `(collar (c√τ))ᶜ` (`‖z‖ > c√τ`) the factor `e^{|θ|}` is UNBOUNDED (with
    `‖z‖ = r₀` fixed and `τ → 0`, `‖z‖³/τ → ∞`), so the linear estimate DIVERGES: the pointwise
    `|ρ − 1| ≤ Cρ‖z‖³/τ` does NOT extend to all of `collarᶜ`.  The a.e. `hdom_comp` carry of
    `SlotInstantiationVI.hcomp_final` (a bound on `collarᶜ`) is therefore NOT the on-collar R1 bound
    directly; it is R1 combined with the SEPARATE off-gate amplitude-vanishing census (`hgate`, phase 6)
    — off gate `‖z‖ ≥ r₀` the amplitude `qc` vanishes, so the product is `0 ≤ comparisonDom`; the
    Gaussian-difference route `gaussDdim_replace_bound` (S5b, a `G_{2τ}` dominator) is the alternative
    that avoids the exp blow-up.  R1 here is the ANALYTIC HEART; the `collarᶜ` assembly is the census.

  R5 — the hf2/hf3 integrand integrabilities.  `Integrable.mono'` on the phase-5 dominators
  (`hf2_dom_integrable`/`hf3_dom_integrable`) + the a.e. dominations, with the integrand a.e.-strong
  measurability built COMPOSITIONALLY from the bundle's BANKED measurability fields
  (`hA1ampmeas`/`hA2ampmeas`/`hFmeas`) times the continuous `z_i/(2τ)` and `gaussDdim` factors — the
  DEFEQ-lesson trap (`fun_prop` on the `.choose`-heavy witness) is AVOIDED: only banked fields are used.

  NO `sorry`, no `:= True`, no new axioms; std-3.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.SlotInstantiationVI

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open QIQTH.SlotInstantiationIV QIQTH.SlotInstantiationV QIQTH.SlotInstantiationVI
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationVII

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — R1: the elementary exponential linearisation and the ρ-deviation bound.
    ############################################################################### -/

/-- **★ `abs_exp_sub_one_le`.**  THE ELEMENTARY MVT-FREE LINEARISATION: for every `θ`,
      `|e^θ − 1| ≤ |θ|·e^{|θ|}`.
    Route: `Real.add_one_le_exp` at `−θ` (times `e^θ`) gives `e^θ − 1 ≤ θ·e^θ`; at `θ` gives
    `1 − e^θ ≤ −θ`; combine with `θ·e^θ ≤ |θ|·e^{|θ|}` and `−θ ≤ |θ| ≤ |θ|·e^{|θ|}`.  NO MVT.  ⚠ NOT
    `a₁ = R/6`. -/
theorem abs_exp_sub_one_le (θ : ℝ) :
    |Real.exp θ - 1| ≤ |θ| * Real.exp |θ| := by
  have hupper : Real.exp θ - 1 ≤ θ * Real.exp θ := by
    have h := Real.add_one_le_exp (-θ)
    have hmul : (-θ + 1) * Real.exp θ ≤ Real.exp (-θ) * Real.exp θ :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos θ).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    nlinarith [hmul]
  have hlower : 1 - Real.exp θ ≤ -θ := by
    have h := Real.add_one_le_exp θ; linarith
  have hexp1 : (1 : ℝ) ≤ Real.exp |θ| := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (abs_nonneg θ)
  have hθexp : θ * Real.exp θ ≤ |θ| * Real.exp |θ| := by
    rcases le_total 0 θ with hθ | hθ
    · rw [abs_of_nonneg hθ]
    · have hexpnn := (Real.exp_pos θ).le
      have h0 : θ * Real.exp θ ≤ 0 := by
        nlinarith [mul_nonneg (neg_nonneg.mpr hθ) hexpnn]
      exact h0.trans (mul_nonneg (abs_nonneg θ) (Real.exp_pos _).le)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have hkey : 1 - Real.exp θ ≤ |θ| * Real.exp |θ| := by
      calc 1 - Real.exp θ ≤ -θ := hlower
        _ ≤ |θ| := neg_le_abs θ
        _ = |θ| * 1 := (mul_one _).symm
        _ ≤ |θ| * Real.exp |θ| := mul_le_mul_of_nonneg_left hexp1 (abs_nonneg θ)
    linarith
  · linarith [hupper, hθexp]

/-- **★★★ R1 — `rhoRatio_sub_one_bound`.**  THE ρ-DEVIATION BOUND, gate/collar-confined.  On the
    `collarRegime` (`0 < τ`, `τ ≤ τ₀`, `z ∈ K`, `‖z‖ < r₀`, `‖z‖ ≤ c√τ`), with the two-sided
    chart near-isometry error `hiso2` (`|r²_z − r²_{W z 0}| ≤ L·‖z‖·r²_z`, banked
    `chartW0_rncRadialSq_error`),
        `|rhoRatio τ z − 1| ≤ (L·n·collarK L c τ₀ / 4)·(‖z‖³/τ)`,
    i.e. `Cρ = L·n·collarK L c τ₀ / 4`.  Route: `abs_exp_sub_one_le` on the exponent
    `θ = (r²_z − r²_{W z 0})/(4τ)`; `|θ| ≤ L·n·‖z‖³/(4τ)` (near-isometry + `rncRadialSq_le_nsq`);
    `e^{|θ|} ≤ collarK` from the collar/window confinement (`‖z‖³ ≤ c³τ√τ`, `√τ ≤ √τ₀`).  This is the
    single analytic heart of the group-(1) residue.  ⚠ NOT `a₁ = R/6` (and see the header note: the
    bound is HONEST only on the confined region — it does NOT extend to `collarᶜ`). -/
theorem rhoRatio_sub_one_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (L c τ₀ r₀ : ℝ) (hL : 0 ≤ L)
    (hiso2 : ∀ z ∈ K, ‖z‖ < r₀ →
      |rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)|
        ≤ L * ‖z‖ * rncRadialSq z)
    (τ : ℝ) (z : Point n) (hreg : collarRegime (K := K) r₀ c τ₀ τ z) :
    |rhoRatio g gi hC hK τ z - 1|
      ≤ L * (n : ℝ) * collarK (n := n) L c τ₀ / 4 * (‖z‖ ^ 3 / τ) := by
  obtain ⟨hτ, hττ₀, hzK, hzr, hzc⟩ := hreg
  have h4τ : (0 : ℝ) < 4 * τ := by positivity
  set num := rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0) with hnum
  have hρ : rhoRatio g gi hC hK τ z = Real.exp (num / (4 * τ)) := by rw [rhoRatio, hnum]
  rw [hρ]
  have hsqrtτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hc0 : 0 ≤ c := by nlinarith [le_trans (norm_nonneg z) hzc, hsqrtτ]
  -- |num| ≤ L·n·‖z‖³
  have hnumabs : |num| ≤ L * (n : ℝ) * ‖z‖ ^ 3 := by
    have h1 := hiso2 z hzK hzr
    have h2 : rncRadialSq z ≤ (n : ℝ) * ‖z‖ ^ 2 := AmplitudeDataOnCollar.rncRadialSq_le_nsq z
    calc |num| ≤ L * ‖z‖ * rncRadialSq z := h1
      _ ≤ L * ‖z‖ * ((n : ℝ) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hL (norm_nonneg z))
      _ = L * (n : ℝ) * ‖z‖ ^ 3 := by ring
  -- ‖z‖³ ≤ c³·τ·√τ
  have h3 : ‖z‖ ^ 3 ≤ c ^ 3 * (τ * Real.sqrt τ) := by
    have h3a : ‖z‖ ^ 3 ≤ (c * Real.sqrt τ) ^ 3 := pow_le_pow_left₀ (norm_nonneg z) hzc 3
    have hsq : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
    calc ‖z‖ ^ 3 ≤ (c * Real.sqrt τ) ^ 3 := h3a
      _ = c ^ 3 * (Real.sqrt τ ^ 2 * Real.sqrt τ) := by ring
      _ = c ^ 3 * (τ * Real.sqrt τ) := by rw [hsq]
  -- |θ| ≤ L·n·‖z‖³/(4τ)
  have hθb : |num / (4 * τ)| ≤ L * (n : ℝ) * ‖z‖ ^ 3 / (4 * τ) := by
    rw [abs_div, abs_of_pos h4τ, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnumabs (inv_nonneg.mpr h4τ.le)
  -- exponent budget: |θ| ≤ L·n·c³·√τ₀/4
  have hexpbudget : |num / (4 * τ)| ≤ L * (n : ℝ) * c ^ 3 * Real.sqrt τ₀ / 4 := by
    rw [abs_div, abs_of_pos h4τ, div_le_iff₀ h4τ]
    calc |num| ≤ L * (n : ℝ) * ‖z‖ ^ 3 := hnumabs
      _ ≤ L * (n : ℝ) * (c ^ 3 * (τ * Real.sqrt τ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = L * (n : ℝ) * c ^ 3 * τ * Real.sqrt τ := by ring
      _ ≤ L * (n : ℝ) * c ^ 3 * τ * Real.sqrt τ₀ :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hττ₀) (by positivity)
      _ = L * (n : ℝ) * c ^ 3 * Real.sqrt τ₀ / 4 * (4 * τ) := by ring
  -- e^{|θ|} ≤ collarK
  have hexpθ : Real.exp |num / (4 * τ)| ≤ collarK (n := n) L c τ₀ := by
    rw [collarK]; exact Real.exp_le_exp.mpr hexpbudget
  have hτne : τ ≠ 0 := hτ.ne'
  calc |Real.exp (num / (4 * τ)) - 1|
      ≤ |num / (4 * τ)| * Real.exp |num / (4 * τ)| := abs_exp_sub_one_le _
    _ ≤ (L * (n : ℝ) * ‖z‖ ^ 3 / (4 * τ)) * collarK (n := n) L c τ₀ :=
        mul_le_mul hθb hexpθ (Real.exp_pos _).le
          (div_nonneg (mul_nonneg (mul_nonneg hL (Nat.cast_nonneg n))
            (by positivity)) h4τ.le)
    _ = L * (n : ℝ) * collarK (n := n) L c τ₀ / 4 * (‖z‖ ^ 3 / τ) := by
        field_simp

/-! ###############################################################################
    ### §2 — R5: the hf2/hf3 integrand integrabilities (compositional measurability).
    ############################################################################### -/

/-- **★ R5 (hf2) — `hf2int_at_witness`.**  The term-2 integrand `z_i/(2τ)·G_τ·A1amp·F` is (full-space)
    INTEGRABLE at the witness: from the phase-5 dominator `hf2_dom_integrable` and the a.e. domination
    `hf2dom` (phase 6), via `Integrable.mono'`, with the integrand's a.e.-strong measurability built
    COMPOSITIONALLY (`.mul`) from the bundle's banked `hA1ampmeas`/`hFmeas` fields times the continuous
    `z_i/(2τ)` and `gaussDdim τ` factors.  No `fun_prop` on the `.choose`-heavy witness (DEFEQ lesson).
    ⚠ NOT `a₁ = R/6`. -/
theorem hf2int_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M : ℝ)
    (hf2dom : ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z)) :
    Integrable (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume := by
  have hm1 : Continuous (fun z : Point n => z i / (2 * τ)) := (continuous_apply i).div_const _
  have m1 : AEStronglyMeasurable (fun z : Point n => z i / (2 * τ)) volume :=
    hm1.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun z : Point n => gaussDdim τ z) volume :=
    (gaussDdim_integrable τ hτ).aestronglyMeasurable
  have m3 := data.hA1ampmeas τ
  have m4 := data.hFmeas s
  exact (QIQTH.SlotInstantiationV.hf2_dom_integrable τ hτ i M).mono'
    (((m1.mul m2).mul m3).mul m4) hf2dom

/-- **★ R5 (hf3) — `hf3int_at_witness`.**  The term-3 integrand `G_τ·A2amp·F` is (full-space)
    INTEGRABLE at the witness: from `hf3_dom_integrable` + the a.e. domination `hf3dom` via
    `Integrable.mono'`, measurability compositional from banked `hA2ampmeas`/`hFmeas`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hf3int_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Sconst : ℝ)
    (hf3dom : ∀ᵐ z,
      ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z) :
    Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume := by
  have m2 : AEStronglyMeasurable (fun z : Point n => gaussDdim τ z) volume :=
    (gaussDdim_integrable τ hτ).aestronglyMeasurable
  have m3 := data.hA2ampmeas τ
  have m4 := data.hFmeas s
  exact (QIQTH.SlotInstantiationV.hf3_dom_integrable τ hτ Sconst).mono'
    ((m2.mul m3).mul m4) hf3dom

/-! ###############################################################################
    ### §3 — R3: off-collar residual-difference integrability (re-export, WIRING).
    ############################################################################### -/

/-- **★ R3 — `hcompDiff_int_at_witness`.**  THE off-collar integrability of the comparison-leg
    difference `IchartResidual − hessGaussFactor·qc` at the witness, re-exported from the phase-4
    `hcompDiff_int_residual` (WIRING: `IchartResidual` off-collar integrable + `hessGaussFactor·qc`
    integrable for the bounded `qc = chartAmp·F`).  This is exactly the `hcompDiff_int` carry consumed by
    `SlotInstantiationVI.hcomp_final`.  ⚠ NOT `a₁ = R/6`. -/
theorem hcompDiff_int_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Mqc : ℝ)
    (hqcmeas : AEStronglyMeasurable (fun z => chartAmp g gi hC hK a b τ z 0 * F s z 0) volume)
    (hqcbdd : ∀ z, ‖chartAmp g gi hC hK a b τ z 0 * F s z 0‖ ≤ Mqc)
    (hIchart_int : IntegrableOn (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume) :
    IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume :=
  QIQTH.SlotInstantiationIV.hcompDiff_int_residual g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ
    (fun z => chartAmp g gi hC hK a b τ z 0 * F s z 0) Mqc hqcmeas hqcbdd hIchart_int

/-! ###############################################################################
    ### §4 — R2: the off-collar jet-supply `hform` (pointwise, WIRING).
    ############################################################################### -/

/-- **★ R2 — `hform_at_witness`.**  THE off-collar jet supply `hform`: on `(collar (c√τ))ᶜ`,
      `IchartResidual − hessGaussFactor·qc = hessGaussFactor·((ρ − 1)·qc)`,
    supplied pointwise from the phase-5 `ichartResidual_sub_hess_form` given the regime-uniform jet
    data + the concrete ρ-scaled amplitude identities `hA1eq`/`hA2eq` (`rfl` for the concrete bundle).
    The jet supply is the honest off-collar carry (chart jets + open gate at base `z`, honest wherever
    `z ∈ K`).  ⚠ NOT `a₁ = R/6`. -/
theorem hform_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ)
    (hA1eq : ∀ z, data.A1amp τ z
      = rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0))
    (hA2eq : ∀ z, data.A2amp τ z
      = rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0)
    (hjet : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      z ∈ K ∧ IsOpen (S z) ∧ (0 : Point n) ∈ S z ∧
      ∃ (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ),
        (∀ x k, HasDerivAt
          (fun t : ℝ => uniformInverseChart g gi hC hK z (Function.update x i t) k) (P x k) (x i)) ∧
        (∀ k, HasDerivAt
          (fun t : ℝ => P (Function.update (0 : Point n) i t) k) (Q k) ((0 : Point n) i)) ∧
        (∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x) ∧
        PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n) ∧
        (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i) ∧
        (∑ k, P 0 k ^ 2 = 1) ∧
        (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)) :
    ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) := by
  intro z hz
  obtain ⟨hzK, hSopen, h0, P, Q, hV1, hP1, hA1, hA2, hVP, hPsq, hVQ⟩ := hjet z hz
  exact QIQTH.SlotInstantiationV.ichartResidual_sub_hess_form g gi hC hK S a b F i T τ₀ r₀ c data τ s
    hτ z hzK hSopen h0 P Q hV1 hP1 hA1 hA2 hVP hPsq hVQ (hA1eq z) (hA2eq z)

/-! ###############################################################################
    ### PACKAGE — the phase-7 conjunction.
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase7`.**  THE PHASE-7 PACKAGE: the phase-6 group-(1) carries (held as
    `Pphase6`) CONJOINED with
      • R1 (`rhoRatio_sub_one_bound`) — the pointwise ρ-deviation bound `|ρ − 1| ≤ Cρ·‖z‖³/τ` on the
        confined region (`Cρ = L·n·collarK/4`), the analytic heart, AND
      • R5 (`hf2int_at_witness`/`hf3int_at_witness`) — the hf2/hf3 integrand integrabilities from the
        banked measurabilities + the a.e. dominations.
    ⚠ R1 is HONEST ONLY on `collarRegime`; the `collarᶜ` `hdom_comp` assembly still needs the off-gate
    census (see PHASE 7 COVERAGE).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase7 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M Sconst L : ℝ) (hL : 0 ≤ L)
    (hiso2 : ∀ z ∈ K, ‖z‖ < r₀ →
      |rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)|
        ≤ L * ‖z‖ * rncRadialSq z)
    (Pphase6 : Prop) (hphase6 : Pphase6)
    (hf2dom : ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z))
    (hf3dom : ∀ᵐ z,
      ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z) :
    Pphase6
    ∧ (∀ z : Point n, collarRegime (K := K) r₀ c τ₀ τ z →
        |rhoRatio g gi hC hK τ z - 1|
          ≤ L * (n : ℝ) * collarK (n := n) L c τ₀ / 4 * (‖z‖ ^ 3 / τ))
    ∧ Integrable (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume
    ∧ Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume :=
  ⟨hphase6,
   (fun z hreg => rhoRatio_sub_one_bound g gi hC hK L c τ₀ r₀ hL hiso2 τ z hreg),
   hf2int_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ M hf2dom,
   hf3int_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ Sconst hf3dom⟩

end QIQTH.SlotInstantiationVII

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationVII
#print axioms abs_exp_sub_one_le
#print axioms rhoRatio_sub_one_bound
#print axioms hf2int_at_witness
#print axioms hf3int_at_witness
#print axioms hcompDiff_int_at_witness
#print axioms hform_at_witness
#print axioms slotInstantiation_phase7
end AxiomChecks

/-! ###############################################################################
    ## PHASE 7 COVERAGE  (J4-424, Part B, tranche (a))
    ###############################################################################

  R1 — `hdom_comp` ρ-deviation.  OUTCOME: the pointwise bound `|ρ − 1| ≤ (L·n·collarK/4)·(‖z‖³/τ)` is
  DISCHARGED on the confined region `collarRegime` (`rhoRatio_sub_one_bound`), via the elementary
  MVT-free `abs_exp_sub_one_le` (`|e^θ − 1| ≤ |θ|·e^{|θ|}`) + the cubic near-isometry numerator + the
  collar/window exponent budget (`e^{|θ|} ≤ collarK`).  This is the SINGLE ANALYTIC HEART.
    ⚠ WEAKENED-BUT-HONEST / EXACT FAILURE FOR SOL.  The bound does NOT extend to all of `(collar)ᶜ`:
    off collar (`‖z‖ > c√τ`) the factor `e^{|θ|}` with `|θ| ≤ L·n·‖z‖³/(4τ)` is UNBOUNDED (fix
    `‖z‖ = r₀`, let `τ → 0`), so the linear exp estimate diverges.  Hence the a.e. `hdom_comp` carry of
    `hcomp_final` (a bound on `collarᶜ`, with the `G_τ` dominator `comparisonDom`) is NOT R1 alone.  Two
    honest closures for J4-425:
      (a) COMBINE R1 with the off-gate amplitude-vanishing census `hgate` (phase 6): where `‖z‖ ≥ r₀`
          the amplitude `qc` vanishes ⟹ product `0 ≤ comparisonDom`; the finite gate annulus
          `c√τ < ‖z‖ < r₀` STILL has the blow-up, so (a) ALONE is insufficient.
      (b) THE GAUSSIAN-DIFFERENCE ROUTE (recommended).  `hessGaussFactor·(ρ − 1)·qc =
          (z_i²−2τ)/(4τ²)·(G^chart − G_τ)·qc` (since `(ρ−1)·G_τ = G^chart − G_τ` by `gauss_ratio_rho`),
          and S5b `gaussDdim_replace_bound` bounds `|G^chart − G_τ| ≤ (L'‖z‖³/(4τ))·(√2)ⁿ·G_{2τ}`
          GLOBALLY (no exp blow-up).  This yields a `G_{2τ}` dominator whose moment is again `C/√τ` (the
          `τ^{5/2}` κ=2 quintic moment ÷ `1/τ³` prefactor), so it discharges `hdom_comp` on ALL of
          `collarᶜ` at the cost of a NEW `comparisonDom2` (width-`2τ`) + its `κ=2` moment lemma.  This is
          the recommended J4-425 target.

  R2 — `hform` off-collar jet supply.  OUTCOME: DISCHARGED pointwise (`hform_at_witness`) from the
  phase-5 `ichartResidual_sub_hess_form` given the regime-uniform jet data `hjet` + the concrete
  ρ-scaled amplitude identities `hA1eq`/`hA2eq` (`rfl` for `amplitudeDataOn_concrete`).  The jet supply
  `hjet` (chart jets + open gate at base `z`, honest wherever `z ∈ K`) is the standing carry.

  R3 — `hcompDiff_int` off-collar residual-difference integrability.  OUTCOME: DISCHARGED
  (`hcompDiff_int_at_witness`) as a re-export of phase-4 `hcompDiff_int_residual` at `qc = chartAmp·F`
  (WIRING: `IchartResidual` off-collar integrable + `hessGaussFactor·qc` integrable for bounded `qc`).
  Standing inputs: the off-collar integrability of `IchartResidual` (phase-3 `hIchart_int_final`) and
  the bounded-`qc` sup `Mqc` (= R4).

  R4 — `hf2amp`/`hf3amp` (and `Mqc`).  OUTCOME: GENUINE SUP CARRY (NOT dischargeable here without a
  gate-vanishing fact).  The GLOBAL amplitude·Levi sups `∀ z, |A1amp·F| ≤ M`, `|A2amp·F| ≤ Sconst`
  (and `‖chartAmp·F‖ ≤ Mqc`) hold on the regime via the bundle's `hA1ampBdd`/`hA2ampBdd` but need the
  off-regime amplitude vanishing (the gate census) to be GLOBAL.  Carrying an off-gate near-isometry /
  amplitude bound as a hypothesis would be an UNSATISFIABLE (vacuity) hypothesis — deliberately NOT done
  (axiom-budget blind-spot avoidance).  Named honestly as a sup + gate-census carry.

  R5 — `hf2int`/`hf3int` integrand integrabilities.  OUTCOME: DISCHARGED
  (`hf2int_at_witness`/`hf3int_at_witness`) via `Integrable.mono'` on the phase-5 dominators + the a.e.
  dominations, with the integrand a.e.-strong measurability built COMPOSITIONALLY from the bundle's
  BANKED `hA1ampmeas`/`hA2ampmeas`/`hFmeas` fields (× continuous `z_i/(2τ)`, `gaussDdim`).  The DEFEQ
  lesson is respected — no `fun_prop` on the `.choose`-heavy witness; only banked fields + `.mul`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ UPDATED GROUP-(1) RESIDUE (after phases 1–7).  NOT empty — the milestone is NOT reached:
    • R1/`hdom_comp` on `collarᶜ` — the ANALYTIC HEART (on-collar `|ρ−1|` bound) is DONE, but the a.e.
      bound on `collarᶜ` needs the S5b `G_{2τ}` dominator route (J4-425 target (b) above), NOT the
      on-collar bound.
    • R2/`hform` jet supply `hjet` — pointwise discharge DONE; the jet data is the standing carry.
    • R4 — the global amplitude·Levi sups (`M`/`Sconst`/`Mqc`) = sup + gate-census carry.
  R3 (`hcompDiff_int`) and R5 (`hf2int`/`hf3int`) are DISCHARGED (as wiring).  The slot-instantiation
  ALGEBRA of group (1) remains complete; what stands is the ρ-deviation `collarᶜ` closure (S5b) + the
  sup/gate-census carries.  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio +
  geometric-wiring stack.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
