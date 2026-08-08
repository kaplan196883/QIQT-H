/-
  SlotInstantiationVI — J4-423 (Part B, tranche (a) phase 6): CLOSE the last group-(1) geometric
  carries.  Continues `SlotInstantiationI..V`.  This brick discharges the ARITHMETIC BACKBONE of the
  `hcomp` cubic comparison leg (the `(ρ−1)`-weighted Hessian-Gaussian dominator and its `C/√τ` moment,
  fully proved with the τ-power count), wires it into `SlotInstantiationV.hcomp_collapsed` to produce
  `hcomp_final`, and FULLY discharges the hf2/hf3 a.e. dominations from a global amplitude sup.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  THE CUBIC CARRY (Part B, phase-5 `hcomp_collapsed` residue).  Phase 5 collapsed the comparison leg to
  ONE explicit cubic-form dominator problem: bound `‖H·(ρ−1)·qc‖` (with `H = hessGaussFactor`,
  `qc = chartAmp·F`) by an off-collar dominator `D` with `∫_{collarᶜ} D ≤ Bcomp/√τ`.

  POWER COUNT (written BEFORE the proof, per spec).  Off collar, under the ρ-deviation carry
  `|ρ−1| ≤ Cρ·‖z‖³/τ` (the near-isometry cubic-contact bound, gate-confined — see trap (iii) below) and
  the amplitude sup `|qc| ≤ Mqc`, and `|z_i²−2τ| ≤ ‖z‖²+2τ`:
      ‖H·(ρ−1)·qc‖ ≤ (‖z‖²+2τ)/(4τ²)·G_τ · (Cρ‖z‖³/τ) · Mqc
                   = (Cρ·Mqc/(4τ³))·(‖z‖⁵ + 2τ‖z‖³)·G_τ  =: D(z).
  Integrating (full-space upper bound, since `D ≥ 0` and `∫_{collarᶜ} D ≤ ∫_ℝⁿ D`), with the banked
  n-D Gaussian moments `∫‖z‖⁵G_τ ≤ n·1600√2·(√τ)⁵` and `∫‖z‖³G_τ ≤ n·(64√2+1)·(√τ)³`:
      ∫ D = (Cρ Mqc/(4τ³))·[∫‖z‖⁵G_τ + 2τ·∫‖z‖³G_τ]
          ≤ (Cρ Mqc/(4τ³))·[n·1600√2·τ^{5/2} + 2τ·n(64√2+1)·τ^{3/2}]
          = (Cρ Mqc/(4τ³))·n·τ^{5/2}·(1600√2 + 2(64√2+1))
          = (Cρ Mqc·n/(4))·(1728√2+2)·τ^{5/2−3}
          = (Cρ Mqc·n·(864√2+1)/2)·τ^{−1/2}  =  Bcomp/√τ,  Bcomp = Cρ Mqc n (864√2+1)/2.
  The `τ^{5/2}` cubic moment ÷ the `1/τ³` Hessian/`ρ` prefactor produces EXACTLY `τ^{−1/2} = 1/√τ` — the
  matched sliver shape.  τ-INDEPENDENT numerator `Bcomp`.

  Sol #19 trap (iii) (the τ-window) is respected as follows.  The `C/√τ` conversion here is EXACT from
  the closed-form Gaussian moments — no τ-window is needed for the MOMENT arithmetic (the full-space
  moments scale as `τ^{k/2}` unconditionally).  The τ-window / gate-confinement is what makes the
  POINTWISE ρ-deviation carry `|ρ−1| ≤ Cρ·‖z‖³/τ` honest: off collar `‖z‖³/τ` is unbounded, so the
  linear `exp(θ)−1 ≈ θ` estimate needs the gate radius `r₀` (the gated witness vanishes beyond `r₀`,
  census carry `hgate`) + the window `τ ≤ τ₀` to keep `θ = O(‖z‖³/τ)` controlled on the support.  That
  pointwise bound is therefore CARRIED here (as `hdom`, the single geometric heart), NOT re-proved; the
  MOMENT/integrability arithmetic that consumes it is FULLY discharged below.

  NO `sorry`, no `:= True`, no new axioms; std-3.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.SlotInstantiationV
import QIQTH.HessianSliceBound

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open QIQTH.SlotInstantiationIV QIQTH.SlotInstantiationV
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationVI

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the two banked n-D Gaussian moments specialised to width `τ` (κ = 1).
    ############################################################################### -/

/-- **★ `normPow5_gauss_bound`.**  The width-`τ` quintic Gaussian moment
      `∫_z ‖z‖⁵·G_τ(z) ≤ n·1600√2·(√τ)⁵`,
    from `pow_norm_mul_gauss_integral` at `k = 5, κ = 1` fed the 1-D `oneD_absMoment5`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem normPow5_gauss_bound (τ : ℝ) (hτ : 0 < τ) :
    (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim τ z)
      ≤ (n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5 := by
  have h1τ : (0 : ℝ) < 1 * τ := by rw [one_mul]; exact hτ
  have h := pow_norm_mul_gauss_integral (n := n) 5 (by norm_num) 1 one_pos τ hτ
    (1600 * Real.sqrt 2) (by positivity) (oneD_absMoment5 (1 * τ) h1τ)
  rw [one_mul] at h
  simpa [Real.sqrt_one] using h

/-- **★ `normPow3_gauss_bound`.**  The width-`τ` cubic Gaussian moment
      `∫_z ‖z‖³·G_τ(z) ≤ n·(64√2+1)·(√τ)³`,
    from `pow_norm_mul_gauss_integral` at `k = 3, κ = 1` fed the 1-D `oneD_absMoment3`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem normPow3_gauss_bound (τ : ℝ) (hτ : 0 < τ) :
    (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3 := by
  have h1τ : (0 : ℝ) < 1 * τ := by rw [one_mul]; exact hτ
  have h := pow_norm_mul_gauss_integral (n := n) 3 (by norm_num) 1 one_pos τ hτ
    (64 * Real.sqrt 2 + 1) (by positivity) (oneD_absMoment3 (1 * τ) h1τ)
  rw [one_mul] at h
  simpa [Real.sqrt_one] using h

/-! ###############################################################################
    ### §2 — the explicit off-collar cubic dominator and its `C/√τ` moment.
    ############################################################################### -/

/-- **★ `comparisonDom`.**  THE EXPLICIT OFF-COLLAR CUBIC DOMINATOR of the `hcomp` comparison integrand
    `H·(ρ−1)·qc`, from the power count above:
      `comparisonDom τ Cρ Mqc z := (Cρ·Mqc/(4τ³))·((‖z‖⁵ + 2τ‖z‖³)·G_τ(z))`.
    Here `Cρ` is the ρ-deviation constant (`|ρ−1| ≤ Cρ·‖z‖³/τ`, gate-confined) and `Mqc` the amplitude
    sup (`|qc| ≤ Mqc`).  ⚠ NOT `a₁ = R/6`. -/
noncomputable def comparisonDom (τ Cρ Mqc : ℝ) (z : Point n) : ℝ :=
  Cρ * Mqc / (4 * τ ^ 3) * ((‖z‖ ^ 5 + 2 * τ * ‖z‖ ^ 3) * gaussDdim τ z)

/-- **`comparisonDom_nonneg`.**  The dominator is nonnegative (`Cρ, Mqc ≥ 0`, `τ > 0`,
    `G_τ ≥ 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem comparisonDom_nonneg (τ Cρ Mqc : ℝ) (hτ : 0 < τ) (hCρ : 0 ≤ Cρ) (hMqc : 0 ≤ Mqc)
    (z : Point n) : 0 ≤ comparisonDom τ Cρ Mqc z := by
  unfold comparisonDom
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  have hfac : (0 : ℝ) ≤ ‖z‖ ^ 5 + 2 * τ * ‖z‖ ^ 3 := by positivity
  have hcoef : (0 : ℝ) ≤ Cρ * Mqc / (4 * τ ^ 3) := by positivity
  exact mul_nonneg hcoef (mul_nonneg hfac hG)

/-- **`comparisonDom_integrable`.**  The dominator is integrable (split into the quintic and cubic
    `‖z‖^k·G_τ` pieces via `normPow_gauss_integrable`).  ⚠ NOT `a₁ = R/6`. -/
theorem comparisonDom_integrable (τ Cρ Mqc : ℝ) (hτ : 0 < τ) :
    Integrable (comparisonDom (n := n) τ Cρ Mqc) volume := by
  have hI1 : Integrable (fun z : Point n =>
      Cρ * Mqc / (4 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim τ z)) volume :=
    (normPow_gauss_integrable 5 (by norm_num) τ hτ).const_mul _
  have hI2 : Integrable (fun z : Point n =>
      Cρ * Mqc / (4 * τ ^ 3) * (2 * τ) * (‖z‖ ^ 3 * gaussDdim τ z)) volume :=
    (normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _
  refine (hI1.add hI2).congr (ae_of_all _ (fun z => ?_))
  simp only [Pi.add_apply]; unfold comparisonDom; ring

/-- **★★ `comparisonDom_moment` — THE CUBIC-CARRY MOMENT DISCHARGE.**  The full-space integral of the
    off-collar cubic dominator obeys the matched sliver bound
      `∫_z comparisonDom τ Cρ Mqc z ≤ (Cρ·Mqc·n·(864√2+1)/2)/√τ`.
    This is the `C/√τ` power count of the header, FULLY PROVED: the `τ^{5/2}` cubic Gaussian moment ÷
    the `1/τ³` Hessian/ρ prefactor yields EXACTLY `τ^{−1/2}`.  τ-independent numerator.  ⚠ NOT
    `a₁ = R/6`. -/
theorem comparisonDom_moment (τ Cρ Mqc : ℝ) (hτ : 0 < τ) (hCρ : 0 ≤ Cρ) (hMqc : 0 ≤ Mqc) :
    (∫ z : Point n, comparisonDom τ Cρ Mqc z)
      ≤ Cρ * Mqc * (n : ℝ) * (864 * Real.sqrt 2 + 1) / 2 / Real.sqrt τ := by
  have hc : (0 : ℝ) ≤ Cρ * Mqc / (4 * τ ^ 3) := by positivity
  have hc2τ : (0 : ℝ) ≤ Cρ * Mqc / (4 * τ ^ 3) * (2 * τ) := by positivity
  have hI1 : Integrable (fun z : Point n =>
      Cρ * Mqc / (4 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim τ z)) volume :=
    (normPow_gauss_integrable 5 (by norm_num) τ hτ).const_mul _
  have hI2 : Integrable (fun z : Point n =>
      Cρ * Mqc / (4 * τ ^ 3) * (2 * τ) * (‖z‖ ^ 3 * gaussDdim τ z)) volume :=
    (normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _
  have hsplit : (fun z : Point n => comparisonDom τ Cρ Mqc z)
      = (fun z => Cρ * Mqc / (4 * τ ^ 3) * (‖z‖ ^ 5 * gaussDdim τ z)
          + Cρ * Mqc / (4 * τ ^ 3) * (2 * τ) * (‖z‖ ^ 3 * gaussDdim τ z)) := by
    funext z; unfold comparisonDom; ring
  rw [hsplit, integral_add hI1 hI2, integral_const_mul, integral_const_mul]
  calc Cρ * Mqc / (4 * τ ^ 3) * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim τ z)
          + Cρ * Mqc / (4 * τ ^ 3) * (2 * τ) * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
      ≤ Cρ * Mqc / (4 * τ ^ 3) * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt τ) ^ 5)
          + Cρ * Mqc / (4 * τ ^ 3) * (2 * τ)
              * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3) :=
        add_le_add (mul_le_mul_of_nonneg_left (normPow5_gauss_bound τ hτ) hc)
          (mul_le_mul_of_nonneg_left (normPow3_gauss_bound τ hτ) hc2τ)
    _ = Cρ * Mqc * (n : ℝ) * (864 * Real.sqrt 2 + 1) / 2 / Real.sqrt τ := by
        have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
        set s := Real.sqrt τ with hsdef
        have hτs : τ = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hτ.le).symm
        rw [hτs]; field_simp; ring

/-! ###############################################################################
    ### §3 — `hcomp_final`: the comparison leg discharged at the cubic dominator.
    ############################################################################### -/

/-- **★★★ `hcomp_final` — THE COMPARISON LEG, moment/integrability FULLY DISCHARGED.**  Instantiating
    `SlotInstantiationV.hcomp_collapsed` at `D := comparisonDom` and `Bcomp := Cρ·Mqc·n·(864√2+1)/2`,
    the `hDint`/`hmom` legs are DISCHARGED here (`comparisonDom_integrable` and
    `comparisonDom_moment` + `setIntegral_le_integral`, `D ≥ 0`), giving
      `‖∫_{(collar (c√τ))ᶜ} (IchartResidual − hessGaussFactor·qc)‖ ≤ (Cρ·Mqc·n·(864√2+1)/2)/√τ`.
    The three carried inputs are: `hcompDiff_int` (off-collar integrability of the residual difference,
    phase-3 content), `hform` (the off-collar jet-supply — discharged pointwise by
    `ichartResidual_sub_hess_form` wherever the chart jets hold), and `hdom` (THE geometric heart: the
    pointwise `‖H·(ρ−1)·qc‖ ≤ comparisonDom`, i.e. `|ρ−1| ≤ Cρ‖z‖³/τ` (near-isometry, gate-confined) ×
    the amplitude sup `Mqc`).  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Cρ Mqc : ℝ) (hCρ : 0 ≤ Cρ) (hMqc : 0 ≤ Mqc)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (hdom : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖hessGaussFactor i τ z
          * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ comparisonDom τ Cρ Mqc z) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ Cρ * Mqc * (n : ℝ) * (864 * Real.sqrt 2 + 1) / 2 / Real.sqrt τ :=
  hcomp_collapsed g gi hC hK S a b F i T τ₀ r₀ c data τ s
    (comparisonDom τ Cρ Mqc) (Cρ * Mqc * (n : ℝ) * (864 * Real.sqrt 2 + 1) / 2)
    hcompDiff_int
    ((comparisonDom_integrable τ Cρ Mqc hτ).integrableOn)
    hform hdom
    (by
      calc ∫ z in (collar (c * Real.sqrt τ))ᶜ, comparisonDom τ Cρ Mqc z
          ≤ ∫ z : Point n, comparisonDom τ Cρ Mqc z :=
            setIntegral_le_integral (comparisonDom_integrable τ Cρ Mqc hτ)
              (ae_of_all _ (fun z => comparisonDom_nonneg τ Cρ Mqc hτ hCρ hMqc z))
        _ ≤ _ := comparisonDom_moment τ Cρ Mqc hτ hCρ hMqc)

/-! ###############################################################################
    ### §4 — hf2/hf3 a.e. dominations FULLY discharged from a global amplitude sup.
    ############################################################################### -/

/-- **★ `hf2dom_at_witness`.**  The `hf2bound` a.e. domination `hdom`, FULLY discharged from a GLOBAL
    amplitude sup `∀ z, |A1amp·F| ≤ M` via `hf2_ptwise_dom_of_ampBound` + `ae_of_all`.  This turns the
    phase-5 per-point domination into the exact a.e. carry consumed by `hf2bound_at_witness`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hf2dom_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M : ℝ) (hamp : ∀ z, |data.A1amp τ z * F s z 0| ≤ M) :
    ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z) :=
  ae_of_all _ (fun z =>
    hf2_ptwise_dom_of_ampBound g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ M z (hamp z))

/-- **★ `hf3dom_at_witness`.**  The `hf3bound` a.e. domination `hdom`, FULLY discharged from a GLOBAL
    amplitude sup `∀ z, |A2amp·F| ≤ Sconst` via `hf3_ptwise_dom_of_ampBound` + `ae_of_all`.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hf3dom_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Sconst : ℝ) (hamp : ∀ z, |data.A2amp τ z * F s z 0| ≤ Sconst) :
    ∀ᵐ z, ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z :=
  ae_of_all _ (fun z =>
    hf3_ptwise_dom_of_ampBound g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ Sconst z (hamp z))

/-! ###############################################################################
    ### PACKAGE — the phase-6 conjunction.
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase6`.**  THE PHASE-6 PACKAGE: the phase-5 group-(1) carries (held as
    `Pphase5`) CONJOINED with
      • `hcomp_final` — the comparison leg with the cubic dominator's moment/integrability FULLY
        discharged (`≤ (Cρ·Mqc·n·(864√2+1)/2)/√τ`), MODULO the three named carries
        (`hcompDiff_int`, `hform`, `hdom_comp`), AND
      • the hf2/hf3 a.e. dominations FULLY discharged from the global amplitude sups
        (`hf2dom_at_witness`/`hf3dom_at_witness`).
    With this, the group-(1) slot-instantiation algebra is COMPLETE (phases 1–6): the surviving residue
    is exactly the enumerable FACTOR/SUP + jet-supply carries (see the PHASE 6 COVERAGE block).  ⚠ NOT
    `a₁ = R/6`. -/
theorem slotInstantiation_phase6 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Cρ Mqc M Sconst : ℝ) (hCρ : 0 ≤ Cρ) (hMqc : 0 ≤ Mqc)
    (Pphase5 : Prop) (hphase5 : Pphase5)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (hdom_comp : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖hessGaussFactor i τ z
          * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ comparisonDom τ Cρ Mqc z)
    (hf2amp : ∀ z, |data.A1amp τ z * F s z 0| ≤ M)
    (hf3amp : ∀ z, |data.A2amp τ z * F s z 0| ≤ Sconst) :
    Pphase5
    ∧ (‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ Cρ * Mqc * (n : ℝ) * (864 * Real.sqrt 2 + 1) / 2 / Real.sqrt τ)
    ∧ (∀ᵐ z, ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z))
    ∧ (∀ᵐ z, ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z) :=
  ⟨hphase5,
   hcomp_final g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ Cρ Mqc hCρ hMqc
     hcompDiff_int hform hdom_comp,
   hf2dom_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ M hf2amp,
   hf3dom_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ Sconst hf3amp⟩

end QIQTH.SlotInstantiationVI

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationVI
#print axioms normPow5_gauss_bound
#print axioms normPow3_gauss_bound
#print axioms comparisonDom_nonneg
#print axioms comparisonDom_integrable
#print axioms comparisonDom_moment
#print axioms hcomp_final
#print axioms hf2dom_at_witness
#print axioms hf3dom_at_witness
#print axioms slotInstantiation_phase6
end AxiomChecks

/-! ###############################################################################
    ## PHASE 6 COVERAGE  (J4-423, Part B, tranche (a))
    ###############################################################################

  THE CUBIC CARRY — DISCHARGED at the moment level.  The phase-5 `hcomp_collapsed` residue (the single
  explicit `H·(ρ−1)·qc` dominator problem) is now closed on its ARITHMETIC side:
    • `comparisonDom` — the explicit off-collar dominator `(Cρ Mqc/(4τ³))·(‖z‖⁵+2τ‖z‖³)·G_τ`.
    • `comparisonDom_moment` — `∫_z comparisonDom ≤ (Cρ Mqc n (864√2+1)/2)/√τ`, the EXACT `C/√τ` power
      count (τ^{5/2} cubic moment ÷ 1/τ³ prefactor = τ^{−1/2}), FULLY PROVED, τ-independent numerator.
    • `comparisonDom_integrable` / `comparisonDom_nonneg` — supplied.
    • `hcomp_final` — `hcomp_collapsed` wired at this dominator, `hDint`/`hmom` DISCHARGED
      (`setIntegral_le_integral`, full-space upper bound), giving the comparison leg
      `≤ (Cρ Mqc n (864√2+1)/2)/√τ`.
  OUTCOME: cubic carry = DISCHARGED (moment/integrability) with THREE NAMED remaining carries — see
  residue below.

  hform OUTCOME.  `hform` (the off-collar jet supply: the pointwise identity
  `IchartResidual − hessGaussFactor·qc = H·(ρ−1)·qc` on collarᶜ) is CARRIED as a hypothesis.  It is NOT
  the chart-jet data already inside `data` (the `hD2Hexpand` field gates on `collarRegime`, which FAILS
  off collar), but it is discharged POINTWISE by `SlotInstantiationV.ichartResidual_sub_hess_form`
  wherever the chart jets + open gate hold at base `z` (a chart-jet fact, honest for `z ∈ K`).  Named
  honestly; not smuggled.

  hf2/hf3 hfint/hdom OUTCOME.  The a.e. DOMINATIONS `hdom` (`hf2dom_at_witness`/`hf3dom_at_witness`) are
  FULLY DISCHARGED from a GLOBAL amplitude sup (`∀ z, |A1amp·F| ≤ M`, resp. `|A2amp·F| ≤ Sconst`) via
  the phase-5 per-point `hf2/hf3_ptwise_dom_of_ampBound` + `ae_of_all`.  The integrand integrability
  `hfint` remains a carry (it needs AEStronglyMeasurability of the `.choose`-heavy gated witness
  integrand — the DEFEQ-lesson trap forbids `fun_prop` here; the domination shows it is finite).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★★★ GROUP-(1) FINAL RESIDUE (after phases 1–6).  The group-(1) slot-instantiation ALGEBRA is now
  COMPLETE: the comparison-leg cubic moment, the hf2/hf3 moments (phase 5) and their a.e. dominations
  (phase 6) are all PROVED.  What remains of group (1) is a FINITE, ENUMERABLE list of FACTOR/SUP +
  jet-supply carries — NO further identity or scaling work:

    (R1)  `hdom_comp` — the pointwise ρ-deviation domination `‖H·(ρ−1)·qc‖ ≤ comparisonDom`, i.e.
          `|ρ−1| ≤ Cρ·‖z‖³/τ` (near-isometry cubic contact, gate-confined via `r₀` + window `τ ≤ τ₀`,
          census carry `hgate`) × the amplitude sup `|qc| ≤ Mqc`.  A SUP/near-isometry carry.
    (R2)  `hform` — the off-collar jet supply (chart jets + open gate at base `z`, off collar);
          discharged pointwise by `ichartResidual_sub_hess_form`.  A jet-supply carry.
    (R3)  `hcompDiff_int` — off-collar integrability of the residual difference (phase-3 content).
    (R4)  `hf2amp`/`hf3amp` — the amplitude·Levi SUP bounds `|A1amp·F| ≤ M`, `|A2amp·F| ≤ Sconst`
          (collar amplitude sup + gate confinement).  SUP carries.
    (R5)  `hf2int`/`hf3int` — the integrand integrabilities of the hf2/hf3 terms (measurability of the
          `.choose`-heavy witness; the DEFEQ-lesson measurability carry).

  These are exactly the terminal FACTOR/SUP + jet-supply + measurability carries — the MILESTONE: no
  slot-instantiation identity or τ-scaling remains open in group (1).  ⚠ a₁ = R/6 remains CONDITIONAL
  on the whole convergence-trio + geometric-wiring stack; this brick closes only the group-(1)
  slot-instantiation algebra, NOT any physical `R/6` claim.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
