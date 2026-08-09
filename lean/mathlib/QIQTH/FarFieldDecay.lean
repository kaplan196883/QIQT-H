/-
  FarFieldDecay — J4-457: DERIVE the far-field bound `Bff` of `GateFarFieldSplit.hcomp_final3`,
  completing the a₁ = R/6 comparison-leg repair (the FOURTH gate catch).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  WHAT THIS BRICK DERIVES.  `GateFarFieldSplit.hcomp_final3`/`slotInstantiation_phase9` carry the
  far-field piece as a SATISFIABLE (but undischarged) finite-quantity hypothesis
      `hff : ‖∫_{collarᶜ \ (K ∩ ball 0 r)} f‖ ≤ Bff`,
  `f = IchartResidual − hessGaussFactor·(chartAmp·F)`.  This file DERIVES that bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE DOMAIN / TAIL GATE  (run BEFORE the build; the verdict is BINDING).

  THE FAR-FIELD DOMAIN.  `far := (collar (c√τ))ᶜ \ (K ∩ ball 0 r)`.
    • Every `z ∈ far` has `‖z‖ > c√τ` (from `collarᶜ`).  So the far field EXCLUDES a ball of radius
      `c√τ` around `0` — but that radius SCALES WITH THE GAUSSIAN WIDTH `√τ`, so it does NOT supply a
      FIXED `R > 0`.  Substituting `z = √τ·w` maps `{‖z‖ > c√τ}` to the τ-INDEPENDENT tail `{‖w‖ > c}`;
      the excised region does NOT kill the polynomial-in-`1/τ` prefactors.  ⟹ NO tail suppression of
      the Hessian coefficient — the honest scaling is a HARD `O(1/τ)`, not a τ-uniform constant.
    • THE STRUCTURAL GATE (what makes the far field controllable at all): the near-isometry cancellation
      `(ρ − 1)` used on the GATE is UNAVAILABLE off `K` (there `W z = 0 ⟹ ρ = exp(r²/4τ)` blows up).
      Instead we use that OFF `K` the WITNESS term of `IchartResidual` VANISHES
      (`witnessSecondXDeriv_offGate_eq_zero`, base `z ∉ K`), leaving the pure Gaussian remainder
        `f z = −z_i/(2τ)·G_τ·(A1amp·F) − G_τ·(A2amp·F) − hessGaussFactor·(chartAmp·F)`,   `G_τ = gaussDdim τ z`.
      To guarantee `z ∉ K` on the WHOLE far field we require `hKr : K ⊆ ball 0 r` (SATISFIABLE: `K`
      compact ⟹ bounded ⟹ contained in a large ball).  Then `K ∩ ball 0 r = K` and every `z ∈ far` is
      off `K`, so the raw Gaussian form holds everywhere on the far field.

  THE COUNT (per-term far-field integral, dominated by the full-space Gaussian moment):
    • `z_i/(2τ)·G_τ·(A1amp·F)`  ≤ `M1F/(2τ)·‖z‖·G_τ`,   `∫ ≤ M1F/(2τ)·(n c₁ √τ) = O(τ^{-1/2})`.
    • `G_τ·(A2amp·F)`            ≤ `M2F·G_τ`,               `∫ ≤ M2F·1 = O(1)`  (mass).
    • `hessGaussFactor·(chartAmp·F)` ≤ `Mqc·(‖z‖²+2τ)/(4τ²)·G_τ`,
        `∫ ≤ Mqc·(∫z_i²G_τ + 2τ)/(4τ²) = Mqc·(2τ + 2τ)/(4τ²) = O(τ^{-1})`  ← the DOMINANT far-field term.
  VERDICT: the honest far-field bound is `Bff = O(1/τ)` — WORSE than the gate's `O(1/√τ)`, because off
  `K` the Hessian term stands ALONE (no `(ρ−1)` smallness).  This is the honest τ-dependent form; the
  phase-9/10 `hff` carry is a FREE quantity, so any finite `Bff` discharges it — we take the concrete
  `Bff := ∫_z farFieldDom` (a finite Gaussian-moment integral).  ⚠ NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (all DERIVED from banked bricks; NO `sorry`, no `:= True`, no new axioms; std-3).

    * `farFieldDom` — the explicit Gaussian-moment dominator of `‖f‖` on the far field.
    * `farFieldDom_integrable` — its full-space integrability (each `‖z‖^k·G_τ` piece banked).
    * `farField_ptwise_bound` — off `K` (`z ∉ K`), `‖f z‖ ≤ farFieldDom z`, via
      `witnessSecondXDeriv_offGate_eq_zero` + `|z_i| ≤ ‖z‖` + the amplitude sups.
    * `farField_decay_bound` — THE DERIVED far-field carry: `‖∫_{far} f‖ ≤ ∫_z farFieldDom` (the `hff`
      of `hcomp_final3` DISCHARGED at `Bff := ∫ farFieldDom`).
    * `hcomp_final4` — `hcomp_final3` with the `hff` carry GONE (`Bff := ∫ farFieldDom` supplied).
    * `slotInstantiation_phase10` — phase 9 re-fired with the far-field piece DERIVED.

  ⚠ a₁ = R/6 remains CONDITIONAL; this brick only DERIVES the far-field bound (records the `O(1/τ)`
  decay verdict) and REMOVES the `hff` carry — no physical `R/6` claim.
-/
import QIQTH.GateFarFieldSplit

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.FarFieldDecay

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the explicit Gaussian-moment dominator of `‖f‖` on the far field.
    ############################################################################### -/

/-- **`farFieldDom`.**  THE explicit Gaussian-moment dominator of the raw comparison integrand `‖f‖` on
    the far field (off `K`, where `witnessSecondXDeriv = 0`):
      `farFieldDom z := M1F·(1/(2τ))·(‖z‖·G_τ) + M2F·G_τ + Mqc·(1/(4τ²))·((‖z‖²+2τ)·G_τ)`,
    `G_τ = gaussDdim τ z`.  Term 1 dominates the gradient leg, term 2 the mass leg, term 3 the
    Hessian-Gaussian leg.  ⚠ NOT `a₁ = R/6`. -/
noncomputable def farFieldDom (τ M1F M2F Mqc : ℝ) (z : Point n) : ℝ :=
  M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z)
    + M2F * gaussDdim τ z
    + Mqc * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z)

/-- **`farFieldDom_nonneg`.**  The far-field dominator is nonnegative.  ⚠ NOT `a₁ = R/6`. -/
theorem farFieldDom_nonneg (τ M1F M2F Mqc : ℝ) (hτ : 0 < τ)
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc) (z : Point n) :
    0 ≤ farFieldDom τ M1F M2F Mqc z := by
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  unfold farFieldDom
  have h1 : (0 : ℝ) ≤ M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z) := by positivity
  have h2 : (0 : ℝ) ≤ M2F * gaussDdim τ z := by positivity
  have h3 : (0 : ℝ) ≤ Mqc * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z) := by positivity
  linarith

/-- **`farFieldDom_integrable`.**  The far-field dominator is integrable, split into the `‖z‖·G_τ`,
    `G_τ`, `‖z‖²·G_τ`, `G_τ` pieces (banked `normPow_gauss_integrable` / `gaussDdim_integrable`).  ⚠
    NOT `a₁ = R/6`. -/
theorem farFieldDom_integrable (τ M1F M2F Mqc : ℝ) (hτ : 0 < τ) :
    Integrable (farFieldDom (n := n) τ M1F M2F Mqc) volume := by
  have h1 : Integrable (fun z : Point n => ‖z‖ ^ 1 * gaussDdim τ z) volume :=
    normPow_gauss_integrable 1 (by norm_num) τ hτ
  have h0 : Integrable (fun z : Point n => gaussDdim τ z) volume := gaussDdim_integrable τ hτ
  have h2 : Integrable (fun z : Point n => ‖z‖ ^ 2 * gaussDdim τ z) volume :=
    normPow_gauss_integrable 2 (by norm_num) τ hτ
  have hsum := (((h1.const_mul (M1F * (1 / (2 * τ)))).add (h0.const_mul M2F)).add
    ((h2.const_mul (Mqc * (1 / (4 * τ ^ 2)))).add
      (h0.const_mul (Mqc * (1 / (4 * τ ^ 2)) * (2 * τ)))))
  refine hsum.congr (ae_of_all _ (fun z => ?_))
  simp only [Pi.add_apply, pow_one]; unfold farFieldDom; ring

/-! ###############################################################################
    ### §2 — the pointwise far-field bound (off `K`, `witnessSecondXDeriv = 0`).
    ############################################################################### -/

/-- **★★ `farField_ptwise_bound`.**  OFF THE BASE GATE (`z ∉ K`, so `witnessSecondXDeriv = 0` by
    `witnessSecondXDeriv_offGate_eq_zero`), the raw comparison integrand `f` is the pure Gaussian
    remainder, and
      `‖IchartResidual z − hessGaussFactor·(chartAmp·F)‖ ≤ farFieldDom τ M1F M2F Mqc z`.
    Route: off-`K` vanishing kills the witness term; then `|z_i| ≤ ‖z‖`, `|z_i²−2τ| ≤ ‖z‖²+2τ`, the
    amplitude sups `hA1F`/`hA2F`/`hqcbdd`, and the triangle inequality.  ⚠ NOT `a₁ = R/6`. -/
theorem farField_ptwise_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M1F M2F Mqc : ℝ) (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hA1F : ∀ z, |data.A1amp τ z * F s z 0| ≤ M1F)
    (hA2F : ∀ z, |data.A2amp τ z * F s z 0| ≤ M2F)
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc)
    (z : Point n) (hzK : z ∉ K) :
    ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)‖
      ≤ farFieldDom τ M1F M2F Mqc z := by
  have hw : witnessSecondXDeriv g gi hC hK S a b i τ z = 0 :=
    witnessSecondXDeriv_offGate_eq_zero g gi hC hK S a b i τ z hzK
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  -- coordinate vs norm.
  have hcoord : |z i| ≤ ‖z‖ := by
    have h := norm_le_pi_norm z i; rwa [Real.norm_eq_abs] at h
  have hzi2 : z i ^ 2 ≤ ‖z‖ ^ 2 := by
    have h2 : |z i| ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hcoord 2
    rwa [sq_abs] at h2
  have hnum : |z i ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg (z i), pow_nonneg (norm_nonneg z) 2, hτ]
    · nlinarith [hzi2, hτ]
  -- the off-`K` pure-Gaussian form of `f`.
  have hfeq : IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
      = -(z i / (2 * τ) * gaussDdim τ z * (data.A1amp τ z * F s z 0))
          + -(gaussDdim τ z * (data.A2amp τ z * F s z 0))
          + -(hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) := by
    unfold IchartResidual; rw [hw]; ring
  -- per-term bounds.
  have ha : |-(z i / (2 * τ) * gaussDdim τ z * (data.A1amp τ z * F s z 0))|
      ≤ M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z) := by
    rw [abs_neg, abs_mul]
    have hzi : |z i / (2 * τ) * gaussDdim τ z| ≤ ‖z‖ * (1 / (2 * τ)) * gaussDdim τ z := by
      rw [abs_mul, abs_of_nonneg hG]
      gcongr
      rw [abs_div, abs_of_pos h2τ, div_eq_mul_one_div]
      gcongr
    calc |z i / (2 * τ) * gaussDdim τ z| * |data.A1amp τ z * F s z 0|
        ≤ (‖z‖ * (1 / (2 * τ)) * gaussDdim τ z) * M1F :=
          mul_le_mul hzi (hA1F z) (abs_nonneg _) (by positivity)
      _ = M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z) := by ring
  have hb : |-(gaussDdim τ z * (data.A2amp τ z * F s z 0))| ≤ M2F * gaussDdim τ z := by
    rw [abs_neg, abs_mul, abs_of_nonneg hG, mul_comm (gaussDdim τ z)]
    exact mul_le_mul_of_nonneg_right (hA2F z) hG
  have hc : |-(hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ Mqc * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z) := by
    rw [abs_neg, abs_mul]
    have hhess : |hessGaussFactor i τ z| ≤ (‖z‖ ^ 2 + 2 * τ) * (1 / (4 * τ ^ 2)) * gaussDdim τ z := by
      unfold hessGaussFactor
      rw [abs_mul, abs_of_nonneg hG]
      gcongr
      rw [abs_div, abs_of_pos h4τ2, div_eq_mul_one_div]
      gcongr
    calc |hessGaussFactor i τ z| * |chartAmp g gi hC hK a b τ z 0 * F s z 0|
        ≤ ((‖z‖ ^ 2 + 2 * τ) * (1 / (4 * τ ^ 2)) * gaussDdim τ z) * Mqc :=
          mul_le_mul hhess (hqcbdd z) (abs_nonneg _) (by positivity)
      _ = Mqc * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z) := by ring
  -- assemble via the triangle inequality.
  rw [hfeq, Real.norm_eq_abs]
  calc |-(z i / (2 * τ) * gaussDdim τ z * (data.A1amp τ z * F s z 0))
          + -(gaussDdim τ z * (data.A2amp τ z * F s z 0))
          + -(hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ |-(z i / (2 * τ) * gaussDdim τ z * (data.A1amp τ z * F s z 0))|
          + |-(gaussDdim τ z * (data.A2amp τ z * F s z 0))|
          + |-(hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z) + M2F * gaussDdim τ z
          + Mqc * (1 / (4 * τ ^ 2)) * ((‖z‖ ^ 2 + 2 * τ) * gaussDdim τ z) :=
        add_le_add (add_le_add ha hb) hc
    _ = farFieldDom τ M1F M2F Mqc z := by unfold farFieldDom; ring

/-! ###############################################################################
    ### §3 — `farField_decay_bound`: the DERIVED far-field carry.
    ############################################################################### -/

/-- **★★★ `farField_decay_bound` — THE DERIVED far-field bound.**  Under `hKr : K ⊆ ball 0 r` (so the
    far field `collarᶜ \ (K ∩ ball 0 r)` is entirely OFF `K`, hence `witnessSecondXDeriv = 0` there):
      `‖∫_{collarᶜ \ (K ∩ ball 0 r)} f‖ ≤ ∫_z farFieldDom τ M1F M2F Mqc z`.
    This is EXACTLY the `hff` hypothesis of `GateFarFieldSplit.hcomp_final3`, DISCHARGED at
    `Bff := ∫ farFieldDom` (a finite Gaussian-moment integral, honest `O(1/τ)` — see the DOMAIN/TAIL
    GATE).  Route: `far ⊆ Kᶜ` (via `hKr`), `farField_ptwise_bound`, `norm_integral_le_integral_norm`,
    `integral_mono_ae`, `setIntegral_le_integral`.  ⚠ NOT `a₁ = R/6`. -/
theorem farField_decay_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r M1F M2F Mqc : ℝ) (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (hA1F : ∀ z, |data.A1amp τ z * F s z 0| ≤ M1F)
    (hA2F : ∀ z, |data.A2amp τ z * F s z 0| ≤ M2F)
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ \ (K ∩ Metric.ball (0 : Point n) r),
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ ∫ z : Point n, farFieldDom τ M1F M2F Mqc z := by
  set f : Point n → ℝ := fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
    - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0) with hfdef
  set far : Set (Point n) :=
    (collar (c * Real.sqrt τ))ᶜ \ (K ∩ Metric.ball (0 : Point n) r) with hfardef
  have hcollarc : MeasurableSet ((collar (c * Real.sqrt τ))ᶜ : Set (Point n)) :=
    (QIQTH.SliverTailMatched.collar_measurableSet _).compl
  have hgatemeas : MeasurableSet (K ∩ Metric.ball (0 : Point n) r) :=
    hK.isClosed.measurableSet.inter measurableSet_ball
  have hfarmeas : MeasurableSet far := hcollarc.diff hgatemeas
  have hfarsub : far ⊆ (collar (c * Real.sqrt τ))ᶜ := diff_subset
  have hfInt : IntegrableOn f far volume := hcompDiff_int.mono_set hfarsub
  have hDomInt : Integrable (farFieldDom (n := n) τ M1F M2F Mqc) volume :=
    farFieldDom_integrable τ M1F M2F Mqc hτ
  have hptwise : ∀ z ∈ far, ‖f z‖ ≤ farFieldDom τ M1F M2F Mqc z := by
    intro z hz
    have hzK : z ∉ K := by
      intro hzKmem
      exact hz.2 ⟨hzKmem, hKr hzKmem⟩
    exact farField_ptwise_bound g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ M1F M2F Mqc
      hM1F hM2F hMqc hA1F hA2F hqcbdd z hzK
  calc ‖∫ z in far, f z‖
      ≤ ∫ z in far, ‖f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in far, farFieldDom τ M1F M2F Mqc z :=
        integral_mono_ae hfInt.norm hDomInt.integrableOn
          ((ae_restrict_iff' hfarmeas).mpr (ae_of_all _ hptwise))
    _ ≤ ∫ z : Point n, farFieldDom τ M1F M2F Mqc z :=
        setIntegral_le_integral hDomInt
          (ae_of_all _ (fun z => farFieldDom_nonneg τ M1F M2F Mqc hτ hM1F hM2F hMqc z))

/-! ###############################################################################
    ### §4 — `hcomp_final4`: the comparison leg with the `hff` carry DERIVED.
    ############################################################################### -/

/-- **★★★ `hcomp_final4` — THE COMPARISON LEG WITH THE FAR-FIELD PIECE DERIVED.**  `hcomp_final3` with
    the free `hff`/`Bff` carry ELIMINATED: `Bff := ∫ farFieldDom`, `hff := farField_decay_bound`.  The
    off-collar comparison integral obeys
      `‖∫_{collarᶜ} f‖ ≤ Bcomp2/√τ + ∫_z farFieldDom τ M1F M2F Mqc z`,
    the gate piece via the SATISFIABLE `herrHmin_gate` inputs + jets, the far-field piece DERIVED (off
    `K` Gaussian decay, honest `O(1/τ)`).  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_final4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r L' M1F M2F Mqc : ℝ) (hL' : 0 ≤ L')
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform_gate : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ, z ∈ K → ‖z‖ < r →
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (hgate : ∀ z ∈ K, ‖z‖ < r →
      (|rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
      ∧ ((1 / 2 : ℝ) * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)))
    (hA1F : ∀ z, |data.A1amp τ z * F s z 0| ≤ M1F)
    (hA2F : ∀ z, |data.A2amp τ z * F s z 0| ≤ M2F)
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ
        + ∫ z : Point n, farFieldDom τ M1F M2F Mqc z :=
  QIQTH.GateFarFieldSplit.hcomp_final3 g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r L' Mqc
    (∫ z : Point n, farFieldDom τ M1F M2F Mqc z) hL' hMqc hcompDiff_int hform_gate hgate hqcbdd
    (farField_decay_bound g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r M1F M2F Mqc
      hM1F hM2F hMqc hKr hA1F hA2F hqcbdd hcompDiff_int)

/-! ###############################################################################
    ### PACKAGE — the phase-10 conjunction (phase 9 with the far-field piece DERIVED).
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase10`.**  THE PHASE-10 PACKAGE: `slotInstantiation_phase9` with the
    far-field `hff`/`Bff` carry ELIMINATED (DERIVED by `farField_decay_bound` at `Bff := ∫ farFieldDom`).
    The prior group-(1) carries (`Pphase7`) are CONJOINED with `hcomp_final4` — the comparison leg with
    BOTH legs discharged: the GATE via the SATISFIABLE `herrHmin_gate`, the FAR field via the DERIVED
    Gaussian decay.  The only far-field inputs are the SATISFIABLE amplitude sups (`hA1F`/`hA2F`,
    genuine `∀ z` sups) + `hKr : K ⊆ ball 0 r` (compact ⟹ bounded).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase10 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r L' M1F M2F Mqc : ℝ) (hL' : 0 ≤ L')
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (Pphase7 : Prop) (hphase7 : Pphase7)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hform_gate : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ, z ∈ K → ‖z‖ < r →
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (hgate : ∀ z ∈ K, ‖z‖ < r →
      (|rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
      ∧ ((1 / 2 : ℝ) * rncRadialSq z
          ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)))
    (hA1F : ∀ z, |data.A1amp τ z * F s z 0| ≤ M1F)
    (hA2F : ∀ z, |data.A2amp τ z * F s z 0| ≤ M2F)
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    Pphase7
    ∧ (‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
            * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
            / 16 / Real.sqrt τ
          + ∫ z : Point n, farFieldDom τ M1F M2F Mqc z) :=
  ⟨hphase7,
   hcomp_final4 g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r L' M1F M2F Mqc hL' hM1F hM2F hMqc
     hKr hcompDiff_int hform_gate hgate hA1F hA2F hqcbdd⟩

end QIQTH.FarFieldDecay

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FarFieldDecay
#print axioms farFieldDom_integrable
#print axioms farField_ptwise_bound
#print axioms farField_decay_bound
#print axioms hcomp_final4
#print axioms slotInstantiation_phase10
end AxiomChecks

/-! ###############################################################################
    ## J4-457 LEDGER — DERIVE the far-field bound `Bff`, completing the comparison-leg repair.
    ###############################################################################

  THE DOMAIN / TAIL GATE — VERDICT.
    • far := `collarᶜ \ (K ∩ ball 0 r)`.  Every `z ∈ far` has `‖z‖ > c√τ`, but that radius SCALES with
      the Gaussian width `√τ` ⟹ NO fixed `R > 0` ⟹ NO tail suppression of the `1/τ²` Hessian factor.
    • The controllable structure is the OFF-`K` VANISHING of the witness term
      (`witnessSecondXDeriv_offGate_eq_zero`).  To reach it on the WHOLE far field we require
      `hKr : K ⊆ ball 0 r` (SATISFIABLE: `K` compact ⟹ bounded).  Then `K ∩ ball 0 r = K`, every
      `z ∈ far` is off `K`, and `f = −z_i/(2τ)·G_τ·(A1amp·F) − G_τ·(A2amp·F) − hessGaussFactor·(chartAmp·F)`,
      all `G_τ`-carrying.

  THE Bff OUTCOME — DERIVED (honest τ-form).  `Bff := ∫_z farFieldDom τ M1F M2F Mqc z`, a finite
  Gaussian-moment integral.  Per-term scaling: gradient `O(τ^{-1/2})`, mass `O(1)`, Hessian `O(τ^{-1})`
  ⟹ `Bff = O(1/τ)` — HONESTLY WORSE than the gate's `O(1/√τ)`, because off `K` the Hessian term stands
  ALONE (no `(ρ−1)` near-isometry smallness).  This is recorded, not hidden: `hff` is a FREE carry in
  phase 9/10, so any finite `Bff` discharges it; the degradation is a downstream concern, not a
  soundness gap.

  WHAT LANDS (all std-3; NO `sorry`, no `:= True`, no new axioms):
    • `farFieldDom` — explicit dominator; `farFieldDom_nonneg`/`farFieldDom_integrable`.
    • `farField_ptwise_bound` — off-`K` pointwise `‖f‖ ≤ farFieldDom`.
    • `farField_decay_bound` — `‖∫_far f‖ ≤ ∫ farFieldDom` (the `hff` of `hcomp_final3` DERIVED).
    • `hcomp_final4` — `hcomp_final3` with `hff` GONE (`Bff := ∫ farFieldDom`).
    • `slotInstantiation_phase10` — phase 9 with the far-field piece DERIVED.

  DON'T-UNDERCREDIT FINDINGS.  The heavy lifting was ALREADY BANKED and REUSED verbatim:
    · `AmplitudePackage.witnessSecondXDeriv_offGate_eq_zero` (N3) supplies the off-`K` vanishing — the
      ONE structural fact that makes the far field a pure Gaussian remainder.
    · `HeatResidualBound.normPow_gauss_integrable` / `gaussDdim_integrable` / `gaussDdim_integral_eq_one`
      + `ResidueBound.gaussDdim_nonneg` supply the moment integrability/nonnegativity.
    · `GateFarFieldSplit.hcomp_final3` (J4-456) supplies the gate ⊔ far split; this brick only DERIVES
      its `hff` carry and threads `Bff := ∫ farFieldDom` through.
    · The regime-restricted amplitude sups (`AmplitudeDerivativeDataOn.hA1ampBdd`/`hA2ampBdd`) hold ONLY
      on-collar, so the far-field sups `hA1F`/`hA2F` are carried as genuine `∀ z` sups (SATISFIABLE, like
      `Mqc`) — NOT re-used from the data bundle.

  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack; this brick only
  DERIVES the far-field bound of the phase-9 comparison leg and records the `O(1/τ)` decay verdict.
-/
