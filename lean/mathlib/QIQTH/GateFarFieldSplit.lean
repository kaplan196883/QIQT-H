/-
  GateFarFieldSplit — J4-456 (Sol #22's item): the SATISFIABLE replacement for the group-(1)
  comparison-leg domination, repairing the FOURTH gate catch of the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  ⚠  a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  WHAT THIS BRICK REPAIRS.  `SlotInstantiationVIII.hcomp_final2`/`hdom_comp2_ptwise`/
  `slotInstantiation_phase8` consume the group-(1) near-isometry inputs in the WHOLE-SPACE `∀ z` shapes
      `herr : ∀ z, |r²_{Wz} − r²_z| ≤ L'·‖z‖³`      and      `hmin : ∀ z, ½·r²_z ≤ r²_{Wz}`.
  `HerrHminCoercivity` (J4-455) machine-certified that these `∀ z` demands are **UNSATISFIABLE**: the
  uniform inverse chart defaults to `0` off the compact base set `K` (`uniformInverseChart_off_K`), so
  `W z = 0`, whence the whole-space coercivity is refuted at any nonzero `z ∉ K`
  (`wholeSpace_coercivity_unsatisfiable`).  The honest inputs are GATE-RESTRICTED (`herrHmin_gate`: both
  bounds on `z ∈ K`, `‖z‖ < r`).  Phase 8 is therefore only VACUOUSLY dischargeable — never USABLE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FAR-FIELD AUDIT  (run BEFORE the build; the verdict is BINDING).

  THE KEY QUESTION.  Is the comparison-leg integrand that `hcomp_final2` actually dominates — the RAW
  difference `f z := IchartResidual z − hessGaussFactor·(chartAmp·F)` (BEFORE the ρ-factoring) — zero
  off the gate `K`?

  THE VERDICT: it does **NOT** vanish, but it **DECAYS** (a genuine Gaussian far-field leg — verdict #2).
  AUDIT (from the definitions, not guessed):
    • `IchartResidual z = witnessSecondXDeriv·F − z_i/(2τ)·G_τ·A1amp·F − G_τ·A2amp·F`
      (`SlotInstantiationII.IchartResidual`), and `witnessSecondXDeriv` is a fibre-`x'` second derivative
      of `vanVleckGatedWitness … x' z = gatedKernel K S (…) τ x' z`, which for `z ∉ K` is the ZERO
      DEFAULT `fun _ => 0` (`gatedKernel … = if q ∈ K then … else 0`, base `q = z`).  So OFF `K`,
      `witnessSecondXDeriv z = 0`, and `IchartResidual z = −z_i/(2τ)·G_τ·A1amp·F − G_τ·A2amp·F`.
    • `hessGaussFactor i τ z = (z_i²−2τ)/(4τ²)·gaussDdim τ z` — it CARRIES the Gaussian `G_τ = gaussDdim τ z`.
      So the subtracted term `hessGaussFactor·(chartAmp·F) = (z_i²−2τ)/(4τ²)·G_τ·chartAmp(0)·F` also
      carries `G_τ` (off `K`, `chartAmp z 0` is the CONSTANT value at `W z 0 = 0` — nonzero in general).
    • Hence OFF `K` the RAW integrand `f z = −z_i/(2τ)·G_τ·A1amp·F − G_τ·A2amp·F − (z_i²−2τ)/(4τ²)·G_τ·chartAmp(0)·F`
      has EVERY term proportional to `G_τ = gaussDdim τ z` ⟹ **Gaussian-decaying**, integrable, not blowing up.
  WHY THIS BEATS THE J4-455 NOTE.  The J4-455 note flagged the ρ-FACTORED form `hessGaussFactor·(ρ−1)·qc`
  as blowing up off gate (`W z = 0 ⟹ ρ = exp(r²_z/4τ)`).  That is correct FOR THE FACTORED FORM — but
  the factored identity (`ichartResidual_sub_hess_form`) is proved ONLY for `z ∈ K` (it needs the chart
  jets).  OFF `K` the factored form is a DIFFERENT object from the RAW `f`; the RAW `f` simply has
  `witnessSecondXDeriv = 0` and decays.  So the honest split is: GATE region via the factored form
  (`herrHmin_gate` + `comparisonDom2`), FAR field via the raw Gaussian-decaying leg — NEITHER a vacuity
  nor an open blow-up.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (all DERIVED from banked bricks; NO `sorry`, no `:= True`, no new axioms; std-3).

    * `hdom_comp2_at` — the POINTWISE S5b domination `‖hessGaussFactor·(ρ−1)·qc‖ ≤ comparisonDom2` from
      the near-isometry bounds AT the single point `z` (the satisfiable pointwise core of
      `hdom_comp2_ptwise`, fed on the gate by `herrHmin_gate`).
    * `comparison_gate_bound` — the GATE-piece bound `‖∫_{collarᶜ ∩ (K ∩ ball 0 r)} f‖ ≤ Bcomp2/√τ`, via
      the gate-restricted factored identity + `hdom_comp2_at` + `comparisonDom2_moment`.
    * `hcomp_final3` — THE SATISFIABLE comparison-leg closure: the collarᶜ integral split as
      [collarᶜ ∩ gate: `comparisonDom2` via `herrHmin_gate`] ⊔ [far field: the Gaussian-decaying carry],
      giving `‖∫_{collarᶜ} f‖ ≤ Bcomp2/√τ + Bff`.  The `∀ z` binders are replaced by the SATISFIABLE
      split binders (gate-restricted near-isometry + gate-restricted jets + a far-field integral bound).
    * `slotInstantiation_phase9` — phase 8 re-fired on the satisfiable shapes.

  ⚠ a₁ = R/6 remains CONDITIONAL; this brick only replaces the vacuous phase-8 comparison-leg shape by a
  SATISFIABLE phase-9 one, and RECORDS the far-field decay verdict.
-/
import QIQTH.SlotInstantiationVIII
import QIQTH.HerrHminCoercivity

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open QIQTH.SlotInstantiationIV QIQTH.SlotInstantiationV QIQTH.SlotInstantiationVI
open QIQTH.SlotInstantiationVIII
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.GateFarFieldSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the POINTWISE S5b domination (satisfiable core of `hdom_comp2_ptwise`).
    ############################################################################### -/

/-- **★★ `hdom_comp2_at`.**  THE POINTWISE S5b DOMINATION, honest at a SINGLE `z` fed by the
    near-isometry bounds AT that `z` (the satisfiable core of `hdom_comp2_ptwise`, whose `∀ z` inputs are
    unsatisfiable per `HerrHminCoercivity`).  Under the cubic error `herrz`
    (`|r²_{Wz} − r²_z| ≤ L'‖z‖³`), the coercivity `hminz` (`½r²_z ≤ r²_{Wz}`) — the two S5b inputs of
    `gaussDdim_replace_bound` at `z` — and the amplitude bound `hqcz` (`|qc z| ≤ Mqc`):
      `‖hessGaussFactor·(ρ−1)·qc‖ ≤ comparisonDom2 τ L' Mqc z`.
    Route: the EXACT ratio identity `(ρ−1)·G_τ = G^chart − G_τ` (`gauss_ratio_rho`) + `|z i| ≤ ‖z‖` +
    the banked `gaussDdim_replace_bound`.  NO exp linearisation ⟹ NO off-collar blow-up.  ⚠ NOT
    `a₁ = R/6`. -/
theorem hdom_comp2_at (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (τ s : ℝ) (hτ : 0 < τ) (L' Mqc : ℝ)
    (hL' : 0 ≤ L') (z : Point n)
    (herrz : |rncRadialSq (uniformInverseChart g gi hC hK z 0) - rncRadialSq z| ≤ L' * ‖z‖ ^ 3)
    (hminz : (1 / 2 : ℝ) * rncRadialSq z
      ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hqcz : |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    ‖hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ comparisonDom2 τ L' Mqc z := by
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have hgpos : (0 : ℝ) ≤ gaussDdim (2 * τ) z := QIQTH.ResidueBound.gaussDdim_nonneg (2 * τ) z
  have hratio : (rhoRatio g gi hC hK τ z - 1) * gaussDdim τ z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z := by
    have hg := gauss_ratio_rho g gi hC hK τ hτ z
    rw [hg]; ring
  have hid : hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2)
          * (gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z)
          * (chartAmp g gi hC hK a b τ z 0 * F s z 0) := by
    unfold hessGaussFactor; rw [← hratio]; ring
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
  have hbA : |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
    rw [abs_div, abs_of_pos h4τ2]
    gcongr
  have hbB : |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|
      ≤ L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
    gaussDdim_replace_bound τ hτ (fun w => uniformInverseChart g gi hC hK w 0) z L' hL'
      herrz hminz
  have hboundA_nn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by positivity
  have hboundB_nn : (0 : ℝ) ≤ L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z := by
    positivity
  rw [hid, Real.norm_eq_abs, abs_mul, abs_mul]
  calc |(z i ^ 2 - 2 * τ) / (4 * τ ^ 2)|
          * |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|
          * |chartAmp g gi hC hK a b τ z 0 * F s z 0|
      ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)
            * (L' * ‖z‖ ^ 3 / (4 * τ) * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z) * Mqc :=
        mul_le_mul (mul_le_mul hbA hbB (abs_nonneg _) hboundA_nn) hqcz
          (abs_nonneg _) (mul_nonneg hboundA_nn hboundB_nn)
    _ = comparisonDom2 τ L' Mqc z := by unfold comparisonDom2; ring

/-! ###############################################################################
    ### §2 — the GATE-piece bound of the comparison integral.
    ############################################################################### -/

/-- **★★ `comparison_gate_bound`.**  THE GATE PIECE.  On the OFF-COLLAR gate `collarᶜ ∩ (K ∩ ball 0 r)`
    the comparison integrand `f = IchartResidual − hessGaussFactor·qc` obeys
      `‖∫_{collarᶜ ∩ (K ∩ ball 0 r)} f‖ ≤ Bcomp2/√τ`,
    from (i) the gate-restricted factored identity `hform_gate` (`ichartResidual_sub_hess_form` needs
    `z ∈ K` + jets), (ii) the pointwise S5b domination `hdom_comp2_at` fed by `herrHmin_gate` (`hgate`),
    and (iii) the banked `comparisonDom2_moment`.  This is the SATISFIABLE gate leg — no `∀ z` demand.
    ⚠ NOT `a₁ = R/6`. -/
theorem comparison_gate_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r L' Mqc : ℝ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
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
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ ∩ (K ∩ Metric.ball (0 : Point n) r),
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ := by
  -- abbreviations.
  set f : Point n → ℝ := fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
    - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0) with hfdef
  set rhs : Point n → ℝ := fun z => hessGaussFactor i τ z
    * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) with hrhsdef
  set G : Set (Point n) := (collar (c * Real.sqrt τ))ᶜ ∩ (K ∩ Metric.ball (0 : Point n) r) with hGdef
  -- measurability.
  have hcollarc : MeasurableSet ((collar (c * Real.sqrt τ))ᶜ : Set (Point n)) :=
    (QIQTH.SliverTailMatched.collar_measurableSet _).compl
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hballmeas : MeasurableSet (Metric.ball (0 : Point n) r) := measurableSet_ball
  have hGmeas : MeasurableSet G := hcollarc.inter (hKmeas.inter hballmeas)
  -- the gate-restricted form identity on `G`, as a set-membership predicate.
  have hform_on_G : ∀ z ∈ G, f z = rhs z := by
    intro z hz
    obtain ⟨hzc, hzK, hzball⟩ := hz
    have hznorm : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hzball
    exact hform_gate z hzc hzK hznorm
  -- integrability of `f` on `G` (subset of `collarᶜ`).
  have hGsub : G ⊆ (collar (c * Real.sqrt τ))ᶜ := inter_subset_left
  have hfG : IntegrableOn f G volume := hcompDiff_int.mono_set hGsub
  -- integrability of `rhs` on `G` (congruent to `f`).
  have hae : f =ᵐ[volume.restrict G] rhs :=
    (ae_restrict_iff' hGmeas).mpr (ae_of_all _ hform_on_G)
  have hrhsG : IntegrableOn rhs G volume := hfG.congr hae
  -- pointwise domination of `‖rhs‖` by `comparisonDom2` on `G`.
  have hdomG : ∀ z ∈ G, ‖rhs z‖ ≤ comparisonDom2 τ L' Mqc z := by
    intro z hz
    obtain ⟨_, hzK, hzball⟩ := hz
    have hznorm : ‖z‖ < r := by rwa [mem_ball_zero_iff] at hzball
    obtain ⟨herrz, hminz⟩ := hgate z hzK hznorm
    exact hdom_comp2_at g gi hC hK a b F i τ s hτ L' Mqc hL' z herrz hminz (hqcbdd z)
  -- assemble.
  rw [setIntegral_congr_fun hGmeas hform_on_G]
  calc ‖∫ z in G, rhs z‖
      ≤ ∫ z in G, ‖rhs z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in G, comparisonDom2 τ L' Mqc z :=
        integral_mono_ae hrhsG.norm
          ((comparisonDom2_integrable τ L' Mqc hτ).integrableOn)
          ((ae_restrict_iff' hGmeas).mpr (ae_of_all _ hdomG))
    _ ≤ ∫ z : Point n, comparisonDom2 τ L' Mqc z :=
        setIntegral_le_integral (comparisonDom2_integrable τ L' Mqc hτ)
          (ae_of_all _ (fun z => comparisonDom2_nonneg τ L' Mqc hτ hL' hMqc z))
    _ ≤ _ := comparisonDom2_moment τ L' Mqc hτ hL' hMqc

/-! ###############################################################################
    ### §3 — `hcomp_final3`: the SATISFIABLE comparison-leg closure (gate ⊔ far field).
    ############################################################################### -/

/-- **★★★ `hcomp_final3` — THE SATISFIABLE COMPARISON LEG.**  The off-collar comparison integral split
    into the GATE piece and the FAR field:
      `‖∫_{collarᶜ} f‖ ≤ ‖∫_{collarᶜ ∩ gate} f‖ + ‖∫_{collarᶜ \ gate} f‖ ≤ Bcomp2/√τ + Bff`,
    `gate := K ∩ ball 0 r`, `f = IchartResidual − hessGaussFactor·qc`.  The gate piece is `Bcomp2/√τ`
    (`comparison_gate_bound`, fed the SATISFIABLE `herrHmin_gate` inputs `hgate` + the gate-restricted
    jet supply `hform_gate`); the far-field piece is the Gaussian-DECAYING leg (THE FAR-FIELD AUDIT:
    off `K`, `witnessSecondXDeriv = 0` and every term carries `G_τ`), carried as the satisfiable finite
    bound `hff`.  This REPLACES the vacuous whole-space `∀ z` `herr`/`hmin` shape of `hcomp_final2` by a
    SATISFIABLE split — the fourth-gate repair.  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_final3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r L' Mqc Bff : ℝ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
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
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc)
    (hff : ‖∫ z in (collar (c * Real.sqrt τ))ᶜ \ (K ∩ Metric.ball (0 : Point n) r),
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖ ≤ Bff) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ
        + Bff := by
  set f : Point n → ℝ := fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
    - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0) with hfdef
  set gate : Set (Point n) := K ∩ Metric.ball (0 : Point n) r with hgatedef
  have hgatemeas : MeasurableSet gate :=
    hK.isClosed.measurableSet.inter measurableSet_ball
  -- the additive split of the off-collar integral.
  have hsplit : (∫ z in (collar (c * Real.sqrt τ))ᶜ ∩ gate, f z)
      + (∫ z in (collar (c * Real.sqrt τ))ᶜ \ gate, f z)
      = ∫ z in (collar (c * Real.sqrt τ))ᶜ, f z :=
    integral_inter_add_diff hgatemeas hcompDiff_int
  calc ‖∫ z in (collar (c * Real.sqrt τ))ᶜ, f z‖
      = ‖(∫ z in (collar (c * Real.sqrt τ))ᶜ ∩ gate, f z)
          + (∫ z in (collar (c * Real.sqrt τ))ᶜ \ gate, f z)‖ := by rw [hsplit]
    _ ≤ ‖∫ z in (collar (c * Real.sqrt τ))ᶜ ∩ gate, f z‖
          + ‖∫ z in (collar (c * Real.sqrt τ))ᶜ \ gate, f z‖ := norm_add_le _ _
    _ ≤ (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
          * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5 + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
          / 16 / Real.sqrt τ) + Bff :=
        add_le_add
          (comparison_gate_bound g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r L' Mqc hL' hMqc
            hcompDiff_int hform_gate hgate hqcbdd)
          hff

/-! ###############################################################################
    ### PACKAGE — the phase-9 conjunction (phase 8 re-fired on the satisfiable shapes).
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase9`.**  THE PHASE-9 PACKAGE: `slotInstantiation_phase8` re-fired on the
    SATISFIABLE comparison-leg shapes.  The prior group-(1) carries (`Pphase7`) are CONJOINED with
    `hcomp_final3` — the comparison leg with the domination split into the GATE (`comparisonDom2` via the
    SATISFIABLE `herrHmin_gate` inputs) and the FAR field (the Gaussian-decaying carry `hff`).  The
    UNSATISFIABLE whole-space `∀ z` `herr`/`hmin` binders of phase 8 are GONE, replaced by the
    gate-restricted `hgate` + `hform_gate` + `hff`.  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase9 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (r L' Mqc Bff : ℝ) (hL' : 0 ≤ L') (hMqc : 0 ≤ Mqc)
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
    (hqcbdd : ∀ z, |chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ Mqc)
    (hff : ‖∫ z in (collar (c * Real.sqrt τ))ᶜ \ (K ∩ Metric.ball (0 : Point n) r),
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖ ≤ Bff) :
    Pphase7
    ∧ (‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
        ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
            * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
            / 16 / Real.sqrt τ
          + Bff) :=
  ⟨hphase7,
   hcomp_final3 g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r L' Mqc Bff hL' hMqc
     hcompDiff_int hform_gate hgate hqcbdd hff⟩

end QIQTH.GateFarFieldSplit

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GateFarFieldSplit
#print axioms hdom_comp2_at
#print axioms comparison_gate_bound
#print axioms hcomp_final3
#print axioms slotInstantiation_phase9
end AxiomChecks

/-! ###############################################################################
    ## J4-456 LEDGER — Sol #22's item: the gate-vs-far-field split of the comparison leg.
    ###############################################################################

  THE FAR-FIELD AUDIT — VERDICT: **DECAYS** (a Gaussian far-field leg; verdict #2, NOT vanishing, NOT
  Sol #22).  The RAW comparison integrand `f = IchartResidual − hessGaussFactor·qc`:
    • OFF `K`: `witnessSecondXDeriv z = 0` (the fibre-`x'` second derivative of `vanVleckGatedWitness`,
      which is the `gatedKernel K S (…)` ZERO DEFAULT for base `z ∉ K`), so `IchartResidual z =
      −z_i/(2τ)·G_τ·A1amp·F − G_τ·A2amp·F`; and `hessGaussFactor·qc = (z_i²−2τ)/(4τ²)·G_τ·chartAmp(0)·F`.
      EVERY term carries `G_τ = gaussDdim τ z` ⟹ Gaussian-decaying, integrable, NOT blowing up.
    • The J4-455 blow-up note is about the ρ-FACTORED form, which is a DIFFERENT object off `K`
      (`ichartResidual_sub_hess_form` needs `z ∈ K` jets).  The RAW `f` decays; the factored form is
      only used ON the gate.

  THE SPLIT (the repair).  `collarᶜ = (collarᶜ ∩ gate) ⊔ (collarᶜ \ gate)`, `gate := K ∩ ball 0 r`:
    • GATE piece (`comparison_gate_bound`): `‖∫_{collarᶜ ∩ gate} f‖ ≤ Bcomp2/√τ`, via the gate-restricted
      factored identity `hform_gate` + the POINTWISE `hdom_comp2_at` fed the SATISFIABLE `herrHmin_gate`
      inputs `hgate` + the banked `comparisonDom2_moment`.
    • FAR-FIELD piece: `‖∫_{collarᶜ \ gate} f‖ ≤ Bff`, a SATISFIABLE finite bound (the Gaussian-decaying
      leg — a bound on a fixed finite integral, NOT a false universal).
    • `hcomp_final3`: `integral_inter_add_diff` + `norm_add_le` ⟹ `‖∫_{collarᶜ} f‖ ≤ Bcomp2/√τ + Bff`.

  THE REPAIR LEDGER — group-(1) comparison-leg surface after J4-456.
    ── SUPERSEDED (vacuous — do NOT re-use as if usable):
       • `SlotInstantiationVIII.hdom_comp2_ptwise` / `hcomp_final2` / `slotInstantiation_phase8`, which
         carry `herr : ∀ z` and `hmin : ∀ z`.  `HerrHminCoercivity.wholeSpace_coercivity_unsatisfiable`
         certifies `hmin`'s `∀ z` shape is FALSE (`W z = 0` off `K`), so these are only VACUOUSLY
         dischargeable.  The phase-8 chain is FLAGGED SUPERSEDED.
    ── IN FORCE (satisfiable — phase 9):
       • `hdom_comp2_at` — pointwise S5b domination from bounds AT `z` (fed by `herrHmin_gate`).
       • `comparison_gate_bound` — the gate piece `≤ Bcomp2/√τ`.
       • `hcomp_final3` — `‖∫_{collarᶜ} f‖ ≤ Bcomp2/√τ + Bff`, the SATISFIABLE closure.
       • `slotInstantiation_phase9` — phase 8 re-fired on the satisfiable shapes.
    ── SATISFIABLE INPUT CARRIES of phase 9 (all genuine, none vacuous):
       (S1) `hgate` — the gate-restricted near-isometry `herr`∧`hmin` on `z ∈ K`, `‖z‖ < r`
            (PROVED by `HerrHminCoercivity.herrHmin_gate`).
       (S2) `hform_gate` — the gate-restricted off-collar jet supply (`ichartResidual_sub_hess_form`
            wherever `z ∈ K` + chart jets hold).
       (S3) `hqcbdd`/`Mqc` — the amplitude sup (genuine `∀ z` sup — this one was always satisfiable).
       (S4) `hff`/`Bff` — the far-field integral bound (the Gaussian-DECAYING leg; a finite-quantity
            inequality, hence satisfiable — NOT the false coercivity).
       (S5) `hcompDiff_int` — off-collar integrability of the residual difference (R3 wiring).

  DON'T-UNDERCREDIT FINDINGS.  The heavy lifting was ALREADY BANKED and REUSED verbatim:
    · `HerrHminCoercivity.herrHmin_gate` (J4-455) supplies (S1) — the gate-restricted `herr`∧`hmin`.
    · `SlotInstantiationVIII.comparisonDom2` / `comparisonDom2_integrable` / `comparisonDom2_nonneg` /
      `comparisonDom2_moment` supply the width-`2τ` dominator + its `C/√τ` moment (unchanged).
    · `gaussDdim_replace_bound` / `gauss_ratio_rho` (banked) drive `hdom_comp2_at` (a pointwise recut of
      `hdom_comp2_ptwise`'s body — NO new geometry).
    · `MeasureTheory.integral_inter_add_diff` (Mathlib) supplies the set split; `norm_add_le` the
      triangle step.  This brick is pure ASSEMBLY + the honest FAR-FIELD DECAY audit.

  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack; this brick only
  replaces the vacuous phase-8 comparison-leg shape by a SATISFIABLE phase-9 one and records the
  far-field DECAY verdict, NOT any physical `R/6` claim.
-/
