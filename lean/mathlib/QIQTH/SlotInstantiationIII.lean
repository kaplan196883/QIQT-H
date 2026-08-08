/-
  SlotInstantiationIII — J4-420 (Part B, tranche (a) phase 3): CONCRETE discharge of the group-(1)
  Lipschitz carries `hqz`/`hqc` (+ their a.e.-strong measurabilities) and the three full-space
  integrabilities `hWint`/`hf2`/`hf3`, continuing `SlotInstantiationI` (phase 1) and
  `SlotInstantiationII` (phase 2).

  This file supplies, at the SAME true ρ-scaled chart witness used by phases 1-2:
    • `hqz` — the term-1 amplitude · Levi product `(ρ·A_chart)·F` is (globally) Lipschitz, VERBATIM the
      `GpowClosure.leviSecondPairing_inner_bound_concrete` `hqz` shape.  Supplier:
      `DataAmpAssembly.concrete_hqLip_of_carries` (the banked E3 three-factor product-Lipschitz wiring;
      NO new moment analysis).
    • `hqc` — the chart-native comparison amplitude `A_chart·F` is (globally) Lipschitz.  Supplier:
      `DisplacementDerivative.collar_product_lipschitz_increment` (the banked two-factor product core).
    • `hqzmeas`/`hqcmeas` — the a.e.-strong measurability slots, DERIVED FROM the Lipschitz bounds
      (globally Lipschitz ⟹ continuous ⟹ a.e.-strongly-measurable), so no `.choose`-heavy
      measurability tactic is ever run.  Supplier: `aesm_of_lipBound` (this file, via
      `LipschitzWith.of_dist_le_mul`).
    • `hWint`/`hf2`/`hf3` — the three full-space integrabilities, REDUCED to explicit two-Gaussian
      PRODUCT-domination carries (the census shape already traded by `hAdom2cap`/`hFdom` downstream) via
      the banked `CConvV2GaussianPairing.gaussDdim_pair_integrable` + `Integrable.mono'`.  These three
      also complete phase 2's `hIchart_int_concrete` into the unconditional-at-the-witness corollary
      `hIchart_int_final`.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It discharges
  a HONEST PARTIAL of group (1); the geometric CONTENT of the closure now sits ENTIRELY in `hcomp` (the
  comparison leg — that `IchartResidual` has the chart-native `hessCoeff·G^chart·qc` form), which is
  UNCHANGED and remains the honest residue.  No `sorry`, no `:= True`, no new axioms; std-3.  See the
  `## PHASE 3 COVERAGE` block for the honest ledger.
-/
import QIQTH.SlotInstantiationII
import QIQTH.DataAmpAssembly
import QIQTH.CConvV2GaussianPairing
import QIQTH.GaussianHessianCancel
import QIQTH.DisplacementDerivative

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationIII

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### helper — a.e.-strong measurability from a global Lipschitz increment bound.
    ############################################################################### -/

/-- **★ helper — `aesm_of_lipBound`.**  A real-valued function with a GLOBAL Lipschitz increment
    `|q z − q w| ≤ L·dist z w` (`0 ≤ L`) is `LipschitzWith L.toNNReal`, hence continuous, hence
    a.e.-strongly-measurable.  This is the measurability supplier for BOTH `hqzmeas` and `hqcmeas`,
    routed entirely through the Lipschitz carry — so no `.choose`-heavy `fun_prop`/continuity tactic is
    ever run on the chart-native amplitudes.  ⚠ NOT `a₁ = R/6`. -/
theorem aesm_of_lipBound (q : Point n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z w : Point n, |q z - q w| ≤ L * dist z w) :
    AEStronglyMeasurable q volume := by
  have hlw : LipschitzWith L.toNNReal q := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Real.dist_eq, Real.coe_toNNReal L hL]
    exact hlip z w
  exact hlw.continuous.aestronglyMeasurable

/-! ###############################################################################
    ### helper — integrability from a two-Gaussian product domination.
    ############################################################################### -/

/-- **★ helper — `integrable_of_dom_gaussPair`.**  If `‖h z‖ ≤ C·(G_{w₁} z · G_{w₂} z)` pointwise (the
    two-Gaussian PRODUCT dominator, the exact census shape) and `h` is a.e.-strongly-measurable, then
    `h` is integrable — from the banked `CConvV2GaussianPairing.gaussDdim_pair_integrable`
    (`G_{w₁}·G_{w₂}` integrable) via `Integrable.mono'`.  ⚠ NOT `a₁ = R/6`. -/
theorem integrable_of_dom_gaussPair (h : Point n → ℝ) (C w₁ w₂ : ℝ)
    (hmeas : AEStronglyMeasurable h volume)
    (hdom : ∀ z : Point n, ‖h z‖ ≤ C * (gaussDdim w₁ z * gaussDdim w₂ z)) :
    Integrable h volume :=
  Integrable.mono'
    ((QIQTH.CConvV2GaussianPairing.gaussDdim_pair_integrable (n := n) w₁ w₂).const_mul C)
    hmeas (Filter.Eventually.of_forall hdom)

/-! ###############################################################################
    ### B-field 6 — the `hqz` Lipschitz carry (term-1 amplitude · Levi product).
    ############################################################################### -/

/-- **★★ B (slot `hqz`, DISCHARGED-MODULO) — `hqz_concrete`.**  THE `hqz` LIPSCHITZ CARRY of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` at the true ρ-scaled chart witness
    `qz z := (ρ·A_chart)·F` (matching phase-1's `center_identity_concrete`):
      `|(ρ z·A z)·F z − (ρ w·A w)·F w| ≤ (M_ρ·M_A·L_F + (M_ρ·L_A + M_A·L_ρ)·M_F)·dist z w`.
    Discharged directly by the banked E3 wiring `DataAmpAssembly.concrete_hqLip_of_carries` (three-factor
    product-Lipschitz), MODULO the six factor sup/Lipschitz carries `M_ρ`/`M_A`/`M_F`/`L_ρ`/`L_A`/`L_F`
    (no new moment analysis).  ⚠ NOT `a₁ = R/6`. -/
theorem hqz_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (T τ₀ : ℝ)
    (M_ρ M_A M_F L_ρ L_A L_F : ℝ)
    (hMρnn : 0 ≤ M_ρ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hMρ : ∀ τ z, |rhoRatio g gi hC hK τ z| ≤ M_ρ)
    (hMA : ∀ τ z, |chartAmp g gi hC hK a b τ z 0| ≤ M_A)
    (hMF : ∀ s w, |F s w 0| ≤ M_F)
    (hLρ : ∀ τ z w, |rhoRatio g gi hC hK τ z - rhoRatio g gi hC hK τ w| ≤ L_ρ * dist z w)
    (hLA : ∀ τ z w,
      |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : ∀ s z w, |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) τ₀) (s : ℝ) (hs0 : 0 < s) (hsT : s ≤ T) :
    ∀ z w : Point n,
      |(rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) * F s z 0
          - (rhoRatio g gi hC hK τ w * chartAmp g gi hC hK a b τ w 0) * F s w 0|
        ≤ (M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F) * dist z w :=
  fun z w =>
    QIQTH.DataAmpAssembly.concrete_hqLip_of_carries g gi hC hK a b F T τ₀
      M_ρ M_A M_F L_ρ L_A L_F hMρnn hMAnn hMFnn hMρ hMA hMF hLρ hLA hLF
      τ hτ s hs0 hsT z w

/-! ###############################################################################
    ### B-field 7 — the `hqc` Lipschitz carry (chart-native comparison amplitude).
    ############################################################################### -/

/-- **★★ B (slot `hqc`, DISCHARGED-MODULO) — `hqc_concrete`.**  THE `hqc` LIPSCHITZ CARRY of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` at the chart-native comparison amplitude
    `qc z := A_chart·F` (matching phase-1's `qc`):
      `|A z·F z − A w·F w| ≤ (M_A·L_F + M_F·L_A)·dist z w`.
    Discharged by the banked two-factor product core
    `DisplacementDerivative.collar_product_lipschitz_increment` (`f = A_chart 0`, `g = F s·0`), MODULO
    the four factor sup/Lipschitz carries `M_A`/`M_F`/`L_A`/`L_F`.  ⚠ NOT `a₁ = R/6`. -/
theorem hqc_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (τ s : ℝ)
    (M_A M_F L_A L_F : ℝ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hMA : ∀ z, |chartAmp g gi hC hK a b τ z 0| ≤ M_A)
    (hMF : ∀ z, |F s z 0| ≤ M_F)
    (hLA : ∀ z w,
      |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : ∀ z w, |F s z 0 - F s w 0| ≤ L_F * dist z w) :
    ∀ z w : Point n,
      |chartAmp g gi hC hK a b τ z 0 * F s z 0 - chartAmp g gi hC hK a b τ w 0 * F s w 0|
        ≤ (M_A * L_F + M_F * L_A) * dist z w :=
  fun z w =>
    QIQTH.DisplacementDerivative.collar_product_lipschitz_increment
      (fun p => chartAmp g gi hC hK a b τ p 0) (fun p => F s p 0)
      M_A M_F L_A L_F z w hMAnn hMFnn (hMA z) (hMF w) (hLA z w) (hLF z w)

/-! ###############################################################################
    ### B-field 8 — the three full-space integrabilities `hWint`/`hf2`/`hf3`.
    ############################################################################### -/

/-- **★★ B (slot `hWint`, DISCHARGED-MODULO) — `hWint_of_dom`.**  THE `hWint` FULL-SPACE INTEGRABILITY
    `Integrable (witnessSecondXDeriv·F)`, REDUCED to a Gaussian-domination carry on the witness
    `|witnessSecondXDeriv τ z| ≤ Cw·G_{w₁} z` (the `hAdom2cap` census shape) combined with the bundle's
    own Levi domination `data.hFdom` (`|F s z 0| ≤ C_L·G_{2s} z`).  Route: the product is dominated by
    `(Cw·C_L)·(G_{w₁}·G_{2s})`, integrable by `integrable_of_dom_gaussPair`.  ⚠ NOT `a₁ = R/6`. -/
theorem hWint_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hs0 : 0 < s) (hsT : s ≤ T) (Cw w₁ : ℝ) (hCw : 0 ≤ Cw)
    (hWmeas : AEStronglyMeasurable
      (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0) volume)
    (hWdom : ∀ z, |witnessSecondXDeriv g gi hC hK S a b i τ z| ≤ Cw * gaussDdim w₁ z) :
    Integrable (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0) volume := by
  apply integrable_of_dom_gaussPair _ (Cw * data.C_L) w₁ (2 * s) hWmeas
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  have hF := data.hFdom s hs0 hsT z 0
  rw [sub_zero] at hF
  calc |witnessSecondXDeriv g gi hC hK S a b i τ z| * |F s z 0|
      ≤ (Cw * gaussDdim w₁ z) * (data.C_L * gaussDdim (2 * s) z) :=
        mul_le_mul (hWdom z) hF (abs_nonneg _)
          (mul_nonneg hCw (gaussDdim_nonneg' _ _))
    _ = (Cw * data.C_L) * (gaussDdim w₁ z * gaussDdim (2 * s) z) := by ring

/-- **★★ B (slot `hf2`, DISCHARGED-MODULO) — `hf2_of_dom`.**  THE `hf2` FULL-SPACE INTEGRABILITY of the
    gradient term `z_i/(2τ)·G_τ·A1amp·F`, REDUCED to a Gaussian-domination carry on the
    coordinate·Gaussian·amplitude product `|z_i/(2τ)·G_τ z·A1amp τ z| ≤ C₂·G_{w₂} z` (a TRUE-Gaussian
    product carry) combined with `data.hFdom`.  Measurability is compositional from the bundle's
    `data.hA1ampmeas`/`data.hFmeas` + coordinate continuity + `gaussDdim` (no `.choose`-heavy tactic).
    ⚠ NOT `a₁ = R/6`. -/
theorem hf2_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ0 : 0 < τ) (hs0 : 0 < s) (hsT : s ≤ T) (C₂ w₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (h2dom : ∀ z, |z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z| ≤ C₂ * gaussDdim w₂ z) :
    Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume := by
  have hcoord : AEStronglyMeasurable (fun z : Point n => z i / (2 * τ)) volume := by
    simp only [div_eq_mul_inv]
    exact ((measurable_pi_apply (X := fun _ : Fin n => ℝ) i).aestronglyMeasurable).mul_const
      (2 * τ)⁻¹
  have hmeas : AEStronglyMeasurable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume :=
    (((hcoord.mul (gaussDdim_integrable' τ hτ0).aestronglyMeasurable).mul
        (data.hA1ampmeas τ)).mul (data.hFmeas s))
  apply integrable_of_dom_gaussPair _ (C₂ * data.C_L) w₂ (2 * s) hmeas
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  have hF := data.hFdom s hs0 hsT z 0
  rw [sub_zero] at hF
  calc |z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z| * |F s z 0|
      ≤ (C₂ * gaussDdim w₂ z) * (data.C_L * gaussDdim (2 * s) z) :=
        mul_le_mul (h2dom z) hF (abs_nonneg _)
          (mul_nonneg hC₂ (gaussDdim_nonneg' _ _))
    _ = (C₂ * data.C_L) * (gaussDdim w₂ z * gaussDdim (2 * s) z) := by ring

/-- **★★ B (slot `hf3`, DISCHARGED-MODULO) — `hf3_of_dom`.**  THE `hf3` FULL-SPACE INTEGRABILITY of the
    mass term `G_τ·A2amp·F`, REDUCED to a Gaussian-domination carry on the Gaussian·amplitude product
    `|G_τ z·A2amp τ z| ≤ C₃·G_{w₃} z` (a TRUE-Gaussian product carry) combined with `data.hFdom`.
    Measurability is compositional from `data.hA2ampmeas`/`data.hFmeas` + `gaussDdim`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hf3_of_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ0 : 0 < τ) (hs0 : 0 < s) (hsT : s ≤ T) (C₃ w₃ : ℝ) (hC₃ : 0 ≤ C₃)
    (h3dom : ∀ z, |gaussDdim τ z * data.A2amp τ z| ≤ C₃ * gaussDdim w₃ z) :
    Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume := by
  have hmeas : AEStronglyMeasurable
      (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume :=
    (((gaussDdim_integrable' τ hτ0).aestronglyMeasurable.mul (data.hA2ampmeas τ)).mul
      (data.hFmeas s))
  apply integrable_of_dom_gaussPair _ (C₃ * data.C_L) w₃ (2 * s) hmeas
  intro z
  rw [Real.norm_eq_abs, abs_mul]
  have hF := data.hFdom s hs0 hsT z 0
  rw [sub_zero] at hF
  calc |gaussDdim τ z * data.A2amp τ z| * |F s z 0|
      ≤ (C₃ * gaussDdim w₃ z) * (data.C_L * gaussDdim (2 * s) z) :=
        mul_le_mul (h3dom z) hF (abs_nonneg _)
          (mul_nonneg hC₃ (gaussDdim_nonneg' _ _))
    _ = (C₃ * data.C_L) * (gaussDdim w₃ z * gaussDdim (2 * s) z) := by ring

/-! ###############################################################################
    ### B-field 9 — `hIchart_int_final` (phase-2 off-collar integrability, now unconditional).
    ############################################################################### -/

/-- **★★ B (slot `hIchart_int`, FINAL) — `hIchart_int_final`.**  PHASE 2's `hIchart_int_concrete` was
    reduced to the three full-space integrabilities `hWint`/`hf2`/`hf3`.  Feeding the phase-3 discharges
    (`hWint_of_dom`/`hf2_of_dom`/`hf3_of_dom`), the off-collar integrability
    `IntegrableOn IchartResidual (collar (c√τ))ᶜ` holds at the witness MODULO ONLY the three
    Gaussian-domination carries + the witness measurability — a strictly more primitive census than the
    three abstract `Integrable` slots.  ⚠ NOT `a₁ = R/6`. -/
theorem hIchart_int_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ0 : 0 < τ) (hs0 : 0 < s) (hsT : s ≤ T)
    (Cw w₁ C₂ w₂ C₃ w₃ : ℝ) (hCw : 0 ≤ Cw) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hWmeas : AEStronglyMeasurable
      (fun z => witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0) volume)
    (hWdom : ∀ z, |witnessSecondXDeriv g gi hC hK S a b i τ z| ≤ Cw * gaussDdim w₁ z)
    (h2dom : ∀ z, |z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z| ≤ C₂ * gaussDdim w₂ z)
    (h3dom : ∀ z, |gaussDdim τ z * data.A2amp τ z| ≤ C₃ * gaussDdim w₃ z) :
    IntegrableOn (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume :=
  hIchart_int_concrete g gi hC hK S a b F i T τ₀ r₀ c data τ s
    (hWint_of_dom g gi hC hK S a b F i T τ₀ r₀ c data τ s hs0 hsT Cw w₁ hCw hWmeas hWdom)
    (hf2_of_dom g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ0 hs0 hsT C₂ w₂ hC₂ h2dom)
    (hf3_of_dom g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ0 hs0 hsT C₃ w₃ hC₃ h3dom)

/-! ###############################################################################
    ### PACKAGE — the phase-3 conjunction (phase 2 ∧ the Lipschitz/measurability/integrability fields).
    ############################################################################### -/

/-- **★★★ B (phase-3 package) — `slotInstantiation_phase3`.**  The conjunction of the group-(1) slot
    carries discharged through phase 3, at the true ρ-scaled chart witness (built on
    `slotInstantiation_phase2`), given the enumerated factor sup/Lipschitz carries + the three
    Gaussian-domination carries:
      • phase 2 (`h0`, `hgate`, `hoff`, `hIchart_int`) — with `hWint`/`hf2`/`hf3` now DERIVED here from
        the domination carries (so `hIchart_int` is discharged at the witness), AND
      • `hqz` (`hqz_concrete`), `hqc` (`hqc_concrete`) — the two Lipschitz carries, AND
      • `hqzmeas`, `hqcmeas` (`aesm_of_lipBound`) — their a.e.-strong measurabilities.
    All are VERBATIM arguments of `GpowClosure.leviSecondPairing_inner_bound_concrete` at the same
    concrete witness.  The remaining group-(1) residue is `hcomp` (the comparison leg — the LOCUS OF THE
    GEOMETRIC CONTENT) and the `hf2bound`/`hf3bound` Gaussian-moment dominators.  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hChr hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ0 : 0 < τ) (hττ₀ : τ < τ₀) (hs0 : 0 < s) (hsT : s ≤ T)
    (hcr : c * Real.sqrt τ < r₀)
    (hKcover : ∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K)
    -- factor sup / Lipschitz carries (feed both `hqz` and `hqc`):
    (M_ρ M_A M_F L_ρ L_A L_F : ℝ)
    (hMρnn : 0 ≤ M_ρ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hLρnn : 0 ≤ L_ρ) (hLAnn : 0 ≤ L_A) (hLFnn : 0 ≤ L_F)
    (hMρ : ∀ τ z, |rhoRatio g gi hChr hK τ z| ≤ M_ρ)
    (hMA : ∀ τ z, |chartAmp g gi hChr hK a b τ z 0| ≤ M_A)
    (hMF : ∀ s w, |F s w 0| ≤ M_F)
    (hLρ : ∀ τ z w, |rhoRatio g gi hChr hK τ z - rhoRatio g gi hChr hK τ w| ≤ L_ρ * dist z w)
    (hLA : ∀ τ z w,
      |chartAmp g gi hChr hK a b τ z 0 - chartAmp g gi hChr hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : ∀ s z w, |F s z 0 - F s w 0| ≤ L_F * dist z w)
    -- the three Gaussian-domination carries (the census shape):
    (Cw w₁ C₂ w₂ C₃ w₃ : ℝ) (hCw : 0 ≤ Cw) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hWmeas : AEStronglyMeasurable
      (fun z => witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0) volume)
    (hWdom : ∀ z, |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ Cw * gaussDdim w₁ z)
    (h2dom : ∀ z, |z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z| ≤ C₂ * gaussDdim w₂ z)
    (h3dom : ∀ z, |gaussDdim τ z * data.A2amp τ z| ≤ C₃ * gaussDdim w₃ z) :
    -- phase 2:
    (((rhoRatio g gi hChr hK τ 0 * chartAmp g gi hChr hK a b τ 0 0) * F s 0 0
        = chartAmp g gi hChr hK a b τ 0 0 * F s 0 0)
    ∧ (∀ z ∈ collar (n := n) (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    ∧ (∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
        witnessSecondXDeriv g gi hChr hK S a b i τ z * F s z 0
          = IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s z
            + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
            + gaussDdim τ z * data.A2amp τ z * F s z 0)
    ∧ IntegrableOn (IchartResidual g gi hChr hK S a b F i T τ₀ r₀ c data τ s)
        (collar (c * Real.sqrt τ))ᶜ volume)
    -- phase 3 (the two Lipschitz carries + their measurabilities):
    ∧ (∀ z w : Point n,
        |(rhoRatio g gi hChr hK τ z * chartAmp g gi hChr hK a b τ z 0) * F s z 0
            - (rhoRatio g gi hChr hK τ w * chartAmp g gi hChr hK a b τ w 0) * F s w 0|
          ≤ (M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F) * dist z w)
    ∧ (∀ z w : Point n,
        |chartAmp g gi hChr hK a b τ z 0 * F s z 0 - chartAmp g gi hChr hK a b τ w 0 * F s w 0|
          ≤ (M_A * L_F + M_F * L_A) * dist z w)
    ∧ AEStronglyMeasurable
        (fun z => (rhoRatio g gi hChr hK τ z * chartAmp g gi hChr hK a b τ z 0) * F s z 0) volume
    ∧ AEStronglyMeasurable
        (fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0) volume := by
  have hτmem : τ ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hτ0, hττ₀⟩
  -- derive the three integrabilities from the domination carries.
  have hWint := hWint_of_dom g gi hChr hK S a b F i T τ₀ r₀ c data τ s hs0 hsT Cw w₁ hCw hWmeas hWdom
  have hf2 := hf2_of_dom g gi hChr hK S a b F i T τ₀ r₀ c data τ s hτ0 hs0 hsT C₂ w₂ hC₂ h2dom
  have hf3 := hf3_of_dom g gi hChr hK S a b F i T τ₀ r₀ c data τ s hτ0 hs0 hsT C₃ w₃ hC₃ h3dom
  -- the two Lipschitz carries.
  have hqz := hqz_concrete g gi hChr hK a b F T τ₀ M_ρ M_A M_F L_ρ L_A L_F
    hMρnn hMAnn hMFnn hMρ hMA hMF hLρ hLA hLF τ hτmem s hs0 hsT
  have hqc := hqc_concrete g gi hChr hK a b F τ s M_A M_F L_A L_F hMAnn hMFnn
    (fun z => hMA τ z) (fun z => hMF s z) (fun z w => hLA τ z w) (fun z w => hLF s z w)
  -- their measurabilities (from the Lipschitz bounds).
  have hLqz : (0 : ℝ) ≤ M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F := by positivity
  have hLqc : (0 : ℝ) ≤ M_A * L_F + M_F * L_A := by positivity
  have hqzmeas := aesm_of_lipBound
    (fun z => (rhoRatio g gi hChr hK τ z * chartAmp g gi hChr hK a b τ z 0) * F s z 0)
    _ hLqz hqz
  have hqcmeas := aesm_of_lipBound
    (fun z => chartAmp g gi hChr hK a b τ z 0 * F s z 0) _ hLqc hqc
  exact ⟨slotInstantiation_phase2 g gi hChr hK h0K S a b F i T τ₀ r₀ c data τ s hcr hKcover
      hWint hf2 hf3,
    hqz, hqc, hqzmeas, hqcmeas⟩

end QIQTH.SlotInstantiationIII

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationIII
#print axioms aesm_of_lipBound
#print axioms integrable_of_dom_gaussPair
#print axioms hqz_concrete
#print axioms hqc_concrete
#print axioms hWint_of_dom
#print axioms hf2_of_dom
#print axioms hf3_of_dom
#print axioms hIchart_int_final
#print axioms slotInstantiation_phase3
end AxiomChecks

/-! ###############################################################################
    ## PHASE 3 COVERAGE  (J4-420, Part B, tranche (a))
    ###############################################################################

  FIELDS DISCHARGED CONCRETELY (at the true ρ-scaled chart witness, `S`-generic; building on phases 1-2):
    • `hqz` (term-1 amplitude · Levi Lipschitz) — via `hqz_concrete`, MODULO the six factor carries
      `M_ρ`/`M_A`/`M_F`/`L_ρ`/`L_A`/`L_F`.  Supplier: `DataAmpAssembly.concrete_hqLip_of_carries`
      (banked E3 three-factor product-Lipschitz wiring — NO new moment analysis).
    • `hqc` (chart-native comparison amplitude Lipschitz) — via `hqc_concrete`, MODULO the four factor
      carries `M_A`/`M_F`/`L_A`/`L_F`.  Supplier:
      `DisplacementDerivative.collar_product_lipschitz_increment` (banked two-factor core).
    • `hqzmeas`/`hqcmeas` (a.e.-strong measurabilities) — via `aesm_of_lipBound` (this file), DERIVED
      from the Lipschitz bounds (`LipschitzWith.of_dist_le_mul` ⟹ continuous ⟹ AESM); no `.choose`-heavy
      measurability tactic is run.
    • `hWint`/`hf2`/`hf3` (full-space integrabilities) — via `hWint_of_dom`/`hf2_of_dom`/`hf3_of_dom`,
      REDUCED to explicit two-Gaussian PRODUCT-domination carries (the `hAdom2cap`/`hFdom` census shape)
      + `data.hFdom`, through `integrable_of_dom_gaussPair` (banked
      `CConvV2GaussianPairing.gaussDdim_pair_integrable` + `Integrable.mono'`).  hf2/hf3 measurabilities
      are compositional from the bundle fields `data.hA1ampmeas`/`data.hA2ampmeas`/`data.hFmeas` +
      coordinate continuity + `gaussDdim`.
    • `hIchart_int` (off-collar integrability) — `hIchart_int_final` promotes phase 2's
      `hIchart_int_concrete` to hold at the witness MODULO ONLY the three Gaussian-domination carries +
      the witness measurability (strictly more primitive than the three abstract `Integrable` slots).
    • (carried through from phases 1-2) `h0`, `hgate`, `Ichart`, `hoff`.

  DONT-UNDERCREDIT CHECK.  Grepped the bank BEFORE building (`hqLip`/`LipschitzOnWith`, `hWint`/
  `intervalIntegrable`, `gaussDdim_*_integrable`):
    · `DataAmpAssembly.concrete_hqLip_of_carries` is the EXACT banked `hqz` supplier (the phase-2 author's
      recommended route) — reused verbatim, so `hqz` is a wiring, not a re-proof.
    · `DisplacementDerivative.collar_product_lipschitz_increment` is the banked TWO-factor core; the
      chart-native `qc = A_chart·F` needs exactly it (the three-factor `Aamp_times_F_lipschitz` carries a
      spurious `ρ` factor absent from `qc`), so `hqc_concrete` is the honest new two-factor wiring.
    · `CConvV2GaussianPairing.gaussDdim_pair_integrable` (+ `gaussDdim_integrable'`/`gaussDdim_nonneg'`
      from `GaussianHessianCancel`) are the banked integrability workhorses; the three integrabilities
      are `Integrable.mono'` reductions onto them.  NO banked lemma constructs the full-space
      integrability of `witnessSecondXDeriv·F` / the gradient / the mass term unconditionally — they are
      genuinely CARRIED (reduced to the domination shape), matching the `gpow_closure_carries` census.

  REMAINING RESIDUE (honest; J4-421+; each with a one-line plan):
    • `hcomp` (comparison leg) — ★ THE LOCUS OF THE GEOMETRIC CONTENT.  Plan: `GpowClosure.hcomp_concrete`
      (= `SliverAssemblyMatched.comparison_leg_of_dom`) fed by (a) `hcompDiff_int` (integrability of
      `IchartResidual − hessGaussFactor·qc` off collar — a `Integrable.sub`-style reduction like phase 2),
      (b) the pointwise dominator `D` with `‖IchartResidual − hessGaussFactor·qc‖ ≤ D`, and (c) the moment
      bound `∫_{collarᶜ} D ≤ Bcomp/√τ` (the `cubic_gaussian_moment_witness` family).  This is where the
      chart-native `hessCoeff·G^chart·qc` FORM of `IchartResidual` must finally be proved — the true
      geometric input, NOT a wiring.
    • `hf2bound`/`hf3bound` (gradient/mass Gaussian-moment ABSOLUTE dominators) — see scoping below.
  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  ─────────────────────────────────────────────────────────────────────────────
  SCOPING — `hf2bound`/`hf3bound` (NOT built here; the demand read off the binder shapes).
  ─────────────────────────────────────────────────────────────────────────────
  The GpowClosure binders are the ABSOLUTE integral bounds
    `hf2bound : |∫ z, z_i/(2τ)·G_τ z·A1amp τ z·F s z 0| ≤ Q/√τ`,
    `hf3bound : |∫ z, G_τ z·A2amp τ z·F s z 0| ≤ Sconst`.
  These are STRICTLY STRONGER than the `hf2`/`hf3` integrabilities discharged above: they need the VALUE
  of the integral bounded, with the `hf2` term carrying an explicit `τ^{-1/2}` (odd first moment of the
  Gaussian against the `z_i/(2τ)` weight → one power of `√τ` in the denominator) and the `hf3` term
  `τ`-uniform (zeroth moment / total-mass-one of `G_τ`, times the collar-uniform `A2amp` sup `M₂`).
  The banked route is `SlotDischarges.hf2bound_slot_of_dom` / `hf3bound_slot_of_dom` fed by
  `abs_integral_le_of_dom` (triangle ⟹ `|∫| ≤ ∫‖·‖`) and the cubic/mass Gaussian-moment family
  (`AmpQuantBundle` `cubic_gaussian_moment_witness` + `gaussDdim_mass_one`).  The genuinely-new content
  is the ODD-MOMENT `√τ` extraction for `hf2bound` (the `z_i/(2τ)` weight against `G_τ` gives
  `∫|z_i|/(2τ)·G_τ ≍ τ^{-1/2}`) — a one-dimensional Gaussian first-absolute-moment computation, plus the
  collar-uniform amplitude sups `M₁`/`M₂` (`data.hA1ampBdd`/`data.hA2ampBdd`, but those are
  REGIME-restricted, so the full-space moment needs the same true-Gaussian product control as the `hf2`/
  `hf3` carries here).  Recommended as its own brick (J4-421), separate from the geometric `hcomp`.
-/
