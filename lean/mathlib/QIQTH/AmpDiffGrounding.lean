/-
  AmpDiffGrounding — J4-495: ground the concrete-remainder on-collar amplitude-difference sup
  `|Aamp·F − chartAmp·F| ≤ M₀` to the (I1)-closed collar data, so `concreteRemainder_order` no
  longer accepts a RAW full-space carried sup but consumes an (I1)-reachable, REGION-MATCHED bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign — remainder-subsystem cleanup.  No
  `sorry` (header prose excepted), no `:= True`, no `admit`, no new axioms, no vacuous / unsatisfiable
  hypothesis, no result equal to (or trivially yielding) the conclusion, no existing file edited,
  nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GATE CATCH (recorded — the full-space `∀ z` amp-diff sup is REGION-MISMATCHED for concrete data).
  `ConcreteRemainderOrder.concreteRemainder_order` carries
      `hAmpDiff : ∀ z, |data.Aamp τ z · F − chartAmp g … a b τ z 0 · F| ≤ M₀`
  as a RAW full-space (`∀ z`) sup.  But it is USED ONLY on the √ε collar `collar (c√τ)` (inside
  `concreteIntegrand_on_collar_le`, under `ae_restrict` to the collar).  For the CONCRETE amplitude
  `data.Aamp τ z = rhoRatio τ z · chartAmp₀`, one has
      `Aamp·F − chartAmp·F = (rhoRatio τ z − 1) · (chartAmp₀ · F)`,
  and `rhoRatio` is UNBOUNDED off the collar (it grows like `exp(‖z‖²/4τ)`), so the full-space `∀ z`
  sup is NOT (I1)-reachable — indeed it is UNSATISFIABLE for the concrete data at any finite `M₀`.
  Feeding a full-space (I1) constant would be a false / region-mismatched binding.  So we do NOT.

  ## WHAT WE ACTUALLY DO (region-matched, (I1)-grounded).  On the collar, `rhoRatio ≤ collarK`
  (`AmplitudeDataOnCollar.rhoRatio_le_collarK`, the (I1)-closed near-isometry bound), and `rhoRatio > 0`
  (`rhoRatio_pos`), so `|rhoRatio − 1| ≤ collarK + 1`.  With the banked global `hqcbdd`
  (`|chartAmp₀ · F| ≤ Mqc`) this gives the ON-COLLAR amplitude-difference sup
      `|Aamp·F − chartAmp·F| ≤ (collarK + 1) · Mqc =: M₀`
  — an (I1)-reachable constant (`collarK = exp(Liso·n·c³·√τ₀/4) > 0`, `Mqc ≥ 0`).  We then re-run the
  EXACT three-region assembly of `concreteRemainder_order` (on-collar Hessian moment + banked
  off-collar comparison leg `hcomp_final4` + collar split), with the on-collar amp-diff bound DERIVED
  per-collar-point from (I1) instead of taken as a raw full-space carry.

  ## WHAT LANDS.
    ★  `concreteIntegrand_on_collar_le_atz` — the PER-POINT on-collar pointwise bound (the `∀ z`
       hypothesis of `concreteIntegrand_on_collar_le` weakened to the single collar point it is used
       at), so the amp-diff bound need only hold WHERE it is used.
    ★★★ `concreteRemainder_order_reach` — the CONCRETE remainder τ-order with `hAmpDiff` DISCHARGED
       from (I1): same explicit `O(1/τ)` as `concreteRemainder_order`, but with
       `M₀ := (collarK Liso c τ₀ + 1) · Mqc` GROUNDED on the (I1) near-isometry carry `hiso`/`hLiso`
       (feeding `collarK`) + the banked `hqcbdd` + the definitional concrete-amplitude form
       `hAampForm : data.Aamp τ z = rhoRatio τ z · chartAmp₀`.  The raw full-space `hAmpDiff` carry is
       GONE; the substantive external carries are `hiso` (the (I1) near-isometry lower bound) and the
       gate carries `hform_gate`/`hgate` (unchanged), plus the banked amplitude/integrability feeds.

  ## HONEST DISTANCE.  This is remainder-subsystem CLEANUP: it swaps a region-mismatched, raw full-space
  sup for an (I1)-reachable on-collar bound, matching the region the capstone actually uses.  ⚠ NOT
  `a₁ = R/6`; the LEADING O(1) coefficient and its `R/6` identification lie BEYOND this remainder
  τ-order.  a₁ = R/6 remains CONDITIONAL.
-/
import QIQTH.ConcreteRemainderOrder

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII
open QIQTH.FarFieldDecay QIQTH.FarFieldMomentOrder QIQTH.OnCollarMomentOrder
open QIQTH.ConcreteRemainderOrder
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.AmpDiffGrounding

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE PER-POINT ON-COLLAR POINTWISE BOUND (region-matched hypothesis).
    ############################################################################### -/

/-- **★ `concreteIntegrand_on_collar_le_atz`.**  The per-collar-point analogue of
    `ConcreteRemainderOrder.concreteIntegrand_on_collar_le`: the amp-difference bound is required only
    at the SINGLE collar point `z` (a `|·| ≤ M₀` hypothesis about that `z`), not as a full-space `∀ z`
    sup — matching the region where the on-collar leg actually consumes it.  Same pure-Hessian argument
    (`GpowClosure.hon_concrete` + `|z_i²−2τ| ≤ ‖z‖²+2τ`).  ⚠ NOT `a₁ = R/6`. -/
theorem concreteIntegrand_on_collar_le_atz (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (hgate : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (M₀ : ℝ) (hM₀ : 0 ≤ M₀)
    (z : Point n) (hz : z ∈ collar (c * Real.sqrt τ))
    (hAmpDiffz : |data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ M₀) :
    ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)‖
      ≤ onCollarDom τ M₀ 0 0 z := by
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
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
  have hon := QIQTH.GpowClosure.hon_concrete g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ hττ₀ hgate
  have hfeq : IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
      = hessGaussFactor i τ z
          * (data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0) := by
    unfold IchartResidual
    rw [hon z hz]
    ring
  rw [hfeq, Real.norm_eq_abs, abs_mul]
  have hhess : |hessGaussFactor i τ z| ≤ (‖z‖ ^ 2 + 2 * τ) * (1 / (4 * τ ^ 2)) * gaussDdim τ z := by
    unfold hessGaussFactor
    rw [abs_mul, abs_of_nonneg hG]
    gcongr
    rw [abs_div, abs_of_pos h4τ2, div_eq_mul_one_div]
    gcongr
  calc |hessGaussFactor i τ z|
        * |data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0|
      ≤ ((‖z‖ ^ 2 + 2 * τ) * (1 / (4 * τ ^ 2)) * gaussDdim τ z) * M₀ :=
        mul_le_mul hhess hAmpDiffz (abs_nonneg _) (by positivity)
    _ = onCollarDom τ M₀ 0 0 z := by unfold onCollarDom; ring

/-! ###############################################################################
    ### ★★★ THE (I1)-GROUNDED CONCRETE REMAINDER-ORDER CAPSTONE.
    ############################################################################### -/

/-- **★★★ `concreteRemainder_order_reach` — CONCRETE REMAINDER τ-ORDER with `hAmpDiff` DISCHARGED
    from (I1).**  Same explicit `O(1/τ)` bound on the full-space integral of the real remainder
    integrand `f = IchartResidual − hessGaussFactor·(chartAmp·F)` as
    `ConcreteRemainderOrder.concreteRemainder_order`, but the on-collar amplitude-difference constant
    is now `M₀ := (collarK Liso c τ₀ + 1) · Mqc`, GROUNDED on:
      • the (I1) near-isometry lower bound `hiso`/`hLiso` (feeding `rhoRatio ≤ collarK`), and
      • the banked global `hqcbdd` (`|chartAmp₀ · F| ≤ Mqc`), and
      • the definitional concrete-amplitude form `hAampForm` (`data.Aamp = rhoRatio · chartAmp₀`).
    The RAW full-space `hAmpDiff` carry is GONE — it is derived per-collar-point via
    `rhoRatio_le_collarK` + `rhoRatio_pos`.  Off-collar it is neither claimed nor needed (the off-collar
    leg is the banked comparison leg `hcomp_final4`, which never touches the amp-diff sup).  ⚠ NOT
    `a₁ = R/6`. -/
theorem concreteRemainder_order_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (r Liso L' M1F M2F Mqc : ℝ) (hLiso : 0 ≤ Liso) (hL' : 0 ≤ L')
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (hgateCollar : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - Liso * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hAampForm : ∀ z : Point n,
      data.Aamp τ z = rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0)
    (hfInt : Integrable
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) volume)
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
    |∫ z : Point n, (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ (collarK (n := n) Liso c τ₀ + 1) * Mqc * ((n : ℝ) + 1) / (2 * τ)
        + (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
              * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                  + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
              / 16 / Real.sqrt τ
            + (M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ))) := by
  -- (I1)-grounded on-collar amp-difference constant.
  have hcK : 0 < collarK (n := n) Liso c τ₀ := collarK_pos Liso c τ₀
  set M₀ := (collarK (n := n) Liso c τ₀ + 1) * Mqc with hM₀def
  have hM₀ : 0 ≤ M₀ := by rw [hM₀def]; exact mul_nonneg (by linarith) hMqc
  have hcollarmeas : MeasurableSet (collar (n := n) (c * Real.sqrt τ)) :=
    QIQTH.SliverTailMatched.collar_measurableSet _
  -- ON-COLLAR LEG (amp-diff bound derived per-point from (I1)).
  have honLeg : |∫ z in collar (n := n) (c * Real.sqrt τ),
      (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ M₀ * ((n : ℝ) + 1) / (2 * τ) := by
    have hmono : ∫ z in collar (n := n) (c * Real.sqrt τ),
          ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
            - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)‖
        ≤ ∫ z in collar (n := n) (c * Real.sqrt τ), onCollarDom τ M₀ 0 0 z := by
      refine integral_mono_ae hfInt.integrableOn.norm
        ((onCollarDom_integrable τ M₀ 0 0 hτ).integrableOn) ?_
      refine (ae_restrict_iff' hcollarmeas).mpr (ae_of_all _ (fun z hz => ?_))
      -- derive the (I1) on-collar amp-diff bound at `z`.
      have hreg : collarRegime (K := K) r₀ c τ₀ τ z := by
        obtain ⟨hzK, hzr⟩ := hgateCollar z hz
        exact ⟨hτ, hττ₀, hzK, hzr, hz⟩
      have hρle : rhoRatio g gi hC hK τ z ≤ collarK (n := n) Liso c τ₀ :=
        rhoRatio_le_collarK g gi hC hK Liso c τ₀ r₀ hLiso hiso τ z hreg
      have hρpos : 0 < rhoRatio g gi hC hK τ z := rhoRatio_pos g gi hC hK τ z
      have hAmpDiffz : |data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ M₀ := by
        have heq : data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0
            = (rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0) := by
          rw [hAampForm z]; ring
        rw [hM₀def, heq, abs_mul]
        have h1 : |rhoRatio g gi hC hK τ z - 1| ≤ collarK (n := n) Liso c τ₀ + 1 := by
          rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
        exact mul_le_mul h1 (hqcbdd z) (abs_nonneg _) (by linarith)
      exact concreteIntegrand_on_collar_le_atz g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ hττ₀
        hgateCollar M₀ hM₀ z hz hAmpDiffz
    have hset : ∫ z in collar (n := n) (c * Real.sqrt τ), onCollarDom τ M₀ 0 0 z
        ≤ M₀ * ((n : ℝ) + 1) / (2 * τ) :=
      (onCollarDom_setIntegral_le τ M₀ 0 0 hτ hM₀ le_rfl le_rfl _).trans (le_of_eq (by ring))
    calc |∫ z in collar (n := n) (c * Real.sqrt τ),
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
        = ‖∫ z in collar (n := n) (c * Real.sqrt τ),
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ z in collar (n := n) (c * Real.sqrt τ),
            ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ M₀ * ((n : ℝ) + 1) / (2 * τ) := le_trans hmono hset
  -- OFF-COLLAR LEG (annulus ∪ far field) — the banked comparison leg (unchanged, no amp-diff sup).
  have hoffLeg : |∫ z in (collar (n := n) (c * Real.sqrt τ))ᶜ,
      (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      ≤ L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
            * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
            / 16 / Real.sqrt τ
          + ∫ z : Point n, farFieldDom τ M1F M2F Mqc z := by
    rw [← Real.norm_eq_abs]
    exact hcomp_final4 g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ r L' M1F M2F Mqc hL'
      hM1F hM2F hMqc hKr hfInt.integrableOn hform_gate hgate hA1F hA2F hqcbdd
  -- COMBINE via the exhaustive collar split.
  have hsplit : (∫ z in collar (n := n) (c * Real.sqrt τ),
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
      + (∫ z in (collar (n := n) (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
      = ∫ z : Point n, (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) :=
    integral_add_compl hcollarmeas hfInt
  calc |∫ z : Point n, (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
      = |(∫ z in collar (n := n) (c * Real.sqrt τ),
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
          + (∫ z in (collar (n := n) (c * Real.sqrt τ))ᶜ,
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))| := by
        rw [hsplit]
    _ ≤ |∫ z in collar (n := n) (c * Real.sqrt τ),
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))|
          + |∫ z in (collar (n := n) (c * Real.sqrt τ))ᶜ,
            (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
              - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))| :=
        abs_add_le _ _
    _ ≤ M₀ * ((n : ℝ) + 1) / (2 * τ)
          + (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
                * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                    + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
                / 16 / Real.sqrt τ
              + ∫ z : Point n, farFieldDom τ M1F M2F Mqc z) :=
        add_le_add honLeg hoffLeg
    _ ≤ M₀ * ((n : ℝ) + 1) / (2 * τ)
          + (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
                * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                    + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
                / 16 / Real.sqrt τ
              + (M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ))) := by
        gcongr
        exact farFieldDom_integral_le τ M1F M2F Mqc hτ hM1F hM2F hMqc

end QIQTH.AmpDiffGrounding

/-! ###############################################################################
    ## J4-495 LEDGER — grounding the concrete-remainder on-collar amp-diff sup to (I1).
    ###############################################################################

  WHAT LANDS.  `concreteRemainder_order_reach` reproves the CONCRETE remainder τ-order
    `|∫ f| ≤ M₀·(n+1)/(2τ) + (Bcomp₂/√τ + (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)))`
  with `M₀ := (collarK Liso c τ₀ + 1)·Mqc` GROUNDED on (I1): the raw full-space `hAmpDiff` carry of
  `concreteRemainder_order` is REPLACED by a per-collar-point derivation from `rhoRatio ≤ collarK`
  (`rhoRatio_le_collarK`, the (I1)-closed near-isometry bound) + `rhoRatio > 0` + the banked global
  `hqcbdd`, via the definitional `hAampForm : data.Aamp = rhoRatio · chartAmp₀`.

  ⚠ THE GATE CATCH.  The RAW `hAmpDiff : ∀ z, |Aamp·F − chartAmp·F| ≤ M₀` was REGION-MISMATCHED: it is
  stated full-space but used only on the collar, and for the concrete data (`Aamp = rhoRatio·chartAmp₀`,
  `rhoRatio` unbounded off-collar) the full-space `∀ z` sup is UNSATISFIABLE at any finite `M₀`.  This
  brick binds `M₀` to a genuinely (I1)-REACHABLE constant on the SAME region the capstone consumes it
  (the collar), and never claims the off-collar bound (the off-collar leg is `hcomp_final4`, which does
  not touch the amp-diff sup).  So the binding is region-matched and satisfiable, NOT vacuous.

  DON'T-UNDERCREDIT.  Heavy analysis reused verbatim: `ConcreteRemainderOrder.concreteRemainder_order`'s
  three-region assembly (`GpowClosure.hon_concrete`, `OnCollarMomentOrder.onCollarDom_setIntegral_le`,
  `FarFieldDecay.hcomp_final4`, `FarFieldMomentOrder.farFieldDom_integral_le`, the collar split), plus
  the (I1)-closed collar bound `AmplitudeDataOnCollar.rhoRatio_le_collarK`.  NEW content: the per-point
  on-collar pointwise lemma (region-matched hypothesis) + the (I1) per-point amp-diff derivation
  (`|rhoRatio−1| ≤ collarK+1`, `|chartAmp₀·F| ≤ Mqc`) wired into the reproved capstone.

  HONEST DISTANCE.  Remainder-subsystem cleanup: it swaps a region-mismatched raw full-space sup for an
  (I1)-reachable on-collar bound.  The substantive external carries reduce to `hiso` (the (I1)
  near-isometry lower bound) + the gate carries `hform_gate`/`hgate` (unchanged) + the banked
  amplitude/integrability feeds.  ⚠ a₁ = R/6 remains CONDITIONAL; the LEADING O(1) coefficient and its
  `R/6` identification lie BEYOND this remainder τ-order.
-/

section AxiomChecks
open QIQTH.AmpDiffGrounding
#print axioms concreteIntegrand_on_collar_le_atz
#print axioms concreteRemainder_order_reach
end AxiomChecks
