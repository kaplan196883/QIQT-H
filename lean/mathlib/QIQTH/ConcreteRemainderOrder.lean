/-
  ConcreteRemainderOrder — J4-494: promote the remainder-assembly τ-order PROXY to the CONCRETE
  heat-trace remainder integrand `f = IchartResidual − hessGaussFactor·(chartAmp·F)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry` (header prose excepted),
  no `:= True`, no new axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT — the CONCRETE remainder integrand's full-space τ-order.  The mission asked to discharge
  the two GENERIC pointwise-domination hypotheses of `RemainderAssembly.remainderIntegral_order` for the
  REAL integrand `f z := IchartResidual g gi … z − hessGaussFactor i τ z · (chartAmp g gi … z · F s z 0)`.

  ## ⚠ THE GATE CATCH (recorded — the literal proxy hypothesis is UNSATISFIABLE for the concrete `f`).
  `remainderIntegral_order` splits the whole space at a SINGLE radius `r₀` into `collar r₀ ⊔ (collar r₀)ᶜ`
  and demands a POINTWISE far-field domination `|f| ≤ farFieldDom` on ALL of `(collar r₀)ᶜ`.  For the
  concrete `f` this cannot hold at any satisfiable common `r₀`, because:
    • the banked far-field pointwise bound (`FarFieldDecay.farField_ptwise_bound`) holds only OFF `K`
      (there `witnessSecondXDeriv = 0`, so `f` is a pure Gaussian remainder), and
    • the banked on-collar identity (`GpowClosure.hon_concrete` / `SliverBoundOnCollar.…`) holds only on
      the √ε collar `collar (c√τ)`.
  Between them sits the ANNULUS `{‖z‖ > c√τ} ∩ K` (off the √ε collar but inside the base gate), where the
  witness term is present and un-expanded — the well-known "off-collar sliver remainder" carry, NOT a
  pointwise Gaussian-moment fact.  A two-way pointwise split at a common `r₀` would require `K = collar r₀`
  (an unsatisfiable geometric coincidence).  So we do NOT feed the concrete `f` to `remainderIntegral_order`
  through a false/unsatisfiable pointwise-far hypothesis.

  ## WHAT WE ACTUALLY DO (the honest concrete assembly, three-region, via the banked GATE leg).  We split
  the full-space integral at the √ε collar `collar (c√τ)` and bound each piece by a BANKED object:
    • ON-COLLAR (`collar (c√τ)`): here `f = hessGaussFactor·(Aamp·F − chartAmp·F)` (from `hon_concrete`),
      a PURE HESSIAN term, so `|f| ≤ onCollarDom τ M₀ 0 0` with `M₀ ≥ sup|Aamp·F − chartAmp·F|` (the
      (I1)-reachable on-collar amplitude-difference sup).  Its collar integral is the near-diagonal
      moment `≤ M₀·(n+1)/(2τ)` (`OnCollarMomentOrder.onCollarDom_setIntegral_le`).  [NEW pointwise brick
      `concreteIntegrand_on_collar_le`.]
    • OFF-COLLAR (`(collar (c√τ))ᶜ`, the ANNULUS ∪ FAR field): the banked INTEGRAL-level comparison leg
      `FarFieldDecay.hcomp_final4` gives `‖∫ f‖ ≤ Bcomp₂/√τ + ∫ farFieldDom` — the annulus by the GATE's
      `(ρ−1)` near-isometry + cubic jet (`O(1/√τ)`), the far field by the off-`K` Gaussian remainder
      (`O(1/τ)`).  This is NOT a pointwise `farFieldDom` domination; it is the honest integral bound that
      handles the annulus the proxy could not.
  Combining via `|∫_full f| ≤ |∫_collar f| + |∫_collarᶜ f|` (`integral_add_compl`, `abs_add_le`) and
  making the far-field integral explicit (`FarFieldMomentOrder.farFieldDom_integral_le`) yields a single,
  fully explicit `O(1/τ)` bound on the CONCRETE remainder integrand.

  ## WHAT LANDS.
    ★  `concreteIntegrand_on_collar_le` — the on-collar pointwise bound `‖f z‖ ≤ onCollarDom τ M₀ 0 0 z`
       on `collar (c√τ)` (from `hon_concrete` + `|z_i²−2τ| ≤ ‖z‖²+2τ` + the amplitude-difference sup).
    ★★★ `concreteRemainder_order` — THE CONCRETE CAPSTONE: the full-space integral of the REAL remainder
       integrand `f` obeys the explicit `O(1/τ)`
         `|∫_z f| ≤ M₀·(n+1)/(2τ)  +  (Bcomp₂/√τ + (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)))`.

  ## THE GATE (satisfiability — checked BEFORE building).  REACHABLE & NON-VACUOUS.  `M₀ ≥ 0` is the
  (I1)-reachable on-collar sup of `|Aamp·F − chartAmp·F|` (both amplitudes are collar-bounded); the far
  constants `M1F/M2F/Mqc ≥ 0` are the genuine global sups `hcomp_final4` already carries; `hKr : K ⊆ ball 0 r`
  is satisfiable (K compact ⟹ bounded); `hgateCollar`/`hform_gate`/`hgate` are the banked gate carries;
  `f` is genuinely integrable (`IchartResidual` + `hessGaussFactor·qc` both integrable).  The split is at
  `collar (c√τ)` — the SAME radius the on-collar identity uses — so no annulus is silently dropped: it is
  ABSORBED into `hcomp_final4`'s off-collar bound, not into a false pointwise domination.

  ## HONEST DISTANCE.  This is the honest concrete-integrand analogue of the proxy: the FULL heat-trace
  remainder integrand is now τ-order-CONTROLLED as a single explicit `O(1/τ)`, on-collar by the
  (I1)-reachable sup, off-collar by the banked gate+far comparison leg.  It carries the banked, satisfiable
  gate/amplitude/integrability inputs (no generic dominated-`f` hypothesis remains).  ⚠ NOT `a₁ = R/6`;
  the LEADING O(1) coefficient (and its `R/6` identification) lies BEYOND this remainder τ-order.
-/
import QIQTH.RemainderAssembly
import QIQTH.GpowClosure

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII
open QIQTH.FarFieldDecay QIQTH.FarFieldMomentOrder QIQTH.OnCollarMomentOrder
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.ConcreteRemainderOrder

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE ON-COLLAR POINTWISE BOUND of the CONCRETE integrand by `onCollarDom`.
    ############################################################################### -/

/-- **★ `concreteIntegrand_on_collar_le`.**  On the √ε collar `collar (c√τ)`, the concrete remainder
    integrand `f = IchartResidual − hessGaussFactor·(chartAmp·F)` is a PURE HESSIAN term:
    from `GpowClosure.hon_concrete` (`witnessSecondXDeriv·F = hessGaussFactor·(Aamp·F) + f₂ + f₃`) and
    `IchartResidual = witnessSecondXDeriv·F − f₂ − f₃`, one gets
    `f = hessGaussFactor·(Aamp·F − chartAmp·F)`.  Hence with `|z_i²−2τ| ≤ ‖z‖²+2τ` and the
    amplitude-difference sup `M₀`,
      `‖f z‖ ≤ M₀·(1/(4τ²))·((‖z‖²+2τ)·G_τ) = onCollarDom τ M₀ 0 0 z`.
    ⚠ NOT `a₁ = R/6`. -/
theorem concreteIntegrand_on_collar_le (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (hgate : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (M₀ : ℝ) (hM₀ : 0 ≤ M₀)
    (hAmpDiff : ∀ z, |data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ M₀)
    (z : Point n) (hz : z ∈ collar (c * Real.sqrt τ)) :
    ‖IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)‖
      ≤ onCollarDom τ M₀ 0 0 z := by
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
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
  -- the on-collar pure-Hessian form of `f`.
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
        mul_le_mul hhess (hAmpDiff z) (abs_nonneg _) (by positivity)
    _ = onCollarDom τ M₀ 0 0 z := by unfold onCollarDom; ring

/-! ###############################################################################
    ### ★★★ THE CONCRETE REMAINDER-ORDER CAPSTONE.
    ############################################################################### -/

/-- **★★★ `concreteRemainder_order` — THE CONCRETE REMAINDER τ-ORDER.**  The full-space integral of the
    REAL heat-trace remainder integrand `f = IchartResidual − hessGaussFactor·(chartAmp·F)` obeys the
    explicit `O(1/τ)`
      `|∫_z f| ≤ M₀·(n+1)/(2τ)  +  (Bcomp₂/√τ + (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)))`,
    `Bcomp₂ := L'·(√2)ⁿ·Mqc·n·(1600√2·(√2)⁵ + 2·(64√2+1)·(√2)³)/16`.
    Split at the √ε collar `collar (c√τ)`: the on-collar leg via the pure-Hessian pointwise bound
    `concreteIntegrand_on_collar_le` → `OnCollarMomentOrder.onCollarDom_setIntegral_le` (`M₀·(n+1)/(2τ)`),
    the off-collar leg (annulus ∪ far field) via the banked comparison leg `FarFieldDecay.hcomp_final4`
    (`Bcomp₂/√τ + ∫ farFieldDom`), with the far-field integral made explicit by
    `FarFieldMomentOrder.farFieldDom_integral_le`.  The near-diagonal Hessian `M₀·(n+1)/(2τ)` and the
    far Hessian `Mqc·(n+1)/(2τ)` are the DOMINANT `O(1/τ)`.  ⚠ NOT `a₁ = R/6`. -/
theorem concreteRemainder_order (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀)
    (r L' M₀ M1F M2F Mqc : ℝ) (hL' : 0 ≤ L')
    (hM₀ : 0 ≤ M₀) (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc)
    (hKr : K ⊆ Metric.ball (0 : Point n) r)
    (hgateCollar : ∀ z ∈ collar (c * Real.sqrt τ), z ∈ K ∧ ‖z‖ < r₀)
    (hAmpDiff : ∀ z, |data.Aamp τ z * F s z 0 - chartAmp g gi hC hK a b τ z 0 * F s z 0| ≤ M₀)
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
      ≤ M₀ * ((n : ℝ) + 1) / (2 * τ)
        + (L' * (Real.sqrt 2) ^ n * Mqc * (n : ℝ)
              * (1600 * Real.sqrt 2 * (Real.sqrt 2) ^ 5
                  + 2 * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3)
              / 16 / Real.sqrt τ
            + (M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ))) := by
  have hcollarmeas : MeasurableSet (collar (n := n) (c * Real.sqrt τ)) :=
    QIQTH.SliverTailMatched.collar_measurableSet _
  -- ON-COLLAR LEG.
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
      exact concreteIntegrand_on_collar_le g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ hττ₀
        hgateCollar M₀ hM₀ hAmpDiff z hz
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
  -- OFF-COLLAR LEG (annulus ∪ far field) — the banked comparison leg.
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

end QIQTH.ConcreteRemainderOrder

/-! ###############################################################################
    ## J4-494 LEDGER — the concrete heat-trace remainder τ-order.
    ###############################################################################

  WHAT LANDS.  `concreteRemainder_order` bounds the FULL-space integral of the REAL remainder integrand
  `f = IchartResidual − hessGaussFactor·(chartAmp·F)` by the explicit `O(1/τ)`
    `M₀·(n+1)/(2τ) + (Bcomp₂/√τ + (M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)))`,
  the on-collar Hessian `M₀·(n+1)/(2τ)` and far Hessian `Mqc·(n+1)/(2τ)` DOMINANT.  The new pointwise
  brick `concreteIntegrand_on_collar_le` supplies the on-collar `‖f‖ ≤ onCollarDom τ M₀ 0 0`.

  ⚠ THE GATE CATCH.  The GENERIC proxy `RemainderAssembly.remainderIntegral_order` demands a POINTWISE
  far-field domination on ALL of `(collar r₀)ᶜ`.  For the concrete `f` this is UNSATISFIABLE at any common
  `r₀` (the annulus `{‖z‖>c√τ}∩K` carries the un-expanded witness — the "off-collar sliver remainder").
  So the concrete off-collar is handled at the INTEGRAL level by the banked `hcomp_final4` (gate `(ρ−1)`
  + cubic jet for the annulus, off-`K` Gaussian remainder for the far field), NOT by a false pointwise
  bound.  This is the honest three-region concrete assembly, split at the SAME √ε collar the on-collar
  identity uses.

  DON'T-UNDERCREDIT.  Heavy analysis reused verbatim: `GpowClosure.hon_concrete` (on-collar identity),
  `OnCollarMomentOrder.onCollarDom_setIntegral_le` (near-diagonal moment), `FarFieldDecay.hcomp_final4`
  (off-collar gate+far comparison leg), `FarFieldMomentOrder.farFieldDom_integral_le` (explicit far
  moment), + `integral_add_compl`/`abs_add_le`/`norm_integral_le_integral_norm`.  NEW content: the
  on-collar pure-Hessian pointwise bound + the three-region assembly into one explicit `O(1/τ)` on the
  CONCRETE integrand.

  HONEST DISTANCE.  This promotes the proxy to the CONCRETE integrand (no generic dominated-`f` hypothesis
  remains — only banked, satisfiable gate/amplitude/integrability carries).  ⚠ a₁ = R/6 remains CONDITIONAL;
  the LEADING O(1) coefficient (the term surviving the O(1/τ) remainder) and its `R/6` identification lie
  BEYOND this remainder τ-order.
-/

section AxiomChecks
open QIQTH.ConcreteRemainderOrder
#print axioms concreteIntegrand_on_collar_le
#print axioms concreteRemainder_order
end AxiomChecks
