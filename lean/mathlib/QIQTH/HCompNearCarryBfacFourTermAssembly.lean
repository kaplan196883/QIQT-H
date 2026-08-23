/-
  HCompNearCarryBfacFourTermAssembly — J4-NEXT: the COMBINED assembly of `Bfac`'s four sliver-window
  summand bounds (T1 `hsMixed·A` J4-1072, T2/T3 `grⱼ·∂ⱼA`/`grᵢ·∂ᵢA` and T4/LEFTOVER `∂ⱼ∂ᵢA` J4-1071)
  into ONE bound on the FULL 4-term sum, over a SINGLE SHARED `W''S'`-restricted domain and SINGLE
  SHARED `s`-window `(t-ε,t)` — the "highest-leverage next move" flagged by J4-1072's own report.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBSTRUCTION THIS FILE RESOLVES (found before any Lean here, consulted `gpt-5.6-sol` high,
  GO-confirmed the diagnosis and fix below).  J4-1071's `flat_domain_restricted_sliver_window_bound`
  and `grTerm_domain_restricted_sliver_window_bound`, and J4-1072's `hsMixed_domain_restricted_sliver_
  window_bound`, are each separately-stated theorems of shape `∃ S' (ρ), IsOpen S' ∧ q₀∈S' ∧ (0<ρ) ∧
  [bound]`.  Each is proven by *internally* `obtain`-ing its own `S'`/`ρ` witnesses from the SAME
  deterministic construction (`uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀`,
  then `S'_ball_complement_subset_rncRadialSq_tail`) — mathematically the SAME set/radius every time,
  applied to the same `g gi hC hK hq₀`.  BUT: if the four theorems are invoked as opaque black boxes at
  an assembly call site and their `∃`-witnesses `obtain`-ed separately, Lean does **not** know the four
  resulting local `S'`/`ρ` are equal — `obtain` introduces fresh opaque variables per separately-invoked
  existential statement, and Lean's elaborator does not unfold the theorems' proof terms to discover the
  shared internal construction (Sol confirmed: treating the four theorems as black boxes and trying to
  prove `S'_1 = S'_2 = S'_3 = S'_4` externally is NOT sound/reliable — this would be attempting to rely
  on proof-term-implementation-detail defeq, the wrong API).  So a naive "apply all four, `obtain`, sum"
  assembly does NOT type-check on one shared domain.

  THE FIX (Sol-confirmed, option (b)): do NOT invoke the four sliver-window theorems as black boxes.
  Instead, this file (i) reproduces the SHARED `S'`/`ρ` construction ONCE (Part 2's proof), and
  (ii) proves a NEW fixed-`τ` combined bound (`bfac_four_term_domain_restricted_bound`, Part 1) that is
  GENERIC in an externally-supplied `U`/`ρ` (mirroring `heatHessMult_amp_subset_tail_le`'s/`linMult_amp_
  subset_tail_le`'s already-generic-in-`A` design, J4-1023) — reusing the SAME public per-term building
  blocks each sliver-window file used internally (`hsMixed_gaussDdim_mul_amp_lipschitz_bound`,
  `hsMixed_amp_subset_tail_le`, `grTerm_gaussian_mul_amp_lipschitz_bound`, `linMult_amp_subset_tail_le`,
  `heatHessMult`/`linMult`-integrability lemmas, J4-1017–1023) — so the SAME `U`,`ρ` genuinely applies to
  all four summands by construction, not by an unproven external equality.  Part 2 then constructs
  `S'`/`ρ` ONCE and composes Part 1 (per fixed `τ∈(0,ε]`) with the outer `s`-sliver-window integration
  (`pointwise_bound_sliver_window_inv_sqrt`, J4-1065) and the tail-domination folding lemmas
  (`heatHessMult_tail_le_of_sliver`, `grTerm_tail_le_of_sliver`, J4-1071/1072) — REUSED VERBATIM, since
  they are already generic in `ρ,ε,τ`, not tied to any specific `S'` construction.

  ## WHAT LANDS.
    • `bfac_four_term_domain_restricted_bound` — ★★★★ Part 1: for ANY measurable `U` with `Uᶜ ⊆
      {ρ²≤rncRadialSq}`, the FIXED-`τ` bound on `Bfac`'s four-summand sum (`hsMixed`-part + two
      `grTerm`-parts + a flat part) restricted to `U`, `≤` (T1's per-τ bound) + (T2's) + (T3's) + `M`.
    • `bfac_four_term_domain_restricted_sliver_window_bound` — ★★★★★ THE CAPSTONE: composes Part 1
      (at `U := W''S'`, the SAME `S'`,`ρ` for all four terms, constructed ONCE) with the outer
      `s`-sliver-window integration, giving `∃ S' ρ, IsOpen S' ∧ q₀∈S' ∧ 0<ρ ∧ |∫ s in (t-ε)..t, ∫_{W''S'}
      G_{t-s}·(hsMixed·Amp + grTerm(Q2)·Amp2 + grTerm(Q3)·Amp3 + AmpFlat)| ≤ 2·C1·√ε + C2(ε)·ε = O(√ε)`
      — the FULL `Bfac`-shape four-term sum, ONE bound, ONE shared domain, ONE shared window — closing
      the "sum the four bounds" step flagged by J4-1071/1072's reports, WITH THE DOMAIN GENUINELY SHARED
      (not merely assumed), resolving J4-1066's earlier flagged domain-split obstruction for THIS
      (domain-restricted, not full-space) generation of bounds.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  The combined
  bound here is on the ABSTRACT four-term sum `hsMixed·Amp + grTerm(Q2)·Amp2 + grTerm(Q3)·Amp3 + AmpFlat`
  — NOT literally `Bfac` itself, which additionally carries an outer `Levi(s,z)` multiplicative factor
  (`Bfac(z) := Levi(s,z)·(T1+T2+T3+T4)`, `HCompNearCarryKPrimeBaseFieldCoV` BRICK 1) that is NOT composed
  in anywhere in this file (NEITHER folded in, nor claimed to be already present — J4-1028's `Levi`
  regularity work is a SEPARATE, still-untouched composition step).  Nor does it verify the literal
  `∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA` globalization or `Bfac(V w)/|det(fderiv W (V w))|` composed-regularity (J4-1069's
  frontier item 1, UNCHANGED — `Amp`/`Amp2`/`Amp3`/`AmpFlat` remain four INDEPENDENT abstract functions,
  not the literal chart-composed amplitude and its derivatives, which would need to be tied together and
  matched to `Bfac`'s actual four terms' specific relationships).  Does NOT discharge `hxmem` (the shared
  upstream architectural wall, UNCHANGED).  Does NOT discharge `hfac`'s literal carry over `S'` (residuals
  r1/r2 of `HCompNearCarryKPrimeBaseFieldCoV`, UNCHANGED — this file's `S'` comes from `uniformInverse
  Chart_baseSlot_M1M4_image_open_generalK`, the SAME construction J4-1023/1071/1072 use, but reconciling
  it with the actual IFT-selected `S'` of `HCompNearCarryKPrimeBaseFieldCoV` remains open, per those
  files' own firewalls).  Does NOT discharge `nb`, `hCConv`, or any part of `hcomp`.  The far-carry `fb`
  remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  Non-vacuity: every theorem's
  hypotheses are satisfiable by concrete test data (e.g. `Amp := 0`/`Amp2 := 0`/`Amp3 := 0`/`AmpFlat := 0`/
  `L := 0`/`L2 := 0`/`L3 := 0`/`M := 0`/`Q := 0`/`Q2 := 0`/`Q3 := 0`/`PI := 0`/`PJ := 0`), and no theorem's
  hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1DomainRestrictedBound
import QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound
import QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
import QIQTH.HCompNearCarryTerm1LipschitzCancellation
import QIQTH.HCompNearCarryTerm1SliverWindowBound
import QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted
import QIQTH.HCompNearCarryTerm1DomainRestrictedSliverWindowBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open QIQTH.HCompNearCarryTerm1AmpWeightedTail QIQTH.HCompNearCarryTerm1BallGeometry
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.BaseSlotM1M4ImageOpen
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound QIQTH.HCompNearCarryTerm2Term3DomainRestrictedBound
open QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
open QIQTH.HCompNearCarryTerm1SliverWindowBound
open QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted
open QIQTH.HCompNearCarryTerm1DomainRestrictedSliverWindowBound
open scoped Topology BigOperators Interval

namespace QIQTH.HCompNearCarryBfacFourTermAssembly

set_option maxHeartbeats 3200000

variable {n : ℕ}

/-! ###############################################################################
    ### PART 1 — the fixed-`τ` combined bound, generic in an externally-supplied `U`/`ρ`.
    ############################################################################### -/

/-- **★★★★ `bfac_four_term_domain_restricted_bound`.**  For ANY measurable `U` whose complement lies in
    the `ρ`-tail region (`Uᶜ ⊆ {ρ²≤rncRadialSq}`), the fixed-`τ` `W''S'`-restricted bound on `Bfac`'s
    FOUR summands' sum — `hsMixed`-part (T1, jet fields `PI PJ Q`, amp `Amp`/`L`), two `grTerm`-parts
    (T2/T3, jet fields `Q2`/`Q3`, amps `Amp2,L2`/`Amp3,L3`), and a flat part (T4/LEFTOVER, amp `AmpFlat`
    merely bounded by `M`) — is the SUM of each summand's own domain-restricted bound.  Reuses the SAME
    public building blocks `hsMixed_gaussDdim_mul_amp_lipschitz_bound`/`hsMixed_amp_subset_tail_le`
    (J4-1017/1023), `grTerm_gaussian_mul_amp_lipschitz_bound`/`linMult_amp_subset_tail_le` (J4-1019/1023,
    applied to `Q2`,`Q3` independently), and direct Gaussian-mass monotonicity for the flat part (no `ρ`
    needed there at all) — with `U`,`ρ` SHARED across all four by construction (parameters, not
    internally re-derived), resolving the domain-sharing question for a combined assembly. -/
theorem bfac_four_term_domain_restricted_bound
    (τ : ℝ) (hτ : 0 < τ) (ρ : ℝ) (hρ : 0 < ρ)
    (PI PJ Q : Point n) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    (Q2 : Point n) (Amp2 : Point n → ℝ) (hAmp2 : AEStronglyMeasurable Amp2 volume)
    (L2 : ℝ) (hL2 : 0 ≤ L2) (hlip2 : ∀ v : Point n, |Amp2 v - Amp2 0| ≤ L2 * ‖v‖)
    (Q3 : Point n) (Amp3 : Point n → ℝ) (hAmp3 : AEStronglyMeasurable Amp3 volume)
    (L3 : ℝ) (hL3 : 0 ≤ L3) (hlip3 : ∀ v : Point n, |Amp3 v - Amp3 0| ≤ L3 * ‖v‖)
    (AmpFlat : Point n → ℝ) (hAmpFlat : AEStronglyMeasurable AmpFlat volume)
    (M : ℝ) (hM : 0 ≤ M) (hboundFlat : ∀ v : Point n, |AmpFlat v| ≤ M)
    {U : Set (Point n)} (hUmeas : MeasurableSet U)
    (hUcsub : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v}) :
    |∫ v : Point n in U, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v
           + (-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v
           + (-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v
           + AmpFlat v)|
      ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ + (n : ℝ) ^ 2 * L * ‖Q‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|Amp 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + ((n : ℝ) ^ 2 * L2 * ‖Q2‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / (2 * τ))
                * (|Amp2 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + ((n : ℝ) ^ 2 * L3 * ‖Q3‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / (2 * τ))
                * (|Amp3 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + M := by
  have hUcmeas : MeasurableSet Uᶜ := hUmeas.compl
  set f1 : Point n → ℝ := fun v => gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v) with hf1def
  set f2 : Point n → ℝ := fun v => gaussDdim τ v * ((-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v) with hf2def
  set f3 : Point n → ℝ := fun v => gaussDdim τ v * ((-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v) with hf3def
  set f4 : Point n → ℝ := fun v => gaussDdim τ v * AmpFlat v with hf4def
  -- pointwise identities driving integrability.
  have hpt1 : ∀ v : Point n, f1 v = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
    intro v; rw [hf1def]
    have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
        * gaussDdim τ v
      = heatHessMult τ PI PJ v - linMult τ Q v := by
      simp only [heatHessMult, linMult]; ring
    calc gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by ring
      _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
      _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
  have hInt1 : Integrable f1 volume := by
    have h1 := heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip
    have h2 := linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
    exact (h1.sub h2).congr (ae_of_all _ (fun v => (hpt1 v).symm))
  have hpt2 : ∀ v : Point n, f2 v = -(linMult τ Q2 v * Amp2 v) := fun v =>
    grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp τ Q2 v (Amp2 v)
  have hInt2 : Integrable f2 volume :=
    (linMult_mul_lipschitzAmp_integrable τ hτ Q2 Amp2 hAmp2 L2 hlip2).neg.congr
      (ae_of_all _ (fun v => (hpt2 v).symm))
  have hpt3 : ∀ v : Point n, f3 v = -(linMult τ Q3 v * Amp3 v) := fun v =>
    grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp τ Q3 v (Amp3 v)
  have hInt3 : Integrable f3 volume :=
    (linMult_mul_lipschitzAmp_integrable τ hτ Q3 Amp3 hAmp3 L3 hlip3).neg.congr
      (ae_of_all _ (fun v => (hpt3 v).symm))
  have hGnn : ∀ v : Point n, 0 ≤ gaussDdim τ v := fun v => gaussDdim_nonneg' τ v
  have hGint : Integrable (fun v : Point n => gaussDdim τ v) volume := gaussDdim_integrable' τ hτ
  have hD_int : Integrable (fun v : Point n => M * gaussDdim τ v) volume := hGint.const_mul _
  have hptbndFlat : ∀ v : Point n, |f4 v| ≤ M * gaussDdim τ v := fun v => by
    rw [hf4def, abs_mul, abs_of_nonneg (hGnn v)]
    calc gaussDdim τ v * |AmpFlat v| ≤ gaussDdim τ v * M :=
          mul_le_mul_of_nonneg_left (hboundFlat v) (hGnn v)
      _ = M * gaussDdim τ v := by ring
  have hmeasFlat : AEStronglyMeasurable f4 volume := by
    rw [hf4def]; exact hGint.aestronglyMeasurable.mul hAmpFlat
  have hInt4 : Integrable f4 volume :=
    hD_int.mono' hmeasFlat (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs]; exact hptbndFlat v))
  -- split the combined `U`-integral into four pieces.
  have g1 : IntegrableOn f1 U volume := hInt1.integrableOn
  have g2 : IntegrableOn f2 U volume := hInt2.integrableOn
  have g3 : IntegrableOn f3 U volume := hInt3.integrableOn
  have g4 : IntegrableOn f4 U volume := hInt4.integrableOn
  have h12 : IntegrableOn (fun v => f1 v + f2 v) U volume := g1.add g2
  have h123 : IntegrableOn (fun v => f1 v + f2 v + f3 v) U volume := h12.add g3
  have hsplitU : ∫ v : Point n in U, (f1 v + f2 v + f3 v + f4 v)
      = (∫ v in U, f1 v) + (∫ v in U, f2 v) + (∫ v in U, f3 v) + (∫ v in U, f4 v) := by
    rw [integral_add h123 g4, integral_add h12 g3, integral_add g1 g2]
  have heq_goal : (fun v : Point n => gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v
             + (-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v
             + (-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v
             + AmpFlat v))
      = fun v => f1 v + f2 v + f3 v + f4 v := by
    funext v; rw [hf1def, hf2def, hf3def, hf4def]; ring
  rw [heq_goal, hsplitU]
  -- bound `∫_U f1` — reproduces `hsMixed_gaussDdim_mul_amp_domain_restricted_bound`'s internals.
  have hsplit1 := integral_add_compl hUmeas hInt1
  have hGfull1 : |∫ v : Point n, f1 v|
      ≤ L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ + (n : ℝ) ^ 2 * L * ‖Q‖ := by
    simpa only [hf1def] using hsMixed_gaussDdim_mul_amp_lipschitz_bound τ hτ PI PJ Q Amp hAmp L hL hlip
  have hGtail1_0 : |∫ v : Point n in Uᶜ, f1 v|
      ≤ |∫ v : Point n in Uᶜ, heatHessMult τ PI PJ v * Amp v|
          + |∫ v : Point n in Uᶜ, linMult τ Q v * Amp v| := by
    simpa only [hf1def] using
      hsMixed_amp_subset_tail_le τ hτ ρ PI PJ Q Amp hAmp L hL hlip hUcmeas hUcsub
  have hHHtail1 := heatHessMult_amp_subset_tail_le τ hτ ρ PI PJ Amp hAmp L hL hlip hUcmeas hUcsub
  have hLtail1 := linMult_amp_subset_tail_le τ hτ ρ Q Amp hAmp L hL hlip hUcmeas hUcsub
  have hGtail1 := hGtail1_0.trans (add_le_add hHHtail1 hLtail1)
  have hUeq1 : ∫ v : Point n in U, f1 v
      = (∫ v : Point n, f1 v) - ∫ v : Point n in Uᶜ, f1 v := by linarith [hsplit1]
  have habs1 : |∫ v : Point n in U, f1 v|
      ≤ |∫ v : Point n, f1 v| + |∫ v : Point n in Uᶜ, f1 v| := by
    rw [hUeq1, sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
  have hbnd1 : |∫ v : Point n in U, f1 v| ≤
      (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ + (n : ℝ) ^ 2 * L * ‖Q‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|Amp 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
    have := habs1.trans (add_le_add hGfull1 hGtail1)
    linarith [this]
  -- bound `∫_U f2` — reproduces `grTerm_gaussDdim_mul_amp_domain_restricted_bound`'s internals (Q2).
  have hsplit2 := integral_add_compl hUmeas hInt2
  have hGfull2 : |∫ v : Point n, f2 v| ≤ (n : ℝ) ^ 2 * L2 * ‖Q2‖ := by
    simpa only [hf2def] using
      grTerm_gaussian_mul_amp_lipschitz_bound τ hτ Q2 L2 hL2 Amp2 hAmp2 hlip2
  have hLtail2 := linMult_amp_subset_tail_le τ hτ ρ Q2 Amp2 hAmp2 L2 hL2 hlip2 hUcmeas hUcsub
  have hUc_eq2 : ∫ v : Point n in Uᶜ, f2 v = -(∫ v : Point n in Uᶜ, linMult τ Q2 v * Amp2 v) := by
    rw [← integral_neg]; exact setIntegral_congr_fun hUcmeas (fun v _ => hpt2 v)
  have hGtail2 : |∫ v : Point n in Uᶜ, f2 v|
      ≤ Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / (2 * τ))
          * (|Amp2 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
    rw [hUc_eq2, abs_neg]; exact hLtail2
  have hUeq2 : ∫ v : Point n in U, f2 v = (∫ v : Point n, f2 v) - ∫ v : Point n in Uᶜ, f2 v := by
    linarith [hsplit2]
  have habs2 : |∫ v : Point n in U, f2 v|
      ≤ |∫ v : Point n, f2 v| + |∫ v : Point n in Uᶜ, f2 v| := by
    rw [hUeq2, sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
  have hbnd2 : |∫ v : Point n in U, f2 v| ≤
      (n : ℝ) ^ 2 * L2 * ‖Q2‖
        + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / (2 * τ))
            * (|Amp2 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) :=
    habs2.trans (add_le_add hGfull2 hGtail2)
  -- bound `∫_U f3` — reproduces the same, for `Q3`.
  have hsplit3 := integral_add_compl hUmeas hInt3
  have hGfull3 : |∫ v : Point n, f3 v| ≤ (n : ℝ) ^ 2 * L3 * ‖Q3‖ := by
    simpa only [hf3def] using
      grTerm_gaussian_mul_amp_lipschitz_bound τ hτ Q3 L3 hL3 Amp3 hAmp3 hlip3
  have hLtail3 := linMult_amp_subset_tail_le τ hτ ρ Q3 Amp3 hAmp3 L3 hL3 hlip3 hUcmeas hUcsub
  have hUc_eq3 : ∫ v : Point n in Uᶜ, f3 v = -(∫ v : Point n in Uᶜ, linMult τ Q3 v * Amp3 v) := by
    rw [← integral_neg]; exact setIntegral_congr_fun hUcmeas (fun v _ => hpt3 v)
  have hGtail3 : |∫ v : Point n in Uᶜ, f3 v|
      ≤ Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / (2 * τ))
          * (|Amp3 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
    rw [hUc_eq3, abs_neg]; exact hLtail3
  have hUeq3 : ∫ v : Point n in U, f3 v = (∫ v : Point n, f3 v) - ∫ v : Point n in Uᶜ, f3 v := by
    linarith [hsplit3]
  have habs3 : |∫ v : Point n in U, f3 v|
      ≤ |∫ v : Point n, f3 v| + |∫ v : Point n in Uᶜ, f3 v| := by
    rw [hUeq3, sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
  have hbnd3 : |∫ v : Point n in U, f3 v| ≤
      (n : ℝ) ^ 2 * L3 * ‖Q3‖
        + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / (2 * τ))
            * (|Amp3 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) :=
    habs3.trans (add_le_add hGfull3 hGtail3)
  -- bound `∫_U f4` — direct monotonicity, no `ρ` needed (mirrors `flat_gaussDdim_mul_amp_domain_
  -- restricted_bound`'s internals).
  have hstep1_4 : |∫ v : Point n in U, f4 v| ≤ ∫ v : Point n in U, |f4 v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict U)) f4
    simpa only [Real.norm_eq_abs] using h
  have hstep2_4 : ∫ v : Point n in U, |f4 v| ≤ ∫ v : Point n in U, M * gaussDdim τ v :=
    setIntegral_mono_on (g4.abs) (hD_int.integrableOn) hUmeas (fun v _ => hptbndFlat v)
  have hstep3_4 : ∫ v : Point n in U, M * gaussDdim τ v ≤ ∫ v : Point n, M * gaussDdim τ v :=
    setIntegral_le_integral hD_int (Filter.Eventually.of_forall (fun v => mul_nonneg hM (hGnn v)))
  have hbnd4 : |∫ v : Point n in U, f4 v| ≤ M := by
    refine hstep1_4.trans (hstep2_4.trans (hstep3_4.trans ?_))
    rw [integral_const_mul, gaussDdim_mass_one τ hτ, mul_one]
  -- final four-way triangle inequality.
  have hstepA : |(∫ v in U, f1 v) + (∫ v in U, f2 v)|
      ≤ |∫ v in U, f1 v| + |∫ v in U, f2 v| := abs_add_le _ _
  have hstepB : |(∫ v in U, f1 v) + (∫ v in U, f2 v) + (∫ v in U, f3 v)|
      ≤ |(∫ v in U, f1 v) + (∫ v in U, f2 v)| + |∫ v in U, f3 v| := abs_add_le _ _
  have hstepC : |(∫ v in U, f1 v) + (∫ v in U, f2 v) + (∫ v in U, f3 v) + (∫ v in U, f4 v)|
      ≤ |(∫ v in U, f1 v) + (∫ v in U, f2 v) + (∫ v in U, f3 v)| + |∫ v in U, f4 v| := abs_add_le _ _
  linarith [hstepA, hstepB, hstepC, hbnd1, hbnd2, hbnd3, hbnd4]

/-! ###############################################################################
    ### PART 2 — the sliver-window capstone: shared `S'`/`ρ` construction ONCE, composed with the
    ### `ε`-folding tail-domination lemmas (J4-1071/1072, reused verbatim) and the outer `s`-window.
    ############################################################################### -/

/-- **★★★★★ `bfac_four_term_domain_restricted_sliver_window_bound` — THE COMBINED CAPSTONE.**  For the
    base-slot CoV map `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, `Bfac`'s FOUR
    summands' sum (T1 `hsMixed·Amp`, T2/T3 `grTerm(Q2)·Amp2`/`grTerm(Q3)·Amp3`, T4/LEFTOVER `AmpFlat`),
    RESTRICTED to `nb`'s ACTUAL post-CoV domain `W''S'` AND integrated over the ACTUAL shrinking
    `s`-sliver `(t-ε,t)`, is bounded by `2·C1·√ε + C2(ε)·ε = O(√ε)` — with `S'`,`ρ` SHARED across ALL
    FOUR summands by construction (built once via `uniformInverseChart_baseSlot_M1M4_image_open_
    generalK`/`S'_ball_complement_subset_rncRadialSq_tail`, then fed into Part 1 at each `τ` in the
    sliver), resolving the domain-sharing obstruction flagged by J4-1071/1072's reports and by the
    earlier `HCompNearCarrySliverWindowAssembly` (J4-1066) attempt (whose obstruction was a DIFFERENT,
    ball-vs-`ℝⁿ` full-space domain split — genuinely absent here since every summand's bound is
    `W''S'`-restricted from the start).  MEETS (does not beat) `hcomp`'s required `O(√ε)` rate, driven by
    T1's `1/√τ` singularity (T2/T3/T4 are flat). -/
theorem bfac_four_term_domain_restricted_sliver_window_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (PI PJ Q : Point n) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    (Q2 : Point n) (Amp2 : Point n → ℝ) (hAmp2 : AEStronglyMeasurable Amp2 volume)
    (L2 : ℝ) (hL2 : 0 ≤ L2) (hlip2 : ∀ v : Point n, |Amp2 v - Amp2 0| ≤ L2 * ‖v‖)
    (Q3 : Point n) (Amp3 : Point n → ℝ) (hAmp3 : AEStronglyMeasurable Amp3 volume)
    (L3 : ℝ) (hL3 : 0 ≤ L3) (hlip3 : ∀ v : Point n, |Amp3 v - Amp3 0| ≤ L3 * ‖v‖)
    (AmpFlat : Point n → ℝ) (hAmpFlat : AEStronglyMeasurable AmpFlat volume)
    (M : ℝ) (hM : 0 ≤ M) (hboundFlat : ∀ v : Point n, |AmpFlat v| ≤ M) :
    ∃ (S' : Set (Point n)) (ρ : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      |∫ s in (t - ε)..t, ∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim (t - s) v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v
               + (-(∑ k, v k * Q2 k) / (2 * (t - s))) * Amp2 v
               + (-(∑ k, v k * Q3 k) / (2 * (t - s))) * Amp3 v
               + AmpFlat v)|
        ≤ 2 * (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
            + (((n : ℝ) ^ 2 * L * ‖Q‖
                  + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                      * (|Amp 0| * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
                          + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4)
                                  * (ε * Real.sqrt ε)
                                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε)))
                  + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
                      * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + ((n : ℝ) ^ 2 * L2 * ‖Q2‖
                    + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / 2)
                        * (|Amp2 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                            + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + ((n : ℝ) ^ 2 * L3 * ‖Q3‖
                    + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / 2)
                        * (|Amp3 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                            + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + M) * ε := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := W '' S' with hUdef
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : W q₀ = 0 := uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have h0U : (0 : Point n) ∈ U := ⟨q₀, hq0S', hWq0⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := S'_ball_complement_subset_rncRadialSq_tail hWSopen h0U
  have hρsub' : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v} := by
    intro v hv; have := hρsub hv; simpa using this
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  set C1 : ℝ := L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) with hC1def
  set HHTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
      * (|Amp 0| * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
          + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε))) with hHHTaildef
  set LMTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
      * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTaildef
  set LMTail2 : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / 2)
      * (|Amp2 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTail2def
  set LMTail3 : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / 2)
      * (|Amp3 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTail3def
  set C2 : ℝ := ((n : ℝ) ^ 2 * L * ‖Q‖ + HHTail + LMTail)
      + ((n : ℝ) ^ 2 * L2 * ‖Q2‖ + LMTail2) + ((n : ℝ) ^ 2 * L3 * ‖Q3‖ + LMTail3) + M with hC2def
  have hC2nn : 0 ≤ C2 := by
    rw [hC2def, hHHTaildef, hLMTaildef, hLMTail2def, hLMTail3def]; positivity
  refine ⟨S', ρ, hS'open, hq0S', hρpos, ?_⟩
  apply pointwise_bound_sliver_window_inv_sqrt t ε C1 C2 hε
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (s - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (s - s))) * Amp v
               + (-(∑ k, v k * Q2 k) / (2 * (s - s))) * Amp2 v
               + (-(∑ k, v k * Q3 k) / (2 * (s - s))) * Amp3 v
               + AmpFlat v) = 0 := by
      intro v
      -- NOTE: this branch is only reached in the `s = t` boundary case; the flat `AmpFlat v` term does
      -- NOT literally vanish at `τ = 0` in general, so instead of a pointwise-zero identity we bound
      -- the whole `s = t` case directly via `hz0'` below (the pointwise value need not be `0`, but the
      -- WHOLE degenerate `τ = 0` integrand is handled by `gaussDdim 0 v = 0` killing the FIRST three
      -- terms while the flat term `gaussDdim 0 v * AmpFlat v` also vanishes, since it too is multiplied
      -- by the same outer `gaussDdim (s-s) v = gaussDdim 0 v = 0` factor).
      rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]; simp [hn]
      rw [hG0]; ring
    simp only [hz0, MeasureTheory.integral_zero]
    have hnn : (0 : ℝ) ≤ C1 / Real.sqrt (s - s) + C2 := by rw [sub_self]; positivity
    simpa using hnn
  · set τ : ℝ := t - s with hτdef
    have hτ : 0 < τ := by rw [hτdef]; linarith
    have hτε : τ ≤ ε := by rw [hτdef]; linarith [hs.1]
    have hbase := bfac_four_term_domain_restricted_bound τ hτ ρ hρpos
      PI PJ Q Amp hAmp L hL hlip Q2 Amp2 hAmp2 L2 hL2 hlip2 Q3 Amp3 hAmp3 L3 hL3 hlip3
      AmpFlat hAmpFlat M hM hboundFlat hUmeas hρsub'
    have hHHfold := heatHessMult_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε PI PJ (|Amp 0|) L
      (abs_nonneg _) hL
    have hLfold := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q (|Amp 0|) L (abs_nonneg _) hL
    have hLfold2 := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q2 (|Amp2 0|) L2 (abs_nonneg _) hL2
    have hLfold3 := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q3 (|Amp3 0|) L3 (abs_nonneg _) hL3
    have hfinal : |∫ v : Point n in U, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v
             + (-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v
             + (-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v
             + AmpFlat v)|
        ≤ C1 / Real.sqrt τ + C2 := by
      refine hbase.trans ?_
      rw [hC1def, hC2def, hHHTaildef, hLMTaildef, hLMTail2def, hLMTail3def]
      linarith [hHHfold, hLfold, hLfold2, hLfold3]
    rw [hτdef] at hfinal
    exact hfinal

end QIQTH.HCompNearCarryBfacFourTermAssembly

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryBfacFourTermAssembly
#print axioms bfac_four_term_domain_restricted_bound
#print axioms bfac_four_term_domain_restricted_sliver_window_bound
end AxiomChecks
