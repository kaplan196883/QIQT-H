/-
  HCompNearCarryBfacLeviFoldedSliverWindowBound — J4-NEXT: folds the outer `Levi(s,z)` multiplicative
  factor INTO `HCompNearCarryBfacFourTermAssembly`'s (J4-1073) bare four-term-sum sliver-window bound,
  using the WINDOW-UNIFORM `Levi`-bounded/Lipschitz data of `LeviWindowUniformAmpLipschitz` (J4-1075).
  `Bfac(z) := Levi(s,z)·(T1+T2+T3+T4)`, the LITERAL shape of `HCompNearCarryKPrimeBaseFieldCoV`'s
  (J4-1010) BRICK 1 — this file is the FIRST time that literal outer factor is composed into a
  sliver-window `O(√ε)` bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBSTRUCTION THIS FILE RESOLVES (found before any Lean here; consulted `gpt-5.6-sol` high,
  GO-confirmed 2026-08-23).  J4-1074 found that multiplying J4-1073's SIGNED bound on `T1+T2+T3+T4` by
  a pointwise sup `M_Levi` on `|Levi|` is mathematically INVALID (`|∫f|≤B` does not give `|∫Levi·f|≤M·B`
  from a mere pointwise `|Levi|≤M`, absent an L¹/pointwise-domination argument).  J4-1075 scoped the fix
  — fold `Levi(s,z)` INTO each amplitude BEFORE bounding (mirroring `LeviAmpProductGlobalRegularity`'s/
  J4-1028's own pattern for `T1`) — and built the WINDOW-UNIFORM `(M_F,L_F)` bundle for `Levi` itself
  plus a product wrapper, but explicitly did NOT thread it through J4-1073's Part 2 sliver-window
  integration (its own firewall, item (i)).  THIS is that threading.

  THE FIX (Sol-confirmed GO, with two refinements Sol flagged and both adopted below):
    (1) A monotonicity-substitution corollary of J4-1073's Part 1 (`bfac_four_term_domain_restricted_
        bound`), replacing the three `|Amp 0|`/`|Amp2 0|`/`|Amp3 0|` occurrences in its RHS by externally
        supplied UPPER BOUNDS `MA0`/`MA0_2`/`MA0_3` — sound because every coefficient multiplying those
        three terms in the RHS is a manifestly nonnegative product (`Real.exp(...)`, `(√2)^n`, `n^k`,
        norms, `Real.sqrt τ` powers, all ≥ 0 given `τ > 0`), so `gcongr` discharges the substitution.
    (2) Per fixed `s` in the sliver window, DIRECTLY build the product `Levi(s,·)·Amp(·)`'s global
        bounded+Lipschitz data via `LeviAmpProductGlobalRegularity.bounded_lipschitz_mul_global` fed by
        a SINGLE upfront call to `LeviWindowUniformAmpLipschitz.leviBase_window_uniform_bounded_lipschitz`
        (giving window-uniform `(M_F,L_F)`), rather than calling the higher-level `leviAmp_product_
        window_uniform_lipschitz` wrapper per term.  Sol's flagged correction: since `Amp`/`Amp2`/`Amp3`
        must be GLOBALLY (not merely at-0) Lipschitz to fold with `Levi` and still recover Part 1's
        Lipschitz-AT-0 shape (specializing the product's global Lipschitz bound at `w := 0` gives exactly
        Part 1's `hlip` shape), this file's `Amp`/`Amp2`/`Amp3` hypotheses are STRENGTHENED to global
        bounded+Lipschitz (`hbdA/hlipA` etc., matching `bounded_lipschitz_mul_global`'s own hypotheses)
        — a strictly smaller class of amplitudes than J4-1073's Part 1 (which only needed Lipschitz-AT-0),
        but the necessary and sufficient strengthening to legally fold `Levi` in.  `AmpFlat` needs NO
        Lipschitz at all (Part 1's flat hypothesis `hboundFlat` is bound-only): its Levi-folded bound is
        derived DIRECTLY (`|Levi(s,v)·AmpFlat v| = |Levi(s,v)|·|AmpFlat v| ≤ M_F·MF` via `abs_mul` +
        `hFb`/`hboundFlat`), per Sol's explicit (d) guidance — no artificial Lipschitz hypothesis is
        manufactured for `AmpFlat`.  Sol's (c): calling the base window-uniform lemma multiple times with
        identical arguments does NOT give Lean-provably-equal opaque witnesses across separate calls —
        but this file never needs that: `M_F,L_F` are obtained from a SINGLE call and threaded to all
        four per-term product constructions, so no cross-call witness-equality is ever required.  The
        capstone's conclusion EXISTENTIALLY quantifies `(S',ρ,M_F,L_F)` (mirroring how Part 2 itself
        already existentially quantifies `(S',ρ)` rather than inlining their closed forms) — an honest,
        non-brittle way to expose the genuinely-constructed window-uniform Levi data without hard-coding
        `leviBase_window_uniform_bounded_lipschitz`'s internal closed-form witnesses into this file's
        statement.  Per-`s` a.e.-strong-measurability of each Levi-folded product is derived from its OWN
        global Lipschitz bound via the standard `LipschitzWith.of_dist_le_mul` ⟹ `Continuous` ⟹
        `AEStronglyMeasurable` reduction (the same pattern already banked as `SlotInstantiationIII.
        aesm_of_lipBound`; reproduced locally here as a private helper to avoid importing that large
        unrelated file for one six-line lemma).  Finally, `Levi(s,v)·(T1+T2+T3+T4)` is redistributed into
        `T1coeff·(Levi·Amp) + T2coeff·(Levi·Amp2) + T3coeff·(Levi·Amp3) + (Levi·AmpFlat)` by a pure `ring`
        identity (Sol-confirmed (b)) — exactly the shape Part 1's four independent amplitude slots expect.

  ## WHAT LANDS.
    • `bfac_four_term_domain_restricted_bound_of_amp0_bound` — Part 1′: the monotonicity-substitution
      corollary of J4-1073's Part 1, RHS depending only on externally-supplied upper bounds `MA0`/
      `MA0_2`/`MA0_3` on `|Amp 0|`/`|Amp2 0|`/`|Amp3 0|`, not the literal values — ready to be supplied
      `s`-independent window-uniform constants.
    • `bfac_four_term_levi_domain_restricted_sliver_window_bound` — ★★★★★ THE CAPSTONE: for the base-slot
      CoV map and the Levi window-uniform carries, `∃ S' ρ M_F L_F, IsOpen S' ∧ q₀∈S' ∧ 0<ρ ∧ 0≤M_F ∧
      0≤L_F ∧ |∫ s in (t-ε)..t, ∫_{W''S'} gaussDdim(t-s) v · (Levi(s,v)·(T1+T2+T3+T4))| ≤ O(√ε)` — the
      FULL literal `Bfac`-shape (Levi-folded four-term sum), for the FIRST time in this sub-campaign.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  J4-1075's own firewall item (i) (threading `(M',L')` through the outer sliver-window integration) — but
  everything else those two files already flagged as open remains OPEN, UNCHANGED:
    • Does NOT verify the literal `∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA` globalization or `Bfac(V w)/|det(fderiv W (V w))|`
      composed-regularity (J4-1069's frontier item 1) — `Amp`/`Amp2`/`Amp3`/`AmpFlat` remain FOUR
      INDEPENDENT abstract functions (now with a stronger global-Lipschitz hypothesis for the first
      three), not literally the chart-composed amplitude and its derivatives.
    • Does NOT discharge `hxmem` (the shared upstream architectural wall, UNCHANGED).
    • Does NOT discharge `hfac`'s literal carry over `S'` (reconciling THIS file's `S'` — the SAME
      `uniformInverseChart_baseSlot_M1M4_image_open_generalK` construction J4-1023/1071/1072/1073 use —
      with the actual IFT-selected `S'` of `HCompNearCarryKPrimeBaseFieldCoV` remains open).
    • Does NOT discharge `nb`, `hCConv`, or any part of `hcomp`.  The far-carry `fb` remains SEPARATELY
      open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
      UNCHANGED.  NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  Non-vacuity: every theorem's hypotheses are satisfiable by
  concrete test data (e.g. `E := 0`, `Amp := 0`/`Amp2 := 0`/`Amp3 := 0`/`AmpFlat := 0`, all bound/Lipschitz
  constants `:= 0`, `Q := 0`/`Q2 := 0`/`Q3 := 0`/`PI := 0`/`PJ := 0`, `C_L := 0`/`Kc := 0`/`L_E := 0`), and
  no theorem's hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryBfacFourTermAssembly
import QIQTH.LeviWindowUniformAmpLipschitz

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
open QIQTH.HCompNearCarryBfacFourTermAssembly
open QIQTH.TrueHeatKernel QIQTH.HeatDuhamel
open QIQTH.LeviAmpProductGlobalRegularity QIQTH.HZMassCappedWindowClosed
open QIQTH.LeviWindowUniformAmpLipschitz
open scoped Topology BigOperators Interval

namespace QIQTH.HCompNearCarryBfacLeviFoldedSliverWindowBound

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### helper — a.e.-strong measurability from a global Lipschitz increment bound (local
    ### reproduction of `SlotInstantiationIII.aesm_of_lipBound`, to avoid importing that unrelated file
    ### for a single six-line lemma).
    ############################################################################### -/

private theorem aesm_of_lipBound (q : Point n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z w : Point n, |q z - q w| ≤ L * dist z w) :
    AEStronglyMeasurable q volume := by
  have hlw : LipschitzWith L.toNNReal q := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Real.dist_eq, Real.coe_toNNReal L hL]
    exact hlip z w
  exact hlw.continuous.aestronglyMeasurable

/-! ###############################################################################
    ### PART 1′ — the monotonicity-substitution corollary: RHS depends only on UPPER BOUNDS on
    ### `|Amp 0|`/`|Amp2 0|`/`|Amp3 0|`, not their literal values.
    ############################################################################### -/

/-- **★★★★ `bfac_four_term_domain_restricted_bound_of_amp0_bound` — Part 1′.**  Same hypotheses as
    `bfac_four_term_domain_restricted_bound`, PLUS externally-supplied nonnegative upper bounds `MA0 ≥
    |Amp 0|`, `MA0_2 ≥ |Amp2 0|`, `MA0_3 ≥ |Amp3 0|`; the conclusion is the SAME bound with those three
    literal `|Amp 0|`-type terms replaced by `MA0`/`MA0_2`/`MA0_3`.  Sound because every coefficient
    multiplying those three terms in the RHS is a nonnegative product (`Real.exp`, `(√2)^n`, `n^k`, norms,
    `Real.sqrt τ` powers, all ≥ 0 given `τ > 0`), so the substitution is monotone. -/
theorem bfac_four_term_domain_restricted_bound_of_amp0_bound
    (τ : ℝ) (hτ : 0 < τ) (ρ : ℝ) (hρ : 0 < ρ)
    (PI PJ Q : Point n) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    (MA0 : ℝ) (hMA0 : 0 ≤ MA0) (hAmp0 : |Amp 0| ≤ MA0)
    (Q2 : Point n) (Amp2 : Point n → ℝ) (hAmp2 : AEStronglyMeasurable Amp2 volume)
    (L2 : ℝ) (hL2 : 0 ≤ L2) (hlip2 : ∀ v : Point n, |Amp2 v - Amp2 0| ≤ L2 * ‖v‖)
    (MA0_2 : ℝ) (hMA0_2 : 0 ≤ MA0_2) (hAmp0_2 : |Amp2 0| ≤ MA0_2)
    (Q3 : Point n) (Amp3 : Point n → ℝ) (hAmp3 : AEStronglyMeasurable Amp3 volume)
    (L3 : ℝ) (hL3 : 0 ≤ L3) (hlip3 : ∀ v : Point n, |Amp3 v - Amp3 0| ≤ L3 * ‖v‖)
    (MA0_3 : ℝ) (hMA0_3 : 0 ≤ MA0_3) (hAmp0_3 : |Amp3 0| ≤ MA0_3)
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
                * (MA0 * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                * (MA0 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + ((n : ℝ) ^ 2 * L2 * ‖Q2‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / (2 * τ))
                * (MA0_2 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + ((n : ℝ) ^ 2 * L3 * ‖Q3‖
            + Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / (2 * τ))
                * (MA0_3 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                    + L3 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)))
        + M := by
  have hbase := bfac_four_term_domain_restricted_bound τ hτ ρ hρ
    PI PJ Q Amp hAmp L hL hlip Q2 Amp2 hAmp2 L2 hL2 hlip2 Q3 Amp3 hAmp3 L3 hL3 hlip3
    AmpFlat hAmpFlat M hM hboundFlat hUmeas hUcsub
  refine hbase.trans ?_
  gcongr

/-! ###############################################################################
    ### PART 2′ — THE LEVI-FOLDED CAPSTONE: `Bfac(z) := Levi(s,z)·(T1+T2+T3+T4)`, sliver window, `O(√ε)`.
    ############################################################################### -/

/-- **★★★★★ `bfac_four_term_levi_domain_restricted_sliver_window_bound` — THE LEVI-FOLDED CAPSTONE.**
    Folds the outer `Levi(s,z) := leviSeries E s z 0` factor into `HCompNearCarryBfacFourTermAssembly`'s
    Part 2, giving an `O(√ε)` bound on the LITERAL `Bfac`-shape `Levi(s,z)·(T1+T2+T3+T4)`, restricted to
    `W''S'` and integrated over the sliver `s ∈ (t-ε,t)`, `S'`/`ρ` shared across all four summands
    (constructed once, as in Part 2), and `(M_F,L_F)` the window-uniform `Levi` bound/Lipschitz data
    (constructed once, as in `LeviWindowUniformAmpLipschitz`).  `Amp`/`Amp2`/`Amp3` carry GLOBAL
    bounded+Lipschitz hypotheses (strengthened from Part 1's Lipschitz-AT-0, the necessary strengthening
    to legally fold with `Levi`); `AmpFlat` needs no Lipschitz at all.  NOT `a₁ = R/6`. -/
theorem bfac_four_term_levi_domain_restricted_sliver_window_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε) (hεt : ε < t)
    (E : ℝ → Point n → Point n → ℝ) (C_L Kc L_E : ℝ)
    (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ s ∈ Set.Icc (t - ε) t, ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ s ∈ Set.Icc (t - ε) t, ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2))
    (PI PJ Q : Point n) (Amp : Point n → ℝ) (MA LA : ℝ) (hMA : 0 ≤ MA) (hLA : 0 ≤ LA)
    (hbdA : ∀ v : Point n, |Amp v| ≤ MA) (hlipA : ∀ v w : Point n, |Amp v - Amp w| ≤ LA * dist v w)
    (Q2 : Point n) (Amp2 : Point n → ℝ) (MA2 LA2 : ℝ) (hMA2 : 0 ≤ MA2) (hLA2 : 0 ≤ LA2)
    (hbdA2 : ∀ v : Point n, |Amp2 v| ≤ MA2)
    (hlipA2 : ∀ v w : Point n, |Amp2 v - Amp2 w| ≤ LA2 * dist v w)
    (Q3 : Point n) (Amp3 : Point n → ℝ) (MA3 LA3 : ℝ) (hMA3 : 0 ≤ MA3) (hLA3 : 0 ≤ LA3)
    (hbdA3 : ∀ v : Point n, |Amp3 v| ≤ MA3)
    (hlipA3 : ∀ v w : Point n, |Amp3 v - Amp3 w| ≤ LA3 * dist v w)
    (AmpFlat : Point n → ℝ) (hAmpFlat : AEStronglyMeasurable AmpFlat volume)
    (MF : ℝ) (hMFnn0 : 0 ≤ MF) (hboundFlat : ∀ v : Point n, |AmpFlat v| ≤ MF) :
    ∃ (S' : Set (Point n)) (ρ M_F L_F : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧
      |∫ s in (t - ε)..t, ∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim (t - s) v * (leviSeries E s v 0
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v
               + (-(∑ k, v k * Q2 k) / (2 * (t - s))) * Amp2 v
               + (-(∑ k, v k * Q3 k) / (2 * (t - s))) * Amp3 v
               + AmpFlat v))|
        ≤ 2 * ((M_F * LA + MA * L_F) * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
            + (((n : ℝ) ^ 2 * (M_F * LA + MA * L_F) * ‖Q‖
                  + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                      * ((M_F * MA) * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
                          + (M_F * LA + MA * L_F)
                              * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4)
                                  * (ε * Real.sqrt ε)
                                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε)))
                  + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
                      * ((M_F * MA) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                          + (M_F * LA + MA * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + ((n : ℝ) ^ 2 * (M_F * LA2 + MA2 * L_F) * ‖Q2‖
                    + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / 2)
                        * ((M_F * MA2) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                            + (M_F * LA2 + MA2 * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + ((n : ℝ) ^ 2 * (M_F * LA3 + MA3 * L_F) * ‖Q3‖
                    + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / 2)
                        * ((M_F * MA3) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                            + (M_F * LA3 + MA3 * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)))
                + (M_F * MF)) * ε := by
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
  -- window-uniform Levi bound/Lipschitz data, built ONCE.
  obtain ⟨M_F, L_F, hMFnn, hLFnn, hFb, hFl⟩ :=
    leviBase_window_uniform_bounded_lipschitz E t ε C_L Kc L_E hε hεt hC_L hKc hL_E
      hFdom hVol hE1 hIz hSlice
  refine ⟨S', ρ, M_F, L_F, hS'open, hq0S', hρpos, hMFnn, hLFnn, ?_⟩
  set C1 : ℝ := (M_F * LA + MA * L_F) * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)
    with hC1def
  set HHTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
      * ((M_F * MA) * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
          + (M_F * LA + MA * L_F)
              * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε))) with hHHTaildef
  set LMTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
      * ((M_F * MA) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + (M_F * LA + MA * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTaildef
  set LMTail2 : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q2‖ / 2)
      * ((M_F * MA2) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + (M_F * LA2 + MA2 * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTail2def
  set LMTail3 : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q3‖ / 2)
      * ((M_F * MA3) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + (M_F * LA3 + MA3 * L_F) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTail3def
  set C2 : ℝ := ((n : ℝ) ^ 2 * (M_F * LA + MA * L_F) * ‖Q‖ + HHTail + LMTail)
      + ((n : ℝ) ^ 2 * (M_F * LA2 + MA2 * L_F) * ‖Q2‖ + LMTail2)
      + ((n : ℝ) ^ 2 * (M_F * LA3 + MA3 * L_F) * ‖Q3‖ + LMTail3) + (M_F * MF) with hC2def
  have hC2nn : 0 ≤ C2 := by
    rw [hC2def, hHHTaildef, hLMTaildef, hLMTail2def, hLMTail3def]; positivity
  apply pointwise_bound_sliver_window_inv_sqrt t ε C1 C2 hε
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v * (leviSeries E s v 0
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (s - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (s - s))) * Amp v
               + (-(∑ k, v k * Q2 k) / (2 * (s - s))) * Amp2 v
               + (-(∑ k, v k * Q3 k) / (2 * (s - s))) * Amp3 v
               + AmpFlat v)) = 0 := by
      intro v
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
    have hsIcc : s ∈ Set.Icc (t - ε) t := ⟨hs.1.le, hs.2⟩
    -- window-uniform product bound/Lipschitz data for the three amplitude terms, at THIS `s`.
    obtain ⟨hb1, hl1⟩ := bounded_lipschitz_mul_global (fun z => leviSeries E s z 0) Amp M_F L_F MA LA
      hMFnn hLFnn hMA hLA (hFb s hsIcc) (hFl s hsIcc) hbdA hlipA
    obtain ⟨hb2, hl2⟩ := bounded_lipschitz_mul_global (fun z => leviSeries E s z 0) Amp2 M_F L_F MA2 LA2
      hMFnn hLFnn hMA2 hLA2 (hFb s hsIcc) (hFl s hsIcc) hbdA2 hlipA2
    obtain ⟨hb3, hl3⟩ := bounded_lipschitz_mul_global (fun z => leviSeries E s z 0) Amp3 M_F L_F MA3 LA3
      hMFnn hLFnn hMA3 hLA3 (hFb s hsIcc) (hFl s hsIcc) hbdA3 hlipA3
    have hL1'nn : 0 ≤ M_F * LA + MA * L_F := add_nonneg (mul_nonneg hMFnn hLA) (mul_nonneg hMA hLFnn)
    have hM1'nn : 0 ≤ M_F * MA := mul_nonneg hMFnn hMA
    have hL2'nn : 0 ≤ M_F * LA2 + MA2 * L_F := add_nonneg (mul_nonneg hMFnn hLA2) (mul_nonneg hMA2 hLFnn)
    have hM2'nn : 0 ≤ M_F * MA2 := mul_nonneg hMFnn hMA2
    have hL3'nn : 0 ≤ M_F * LA3 + MA3 * L_F := add_nonneg (mul_nonneg hMFnn hLA3) (mul_nonneg hMA3 hLFnn)
    have hM3'nn : 0 ≤ M_F * MA3 := mul_nonneg hMFnn hMA3
    have hM4'nn : 0 ≤ M_F * MF := mul_nonneg hMFnn hMFnn0
    have hlipAt0_1 : ∀ v : Point n,
        |leviSeries E s v 0 * Amp v - leviSeries E s (0 : Point n) 0 * Amp 0| ≤ (M_F * LA + MA * L_F) * ‖v‖ := by
      intro v; have h0 := hl1 v (0 : Point n); rwa [dist_zero_right] at h0
    have hlipAt0_2 : ∀ v : Point n,
        |leviSeries E s v 0 * Amp2 v - leviSeries E s (0 : Point n) 0 * Amp2 0|
          ≤ (M_F * LA2 + MA2 * L_F) * ‖v‖ := by
      intro v; have h0 := hl2 v (0 : Point n); rwa [dist_zero_right] at h0
    have hlipAt0_3 : ∀ v : Point n,
        |leviSeries E s v 0 * Amp3 v - leviSeries E s (0 : Point n) 0 * Amp3 0|
          ≤ (M_F * LA3 + MA3 * L_F) * ‖v‖ := by
      intro v; have h0 := hl3 v (0 : Point n); rwa [dist_zero_right] at h0
    have hAmp0at0_1 : |leviSeries E s (0 : Point n) 0 * Amp 0| ≤ M_F * MA := hb1 0
    have hAmp0at0_2 : |leviSeries E s (0 : Point n) 0 * Amp2 0| ≤ M_F * MA2 := hb2 0
    have hAmp0at0_3 : |leviSeries E s (0 : Point n) 0 * Amp3 0| ≤ M_F * MA3 := hb3 0
    have hmeas1 : AEStronglyMeasurable (fun v => leviSeries E s v 0 * Amp v) volume :=
      aesm_of_lipBound _ (M_F * LA + MA * L_F) hL1'nn hl1
    have hmeas2 : AEStronglyMeasurable (fun v => leviSeries E s v 0 * Amp2 v) volume :=
      aesm_of_lipBound _ (M_F * LA2 + MA2 * L_F) hL2'nn hl2
    have hmeas3 : AEStronglyMeasurable (fun v => leviSeries E s v 0 * Amp3 v) volume :=
      aesm_of_lipBound _ (M_F * LA3 + MA3 * L_F) hL3'nn hl3
    -- flat term: no Lipschitz needed, direct product bound + measurability.
    have hLevi_lip_self : ∀ z w : Point n, |leviSeries E s z 0 - leviSeries E s w 0| ≤ L_F * dist z w :=
      hFl s hsIcc
    have hmeasLevi : AEStronglyMeasurable (fun v => leviSeries E s v 0) volume :=
      aesm_of_lipBound _ L_F hLFnn hLevi_lip_self
    have hmeas4 : AEStronglyMeasurable (fun v => leviSeries E s v 0 * AmpFlat v) volume :=
      hmeasLevi.mul hAmpFlat
    have hboundFlat4 : ∀ v : Point n, |leviSeries E s v 0 * AmpFlat v| ≤ M_F * MF := by
      intro v
      rw [abs_mul]
      exact mul_le_mul (hFb s hsIcc v) (hboundFlat v) (abs_nonneg _) (abs_nonneg _ |>.trans (hFb s hsIcc v))
    have hbase := bfac_four_term_domain_restricted_bound_of_amp0_bound τ hτ ρ hρpos
      PI PJ Q (fun v => leviSeries E s v 0 * Amp v) hmeas1 (M_F * LA + MA * L_F) hL1'nn hlipAt0_1
      (M_F * MA) hM1'nn hAmp0at0_1
      Q2 (fun v => leviSeries E s v 0 * Amp2 v) hmeas2 (M_F * LA2 + MA2 * L_F) hL2'nn hlipAt0_2
      (M_F * MA2) hM2'nn hAmp0at0_2
      Q3 (fun v => leviSeries E s v 0 * Amp3 v) hmeas3 (M_F * LA3 + MA3 * L_F) hL3'nn hlipAt0_3
      (M_F * MA3) hM3'nn hAmp0at0_3
      (fun v => leviSeries E s v 0 * AmpFlat v) hmeas4 (M_F * MF) hM4'nn hboundFlat4
      hUmeas hρsub'
    have heqInteg : (fun v : Point n => gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * (leviSeries E s v 0 * Amp v)
             + (-(∑ k, v k * Q2 k) / (2 * τ)) * (leviSeries E s v 0 * Amp2 v)
             + (-(∑ k, v k * Q3 k) / (2 * τ)) * (leviSeries E s v 0 * Amp3 v)
             + (leviSeries E s v 0 * AmpFlat v)))
      = fun v : Point n => gaussDdim τ v * (leviSeries E s v 0
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v
               + (-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v
               + (-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v
               + AmpFlat v)) := by
      funext v; ring
    rw [heqInteg] at hbase
    have hHHfold := heatHessMult_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε PI PJ (M_F * MA)
      (M_F * LA + MA * L_F) hM1'nn hL1'nn
    have hLfold := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q (M_F * MA) (M_F * LA + MA * L_F)
      hM1'nn hL1'nn
    have hLfold2 := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q2 (M_F * MA2) (M_F * LA2 + MA2 * L_F)
      hM2'nn hL2'nn
    have hLfold3 := grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q3 (M_F * MA3) (M_F * LA3 + MA3 * L_F)
      hM3'nn hL3'nn
    have hfinal : |∫ v : Point n in U, gaussDdim τ v * (leviSeries E s v 0
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v
             + (-(∑ k, v k * Q2 k) / (2 * τ)) * Amp2 v
             + (-(∑ k, v k * Q3 k) / (2 * τ)) * Amp3 v
             + AmpFlat v))|
        ≤ C1 / Real.sqrt τ + C2 := by
      refine hbase.trans ?_
      rw [hC1def, hC2def, hHHTaildef, hLMTaildef, hLMTail2def, hLMTail3def]
      linarith [hHHfold, hLfold, hLfold2, hLfold3]
    rw [hτdef] at hfinal
    exact hfinal

end QIQTH.HCompNearCarryBfacLeviFoldedSliverWindowBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryBfacLeviFoldedSliverWindowBound
#print axioms bfac_four_term_domain_restricted_bound_of_amp0_bound
#print axioms bfac_four_term_levi_domain_restricted_sliver_window_bound
end AxiomChecks
