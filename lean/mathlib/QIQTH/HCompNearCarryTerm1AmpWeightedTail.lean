/-
  HCompNearCarryTerm1AmpWeightedTail — J4-1021: the `Amp`-weighted tail bounds Sol's (`gpt-5.6-sol`,
  high) J4-1020 audit named as gap (I), PLUS a mechanical unconditional strengthening of the diagonal
  vanishing fact needed for gap (II), toward wiring `HCompNearCarryTerm1LipschitzCancellation`'s
  (J4-1019) full-space `hsMixed`-weighted Lipschitz bound onto `nb`'s actual bounded post-CoV domain.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TWO GAPS (Sol, `gpt-5.6-sol`, high, 2026-08-23, auditing J4-1020 before this dispatch).

  (I) `HeatHessMultBallTailBound`/`HCompNearCarryTerm1BallGeometry`'s tail bounds are on the RAW
  (un-weighted) `heatHessMult`/`linMult` objects.  `nb`'s real integrand is `Amp`-WEIGHTED (per
  J4-1019's full-space Lipschitz payoff).  Need: `∫_{tail} |heatHessMult·Amp|` and
  `∫_{tail} |linMult·Amp|` ALSO exponentially small in `τ`, for `Amp` Lipschitz-at-`0`.

  (II) J4-1018/J4-1020's tail-bound convention is centred at `0`; `nb`'s actual base-slot CoV
  (`HCompNearCarryKPrimeBaseFieldCoV`, J4-1010) base point is `x`.  Is the "`v`" in the tail bounds
  ALREADY a `0`-centred displacement matching the CoV's own output variable, or does it need translating?

  ## GAP (I) — RESOLVED, MECHANICALLY, AS PREDICTED.

  Since `Amp` is Lipschitz-at-`0` (`|Amp v − Amp 0| ≤ L‖v‖`), the triangle inequality gives `|Amp v| ≤
  |Amp 0| + L‖v‖` — `Amp` grows AT MOST LINEARLY.  Composed with `heatHessMult`'s/`linMult`'s ALREADY-
  BANKED pointwise majorants (`abs_heatHessMult_le`: `O(‖v‖²)·G_τ`; `abs_linMult_le`: `O(‖v‖)·G_τ`),
  this gives a pointwise majorant that is a SUM of `‖v‖ᵏ·G_τ(v)` terms for `k ∈ {0,1,2,3}`
  (`heatHessMult·Amp`) or `k ∈ {1,2}` (`linMult·Amp`) — EVERY one of which ALREADY has a banked
  exponentially-small tail bound (`gaussDdim_tail_mass_le` for `k=0`; `normPow_gaussDdim_tail_le`,
  fed `oneD_absMoment1/2/3`, for `k=1,2,3` — ALL FOUR moments ALREADY banked in
  `GaussianMomentEnvelope.lean`, no new moment machinery needed).  Composing these — polynomial growth
  (from `Amp`'s Lipschitz bound) times exponential-Gaussian-tail decay is still exponentially decaying
  — is genuinely MECHANICAL, the SAME pattern already used for `normPow_gaussDdim_tail_le` itself
  (J4-1018).  NO new sympy check is needed: no new asymptotic RATE is introduced (same
  `exp(−R²/(8τ))` tail factor as J4-1018/J4-1020, just a longer, still-finite linear combination of
  the SAME four already-verified moment terms) — a genuinely different situation from J4-1018/
  J4-1019/J4-1020, each of which DID introduce a new rate and was sympy-checked first.

  ## GAP (II) — PARTIALLY RESOLVED: the "`v` = `w`" identification IS confirmed, but full domain
  reconciliation (openness of the CoV's image on `nb`'s actual restricted domain) remains open.

  Tracing the LITERAL chain (`HCompNearCarryKPrimeBaseFieldCoV`, J4-1010, BRICK 1 + BRICK 2):
  BRICK 1's `ring` factorization exhibits `(kPrime … x z)(eⱼ) = gaussDdim (t−s) (U z x) · Bfac(z)`,
  where `U z x := uniformInverseChart g gi hC hK z x`, and `Bfac`'s `hsMixed`-term literally uses
  `U z x` as `hsMixed`'s "`v`" argument (`⟨U z x, PI⟩⟨U z x, PJ⟩/(4τ²) − …`).  BRICK 2 then applies
  `BaseSlotM1M4Assembly`'s CoV `∫ z in S', gaussDdim τ (W z) · B z = ∫ w in W''S', gaussDdim τ w ·
  (B (V w)/|det|)` at `W := fun p => uniformInverseChart g gi hC hK p x`, producing an outer integral
  literally over `gaussDdim (t−s) w` — i.e. THE CoV'S OWN OUTPUT VARIABLE `w` is, BY CONSTRUCTION, the
  SAME quantity as `hsMixed`'s "`v`" (both are literally `uniformInverseChart g gi hC hK z x`, `w = W
  z = U z x`, before/after the substitution).  So: **`v` (the tail bounds' argument) IS `w` (the CoV's
  integration variable) — NOT a display-then-shift; `gaussDdim τ w` is inherently `0`-centred in `w`
  by the very definition of `gaussDdim`, and this IS exactly the argument `hsMixed`/`heatHessMult`/
  `linMult` consume.  There is NO additional "recentre `v` at `x`" step needed at the value level** —
  contradicting J4-1020's own (more cautious) framing that this was "UNVERIFIED".

  HOWEVER, tracing further: `nb`'s actual domain-restriction question is whether `S'ᶜ` (in `z`-space,
  `BaseSlotM1M4Assembly`'s IFT set) is controlled by the tail bounds — but the tail bounds live in
  `w`-space (`v = w`, NOT `z`).  The correct question is thus whether `(W '' S')ᶜ` (the `w`-space
  IMAGE's complement) is controlled — i.e. whether `W '' S'` contains a ball around `0` (since `0 = W
  x` — PROVED below, `uniformInverseChart_diag_zero_of_mem`, upgrading the existing `∀ᶠ`-local fact to
  an UNCONDITIONAL one).  J4-1020's Brick B (`S'_ball_complement_subset_rncRadialSq_tail`) proves this
  for a GENERIC `IsOpen S' ∧ x ∈ S'` — but it was applied (in its own docstring, honestly flagged) to
  `S'` ITSELF (`z`-space, centred at `x`), NOT to `W '' S'` (`w`-space, centred at `0`, which is the
  object gap (II) genuinely needs).  Re-applying Brick B's LEMMA (which is fully generic in its input
  open set) to `W '' S'` instead of `S'` would resolve gap (II) COMPLETELY, PROVIDED `IsOpen (W '' S')`
  — but `BaseSlotM1M4Assembly`'s public interface exposes only `IsOpen S'` (an existential unpacking of
  Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`, whose UNDERLYING `OpenPartialHomeomorph` DOES
  have `IsOpen e.target` and `e '' e.source = e.target`, but this is NOT exposed through the existing
  public lemma's return type) — establishing `IsOpen (W '' S')` from the exposed data would need
  RE-DERIVING the IFT invocation with the image-openness exposed (a genuine, still-open follow-on, NOT
  attempted here; would need `PartialHomeomorph.isOpen_image_of_subset_source`, the SAME lemma already
  used elsewhere in this campaign, `UniformChartRadius.lean` line 211, on a LOCALLY reconstructed `e`).

  Consulted Sol (`gpt-5.6-sol`, high, 2026-08-23) with this exact chain-trace BEFORE Lean: GO — confirmed
  gap (I)'s composition is genuinely mechanical (no new asymptotic content) and safe to bank without a
  fresh sympy check; confirmed the `v = w` identification for gap (II) is sound and non-circular (it is
  a literal unfolding of BRICK 1 + BRICK 2's own definitions, not a new geometric claim); confirmed the
  `IsOpen (W '' S')` gap is a genuine, SEPARATE remaining item — NOT closable by re-using
  `BaseSlotM1M4Assembly`'s existing public lemma (its existential hides the needed structure), would need
  a fresh IFT-exposing lemma; flagged this file should NOT attempt the full `nb`-domain-restricted
  payoff given this residual, and should bank gap (I) + the `v=w`/diagonal-zero pieces of gap (II) as
  genuine, separately useful infrastructure.

  ## WHAT LANDS.
    • `heatHessMult_amp_tail_le` — ★ GAP (I), heatHessMult: for `τ > 0`, `R : ℝ`, `p q : Point n`, `Amp`
      Lipschitz-at-`0` (modulus `L ≥ 0`, `AEStronglyMeasurable`), `|∫_{R²≤rncRadialSq v} heatHessMult τ
      p q v · Amp v|` is bounded by an EXPONENTIALLY SMALL (`exp(−R²/(8τ))`) expression, combining the
      `k=0,1,2,3` tail moments.
    • `linMult_amp_tail_le` — ★ GAP (I), linMult: the analogous `k=1,2` bound for `linMult`.
    • `hsMixed_amp_tail_le` — ★★ the COMBINED tail bound: `|∫_{R²≤rncRadialSq v} G_τ(v)·(hsMixed(v)·
      Amp v)| ≤` [heatHessMult tail bound] `+` [linMult tail bound], via the SAME pointwise `ring`
      identity `hsMixed_gaussDdim_mul_amp_eq_diff` uses, restricted to the tail set.
    • `uniformInverseChart_diag_zero_of_mem` — the UNCONDITIONAL diagonal-vanishing fact `q ∈ K →
      uniformInverseChart g gi hC hK q q = 0` (strengthening `uniformInverseChart_diag_eventually_
      generalK`'s `∀ᶠ`-local version to a genuine pointwise fact for ANY `q ∈ K` — the SAME proof,
      minus the unnecessary filter wrapper), confirming `W x = uniformInverseChart x x = 0` for the
      field point `x` used in `nb`'s CoV.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It does
  **NOT** attempt the full domain-restricted `nb` payoff — the `IsOpen (W '' S')` gap identified above
  (re-deriving the IFT invocation with image-openness exposed) is a genuine, SEPARATE, still-open item,
  explicitly NOT attempted here.  `hsMixed_amp_tail_le` is stated on the GENERIC Euclidean-radial tail
  set `{v | R² ≤ rncRadialSq v}`, NOT yet identified with `(W '' S')ᶜ` for ANY concrete `S'`/`W` (that
  identification needs the `IsOpen (W '' S')` gap closed first).  Does NOT discharge `nb`, `hCConv`, or
  any part of `hcomp`; does NOT address `Bfac`'s OTHER 3 terms (only term1/`hsMixed` infrastructure is
  touched); the far-carry `fb` remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion (all four landed
  theorems are genuine new quantitative/logical facts, not restatements of existing banked theorems), no
  existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatHessMultBallTailBound
import QIQTH.HCompNearCarryTerm1LipschitzCancellation
import QIQTH.NearIsometryBudget
import QIQTH.UniformChartRadius

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.HCompNearCarryTerm1AmpWeightedTail

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### GAP (I), Brick A — the `Amp`-weighted `heatHessMult` tail bound.
    ############################################################################### -/

/-- **★★★ `heatHessMult_amp_tail_le` — GAP (I), THE `heatHessMult` PAYOFF.**  For `τ > 0`, `R : ℝ`,
    `p q : Point n`, and `Amp` Lipschitz-at-`0` with modulus `L ≥ 0`, the `Amp`-WEIGHTED tail integral
    `∫_{R² ≤ rncRadialSq v} heatHessMult τ p q v · Amp v` is bounded EXPONENTIALLY SMALL in `R²/τ`:
    the pointwise bound `|Amp v| ≤ |Amp 0| + L‖v‖` composes with `abs_heatHessMult_le`'s `O(‖v‖²)`
    majorant to give a `k = 0,1,2,3` combined tail, each piece ALREADY bounded by `gaussDdim_tail_mass_le`
    / `normPow_gaussDdim_tail_le`.  NOT `a₁ = R/6`. -/
theorem heatHessMult_amp_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (p q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    |∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, heatHessMult τ p q v * Amp v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖p‖ * ‖q‖)
          * (|Amp 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                + (1 / (2 * τ)))
              + L * ((1 / (4 * τ ^ 2))
                    * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                  + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1))) := by
  set S : Set (Point n) := {v | R ^ 2 ≤ rncRadialSq v} with hSdef
  have hSmeas : MeasurableSet S := tailSet_measurableSet R
  have hHHAmp_int : Integrable (fun v : Point n => heatHessMult τ p q v * Amp v) volume :=
    heatHessMult_mul_lipschitzAmp_integrable τ hτ p q Amp hAmp L hlip
  have hstep1 : |∫ v : Point n in S, heatHessMult τ p q v * Amp v|
      ≤ ∫ v : Point n in S, |heatHessMult τ p q v * Amp v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict S))
      (fun v : Point n => heatHessMult τ p q v * Amp v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  set Cco : ℝ := (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ with hCcodef
  have hCconn : 0 ≤ Cco := by rw [hCcodef]; positivity
  set c0 : ℝ := Cco * |Amp 0| / (2 * τ) with hc0def
  set c1 : ℝ := Cco * L / (2 * τ) with hc1def
  set c2 : ℝ := Cco * |Amp 0| / (4 * τ ^ 2) with hc2def
  set c3 : ℝ := Cco * L / (4 * τ ^ 2) with hc3def
  have hc0nn : 0 ≤ c0 := by rw [hc0def]; positivity
  have hc1nn : 0 ≤ c1 := by rw [hc1def]; positivity
  have hc2nn : 0 ≤ c2 := by rw [hc2def]; positivity
  have hc3nn : 0 ≤ c3 := by rw [hc3def]; positivity
  set D : Point n → ℝ := fun v =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v)
        + c2 * (‖v‖ ^ 2 * gaussDdim τ v) + c3 * (‖v‖ ^ 3 * gaussDdim τ v) with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact ((((gaussDdim_integrable τ hτ).const_mul _).add
      ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _)).add
      ((normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _)).add
      ((normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _)
  have hpt : ∀ v : Point n, |heatHessMult τ p q v * Amp v| ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    have hAmpv : |Amp v| ≤ |Amp 0| + L * ‖v‖ := by
      calc |Amp v| = |Amp 0 + (Amp v - Amp 0)| := by ring_nf
        _ ≤ |Amp 0| + |Amp v - Amp 0| := abs_add_le _ _
        _ ≤ |Amp 0| + L * ‖v‖ := by linarith [hlip v]
    calc |heatHessMult τ p q v * Amp v| = |heatHessMult τ p q v| * |Amp v| := abs_mul _ _
      _ ≤ (Cco * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)) * (|Amp 0| + L * ‖v‖) := by
          refine mul_le_mul (by rw [hCcodef]; exact abs_heatHessMult_le τ hτ p q v) hAmpv
            (abs_nonneg _) (by positivity)
      _ = D v := by rw [hDdef, hc0def, hc1def, hc2def, hc3def]; ring
  have hstep2 : ∫ v : Point n in S, |heatHessMult τ p q v * Amp v| ≤ ∫ v : Point n in S, D v :=
    setIntegral_mono_on (hHHAmp_int.abs.integrableOn) hD_int.integrableOn hSmeas (fun v _ => hpt v)
  refine hstep2.trans ?_
  have hi0 : IntegrableOn (fun v : Point n => c0 * gaussDdim τ v) S volume :=
    ((gaussDdim_integrable τ hτ).integrableOn).const_mul _
  have hi1 : IntegrableOn (fun v : Point n => c1 * (‖v‖ ^ 1 * gaussDdim τ v)) S volume :=
    ((normPow_gauss_integrable 1 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi2 : IntegrableOn (fun v : Point n => c2 * (‖v‖ ^ 2 * gaussDdim τ v)) S volume :=
    ((normPow_gauss_integrable 2 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi3 : IntegrableOn (fun v : Point n => c3 * (‖v‖ ^ 3 * gaussDdim τ v)) S volume :=
    ((normPow_gauss_integrable 3 (by norm_num) τ hτ).integrableOn).const_mul _
  have hi01 : IntegrableOn (fun v : Point n =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v)) S volume := hi0.add hi1
  have hi012 : IntegrableOn (fun v : Point n =>
      c0 * gaussDdim τ v + c1 * (‖v‖ ^ 1 * gaussDdim τ v) + c2 * (‖v‖ ^ 2 * gaussDdim τ v)) S
      volume := hi01.add hi2
  have hval : ∫ v : Point n in S, D v
      = c0 * (∫ v : Point n in S, gaussDdim τ v) + c1 * (∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v)
        + (c2 * (∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v)
            + c3 * (∫ v : Point n in S, ‖v‖ ^ 3 * gaussDdim τ v)) := by
    rw [hDdef, integral_add hi012 hi3, integral_add hi01 hi2,
      integral_add hi0 hi1, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul]
    ring
  rw [hval]
  have ht0 : ∫ v : Point n in S, gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n := gaussDdim_tail_mass_le τ hτ R
  have ht1 : ∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1) :=
    normPow_gaussDdim_tail_le 1 (by norm_num) τ hτ R (3 / 2) (by norm_num)
      (by simpa using oneD_absMoment1 (2 * τ) (by positivity))
  have ht2 : ∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2) :=
    normPow_gaussDdim_tail_le 2 (by norm_num) τ hτ R 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) (by positivity))
  have ht3 : ∫ v : Point n in S, ‖v‖ ^ 3 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3) :=
    normPow_gaussDdim_tail_le 3 (by norm_num) τ hτ R (64 * Real.sqrt 2 + 1) (by positivity)
      (oneD_absMoment3 (2 * τ) (by positivity))
  have hfinal : c0 * (∫ v : Point n in S, gaussDdim τ v)
        + c1 * (∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v)
        + (c2 * (∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v)
            + c3 * (∫ v : Point n in S, ‖v‖ ^ 3 * gaussDdim τ v))
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * (c0 + c1 * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + (c2 * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                  + c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3))) := by
    have e0 := mul_le_mul_of_nonneg_left ht0 hc0nn
    have e1 := mul_le_mul_of_nonneg_left ht1 hc1nn
    have e2 := mul_le_mul_of_nonneg_left ht2 hc2nn
    have e3 := mul_le_mul_of_nonneg_left ht3 hc3nn
    have hcomb := add_le_add (add_le_add e0 e1) (add_le_add e2 e3)
    refine hcomb.trans_eq ?_
    ring
  refine hfinal.trans_eq ?_
  rw [hc0def, hc1def, hc2def, hc3def]
  ring

/-! ###############################################################################
    ### GAP (I), Brick B — the `Amp`-weighted `linMult` tail bound.
    ############################################################################### -/

/-- **★★★ `linMult_amp_tail_le` — GAP (I), THE `linMult` PAYOFF.**  For `τ > 0`, `R : ℝ`, `Q : Point n`,
    and `Amp` Lipschitz-at-`0` with modulus `L ≥ 0`, the `Amp`-WEIGHTED tail integral
    `∫_{R² ≤ rncRadialSq v} linMult τ Q v · Amp v` is bounded EXPONENTIALLY SMALL in `R²/τ`, combining
    `abs_linMult_le`'s `O(‖v‖)` majorant with `|Amp v| ≤ |Amp 0| + L‖v‖` into a `k = 1, 2` tail. NOT
    `a₁ = R/6`. -/
theorem linMult_amp_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    |∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, linMult τ Q v * Amp v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
          * (|Amp 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
              + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)) := by
  set S : Set (Point n) := {v | R ^ 2 ≤ rncRadialSq v} with hSdef
  have hSmeas : MeasurableSet S := tailSet_measurableSet R
  have hLAmp_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
    linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
  have hstep1 : |∫ v : Point n in S, linMult τ Q v * Amp v|
      ≤ ∫ v : Point n in S, |linMult τ Q v * Amp v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict S))
      (fun v : Point n => linMult τ Q v * Amp v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  set Cco : ℝ := (n : ℝ) * ‖Q‖ / (2 * τ) with hCcodef
  have hCconn : 0 ≤ Cco := by rw [hCcodef]; positivity
  set d1 : ℝ := Cco * |Amp 0| with hd1def
  set d2 : ℝ := Cco * L with hd2def
  have hd1nn : 0 ≤ d1 := by rw [hd1def]; positivity
  have hd2nn : 0 ≤ d2 := by rw [hd2def]; positivity
  set D : Point n → ℝ := fun v => d1 * (‖v‖ ^ 1 * gaussDdim τ v) + d2 * (‖v‖ ^ 2 * gaussDdim τ v)
    with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _).add
      ((normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _)
  have hpt : ∀ v : Point n, |linMult τ Q v * Amp v| ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    have hAmpv : |Amp v| ≤ |Amp 0| + L * ‖v‖ := by
      calc |Amp v| = |Amp 0 + (Amp v - Amp 0)| := by ring_nf
        _ ≤ |Amp 0| + |Amp v - Amp 0| := abs_add_le _ _
        _ ≤ |Amp 0| + L * ‖v‖ := by linarith [hlip v]
    calc |linMult τ Q v * Amp v| = |linMult τ Q v| * |Amp v| := abs_mul _ _
      _ ≤ (Cco * ‖v‖ * gaussDdim τ v) * (|Amp 0| + L * ‖v‖) := by
          refine mul_le_mul ?_ hAmpv (abs_nonneg _) (by positivity)
          have hb := abs_linMult_le τ hτ Q v
          rw [hCcodef]; exact hb
      _ = D v := by rw [hDdef, hd1def, hd2def]; ring
  have hstep2 : ∫ v : Point n in S, |linMult τ Q v * Amp v| ≤ ∫ v : Point n in S, D v :=
    setIntegral_mono_on (hLAmp_int.abs.integrableOn) hD_int.integrableOn hSmeas (fun v _ => hpt v)
  refine hstep2.trans ?_
  have hval : ∫ v : Point n in S, D v
      = d1 * (∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v)
          + d2 * (∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v) := by
    rw [hDdef, integral_add
      (((normPow_gauss_integrable 1 (by norm_num) τ hτ).integrableOn).const_mul _)
      (((normPow_gauss_integrable 2 (by norm_num) τ hτ).integrableOn).const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hval]
  have ht1 : ∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1) :=
    normPow_gaussDdim_tail_le 1 (by norm_num) τ hτ R (3 / 2) (by norm_num)
      (by simpa using oneD_absMoment1 (2 * τ) (by positivity))
  have ht2 : ∫ v : Point n in S, ‖v‖ ^ 2 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2) :=
    normPow_gaussDdim_tail_le 2 (by norm_num) τ hτ R 2 (by norm_num)
      (oneD_absMoment2 (2 * τ) (by positivity))
  have hfinal := add_le_add (mul_le_mul_of_nonneg_left ht1 hd1nn) (mul_le_mul_of_nonneg_left ht2 hd2nn)
  refine hfinal.trans_eq ?_
  rw [hd1def, hd2def, hCcodef]
  ring

/-! ###############################################################################
    ### GAP (I) combined — the `hsMixed` `Amp`-weighted tail bound.
    ############################################################################### -/

/-- **★★★ `hsMixed_amp_tail_le` — THE COMBINED GAP (I) PAYOFF.**  For `τ > 0`, `R : ℝ`, chart-Jacobian
    jet fields `PI PJ Q : Point n`, and `Amp` Lipschitz-at-`0` with modulus `L ≥ 0`, the `Amp`-weighted
    tail integral of `hsMixed`'s Gaussian-weighted product is bounded by the SUM of the `heatHessMult`
    and `linMult` `Amp`-weighted tail bounds — via the SAME pointwise `ring` identity
    `G_τ(v)·hsMixed(v)·Amp v = heatHessMult v · Amp v − linMult v · Amp v` that
    `hsMixed_gaussDdim_mul_amp_eq_diff` uses, restricted here to the tail set `S`. NOT `a₁ = R/6`. -/
theorem hsMixed_amp_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    |∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
      ≤ |∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, heatHessMult τ PI PJ v * Amp v|
          + |∫ v : Point n in {v | R ^ 2 ≤ rncRadialSq v}, linMult τ Q v * Amp v| := by
  set S : Set (Point n) := {v | R ^ 2 ≤ rncRadialSq v} with hSdef
  have hSmeas : MeasurableSet S := tailSet_measurableSet R
  have hpt1 : ∀ v : Point n, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
    intro v
    have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
        * gaussDdim τ v
      = heatHessMult τ PI PJ v - linMult τ Q v := by
      simp only [heatHessMult, linMult]; ring
    calc gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by
          ring
      _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
      _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
  have hHH_int : Integrable (fun v : Point n => heatHessMult τ PI PJ v * Amp v) volume :=
    heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip
  have hL_int : Integrable (fun v : Point n => linMult τ Q v * Amp v) volume :=
    linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
  have hcong : ∫ v : Point n in S, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = (∫ v : Point n in S, heatHessMult τ PI PJ v * Amp v) - ∫ v : Point n in S, linMult τ Q v * Amp v := by
    rw [setIntegral_congr_fun hSmeas (fun v _ => hpt1 v)]
    exact integral_sub hHH_int.integrableOn hL_int.integrableOn
  rw [hcong, sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]

/-! ###############################################################################
    ### GAP (II), mechanical piece — the UNCONDITIONAL diagonal-vanishing fact.
    ############################################################################### -/

/-- **★ `uniformInverseChart_diag_zero_of_mem` — GAP (II)'s mechanical piece.**  The UNCONDITIONAL
    diagonal-vanishing fact `uniformInverseChart g gi hC hK q q = 0` for ANY `q ∈ K` (strengthening
    `HerrHminGeneralQ0GeneralK.uniformInverseChart_diag_eventually_generalK`'s `∀ᶠ q in 𝓝 q₀, …`
    LOCAL statement to a genuine POINTWISE fact for EVERY `q ∈ K` — the underlying proof
    (`uniformInverseChart_huniformChart`'s germ, `Filter.EventuallyEq.eq_of_nhds`, `uniformFlowExp_zero`)
    never actually used nearness to any `q₀`; it is the SAME argument, minus the unnecessary filter
    wrapper).  Confirms `W x = uniformInverseChart g gi hC hK x x = 0` for `nb`'s CoV base map
    `W p := uniformInverseChart g gi hC hK p x` at `p = x` — the `0`-in-`W''S'` fact GAP (II)'s
    remaining `IsOpen (W''S')` reconciliation needs. NOT `a₁ = R/6`. -/
theorem uniformInverseChart_diag_zero_of_mem (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q : Point n} (hq : q ∈ K) :
    uniformInverseChart g gi hC hK q q = 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec q hq
  have hgerm := (hgermC2 0 (by rw [norm_zero]; exact hδ₀)).1
  have h := hgerm.eq_of_nhds
  rwa [uniformFlowExp_zero g gi hC hK q hq] at h

end QIQTH.HCompNearCarryTerm1AmpWeightedTail

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1AmpWeightedTail
#print axioms heatHessMult_amp_tail_le
#print axioms linMult_amp_tail_le
#print axioms hsMixed_amp_tail_le
#print axioms uniformInverseChart_diag_zero_of_mem
end AxiomChecks
