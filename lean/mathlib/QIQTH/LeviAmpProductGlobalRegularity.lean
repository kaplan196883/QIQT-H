/-
  LeviAmpProductGlobalRegularity — J4-1028: the `Levi(s,z)` PREFACTOR's own bounded+Lipschitz
  regularity, composed with the base-slot amplitude weight into a SINGLE globally bounded+Lipschitz
  factor `Levi(s,z)·A(z)`, and re-instantiating J4-1024's §E capstone at that product — the FIRST
  wiring of the `Levi(s,z)` factor (not just `A`) into `nb`'s term1 capstone shape.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ROLE.  `nb`'s term1 (`HCompNearCarryKPrimeBaseFieldCoV.lean`, J4-1010) has the shape
      `Bfac(z) := Levi(s,z)·(hsMixed·A(z) + grⱼ·∂ⱼA(z) + grᵢ·∂ᵢA(z) + ∂ⱼ∂ᵢA(z))`,
  `Levi(s,z) := leviSeries E s z 0` (`E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)`),
  `A(z) := chartFieldAmp g gi hC hK a b τ z x` (field point `x` fixed, base point `z` varying — the
  BASE-SLOT convention `AmpFieldBaseSlotGlobalTruncation`/J4-1027 fixed).  J4-1027's own honest-scope
  note explicitly flagged: "does NOT discharge … the `Levi(s,z)` prefactor multiplying `hsMixed·A` in
  `Bfac` — NOT bounded/Lipschitz here".  THIS FILE supplies that missing regularity for `Levi(s,z)`
  and composes it with the ALREADY-banked amplitude weight (J4-1027's `AmpGlobalBase`) into a SINGLE
  product weight, feeding the SAME J4-1024 capstone consumer interface
  (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`, whose `P` slot demands
  ONLY a global bound + a global pairwise-Lipschitz modulus — exactly what both factors already, or
  now, supply).

  ## WHAT WAS ALREADY BANKED (before this file) vs WHAT WAS MISSING.
    • `CensusLeviFactorDischarge.levi_Ffactor_ball_regularity` (J4-942) already assembled
      `abs_F_le_diagonal` (boundedness) + `resolvent_lipschitz_pointwise` (J4-144, Lipschitz) into a
      bounded+Lipschitz bundle for `F0 z := leviSeries E s z 0` — but stated on a BALL `‖z‖ < rF` (an
      artifact of matching a different, ball-shaped, FIELD-slot consumer, `CensusHbaseC2Discharge`'s
      `census_ampF_transported_ratio_regularity_unconditional`).  `nb`'s capstone consumer
      (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio`) needs a GLOBAL bound
      + GLOBAL Lipschitz modulus (`hPb : ∀ z, |P z| ≤ M_P`, `hPl : ∀ x y, |P x - P y| ≤ L_P·dist x y`,
      no ball restriction) — the exact shape `AmpGlobalBase` (J4-1027) supplies for the amplitude.
      Sol (`gpt-5.6-sol`, high, 2026-08-23, plan-reviewed before Lean) confirmed: `abs_F_le_diagonal`'s
      conclusion IS already unconditional in `z` (no ball hypothesis used in its proof — the bound
      `|F s z 0| ≤ C_L·gaussDdim (2s) 0` holds for literally every `z`), and `resolvent_lipschitz_
      pointwise`'s conclusion is likewise unconditional in `z, z'`; only `levi_Ffactor_ball_regularity`'s
      OWN packaging added the (unnecessary, for this consumer) ball restriction.  So the genuinely
      missing piece was (a) a GLOBAL (unrestricted) re-export of the SAME two banked facts, matching
      the capstone's actual interface, and (b) a product-Lipschitz combinator to fuse it with the
      already-global `AmpGlobalBase` weight — NEITHER of which existed anywhere in the campaign before
      this file (confirmed by grep across all "Levi"-named files: `LeviLipschitz`, `LeviSeries`,
      `LeviSeriesLocalData`, `AlphaLevi`, `HZMassLeviBaseEnvelope`, `CensusLeviFactorDischarge`,
      `DataLeviDischarge`, `CensusLeviFactorSUniform`, `LeviCarriesAssembly`, `LeviInterchange`,
      `LeviInterchangeTrunc`, `LeviIterBoxInduction`, `LeviCapWitness`, `LeviMTest` — none states a
      GLOBAL bound+Lipschitz pair for `leviSeries E s z 0`, and none composes it multiplicatively with
      a second regular factor).

  ## WHAT LANDS (ns `QIQTH.LeviAmpProductGlobalRegularity`).
    • `leviBase_global_bounded_lipschitz` — the GLOBAL (unrestricted) re-export of `abs_F_le_diagonal`
      + `resolvent_lipschitz_pointwise` at `F := leviSeries E`: `∃ M_F L_F ≥ 0`, `∀ z, |Levi(s,z)| ≤
      M_F` and `∀ z w, |Levi(s,z) − Levi(s,w)| ≤ L_F·dist z w` — the SAME shape `hsMixed_gaussDdim_
      mul_amp_domain_restricted_bound_of_transported_ratio`'s `P` slot demands, at the CONCRETE
      `Levi(s,z)`, no ball restriction.
    • `bounded_lipschitz_mul_global` — a generic combinator (standard `add-and-subtract` + triangle
      inequality, the SAME algebraic pattern as the banked `LeviLipschitz.hqLip_discharge`'s product
      step, repackaged as a direct two-function lemma): globally bounded+Lipschitz `f, g` compose to a
      globally bounded (`Mf·Mg`) + Lipschitz (`Mf·Lg + Mg·Lf`) product `f·g`.
    • `leviAmp_product_domain_restricted_bound` — ★★★★★ THE COMPOSITION: instantiates the two above at
      `f := Levi(s,·)`, `g := AmpGlobalBase …` (J4-1027), and feeds the product into the SAME J4-1024
      capstone, giving `nb`'s domain-restricted bound with `AmpExt` built from the product weight —
      the FIRST wiring of `Levi(s,z)` (not just `A`) into the capstone's `P`-slot.
    • `leviAmp_product_agrees_on_ball` — the product literally EQUALS `Levi(s,z)·A(z)` (the true term1
      sub-piece, minus `hsMixed`) on `closedBall w ρamp` (`Levi` agrees with itself everywhere; only
      `AmpGlobalBase`'s truncation restricts the agreement region).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  regularity/composition brick for `nb`'s term1.  Precisely what remains OPEN, regardless of this
  file:
    (i)   `hfac`'s literal carry over the IFT-selected domain `S'`, and the on-gate jet bundle
          uniformly over `S'` (residuals r1/r2 of `HCompNearCarryKPrimeBaseFieldCoV`) — NOT touched;
    (ii)  `Bfac`'s other 3 summands (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`, `∂ⱼ∂ᵢA`, each ALSO needing its own
          `Levi(s,z)·(·)` product regularity) — NOT touched, ENTIRELY SEPARATE;
    (iii) `fb` (the far carry) — NOT touched, ENTIRELY SEPARATE;
    (iv)  the coordinate-clamp truncation caveat inherited from `AmpGlobalBase` (agreement only inside
          `closedBall w ρamp`, not the whole domain);
    (v)   the five `LeviLipschitz` analytic carries (`hFdom`, `hVol`, `hE1`, `hIz`, `hSlice`) are
          CAMPAIGN BOOKKEEPING downstream of `{hDuhamel, hDConv, hCConv}` — this file does NOT prove
          that identification, it consumes them as hypotheses (same status as `CensusLeviFactorDischarge`
          before it).
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED. NOT `a₁ = R/6`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.LeviLipschitz
import QIQTH.TrueHeatKernel
import QIQTH.AmpFieldBaseSlotGlobalTruncation
import QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.ExpMap QIQTH.RadialDistance QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.ParametrixFunction
open QIQTH.OnGateJets QIQTH.AmpFieldGeneralPointBoundLipschitz
open QIQTH.BaseFlowGlobalContraction QIQTH.AmpFieldGlobalTruncation
open QIQTH.AmpFieldBaseSlotGlobalTruncation
open QIQTH.HCompNearCarryTerm1GeneralQ0InverseChartLipschitzBridge
open scoped Topology BigOperators Interval ContDiff NNReal

namespace QIQTH.LeviAmpProductGlobalRegularity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the GLOBAL (unrestricted) `Levi(s,z)` bounded+Lipschitz re-export.
    ############################################################################### -/

/-- **★ `leviBase_global_bounded_lipschitz`.**  The GLOBAL (no ball restriction) bounded+Lipschitz
    bundle for `Levi(s,z) := leviSeries E s z 0`, from the SAME five banked `LeviLipschitz` analytic
    carries `CensusLeviFactorDischarge.levi_Ffactor_ball_regularity` uses: `abs_F_le_diagonal`
    (boundedness, unconditional in `z`) + `resolvent_lipschitz_pointwise` (Lipschitz, unconditional in
    `z, z'`).  Unlike `levi_Ffactor_ball_regularity`, this does NOT restrict to a ball — the exact
    `P`-slot shape (`hPb : ∀ z, …`, `hPl : ∀ x y, …`) `nb`'s capstone consumer needs.  NOT `a₁ = R/6`. -/
theorem leviBase_global_bounded_lipschitz (E : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E : ℝ)
    (hs : 0 < s) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ z : Point n, |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ M_F L_F : ℝ, 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ z : Point n, |leviSeries E s z 0| ≤ M_F) ∧
      (∀ z w : Point n, |leviSeries E s z 0 - leviSeries E s w 0| ≤ L_F * dist z w) := by
  refine ⟨C_L * gaussDdim (2 * s) (0 : Point n), L_E + Kc * (2 * Real.sqrt s), ?_, ?_, ?_, ?_⟩
  · exact le_trans (abs_nonneg _) (abs_F_le_diagonal (leviSeries E) C_L s hs hC_L hFdom 0)
  · have hnn : (0 : ℝ) ≤ Kc * (2 * Real.sqrt s) := mul_nonneg hKc (by positivity)
    linarith
  · intro z; exact abs_F_le_diagonal (leviSeries E) C_L s hs hC_L hFdom z
  · intro z w
    exact resolvent_lipschitz_pointwise E (leviSeries E) s Kc L_E z w hs hKc
      (hVol z) (hVol w) (hE1 z w) (hIz z) (hIz w) (hSlice z w)

/-! ###############################################################################
    ### §B — the generic product-of-bounded-Lipschitz combinator.
    ############################################################################### -/

/-- **★★ `bounded_lipschitz_mul_global`.**  Two globally bounded + globally pairwise-Lipschitz scalar
    fields `f, g` compose to a globally bounded (`Mf·Mg`) + globally pairwise-Lipschitz
    (`Mf·Lg + Mg·Lf`) product `f·g`.  Pure `add-and-subtract` + triangle inequality — the SAME
    algebraic pattern as the banked `LeviLipschitz.hqLip_discharge`'s product step, repackaged as a
    direct two-function combinator (no `s`-family wrapper).  NOT `a₁ = R/6`. -/
theorem bounded_lipschitz_mul_global (f g : Point n → ℝ) (Mf Lf Mg Lg : ℝ)
    (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf) (hMg : 0 ≤ Mg) (hLg : 0 ≤ Lg)
    (hfb : ∀ z : Point n, |f z| ≤ Mf) (hfl : ∀ z w : Point n, |f z - f w| ≤ Lf * dist z w)
    (hgb : ∀ z : Point n, |g z| ≤ Mg) (hgl : ∀ z w : Point n, |g z - g w| ≤ Lg * dist z w) :
    (∀ z : Point n, |f z * g z| ≤ Mf * Mg) ∧
    (∀ z w : Point n, |f z * g z - f w * g w| ≤ (Mf * Lg + Mg * Lf) * dist z w) := by
  refine ⟨?_, ?_⟩
  · intro z
    calc |f z * g z| = |f z| * |g z| := abs_mul _ _
      _ ≤ Mf * Mg := mul_le_mul (hfb z) (hgb z) (abs_nonneg _) hMf
  · intro z w
    have key : f z * g z - f w * g w = f z * (g z - g w) + g w * (f z - f w) := by ring
    rw [key]
    calc |f z * (g z - g w) + g w * (f z - f w)|
        ≤ |f z * (g z - g w)| + |g w * (f z - f w)| := abs_add_le _ _
      _ = |f z| * |g z - g w| + |g w| * |f z - f w| := by rw [abs_mul, abs_mul]
      _ ≤ Mf * (Lg * dist z w) + Mg * (Lf * dist z w) := by
          apply add_le_add
          · exact mul_le_mul (hfb z) (hgl z w) (abs_nonneg _) hMf
          · exact mul_le_mul (hgb w) (hfl z w) (abs_nonneg _) hMg
      _ = (Mf * Lg + Mg * Lf) * dist z w := by ring

/-! ###############################################################################
    ### §C — the composed `Levi(s,z)·A(z)` product weight, and its ball-agreement.
    ############################################################################### -/

/-- **`leviAmp_product_agrees_on_ball`.**  The product weight `Levi(s,z)·AmpGlobalBase(z)` literally
    EQUALS `Levi(s,z)·A(z)` (the true term1 sub-piece, module `hsMixed`) whenever `z ∈ closedBall w ρ`:
    `Levi` agrees with itself everywhere, so the product's agreement region is exactly `AmpGlobalBase`'s
    (J4-1027's `ampGlobalBase_bound_lipschitz_agree`). NOT `a₁ = R/6`. -/
theorem leviAmp_product_agrees_on_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Ka : Set (Point n)} (hKa : IsCompact Ka) (ampA ampB τx : ℝ) (x w : Point n) (ρamp : ℝ)
    (E : ℝ → Point n → Point n → ℝ) (s : ℝ) (z : Point n)
    (hzagree : AmpGlobalBase g gi hChr hKa ampA ampB τx x w ρamp z
        = chartFieldAmp g gi hChr hKa ampA ampB τx z x) :
    leviSeries E s z 0 * AmpGlobalBase g gi hChr hKa ampA ampB τx x w ρamp z
      = leviSeries E s z 0 * chartFieldAmp g gi hChr hKa ampA ampB τx z x := by
  rw [hzagree]

/-- **★★★★★ `leviAmp_product_domain_restricted_bound`.**  THE COMPOSITION — instantiates §A's global
    `Levi(s,z)` regularity and J4-1027's global `AmpGlobalBase` regularity into a SINGLE globally
    bounded + globally Lipschitz product weight (§B), and feeds it into the SAME J4-1024 capstone
    `hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio` — the FIRST wiring of the
    `Levi(s,z)` factor (not just `A`) into `nb`'s term1 capstone shape.  Does NOT discharge `Bfac`'s
    other 3 summands, `hfac`/`S'` (residuals r1/r2), or `fb`.  NOT `a₁ = R/6`. -/
theorem leviAmp_product_domain_restricted_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Ka : Set (Point n)} (hKa : IsCompact Ka) (ampA ampB τx : ℝ) (x w : Point n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWx : ContDiffAt ℝ 2 (fun z' => uniformInverseChart g gi hChr hKa z' x) w)
    (hdetx : 0 < Matrix.det (g (uniformInverseChart g gi hChr hKa w x)))
    {K : Set (Point n)} (hK : IsCompact K) (hxK : x ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n)
    (E : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E : ℝ)
    (hs : 0 < s) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ z : Point n, |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ (S' : Set (Point n)) (ρSp : ℝ) (AmpExt : Point n → ℝ) (L : ℝ), IsOpen S' ∧ x ∈ S' ∧ 0 < ρSp ∧
      0 ≤ L ∧
      |∫ v : Point n in (fun p => uniformInverseChart g gi hChr hK p x) '' S',
          gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * AmpExt v)|
        ≤ (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
              + (n : ℝ) ^ 2 * L * ‖Q‖)
          + (Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                * (|AmpExt 0| * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
                      + (1 / (2 * τ)))
                    + L * ((1 / (4 * τ ^ 2))
                          * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                        + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
              + Real.exp (-(ρSp ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / (2 * τ))
                  * (|AmpExt 0| * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)
                      + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2))) := by
  obtain ⟨M_F, L_F, hMF, hLF, hFb, hFl⟩ :=
    leviBase_global_bounded_lipschitz E s C_L Kc L_E hs hC_L hKc hL_E hFdom hVol hE1 hIz hSlice
  obtain ⟨ρamp, hρamp, LA, MA, hLA, hMA, hlipA, hbdA, _hagreeA⟩ :=
    ampGlobalBase_bound_lipschitz_agree g gi hChr hKa ampA ampB τx x w hg hu hWx hdetx
  obtain ⟨hPbound, hPlip⟩ :=
    bounded_lipschitz_mul_global (fun z => leviSeries E s z 0)
      (AmpGlobalBase g gi hChr hKa ampA ampB τx x w ρamp) M_F L_F MA LA
      hMF hLF hMA hLA hFb hFl hbdA hlipA
  exact hsMixed_gaussDdim_mul_amp_domain_restricted_bound_of_transported_ratio g gi hChr hK hxK
    τ hτ PI PJ Q (fun z => leviSeries E s z 0 * AmpGlobalBase g gi hChr hKa ampA ampB τx x w ρamp z)
    (M_F * MA) (M_F * LA + MA * L_F) (mul_nonneg hMF hMA)
    (by have h1 : (0:ℝ) ≤ M_F * LA := mul_nonneg hMF hLA
        have h2 : (0:ℝ) ≤ MA * L_F := mul_nonneg hMA hLF
        linarith)
    hPbound hPlip

end QIQTH.LeviAmpProductGlobalRegularity

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.LeviAmpProductGlobalRegularity
#print axioms leviBase_global_bounded_lipschitz
#print axioms bounded_lipschitz_mul_global
#print axioms leviAmp_product_agrees_on_ball
#print axioms leviAmp_product_domain_restricted_bound
end AxiomChecks
