/-
  HFarEnvFromAmplitude — NET-DISCHARGE the crude time-derivative envelope `hAcrude` inside the
  window-level engine bundle `hEnv` that J4-970's `censusFTC_bridge` / `hfar_concrete_of_engine`
  consume, by wiring the banked any-`S` `∂_τ` domination envelope `witnessTimeDeriv_domination_global_anyS`
  (J4-950) into the per-`(s,a)` provider `hEnv_of_witnessCrudeEnv` (J4-916), PER POINT of the far window.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  analysis-infrastructure / carrier-reduction brick.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT J4-970 LEFT.  `hfar_concrete_of_engine` reduced the FTC-in-`c` bridge to three carriers
      {`hFmeasG` (global slice measurability), `hEnv` (the differentiation-under-∫ engine bundle over the
       window `s ∈ Ioo(u−ε)u`, `a ∈ Icc u (u+h)`), `hRint` (c-integrability of the integrated rate)}.
  The window-level `hEnv` at each `(s,a)` is EXACTLY the output of `hEnv_of_witnessCrudeEnv` (J4-916),
  whose carries are `{hAcrude, hFdom, hmeas, hbase}` plus scalars + the diagonal-avoidance `τ₀ < a−s < τ₁`.

  ## THE PER-POINT WIRING (genuine net discharge of `hAcrude`).  In the far window one always has
  `a − s ≥ u − s > 0` (strictly positive PER POINT, since `s < u ≤ a`), so per-`(s,a)` interval selection
  `τ₀ := (a−s)/2`, `τ₁ := 2(a−s)` is legal (the `∃` in `hEnv` is per point — a uniform lower bound on
  `a−s` is NOT needed).  With `a − s < h + ε`, one has `τ₁ = 2(a−s) < 2(h+ε) ≤ τ₀cap`, so the FIXED-cap
  any-`S` envelope `witnessTimeDeriv_domination_global_anyS` (J4-950) supplies the crude bound
      `|deriv (fun r ↦ Wit r 0 z) τ| ≤ C·τ⁻¹·gaussDdim (4·D.lam·τ) z`  for every `τ ∈ Icc τ₀ τ₁`,
  which — after the origin-evenness rewrite `gaussDdim t (0−z) = gaussDdim t z` (`gaussDdim_zero_sub`) —
  is EXACTLY the `hAcrude` shape (`wL := 4·D.lam`, `Ccr := C`).  So `hAcrude` is REPLACED by the mildest
  accepted class — the zeroth-amplitude sup-bounds `{hAmp0, hCfield, hSupp}` (J4-949/957/958 further
  reduce those) — with NO separate crude-envelope carry.

  ## WHAT THIS DOES — AND DOES NOT — DO.  It reduces the window-level `hEnv` (and, composed, the whole
  `hfar_concrete_of_engine` far-envelope) from the opaque engine bundle to
      {amplitude sups `hAmp0`/`hCfield`/`hSupp`, the G3 F-bound `hFdom`, `hmeas`, `hbase`}
  — genuine (and, for arbitrary free `F`, IRREDUCIBLE) F-side regularity carries, NOT a new analytic wall.
  It does NOT discharge `hFmeasG`, `hRint`, `hrate`, nor the G3 F-bound; and — since `F` is an arbitrary
  free field — it does NOT close `hEnv` unconditionally.  It discharges NONE of
  `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCrossDerivEngineWired
import QIQTH.HFarFTCBridgeFromEngine
import QIQTH.CensusTauDerivAnySEnvelope

open MeasureTheory Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.InverseChartNormalJets
open QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusTauDerivAnySEnvelope
open scoped Interval Topology

namespace QIQTH.HFarEnvFromAmplitude

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the window-level `hEnv` from amplitude sups + F-side carries (net discharge of `hAcrude`).
    ############################################################################### -/

/-- **★★★ `hEnv_window_of_amplitudeAndFdom` — the window-level engine bundle `hEnv` from the banked
    any-`S` `∂_τ` envelope (J4-950) + F-side carries.**  Produces the EXACT `hEnv` bundle that J4-970's
    `censusFTC_bridge` / `hfar_concrete_of_engine` consume — `∀ s ∈ Ioo(u−ε)u, ∀ a ∈ Icc u (u+h), ∃ V ∈ 𝓝 a, …`
    — from:
      • the zeroth-amplitude sup-bounds `hAmp0` (on `chartFieldAmp`, up to the fixed cap `τ₀cap`),
        `hCfield` (on the affine slope `censusAmpTauDeriv`), and the support fact `hSupp` — the mildest
        accepted class, feeding `witnessTimeDeriv_domination_global_anyS` (J4-950);
      • the s-uniform G3 F-bound `hFdom` (`|F s z 0| ≤ CF·gaussDdim(wF·s) z`);
      • window-uniform slice-measurability `hmeas` and base-integrability `hbase`.
    The crude time-derivative envelope `hAcrude` is NET-DISCHARGED per point via J4-950 (interval selection
    `τ₀ := (a−s)/2`, `τ₁ := 2(a−s)`, valid since `a−s > 0`; the cap covers `τ₁` since `2(a−s) < 2(h+ε) ≤ τ₀cap`).
    NOT `a₁ = R/6`. -/
theorem hEnv_window_of_amplitudeAndFdom (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hulo : 0 ≤ u - ε)
    (D : FixedFlowGateData g gi hC hK) (τ₀cap M M' CF wF : ℝ)
    (hcap : 2 * (h + ε) ≤ τ₀cap) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hCF : 0 ≤ CF) (hwF : 0 < wF)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀cap → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFdom : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        AEStronglyMeasurable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
            * F s z 0) volume)
    (hbase : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        Integrable
          (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume) :
    ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        ∃ V ∈ 𝓝 a, ∃ Dz : Point n → ℝ,
          Integrable Dz volume ∧
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume ∧
          (∀ᵐ z ∂volume, ∀ a' ∈ V,
            ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0‖
              ≤ Dz z) ∧
          (∀ᵐ z ∂volume, ∀ a' ∈ V,
            HasDerivAt
              (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
              (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s)
                * F s z 0) a') := by
  have hcap0 : 0 < τ₀cap := lt_of_lt_of_le (by positivity) hcap
  -- extract the SINGLE uniform J4-950 constant `C` valid up to the fixed cap `τ₀cap`.
  obtain ⟨C, hCpos, hbound⟩ :=
    witnessTimeDeriv_domination_global_anyS hn g gi hC hK S cutA cutB D τ₀cap M M'
      hcap0 hM hM' hAmp0 hCfield hSupp
  have hlam0 : 0 < 4 * D.lam := by have := D.hlam; linarith
  intro s hs a ha
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ha1, ha2⟩ := ha
  have hτpos : 0 < a - s := by linarith
  have hspos : 0 < s := by linarith
  have hasle : a - s < h + ε := by linarith
  -- feed the per-`(s,a)` provider with the interval `[(a−s)/2, 2(a−s)]` and `hAcrude` from J4-950.
  refine hEnv_of_witnessCrudeEnv g gi hC hK S cutA cutB F s a
    ((a - s) / 2) (2 * (a - s)) C (4 * D.lam) CF wF
    (half_pos hτpos) hlam0 hCpos.le hCF hwF hspos
    (half_lt_self hτpos) (by linarith) ?_ (hFdom s (Set.mem_Ioo.mpr ⟨hs1, hs2⟩))
    (hmeas s (Set.mem_Ioo.mpr ⟨hs1, hs2⟩) a (Set.mem_Icc.mpr ⟨ha1, ha2⟩))
    (hbase s (Set.mem_Ioo.mpr ⟨hs1, hs2⟩) a (Set.mem_Icc.mpr ⟨ha1, ha2⟩))
  -- `hAcrude`: J4-950 crude bound on `Icc ((a−s)/2) (2(a−s))`, origin-evenness rewrite.
  intro z τ hτ
  have hτ0 : 0 < τ := lt_of_lt_of_le (half_pos hτpos) hτ.1
  have hτcap : τ ≤ τ₀cap := le_trans hτ.2 (by linarith)
  rw [gaussDdim_zero_sub]
  exact hbound τ hτ0 hτcap z

/-! ###############################################################################
    ### §B — THE CAPSTONE: the concrete `H_far` far-envelope with `hEnv` reduced to amplitude + F carries.
    ############################################################################### -/

/-- **★★★ `hfar_concrete_from_amplitude` — the live `H_far` far-envelope for the concrete census
    convolution, with the engine bundle `hEnv` REDUCED to amplitude sups + F-side carries.**  Composes
    `hEnv_window_of_amplitudeAndFdom` (§A) with `hfar_concrete_of_engine` (J4-970): the opaque
    differentiation-under-∫ bundle `hEnv` is NO LONGER carried — it is supplied internally from
    `{hAmp0, hCfield, hSupp, hFdom, hmeas, hbase}`.  The remaining carriers are the honest F-side data
    `{hFmeasG, hRint}` and the rate `hrate` (= on-ball `hballrate` mod-G2 (J4-960) + off-ball envelope
    (J4-969)).  NOT `a₁ = R/6`. -/
theorem hfar_concrete_from_amplitude (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h Cpair : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hCp : 0 ≤ Cpair) (hulo : 0 ≤ u - ε)
    (D : FixedFlowGateData g gi hC hK) (τ₀cap M M' CF wF : ℝ)
    (hcap : 2 * (h + ε) ≤ τ₀cap) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hCF : 0 ≤ CF) (hwF : 0 < wF)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀cap → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (hFdom : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
        |F s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hmeas : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        AEStronglyMeasurable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
            * F s z 0) volume)
    (hbase : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
        Integrable
          (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume)
    (hFmeasG : ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (hRint : ∀ s ∈ Set.Ioo (u - ε) u,
        IntervalIntegrable
          (fun c => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
            * F s z 0) volume u (u + h))
    (hrate : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s) * F s z 0|
          ≤ Cpair * (c - s) ^ (-(1 : ℝ) / 2)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
          - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)|
        ≤ Cpair * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hEnv := hEnv_window_of_amplitudeAndFdom hn g gi hC hK S cutA cutB F u ε h
    hε hh hulo D τ₀cap M M' CF wF hcap hM hM' hCF hwF hAmp0 hCfield hSupp hFdom hmeas hbase
  exact QIQTH.HFarFTCBridgeFromEngine.hfar_concrete_of_engine
    g gi hC hK S cutA cutB F u ε h Cpair hε hh hCp hFmeasG hEnv hRint hrate

/-! ###############################################################################
    ### §C — NON-VACUITY (TEETH).  The full carrier bundle of §A is jointly satisfiable at a PROPER
    ###       (non-`univ`) gate — no unsatisfiable-antecedent trap, no cp466-style vacuity.
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `hEnv_window_of_amplitudeAndFdom`.**  For any geometry `(g, gi, hC)` with
    `n > 0`, the ENTIRE hypothesis bundle of §A — amplitude sups `{hAmp0, hCfield, hSupp}` at a PROPER
    gate `S z ≠ univ`, the cap condition, and the F-side carries `{hFdom, hmeas, hbase}` — is JOINTLY
    satisfiable (reusing the proper-gate amplitude witness `census_anyS_env_satisfiable_properGate` of
    J4-950, with `F ≡ 0` making the F-carries trivial and `u := ε := h := τ₀gate/8` giving `2(h+ε) ≤ τ₀gate`
    and `0 ≤ u−ε`).  So §A is NOT vacuously conditioned, and — crucially — the gate is PROPER (`S z ≠ univ`),
    refuting any cp466-style vacuity analogy.  NOT `a₁ = R/6`. -/
theorem hEnv_window_of_amplitudeAndFdom_hyp_satisfiable (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (cutA cutB : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (F : ℝ → Point n → Point n → ℝ) (u ε h : ℝ)
      (D : FixedFlowGateData g gi hC hK) (τ₀cap M M' CF wF : ℝ),
      0 < ε ∧ 0 ≤ h ∧ 0 ≤ u - ε ∧
      2 * (h + ε) ≤ τ₀cap ∧ 0 ≤ M ∧ 0 ≤ M' ∧ 0 ≤ CF ∧ 0 < wF ∧
      (∀ z, S z ≠ Set.univ) ∧
      (∀ τ, 0 < τ → τ ≤ τ₀cap → ∀ z ∈ K, ‖z‖ < D.r →
          |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M') ∧
      (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n,
          |F s z 0| ≤ CF * gaussDdim (wF * s) z) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          AEStronglyMeasurable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          Integrable
            (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume) := by
  obtain ⟨K, hK, S, D, τ₀g, M, M', h0K, hτ₀g, hM, hM', hS0, hSne, hAmp0, hCfield, hSupp⟩ :=
    census_anyS_env_satisfiable_properGate hn g gi hC cutA cutB
  refine ⟨K, hK, S, fun _ _ _ => 0, τ₀g / 8, τ₀g / 8, τ₀g / 8, D, τ₀g, M, M', 0, 1,
    by linarith, by linarith, by linarith, by linarith, hM, hM', le_refl 0, one_pos,
    hSne, ?_, hCfield, hSupp, ?_, ?_, ?_⟩
  · -- hAmp0 at cap `τ₀g` = the witness cap.
    exact hAmp0
  · -- hFdom: `|0| ≤ 0 · gaussDdim` trivially.
    intro s _ z; simp
  · -- hmeas: `deriv · 0 = 0`, measurable.
    intro s _ a _; simp only [mul_zero]; exact aestronglyMeasurable_const
  · -- hbase: `witness · 0 = 0`, integrable.
    intro s _ a _; simp only [mul_zero]; exact integrable_zero _ _ _

end QIQTH.HFarEnvFromAmplitude

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarEnvFromAmplitude
#print axioms hEnv_window_of_amplitudeAndFdom
#print axioms hfar_concrete_from_amplitude
#print axioms hEnv_window_of_amplitudeAndFdom_hyp_satisfiable
end AxiomChecks
