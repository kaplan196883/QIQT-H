/-
  HFarFTCBridgeFromEngine — DISCHARGE the FTC-in-`c` bridge `hFTC` of J4-967's `H_far` reduction,
  for the CONCRETE frozen convolution, from the ALREADY-BANKED census-integral time-`HasDerivAt`
  (`censusDeriv_hasDerivAt`, J4-929, engine-wired) + Mathlib's fundamental theorem of calculus.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE bridge brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT J4-967 (`HFarFromBallrate.lean`) LEFT.  `hfar_of_ballrate_ftc` / `_conv` produce the exact
  live `H_far` far-envelope
      `∀ s ∈ Ioo(u−ε)u, |Φ(u+h,s) − Φ(u,s)| ≤ Cpair·h·(u−s)^{−1/2}`,   `Φ(c,s) := ∫ z, A(c−s) x z·B s z y`,
  from (i) a `hballrate`-shaped pointwise-in-`c` rate `hrate` and (ii) the **FTC-in-`c` bridge**
      `hFTC : ∀ s ∈ Ioo(u−ε)u, Φ(u+h,s) − Φ(u,s) = ∫ c in u..(u+h), R c s`.
  J4-967/968/969 CARRIED `hFTC` abstractly.  This file DISCHARGES `hFTC` for the CONCRETE census
  convolution `A := vanVleckGatedWitness …`, `x = 0`, `B := F`, `y = 0`, with the rate integrand
  `R c s := ∫ z, deriv(fun r ↦ witness r 0 z)(c−s)·F s z 0`.

  ## THE COMPOSITION (routine, but genuine).  Mathlib's FTC-2
      `intervalIntegral.integral_eq_sub_of_hasDerivAt : (∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) →
        IntervalIntegrable f' volume a b → ∫ y in a..b, f' y = f b − f a`
  applied with `f := fun a' ↦ Φ(a',s)`, `f' := fun c ↦ R c s`, `a := u`, `b := u+h` gives EXACTLY
  `∫ c in u..(u+h), R c s = Φ(u+h,s) − Φ(u,s)` (whence `hFTC` by `.symm`), from
    • the per-`c` `HasDerivAt` `∀ c ∈ Icc u (u+h), HasDerivAt (fun a' ↦ Φ(a',s)) (R c s) c` — supplied
      by the ENGINE-wired `censusDeriv_hasDerivAt` (J4-929, differentiation-under-the-`z`-integral,
      banked; its per-`(s,c)` engine-carry bundle `hEnv` is the SAME one `hcross_of_censusIntegral_bound`
      consumes, non-vacuously inhabited by `hEnv_of_witnessCrudeEnv` = J4-916), and
    • `IntervalIntegrable (fun c ↦ R c s) volume u (u+h)` — the integrability carry `hRint` (already on
      `H_far`'s carrier list).
  Since `0 ≤ h`, `uIcc u (u+h) = Icc u (u+h)`, matching the `hEnv`/`censusDeriv_hasDerivAt` domain.

  ## WHAT THIS DOES — AND DOES NOT — DO.  It supplies the concrete `hFTC` from the ALREADY-BANKED
  differentiation-under-∫ engine + FTC + integrability — so the "FTC-in-`c` bridge" is NO LONGER an
  abstractly-carried premise for the concrete convolution: it reduces to {the engine `hEnv` bundle
  (banked, modulo the accepted census crude-env amplitude data + G3 F-bound), slice-measurability
  `hFmeasG`, `IntervalIntegrable` of `R`}.  Composed with `hfar_of_ballrate_ftc_conv` (J4-967) and the
  concrete rate `hrate` (on-ball `hballrate` mod-G2 (J4-960) + off-ball envelope (J4-969)), it yields
  `H_far` for the concrete convolution modulo ONLY the standard carried carriers.

  It does NOT discharge `hballrate`, the integrability `hRint`, or the G3 F-bound; it does NOT touch the
  chart-CoV SCALAR census inequality (= the opaque chart wall inside `hrate`).  It discharges NONE of
  `{hballrate, hDuhamel, hDConv, hCConv}` as a top-level τ-carry.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCrossDerivEngineWired
import QIQTH.HFarFromBallrate

open MeasureTheory Set
open QIQTH.Curvature QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.HFarFTCBridgeFromEngine

variable {n : ℕ}

/-! ###############################################################################
    ### §A — the ABSTRACT FTC-in-`c` adapter (pure Mathlib FTC-2 wrapper).
    ############################################################################### -/

/-- **★★ `hFTC_of_hasDerivAt` — the abstract FTC-in-`c` bridge.**  For ANY `Φ R : ℝ → ℝ → ℝ`, given
    `0 ≤ h`, a per-`c` time-`HasDerivAt` of `a' ↦ Φ(a',s)` with derivative `R c s` on `uIcc u (u+h)`,
    and interval-integrability of `c ↦ R c s` on `[u, u+h]`, the finite difference equals the
    `c`-integral of the rate:
        `∀ s ∈ Ioo(u−ε)u, Φ(u+h,s) − Φ(u,s) = ∫ c in u..(u+h), R c s`.
    Pure `.symm` of `intervalIntegral.integral_eq_sub_of_hasDerivAt`.  NOT `a₁ = R/6`. -/
theorem hFTC_of_hasDerivAt (Φ R : ℝ → ℝ → ℝ) (u ε h : ℝ)
    (hderiv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.uIcc u (u + h),
        HasDerivAt (fun a => Φ a s) (R c s) c)
    (hint : ∀ s ∈ Set.Ioo (u - ε) u,
        IntervalIntegrable (fun c => R c s) volume u (u + h)) :
    ∀ s ∈ Set.Ioo (u - ε) u, Φ (u + h) s - Φ u s = ∫ c in u..(u + h), R c s := by
  intro s hs
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (hderiv s hs) (hint s hs)).symm

/-! ###############################################################################
    ### §B — the CONCRETE census FTC bridge (engine-wired `HasDerivAt` + FTC + integrability).
    ############################################################################### -/

/-- **★★★ `censusFTC_bridge` — the FTC-in-`c` bridge for the CONCRETE census convolution.**  For the
    concrete gated van-Vleck witness `A := vanVleckGatedWitness g gi hC hK S cutA cutB` and frozen field
    `F`, with `0 ≤ h`, GIVEN
      • `hFmeasG` — the global slice-measurability the engine needs,
      • `hEnv` — the per-`(s,c)` engine-carry bundle (SAME bundle `hcross_of_censusIntegral_bound`
        consumes; inhabited by `hEnv_of_witnessCrudeEnv`, J4-916), and
      • `hRint` — interval-integrability of the rate `c ↦ ∫ z, ∂_τ(witness)(c−s)·F` on `[u,u+h]`,
    the finite difference of the census convolution equals the `c`-integral of its time-rate:
        `∀ s ∈ Ioo(u−ε)u,
           (∫ z, witness(u+h−s) 0 z·F s z 0) − (∫ z, witness(u−s) 0 z·F s z 0)
             = ∫ c in u..(u+h), (∫ z, deriv(fun r ↦ witness r 0 z)(c−s)·F s z 0)`.
    This is EXACTLY the `hFTC` premise `hfar_of_ballrate_ftc_conv` (J4-967) consumes.  Route: FTC-2
    (`hFTC_of_hasDerivAt`) fed the engine `HasDerivAt` `censusDeriv_hasDerivAt` (J4-929) at each `c`.
    NOT `a₁ = R/6`. -/
theorem censusFTC_bridge
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h : ℝ) (hh : 0 ≤ h)
    (hFmeasG : ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (hEnv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
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
                * F s z 0) a'))
    (hRint : ∀ s ∈ Set.Ioo (u - ε) u,
        IntervalIntegrable
          (fun c => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
            * F s z 0) volume u (u + h)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
        - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
        = ∫ c in u..(u + h),
            (∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
              * F s z 0) := by
  refine hFTC_of_hasDerivAt
    (fun c s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (c - s) 0 z * F s z 0)
    (fun c s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
      * F s z 0)
    u ε h ?_ hRint
  intro s hs c hc
  rw [Set.uIcc_of_le (by linarith : u ≤ u + h)] at hc
  obtain ⟨V, hV, Dz, hDz, hFint, hF'meas, hbnd, hdiff⟩ := hEnv s hs c hc
  exact censusDeriv_hasDerivAt g gi hC hK S cutA cutB F s c (hFmeasG s) V hV Dz hDz hFint
    hF'meas hbnd hdiff

/-! ###############################################################################
    ### §C — THE CAPSTONE: `H_far` for the concrete convolution, FTC bridge DISCHARGED.
    ############################################################################### -/

/-- **★★★ `hfar_concrete_of_engine` — the live `H_far` far-envelope for the CONCRETE census
    convolution, with the FTC-in-`c` bridge DISCHARGED via the banked engine.**  Composes
    `censusFTC_bridge` (§B, the now-DISCHARGED `hFTC`) with `hfar_of_ballrate_ftc_conv` (J4-967) to
    produce the exact live `H_far` argument shape
        `∀ s ∈ Ioo(u−ε)u,
           |(∫ z, witness(u+h−s) 0 z·F s z 0) − (∫ z, witness(u−s) 0 z·F s z 0)|
             ≤ Cpair·h·(u−s)^{−1/2}`,
    from {`hFmeasG`, the engine bundle `hEnv`, integrability `hRint`, and the `hballrate`-shaped rate
    `hrate`}.  The FTC-in-`c` bridge is NO LONGER an abstractly-carried premise: it is supplied
    internally by the engine.  The ONLY remaining analytic carry is `hrate` (= on-ball `hballrate`
    mod-G2 (J4-960) + off-ball envelope (J4-969)) plus the integrability `hRint` and the engine
    bundle `hEnv`.  NOT `a₁ = R/6`. -/
theorem hfar_concrete_of_engine
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (u ε h Cpair : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hCp : 0 ≤ Cpair)
    (hFmeasG : ∀ s u' : ℝ, AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume)
    (hEnv : ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
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
                * F s z 0) a'))
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
  have hFTC := censusFTC_bridge g gi hC hK S cutA cutB F u ε h hh hFmeasG hEnv hRint
  exact QIQTH.HFarFromBallrate.hfar_of_ballrate_ftc_conv
    (vanVleckGatedWitness g gi hC hK S cutA cutB) F 0 0
    (fun c s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
      * F s z 0)
    u ε h Cpair hε hh hCp hFTC hrate

/-! ###############################################################################
    ### §D — NON-VACUITY (TEETH).  The abstract FTC bridge is satisfiable at a genuinely
    ###       non-affine, singular-rate witness with the derivative genuinely ACTIVE.
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of `hFTC_of_hasDerivAt`.**  The per-`c` `HasDerivAt` hypothesis and the
    interval-integrability are JOINTLY satisfiable at the GENUINELY non-affine witness
        `Φ c s := Real.sin (c − s)`,   `R c s := Real.cos (c − s)`,
    with `u = 0, ε = 1, h = 1`, and the resulting FTC identity `sin(1−s) − sin(−s) = ∫_0^1 cos(c−s) dc`
    holds with a genuinely NON-CONSTANT rate (`R (u+h) s = cos(1−s) ≠ 0` on a subwindow — the
    derivative is genuinely ACTIVE, NOT `0 = 0`).  Confirms the bridge is not vacuously conditioned. -/
theorem hFTC_of_hasDerivAt_hyp_satisfiable :
    ∃ (Φ R : ℝ → ℝ → ℝ) (u ε h : ℝ),
      0 < ε ∧ 0 ≤ h ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.uIcc u (u + h),
          HasDerivAt (fun a => Φ a s) (R c s) c) ∧
      (∀ s ∈ Set.Ioo (u - ε) u,
          IntervalIntegrable (fun c => R c s) volume u (u + h)) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, Φ (u + h) s - Φ u s = ∫ c in u..(u + h), R c s) ∧
      R 1 (-1/2) ≠ 0 := by
  refine ⟨fun c s => Real.sin (c - s), fun c s => Real.cos (c - s), 0, 1, 1,
    one_pos, zero_le_one, ?_, ?_, ?_, ?_⟩
  · -- per-`c` HasDerivAt: `a ↦ sin(a−s)` has derivative `cos(c−s)` at `c`.
    intro s _ c _
    have h1 : HasDerivAt (fun a : ℝ => a - s) (1 : ℝ) c := by
      simpa using (hasDerivAt_id c).sub_const s
    simpa using (Real.hasDerivAt_sin (c - s)).comp c h1
  · -- interval-integrability of `c ↦ cos(c−s)`.
    intro s _
    exact (Real.continuous_cos.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  · -- FTC identity via `hFTC_of_hasDerivAt` applied to this witness.
    refine hFTC_of_hasDerivAt (fun c s => Real.sin (c - s)) (fun c s => Real.cos (c - s)) 0 1 1
      ?_ ?_
    · intro s _ c _
      have h1 : HasDerivAt (fun a : ℝ => a - s) (1 : ℝ) c := by
        simpa using (hasDerivAt_id c).sub_const s
      simpa using (Real.hasDerivAt_sin (c - s)).comp c h1
    · intro s _
      exact (Real.continuous_cos.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  · -- teeth: `cos(1 − (−1/2)) = cos(3/2) ≠ 0`.
    show Real.cos (1 - -1 / 2) ≠ 0
    rw [show ((1 : ℝ) - -1 / 2) = 3/2 by norm_num]
    have h32 : (3/2 : ℝ) < Real.pi / 2 := by
      have := Real.pi_gt_three
      linarith
    have hpos : 0 < Real.cos (3/2) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_gt_three], h32⟩
    exact ne_of_gt hpos

end QIQTH.HFarFTCBridgeFromEngine

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HFarFTCBridgeFromEngine
#print axioms hFTC_of_hasDerivAt
#print axioms censusFTC_bridge
#print axioms hfar_concrete_of_engine
#print axioms hFTC_of_hasDerivAt_hyp_satisfiable
end AxiomChecks
