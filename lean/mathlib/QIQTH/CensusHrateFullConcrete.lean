/-
  CensusHrateFullConcrete — DISCHARGING the abstract full-domain rate `hrate` of the live
  `H_far` far-envelope (`HFarFullyWired.hfar_concrete_fully_wired`, J4-974) as a CONCRETE std-3
  term, by composing the on-ball census rate (`hballrate_moduloG2`, J4-960) with the off-ball
  Gaussian envelope (`offBall_env_of_derivEnv_Fbound` / `invTau_gaussDdim_offBall_absorb`, J4-969)
  and the ball→full-domain absorber (`far_rate_of_ball_and_gaussEnv`, J4-968).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  carrier-discharge / composition brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.  std-3 only.

  ## THE OBJECT — the abstract rate that J4-974 CARRIED.  `hfar_concrete_fully_wired` (J4-974) is the
  live `H_far` far-envelope for the concrete census convolution.  It internalizes the FTC-in-`c` bridge
  (via the differentiation engine `censusDeriv_hasDerivAt`, J4-929) and carries, as its LAST abstract
  analytic premise, the FULL-DOMAIN derivative-product rate
      `hrate : ∀ s ∈ Ioo(u−ε)u, ∀ c ∈ Icc u (u+h),
          |∫ z, deriv (fun r ↦ vanVleckGatedWitness … r 0 z) (c−s) · F s z 0| ≤ Cpair·(c−s)^{−1/2}` .
  The cp842 audit named this `hrate` "the dominant unknown, still importing the chart-CoV census
  assumptions".  This file REFUTES that provenance claim: the full-domain `hrate` is derivable from
  three already-banked std-3 estimates whose interfaces contain NO `hDuhamel`/`hDConv`/`hCConv`.

  ## THE COMPOSITION (gpt-5.6-sol high GO 2026-08-22).  Fix `s ∈ Ioo(u−ε)u`, `c ∈ Icc u (u+h)`; put
  `τ := c−s` (`0 < τ ≤ h+ε`).  Apply `far_rate_of_ball_and_gaussEnv` pointwise:
    • ON-BALL slot ← `hballrate_moduloG2` (J4-960): produces `ρ = δ > 0`, `Cball ≥ 0` with
        `|∫_{ball 0 δ} deriv(witness)(c−s)·F| ≤ Cball·(c−s)^{−1/2}` — from geometry + numeric window +
        the local F-regularity `{hFb, hFl}` + the G2 gate `hS` (grounded for `constGate` by
        `g2_for_constGate`, J4-962).  No `hDuhamel/hDConv/hCConv`.
    • OFF-BALL slot ← `offBall_env_of_derivEnv_Fbound` (J4-969), fed by the concrete census
        time-derivative envelope `witnessTimeDeriv_domination_global_anyS` (J4-950, from amplitude data
        `{hAmp0, hCfield, hSupp}`) and the GLOBAL F-bound `hFglob`, absorbed by
        `invTau_gaussDdim_offBall_absorb` at `q = 4·D.lam ↦ q' = 8·D.lam` and radius `ρ = δ`:
        `|deriv(witness)(c−s)·F| ≤ (Ccen·MF·Kabs)·gaussDdim (8·D.lam·(c−s)) z` for `δ ≤ ‖z‖`.  Uniform
        `Cenv := Ccen·MF·Kabs` in `(s,c)` (Kabs, Ccen fixed); the Gaussian scale `8·D.lam·(c−s)` is
        applied pointwise, only `Cenv` must be uniform.  No `hDuhamel/hDConv/hCConv`.
    • INTEGRABILITY slot ← `hgint` (an honest F-side carry: `Integrable (deriv(witness)(c−s)·F s ·)`).
  `far_rate_of_ball_and_gaussEnv` yields the full-domain rate with
      `Cfull = Cball + (Ccen·MF·Kabs)·(√2)ⁿ·√(h+ε)` (uniform in `s,c`).

  ## HONEST STATUS (blunt; gpt-5.6-sol high final audit 2026-08-22).  The full-domain `hrate` genuinely
  composes from std-3 pieces WITHOUT `{hDuhamel, hDConv, hCConv}` — those three do NOT gate the
  `H_far`/`hCross` rate branch.  Its carriers are ALL explicit: geometry, numeric window, G2 gate,
  local F-regularity `{hFb, hFl}`, amplitude sups `{hAmp0, hCfield, hSupp}`, GLOBAL F-bound `hFglob`
  (distinct from the LOCAL `hFb`), and the derivative-product integrability `hgint`.  These are honest
  F-side / geometry bookkeeping, NOT `hDuhamel/hDConv/hCConv`.  This file therefore corrects the cp842
  provenance flag on `hrate`.  It does NOT establish that the top-level `a₁ = R/6` capstone is
  conditional ONLY on `hCConv`: any Duhamel/convergence/convolution/coefficient-identification premise
  used OUTSIDE `hCross` remains load-bearing until separately audited on the rebuilt capstone.  Bank as
  a CONDITIONAL composition/discharge, following the `HFarFullyWired` posture: individual teeth are
  carried by the components; JOINT realizability of the merged bundle at a genuine curved (`n ≥ 2`,
  non-flat) witness is NOT claimed here (unknown compatibility).  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}` (with the H_far/hCross rate branch now abstract-rate-free), UNCHANGED.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusHballrateModuloG2
import QIQTH.CensusTauDerivAnySEnvelope
import QIQTH.HFarOffBallEnvFromCensus
import QIQTH.HFarOffBallDischarge
import QIQTH.HFarFullyWired

open MeasureTheory Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatResidualBound QIQTH.ParametrixFunction
open QIQTH.HeatTransportRecursion QIQTH.InverseChartNormalJets
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusHrateFullConcrete

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★ `hrate_full_concrete` — the FULL-DOMAIN derivative-product rate, DISCHARGED.**  For the
    concrete gated van-Vleck witness and a free field `F`, under the standing geometry, the numeric
    window, the local F-regularity `{hFb, hFl}`, the amplitude sups `{hAmp0, hCfield, hSupp}`, a GLOBAL
    F-bound `hFglob`, the G2 gate `hS`, and the derivative-product integrability `hgint`, there is a
    single `Cfull ≥ 0` with, for EVERY `s ∈ Ioo(u−ε)u` and EVERY `c ∈ Icc u (u+h)`,
      `|∫ z, deriv (fun r ↦ vanVleckGatedWitness … r 0 z) (c−s) · F s z 0| ≤ Cfull·(c−s)^{−1/2}` .
    This is EXACTLY the `hrate` premise-shape of `HFarFullyWired.hfar_concrete_fully_wired` (J4-974).
    It requires NONE of `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`. -/
theorem hrate_full_concrete (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (D : FixedFlowGateData g gi hC hK)
    (F : ℝ → Point n → Point n → ℝ) (u ε h τ₀ : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (M M' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r)
    (MF : ℝ) (hMFg : 0 ≤ MF) (hFglob : ∀ s z, |F s z 0| ≤ MF)
    (hS : ∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z})
    (hgint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        Integrable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
            * F s z 0) volume) :
    ∃ Cfull : ℝ, 0 ≤ Cfull ∧
      ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s) * F s z 0|
          ≤ Cfull * (c - s) ^ (-(1 : ℝ) / 2) := by
  classical
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  -- ═══ ON-BALL census rate (J4-960): produces the split radius `ρ = δ` and `Cball`. ═══
  obtain ⟨ρ, Cball, hρ0, hCball0, hball⟩ :=
    QIQTH.CensusHballrateModuloG2.hballrate_moduloG2 hn g gi hC hK S cutA cutB h0Kmem hg hg0 hu
      F u ε h τ₀ hε hτ₀ hh hcap rF M_F L_F hrF hMF hLF hFb hFl hS
  -- ═══ concrete census time-derivative envelope (J4-950), from amplitude data. ═══
  obtain ⟨Ccen, hCcen, hcensus⟩ :=
    QIQTH.CensusTauDerivAnySEnvelope.witnessTimeDeriv_domination_global_anyS hn g gi hC hK S cutA cutB
      D τ₀ M M' hτ₀ hM hM' hAmp0 hCfield hSupp
  -- ═══ off-ball `τ⁻¹`-absorption at `q = 4·D.lam ↦ q' = 8·D.lam`, radius `ρ = δ`. ═══
  obtain ⟨Kabs, hKabs, habs⟩ :=
    QIQTH.HFarOffBallEnvFromCensus.invTau_gaussDdim_offBall_absorb (n := n)
      (q := 4 * D.lam) (q' := 8 * D.lam) (ρ := ρ) (by positivity) (by linarith) hρ0
  -- ═══ the concrete off-ball Gaussian envelope on the deriv-product integrand. ═══
  have hcap' : h + ε ≤ τ₀ := by linarith
  have henv := QIQTH.HFarOffBallEnvFromCensus.offBall_env_of_derivEnv_Fbound
    (Dfun := fun τ z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) τ)
    (Ffun := fun s z => F s z 0)
    u ε h ρ τ₀ (4 * D.lam) (8 * D.lam) Ccen MF Kabs hCcen.le hMFg hcap'
    hcensus (fun s z => hFglob s z) habs
  -- ═══ the uniform full-domain constant. ═══
  have hCenv_nn : (0 : ℝ) ≤ Ccen * MF * Kabs :=
    mul_nonneg (mul_nonneg hCcen.le hMFg) hKabs.le
  refine ⟨Cball + (Ccen * MF * Kabs) * (Real.sqrt 2 ^ n * Real.sqrt (h + ε)),
    add_nonneg hCball0 (mul_nonneg hCenv_nn (by positivity)), ?_⟩
  intro s hs c hc
  have hcs : 0 < c - s := by have h1 := hs.2; have h2 := hc.1; linarith
  have hcsM : c - s ≤ h + ε := by have h1 := hc.2; have h2 := hs.1; linarith
  -- pointwise application of the ball→full-domain absorber.
  exact QIQTH.HFarOffBallDischarge.far_rate_of_ball_and_gaussEnv
    ρ (8 * D.lam * (c - s)) (Ccen * MF * Kabs) Cball (c - s) (h + ε)
    (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s) * F s z 0)
    (by positivity) hρ0.le hCenv_nn hCball0 hcs hcsM
    (hgint s hs c hc) (henv s hs c hc) (hball s hs c hc)

/-- **★★★ `hfar_concrete_rate_discharged` — the live `H_far` far-envelope with the abstract `hrate`
    REMOVED.**  Instantiates `HFarFullyWired.hfar_concrete_fully_wired` (J4-974) at the concrete
    full-domain rate produced by `hrate_full_concrete`, so the resulting declaration carries NO abstract
    `hrate` (nor `hFTC`, `hDuhamel`, `hDConv`, `hCConv`).  Its remaining assumptions are ALL explicit:
    geometry + numeric window, gate/G2 `hS`, local F-regularity `{hFb, hFl}`, GLOBAL F-bound `hFglob`,
    amplitude sups `{hAmp0, hCfield, hSupp}`, the Gaussian F-domination `hFdom`, measurability/
    integrability `{hmeas, hbase, hFslice, hgint}`, and witness-side infra `{hKm, hSm0, hIn}`.  The
    `τ₀cap` window is reused as the rate horizon (`ε+h ≤ τ₀cap` from `2(h+ε) ≤ τ₀cap`, `h+ε > 0`).
    NOT `a₁ = R/6`. -/
theorem hfar_concrete_rate_discharged (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ) (u ε h : ℝ)
    (hε : 0 < ε) (hh : 0 ≤ h) (hulo : 0 ≤ u - ε)
    (D : FixedFlowGateData g gi hC hK) (τ₀cap M M' CF wF : ℝ)
    (hcap : 2 * (h + ε) ≤ τ₀cap) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hCF : 0 ≤ CF) (hwF : 0 < wF)
    (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (MF : ℝ) (hMFg : 0 ≤ MF) (hFglob : ∀ s z, |F s z 0| ≤ MF)
    (hS : ∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z})
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
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hIn : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) cutA cutB
        (uniformInverseChart g gi hC hK) τ (0 : Point n) z)
      (volume : Measure (Point n)))
    (hFslice : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) (volume : Measure (Point n)))
    (hgint : ∀ s ∈ Set.Ioo (u - ε) u, ∀ c ∈ Set.Icc u (u + h),
        Integrable
          (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (c - s)
            * F s z 0) volume) :
    ∃ Cfull : ℝ, 0 ≤ Cfull ∧ ∀ s ∈ Set.Ioo (u - ε) u,
      |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
          - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)|
        ≤ Cfull * h * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hpe : 0 < h + ε := by linarith
  have hcaprate : ε + h ≤ τ₀cap := by linarith
  -- build the concrete full-domain rate at horizon `τ₀ := τ₀cap`.
  obtain ⟨Cfull, hCfull0, hrate⟩ :=
    hrate_full_concrete hn g gi hC hK S cutA cutB h0Kmem hg hg0 hu D F u ε h τ₀cap
      hε (by linarith) hh hcaprate rF M_F L_F hrF hMF hLF hFb hFl M M' hM hM' hAmp0 hCfield hSupp
      MF hMFg hFglob hS hgint
  refine ⟨Cfull, hCfull0, ?_⟩
  -- feed it into the fully-wired far-envelope, discharging its abstract `hrate`.
  exact QIQTH.HFarFullyWired.hfar_concrete_fully_wired hn g gi hC hK S cutA cutB F u ε h Cfull
    hε hh hCfull0 hulo D τ₀cap M M' CF wF hcap hM hM' hCF hwF hAmp0 hCfield hSupp hFdom hmeas hbase
    hKm hSm0 hIn hFslice hrate

end QIQTH.CensusHrateFullConcrete

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusHrateFullConcrete
#print axioms hrate_full_concrete
#print axioms hfar_concrete_rate_discharged
end AxiomChecks
