/-
  DaLimLUOrder0Discharge — J4-763: the `hDaLimLU` loc-unif `Da`-limit (`DaLimLUGoal`) PORTED to the
  CONCRETE ORDER-0 gated cutoff-parametrix witness actually consumed by the live Seeley–DeWitt capstone
  (`GatedGlobalWitnessLeviIntInter.trueKernel_diagonal_a1_eq_R6_residual_hInt_hInter_hDH_discharged`),
  with the residual nonpositive-time vanishing member (`hEzero`) DISCHARGED INTERNALLY from geometry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / order-0-gate-porting brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypotheses, no hypothesis equal to (or trivially yielding) the conclusion, no existing
  file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT `hDaLimLU` IS, AND WHAT THIS FILE DOES.

  `hDaLimLU` is the locally-uniform `Da`-limit (the abbrev `DaLimLUWallRecon.DaLimLUGoal`)
      `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
         (fun u => Δ_g (H*F)(u) + (E*F)(u)) atTop U`,
  the sole hard residue of BOTH `hDuhamel` and `hDConv` in the order-0 Duhamel-principle reduction
  (`DuhamelLimitWiring.hDuhamel_leviSeries_final` / the `hDConv` thread).  `ETailRateBound.hDaLimLU_from_data`
  (J4-221) reduced `DaLimLUGoal g gi H F U` ENTIRELY to DATA about `H`/`F` — and it does so **abstractly
  in `H` and `F`**: the gauge (`hgi`/`hΓ`), the second-`x`-partial kernel `pdpdH`, the interchange member
  `hInterchange`, the untruncated interchange `hLapFull`, the adjacency + strip interval-integrabilities,
  the `√ε` sliver amplitudes, the two Gaussian dominations, and the `E`-combination `hEcomb`.

  `DaLimLUConcreteDischarge.hDaLimLU_concrete` (J4-266) instantiated that reduction at the DIFFERENT
  `vanVleckGatedWitness` chain (order-`N=1`), additionally discharging `hInterchange` (via the concrete
  W2 engine `witness_MemInterchange`) and `hEzero` (via `hEzeroE_concrete`).  Neither builder exists for
  the ORDER-0 `globalCutoffParametrixWitness` chain, so `hDaLimLU` was — per the J4-762 ledger entry —
  "unproven for any witness at the leaf itself, and **unported to order-0**".

  HERE we PORT the abstract reduction to the EXACT order-0 witness the live capstone uses,
      `H := gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap)`,
  and discharge ONE member INTERNALLY from geometry:
    • `hEzero` (the residual heat operator vanishing at nonpositive time) — SUPPLIED by
      `gatedGlobalWitness_residual_hEzero` (needs `1 ≤ n`); the SAME order-0 vanishing already used
      to discharge `hInt`/`hInter` in `GatedGlobalWitnessLeviIntInter` (J4-762).

  Everything else stays as the honest DATA census about the order-0 witness `H` / the source `F` —
  each a genuine satisfiable analytic fact, NONE the conclusion, none vacuous.  `hAnear` (the W1
  boundary structural wall) does NOT appear — the `Da`-limit is free of it (`hDaLimLU_from_data` never
  references it).

  ## WHY THIS ADVANCES THE ORDER-0 CHAIN.
  `hDuhamel` and `hDConv` in `trueKernel_diagonal_a1_eq_R6_residual_hInt_hInter_hDH_discharged` both
  bottleneck on `DaLimLUGoal g gi H (leviSeries (heatOp g gi H)) U` at THIS order-0 `H`.  This file
  delivers exactly that `DaLimLUGoal` (for a GENERIC source `F`, hence instantiable at
  `leviSeries (heatOp g gi H)`), reduced to the ETailRateBound data census with the order-0 `hEzero`
  already supplied — the FIRST time the `hDaLimLU` reduction is wired to the order-0
  `globalCutoffParametrixWitness` chain.  STILL CONDITIONAL; NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ETailRateBound
import QIQTH.GatedGlobalWitnessLeviIntInter

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.GaussianConvolution QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound
open scoped Interval Topology

namespace QIQTH.DaLimLUOrder0Discharge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ `hDaLimLU_order0` — the `DaLimLUGoal` `Da`-limit at the concrete order-0
    ### gated cutoff-parametrix witness, with the residual `hEzero` member discharged.
    ############################################################################### -/

/-- **★★★ J4-763 — `hDaLimLU_order0`.**  The COMPLETE `hDaLimLU` conclusion (`DaLimLUGoal`, the loc-unif
    `Da`-limit consumed by the order-0 `hDuhamel`/`hDConv` chain) at the concrete order-0 gated
    cutoff-parametrix witness
        `H := gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap)`,
    for a GENERIC source `F` (instantiable at `leviSeries (heatOp g gi H)`).

    ONE member of `ETailRateBound.hDaLimLU_from_data` is discharged INTERNALLY at the order-0 gate:
      • `hEzero` (residual heat operator vanishing at `τ ≤ 0`) — from `gatedGlobalWitness_residual_hEzero`
        (needs `1 ≤ n`); the same order-0 vanishing used in `GatedGlobalWitnessLeviIntInter` (J4-762).

    The remaining hypotheses are EXACTLY the residual DATA census (see the file header): the RNC gauge,
    the second-`x`-partial kernel `pdpdH`, the interchange `hInterchange`, the untruncated interchange
    `hLapFull`, the adjacency + strip integrabilities, the `√ε` sliver amplitudes, the residual
    width-3/2 domination `hEdom`, and the source domination/vanishing `hFdom`/`hFzero` + `hEcomb` — each
    a genuine satisfiable analytic fact about the order-0 `H` / the source `F`, NONE the conclusion,
    none vacuous.  `hAnear` (W1) does NOT appear.  Pure composition otherwise.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_order0 (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 1 ≤ n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (uu : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n)
    (F : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    -- gauge (RNC normalization at the centre):
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    -- the second-`x`-partial kernel + interchange census:
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange
        (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) F U pdpdH)
    (hLapFull : MemLapFull g gi
        (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) F U pdpdH)
    (hII_lo : MemAdjLo F U pdpdH) (hII_hi : MemAdjHi F U pdpdH)
    -- the `√ε` sliver amplitudes:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- the residual + source dominations, with the uniform time window:
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    -- the residual strip integrabilities of the `E·F` inner pairing:
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) (u - s) 0 z
              * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) (u - s) 0 z
              * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi
        (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) F) :
    DaLimLUGoal g gi (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) F U := by
  -- ★ the residual nonpositive-time vanishing, DISCHARGED from geometry (`1 ≤ n`).
  have hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) τ p q = 0 :=
    gatedGlobalWitness_residual_hEzero g gi hn K S Θ uu a b Vmap
  -- thread into the abstract DATA-reduced `Da`-limit at the order-0 witness.
  exact hDaLimLU_from_data g gi
    (gatedKernel K S (globalCutoffParametrixWitness Θ uu a b Vmap)) F T U hUopen
    hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT hEdom hEzero hFdom hFzero hIlo hIhi hEcomb

end QIQTH.DaLimLUOrder0Discharge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUOrder0Discharge.hDaLimLU_order0
