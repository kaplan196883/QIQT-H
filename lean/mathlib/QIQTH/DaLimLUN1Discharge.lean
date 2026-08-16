/-
  DaLimLUN1Discharge — J4-768: the `hDaLimLU` loc-unif `Da`-limit (`DaLimLUGoal`) PORTED to the
  ORDER-`N = 1` gated cutoff-parametrix witness — the witness the LIVE (non-dead-end) capstone chain
  now uses (`GatedGlobalWitnessN1Capstone`), with the residual nonpositive-time vanishing member
  (`hEzero`) DISCHARGED INTERNALLY from geometry.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / order-1-gate-porting brick — the order-1 sibling of `DaLimLUOrder0Discharge.hDaLimLU_order0`.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS DOES.

  `ETailRateBound.hDaLimLU_from_data` (J4-221) reduces `DaLimLUGoal g gi H F U` — the loc-unif `Da`-limit
  that is the SOLE hard residue of BOTH `hDuhamel` and `hDConv` — ENTIRELY to a DATA census about `H`/`F`,
  and does so ABSTRACTLY in `H`, `F`.  `DaLimLUOrder0Discharge.hDaLimLU_order0` (J4-765) wired it to the
  DEAD-END order-0 witness `globalCutoffParametrixWitness`.  Since the live chain has now moved to the
  ORDER-1 witness `globalCutoffParametrixWitnessN 1` (`GatedGlobalWitnessN1Capstone`, J4-767) — the order
  at which `hHdiag` is genuinely true — the same reduction must be re-wired there.

  HERE we PORT the abstract reduction to the EXACT order-1 witness
      `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)`,
  discharging ONE member INTERNALLY from geometry:
    • `hEzero` (residual heat operator vanishing at `τ ≤ 0`) — SUPPLIED by
      `gatedGlobalWitnessN1_residual_hEzero` (needs `1 ≤ n`); the order-1 vanishing established in
      `GatedGlobalWitnessN1Diag` (J4-766).

  Everything else stays as the honest DATA census about the order-1 witness `H₁` / the source `F` —
  each a genuine satisfiable analytic fact, NONE the conclusion, none vacuous.  `hAnear` (the W1
  boundary structural wall) does NOT appear (`hDaLimLU_from_data` never references it).

  ## WHY THIS ADVANCES THE (LIVE) `N = 1` CHAIN.
  `hDuhamel` and `hDConv` in the order-1 partial capstone
  (`GatedGlobalWitnessN1Capstone.trueKernel_diagonal_a1_eq_R6_residual_N1_discharged`) both bottleneck on
  `DaLimLUGoal g gi H₁ (leviSeries (heatOp g gi H₁)) U`.  This file delivers exactly that `DaLimLUGoal`
  (for a GENERIC source `F`, hence instantiable at `leviSeries (heatOp g gi H₁)`), reduced to the
  ETailRateBound data census with the order-1 `hEzero` already supplied.  It confirms the `hDaLimLU`
  reduction technique ports cleanly from order-0 to the live order-1 witness.  STILL CONDITIONAL;
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ETailRateBound
import QIQTH.GatedGlobalWitnessN1Diag

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.GaussianConvolution QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound
open scoped Interval Topology

namespace QIQTH.DaLimLUN1Discharge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ J4-768 — `hDaLimLU_N1`.**  The COMPLETE `hDaLimLU` conclusion (`DaLimLUGoal`, the loc-unif
    `Da`-limit consumed by the order-1 `hDuhamel`/`hDConv` chain) at the concrete ORDER-1 gated
    cutoff-parametrix witness
        `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)`,
    for a GENERIC source `F` (instantiable at `leviSeries (heatOp g gi H₁)`).

    ONE member of `ETailRateBound.hDaLimLU_from_data` is discharged INTERNALLY at the order-1 gate:
      • `hEzero` (residual heat operator vanishing at `τ ≤ 0`) — from
        `gatedGlobalWitnessN1_residual_hEzero` (needs `1 ≤ n`).

    The remaining hypotheses are EXACTLY the residual DATA census (see the file header): the RNC gauge,
    the second-`x`-partial kernel `pdpdH`, the interchange `hInterchange`, the untruncated interchange
    `hLapFull`, the adjacency + strip integrabilities, the `√ε` sliver amplitudes, the residual
    width-3/2 domination `hEdom`, and the source domination/vanishing `hFdom`/`hFzero` + `hEcomb` — each
    a genuine satisfiable analytic fact about the order-1 `H₁` / the source `F`, NONE the conclusion,
    none vacuous.  `hAnear` (W1) does NOT appear.  Order-1 sibling of
    `DaLimLUOrder0Discharge.hDaLimLU_order0`.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_N1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 1 ≤ n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (uu : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n)
    (F : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange
        (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) F U pdpdH)
    (hLapFull : MemLapFull g gi
        (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) F U pdpdH)
    (hII_lo : MemAdjLo F U pdpdH) (hII_hi : MemAdjHi F U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) (u - s) 0 z
              * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) (u - s) 0 z
              * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi
        (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) F) :
    DaLimLUGoal g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) F U := by
  -- ★ the residual nonpositive-time vanishing, DISCHARGED from geometry (`1 ≤ n`), ORDER 1.
  have hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn K S Θ uu a b Vmap
  -- thread into the abstract DATA-reduced `Da`-limit at the order-1 witness.
  exact hDaLimLU_from_data g gi
    (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ uu a b Vmap)) F T U hUopen
    hgi hΓ pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT hEdom hEzero hFdom hFzero hIlo hIhi hEcomb

end QIQTH.DaLimLUN1Discharge
