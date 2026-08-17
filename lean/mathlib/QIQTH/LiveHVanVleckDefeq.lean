/-
  LiveHVanVleckDefeq — the formal dissolution of the "kernel-family mismatch" wall (J4-817 wall #3).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It records a
  DEFINITIONAL identity: the LEFT kernel `H` carried by the live order-1 reach-aligned capstone
  (`GatedGlobalWitnessN1CapstoneReachAligned.trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned`),
  namely
      `gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`,
  is DEFINITIONALLY EQUAL to `vanVleckGatedWitness g gi hChr hK S a b` — because the latter is DEFINED
  (ConvApproximants.lean) as exactly that expression.

  ── WHY THIS MATTERS (ledger correction).  J4-817 listed as its wall #3 that the capstone `hCConv` is
  about a kernel `H = gatedKernel K S (globalCutoffParametrixWitnessN 1 …)` that is "a DIFFERENT kernel
  than `vanVleckGatedWitness g gi hC hK S a b`", on which the entire mixed/diagonal sliver campaign
  (J4-780→817) was built.  That characterization is INCORRECT: the two are the SAME kernel, up to
  definitional unfolding (and Lean's definitional proof-irrelevance for the chart-smoothness proof
  argument `hChr`/`hC`).  Consequently the closed sliver bounds of J4-817
  (`SliverGatedFullyCombined.witness_sliver2_xuniform_{mixed,diag}_gated_fullyCombined`, stated in terms
  of `vanVleckGatedWitness`) already speak about the capstone's own `H`; NO kernel-family bridge is
  needed.  The `hCConv`/`hDuhamel`/`hDConv` GOALS on the two spellings are the SAME goal, discharged by
  `rfl` (`live_hCConv_goal_eq` below): any spatial-`C²` supply stated at `vanVleckGatedWitness` is,
  definitionally, a supply for the live capstone's `hCConv` slot.

  ── WHAT REMAINS (unaffected by this file).  The genuine remaining wall for `hCConv` is NOT the kernel
  family: it is that the `kPrime`→normal-form bridges (`KPrime{Mixed,Diag}PdBridge`) put the second
  partial `∂²H` at the FIXED field point `x` with the SOURCE slot = the integration variable, whereas
  the closed sliver bounds differentiate at the INTEGRATION variable with the source slot FIXED — a
  field↔source transposition with no symmetry supplier yet.  This file removes wall #3 from the ledger;
  it does not touch that transposition.  STILL CONDITIONAL; NOT `a₁ = R/6`.  No `sorry`, no new axioms,
  no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1CapstoneReachAligned
import QIQTH.ConvApproximants

open MeasureTheory
open QIQTH.Curvature QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.PullbackMetric QIQTH.ParametrixFunction
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **★ WALL #3 IS DEFINITIONAL.**  The live order-1 reach-aligned capstone's left kernel `H` — the
    gated, radially cut-off order-1 van-Vleck parametrix in the uniform inverse chart — is
    DEFINITIONALLY equal to `vanVleckGatedWitness g gi hChr hK S a b`, on which the entire J4-780→817
    sliver campaign was built.  Proof: `rfl` (the RHS is defined to be the LHS).  NOT `a₁ = R/6`. -/
theorem live_H_eq_vanVleckGatedWitness
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    gatedKernel K S
        (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK))
      = vanVleckGatedWitness g gi hChr hK S a b := rfl

/-- **★★ The capstone `hCConv` GOAL is the `vanVleckGatedWitness` `hCConv` goal.**  The spatial map whose
    `ContDiffAt ℝ 2`-at-`0` the live capstone's `hCConv` slot demands — with `H` the capstone's own left
    kernel — is DEFINITIONALLY the same map written at `vanVleckGatedWitness`.  Hence a spatial-`C²`
    supply proved at `vanVleckGatedWitness` discharges the capstone's `hCConv` slot directly (by `rfl`),
    with NO kernel-family reconciliation.  The `heatOp`/`leviSeries`/`heatConv` layers all agree
    definitionally.  NOT `a₁ = R/6`. -/
theorem live_hCConv_goal_eq
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ) :
    (fun p : Point n =>
        heatConv
          (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK)))
          (leviSeries (heatOp g gi
            (gatedKernel K S
              (globalCutoffParametrixWitnessN 1 (vanVleck g)
                (transportCoeff (transportOp (vanVleck g) g gi)) a b
                (uniformInverseChart g gi hChr hK))))) t p 0)
      = (fun p : Point n =>
          heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0) := rfl

end QIQTH.HeatResidualBound
