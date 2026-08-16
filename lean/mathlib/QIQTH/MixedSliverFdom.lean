/-
  MixedSliverFdom — J4-794: concrete discharge of the `hFdom` Gaussian-domination hypothesis of
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` at the CONCRETE Levi-series source
  `F s z y := leviSeries E s z y` (the object the J4-788 wiring feeds as `F`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is one more
  concrete "chart-surface hypothesis verification" step (J4-788 sub-task 2): the sliver rate theorem
  `witness_sliver2_xuniform_mixed` carries the two-point Gaussian domination
      `hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y, |F s z y| ≤ C_L · gaussDdim (2·s) (z − y)`.

  ## THE FINDING.  The BANKED width-2 Levi envelope `LeviSeriesLocalData.hFenv` is EXACTLY this shape at
  order `α = 0` (no `s`-power / no `1/√s` singularity — the factorial/Γ-decayed constant `C_L` alone):
      `hFenv : ∃ C_L ≥ 0, ∀ τ p q, 0 < τ → τ ≤ T → |leviSeries E τ p q| ≤ C_L · baseKernelW 2 0 τ p q`,
  and `baseKernelW 2 0 τ p q = gaussDdim (2·τ) (p − q)` (`ParametrixHEboundWiring.baseKernelW_zero_apply`).
  So `hFdom` for the concrete `F = leviSeries E` is a ONE-rewrite consequence of the `LeviSeriesLocalData`
  package `data` (which the `a₁=R/6` convergence campaign already builds for the gated van-Vleck source).
  `leviSeries_hFdom` is the generic conversion; `leviSeries_hFdom_gated` is the concrete corollary at
  `E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)` — the exact `F` of the J4-788 wiring.

  Every hypothesis is satisfiable and non-vacuous (`E ≡ 0` gives `leviSeries ≡ 0`, both sides `0`), and
  none equals the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LeviSeriesLocalData
import QIQTH.ParametrixHEboundWiring
import QIQTH.ConvApproximants

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.LeviSeriesLocalData

namespace QIQTH.MixedSliverFdom

variable {n : ℕ}

/-- **★ J4-794 — `leviSeries_hFdom` — THE SLIVER `hFdom` FROM THE BANKED LEVI PACKAGE.**  From a
    `LeviSeriesLocalData E C T` package, the concrete Levi source `F := leviSeries E` satisfies the
    EXACT two-point Gaussian domination `witness_sliver2_xuniform_mixed` demands as `hFdom`:
    `∃ C_L ≥ 0, ∀ s, 0 < s → s ≤ T → ∀ z y, |leviSeries E s z y| ≤ C_L · gaussDdim (2·s) (z − y)`.
    ONE rewrite of the banked `hFenv` envelope through `baseKernelW_zero_apply` (the `α = 0` base kernel
    IS the width-2 Gaussian).  NOT `a₁ = R/6`. -/
theorem leviSeries_hFdom (E : ℝ → Point n → Point n → ℝ) (C T : ℝ)
    (data : LeviSeriesLocalData E C T) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries E s z y| ≤ C_L * gaussDdim (2 * s) (z - y) := by
  obtain ⟨C_L, hCL0, hLdom⟩ := data.hFenv
  refine ⟨C_L, hCL0, fun s hs0 hsT z y => ?_⟩
  have h := hLdom s z y hs0 hsT
  rwa [baseKernelW_zero_apply] at h

/-- **★★ J4-794 — `leviSeries_hFdom_gated` — THE CONCRETE `hFdom` AT THE GATED VAN-VLECK LEVI SOURCE.**
    The specialization of `leviSeries_hFdom` to the EXACT source the J4-788 wiring feeds as `F`:
    `E := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)`.  Given the banked
    `LeviSeriesLocalData` package for that gated van-Vleck residual (built by the `a₁=R/6` convergence
    campaign), the `hFdom` slot of `witness_sliver2_xuniform_mixed` is discharged verbatim.
    NOT `a₁ = R/6`. -/
theorem leviSeries_hFdom_gated (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (C T : ℝ)
    (data : LeviSeriesLocalData (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s : ℝ, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z y|
        ≤ C_L * gaussDdim (2 * s) (z - y) :=
  leviSeries_hFdom (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) C T data

end QIQTH.MixedSliverFdom

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverFdom
#print axioms leviSeries_hFdom
#print axioms leviSeries_hFdom_gated
end AxiomChecks
