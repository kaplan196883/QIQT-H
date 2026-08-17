/-
  WitnessThirdPartialUniformBound — Task D (plan v3, JET4_TOWER_PLAN Jet-4 tower / hCConv route):
  package `InverseChartFieldC3.witnessField_contDiffAt3_center`'s field-`C³` into an EXPLICIT local
  bound on the third field-partial `∂³_p H` of the concrete gated van-Vleck witness `H`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  packaging brick of the `hCConv` convergence route (the "p-block" of the joint-Lipschitz assembly).
  No `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no result that is a
  conclusion-in-disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS DELIVERS (the p-block bound), AND THE EXACT SCOPE OF "UNIFORM".

  `InverseChartFieldC3.witnessField_contDiffAt3_center` gives `ContDiffAt ℝ 3` of the witness FIELD
  slice at the chart base `q = 0`:
      `p ↦ vanVleckGatedWitness g gi hChr hK S a b t p 0`   is  `ContDiffAt ℝ 3`  at `p = 0`.
  It is an EXISTENCE statement (`ContDiffAt`), carrying no explicit derivative bound.  This file runs
  the standard "`ContDiffAt` ⟹ locally bounded iterated derivative" step
  (`ContDiffAt.continuousAt_iteratedFDeriv` at order `3` ⟹ `ContinuousAt` of `iteratedFDeriv ℝ 3` ⟹ a
  local sup bound on a ball) to expose an EXPLICIT `(M, r)`:
      `∃ M r, 0 ≤ M ∧ 0 < r ∧ ∀ p, ‖p‖ < r → ‖iteratedFDeriv ℝ 3 (H(·,0)) p‖ ≤ M`.
  This is exactly the p-block third-partial bound that the transposition-chain consumer needs.

  ── ON "UNIFORM OVER A q-NEIGHBOURHOOD" (the scoped target's phrasing).  The p-block bound is delivered
     here at the CHART BASE `q = 0`.  Extending the SAME `M` to all `q` in a neighbourhood of `0`
     (a single constant valid for every `q`-slice) would require joint continuity of the third field-
     partial `∂³_p H` in the base slot `q` — precisely the regularity the chart's per-base
     `Classical.choose` construction does NOT provide (the `.choose`-incoherence firewall: no continuity
     of the third partial across distinct base points; see JET4_TOWER_PLAN J4-836 / plan v3 §"v3 Context").
     So an arbitrary-`q`-uniform constant is NOT available from banked pieces and is NOT claimed here.

  ── WHY THE `q = 0` BOUND IS THE RIGHT p-BLOCK INPUT ANYWAY.  In the transposition assembly (Task F),
     the difference `Φ(0,z) − Φ(z,0)` (where `Φ(p,q) = ∂ⱼ∂ᵢ[p'↦H(p',q)](p)`) is chained through the
     ORIGIN `(0,0)`:
        `Φ(0,z) − Φ(z,0) = [Φ(0,z) − Φ(0,0)] + [Φ(0,0) − Φ(z,0)]`.
     The SECOND bracket varies `p` from `0` to `z` at FIXED base `q = 0` — the p-segment — whose
     mean-value control needs `∂_p Φ = ∂³_p H` bounded exactly on the `q = 0` slice near `p = 0`.
     (The FIRST bracket is the q-block, at fixed `p = 0`; that is Task E.)  So the `q = 0` p-block
     bound proved here is precisely what the origin-chained transposition estimate consumes for the
     p-segment; no arbitrary-`q`-uniform constant is required for that route.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS.
    * `witnessThirdPartial_localBound_center` — ★ explicit `(M, r)` local sup bound on
        `‖iteratedFDeriv ℝ 3 (fun p ↦ vanVleckGatedWitness … t p 0) p‖` on the ball `‖p‖ < r`, from
        the banked field-`C³` (`witnessField_contDiffAt3_center`).  This is the p-block third-partial
        bound of the joint-Lipschitz assembly, at the chart base `q = 0`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.InverseChartFieldC3

open MeasureTheory
open QIQTH.Curvature QIQTH.ExpMap QIQTH.ChartThirdJet
open QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation QIQTH.HeatParametrixOrder
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound QIQTH.PullbackMetric
open scoped BigOperators Topology ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

/-- **★ `witnessThirdPartial_localBound_center` — the explicit p-block third-partial bound.**
    From the banked field-`C³` of the witness diagonal slice at the chart base `q = 0`
    (`witnessField_contDiffAt3_center`), produce an EXPLICIT local sup bound on its third field
    Fréchet derivative: there are `M ≥ 0` and a radius `r > 0` such that
        `∀ p, ‖p‖ < r → ‖iteratedFDeriv ℝ 3 (fun p' ↦ vanVleckGatedWitness … t p' 0) p‖ ≤ M`.
    Standard "`ContDiffAt` ⟹ locally bounded iterated derivative": `ContDiffAt ℝ 3` gives
    `ContinuousAt (iteratedFDeriv ℝ 3 …)` at `0`, and a continuous function is bounded on a small
    ball (its value at `0` plus `1`, on the ball where it stays below that).  This is the p-block
    third-partial bound of the transposition-chain joint-Lipschitz assembly, at `q = 0`.
    NOT `a₁ = R/6`. -/
theorem witnessThirdPartial_localBound_center
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hSopen : IsOpen (S 0))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ M r : ℝ, 0 ≤ M ∧ 0 < r ∧ ∀ p : Point n, ‖p‖ < r →
      ‖iteratedFDeriv ℝ 3 (fun p' => vanVleckGatedWitness g gi hChr hK S a b t p' 0) p‖ ≤ M := by
  -- the banked field-`C³` of the `q = 0` witness slice.
  set f : Point n → ℝ := fun p' => vanVleckGatedWitness g gi hChr hK S a b t p' 0 with hf
  have hC3 : ContDiffAt ℝ 3 f (0 : Point n) :=
    witnessField_contDiffAt3_center g gi hChr hK S a b t hK0 hS0 hSopen hg hg0 hu
  -- `ContDiffAt ℝ 3` ⟹ `ContinuousAt` of the third iterated Fréchet derivative at `0`.
  have hcont : ContinuousAt (iteratedFDeriv ℝ 3 f) (0 : Point n) :=
    hC3.continuousAt_iteratedFDeriv (by norm_num)
  -- a continuous function is bounded (by its value at `0` plus `1`) on a small ball around `0`.
  set M : ℝ := ‖iteratedFDeriv ℝ 3 f (0 : Point n)‖ + 1 with hM
  have hMnonneg : 0 ≤ M := by positivity
  have hlt : ‖iteratedFDeriv ℝ 3 f (0 : Point n)‖ < M := by rw [hM]; linarith
  have hev : ∀ᶠ p in 𝓝 (0 : Point n),
      ‖iteratedFDeriv ℝ 3 f p‖ ≤ M := by
    have htend := (hcont.norm).tendsto
    filter_upwards [htend.eventually_lt tendsto_const_nhds hlt] with p hp using le_of_lt hp
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  refine ⟨M, r, hMnonneg, hr, fun p hp => ?_⟩
  exact hball (by rw [dist_eq_norm, sub_zero]; exact hp)

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms witnessThirdPartial_localBound_center
end AxiomChecks
