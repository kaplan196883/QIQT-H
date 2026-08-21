/-
  CensusTauDerivGateSplit — J4: the CENSUS-SLICE `∂_τ` EVERYWHERE IDENTITY with the ON-GATE / OFF-GATE
  SPLIT baked in — junction piece (1) [the J4-217 `hgate` carry] of J4-933's `hCensusBound` re-audit.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a pure
  differentiation-plumbing brick.  No `sorry`, no new axioms, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS RESOLVES.  J4-933's gpt-5.6-sol high re-audit flagged that `hCensusBound` is NOT assembled
  modulo only `hbaseC2`; the literal composition needs SIX residual junction carries.  This file closes
  piece **(1)** — the J4-217 `hgate` carry — for the exact CENSUS SLICE the census integrates over.

  The census (`hcross_of_censusIntegral_bound`, `HCrossDerivEngineWired`) integrates, over the base `z`,
    `deriv (fun r ↦ vanVleckGatedWitness g gi hC hK S a b r 0 z) (a−s) · F s z 0`,
  i.e. the FIELD point is FIXED at `0` and the BASE ranges over `z`.  To rewrite the `∂_τ` kernel into
  the CoV-transportable BASE-slot closed form (J4-217 `witnessTauDeriv_eq_gatedTauRepProd`) one must
  supply `hgate`, whose two conjuncts at `w = (τ, 0, z)` are
    • the GATE MEMBERSHIP `0 ∈ S z` (for every `z ∈ K`, `τ > 0`), and
    • the on-gate `HasDerivAt (fun u ↦ chartFieldAmp … u z 0) (Cfield z 0) τ`.

  ── THE ANALYTIC HALF IS BANKED + UNCONDITIONAL.  `chartFieldAmp` is AFFINE in `τ`
  (`= radialCutoff(W)·Θ(W)^{−1/2}·(u₀(W) + u₁(W)·τ)`), so its `∂_τ` HasDerivAt holds for EVERY `z, τ`
  with the explicit slope `censusAmpTauDeriv` — this is exactly `OnGateJets.chartFieldAmp_hasDerivAt_tau`.

  ── THE MEMBERSHIP HALF IS DISCHARGED BY AN OFF-GATE SPLIT (NOT forced to `S = univ`).  Rather than
  demand `0 ∈ S z` for ALL `z ∈ K` (over-strong; would force `S = univ`), we prove the EVERYWHERE
  identity whose RHS is the CoV closed form ON the gate (`z ∈ K ∧ 0 ∈ S z`) and `0` OFF it.  OFF the gate
  the gated kernel is identically `0` (`gatedKernel_apply_of_notMem`, `p = 0 ∉ S z` OR `z ∉ K`), so the
  `u`-function is `≡ 0` and its `deriv` is `0` — the RHS is `0` too (the `if` is `False`).  This mirrors
  the successful "off-gate the kernel is `0`" pattern used for `hbint` and
  `fieldHessian_fderiv_eqZero_off_jointGraph` (J4-887/888): OFF the joint gate the derivative object
  VANISHES, contributing NOTHING to the census integral, so the census reduces to the on-gate ball (the
  J4-930 CoV domain / J4-933 domain bridge).

  RESULT.  `censusTauDeriv_gateSplit` needs NO `hgate` and works for ANY `S` — piece (1) is DISCHARGED,
  not merely carried.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedTauDerivRep
import QIQTH.OnGateJets

open Classical
open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusTauDerivGateSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **`censusAmpTauDeriv` — the affine `∂_τ` slope of the census amplitude at the fixed field point `0`.**
    `chartFieldAmp g gi hC hK a b · z 0` is affine in `τ`, so its derivative is this constant slope
    `radialCutoff(W)·(Θ(W)^{−1/2}·u₁(W))`, `W = uniformInverseChart g gi hC hK z 0`.  This is the exact
    `Cfield z 0` witness (`OnGateJets.chartFieldAmp_hasDerivAt_tau`).  NOT `a₁ = R/6`. -/
noncomputable def censusAmpTauDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z : Point n) : ℝ :=
  radialCutoff a b (uniformInverseChart g gi hC hK z 0)
    * (vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2)
        * transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hC hK z 0))

/-- **★ `censusTauDeriv_eqZero_offGate` — OFF the joint census gate the `∂_τ` kernel VANISHES.**
    When `z ∉ K` or the fixed field point `0 ∉ S z`, the gated witness `fun u ↦ H_G u 0 z` is identically
    `0` (`gatedKernel_apply_of_notMem`), so its `τ`-derivative is `0` — the census integrand contributes
    NOTHING there.  This is the census analogue of `fieldHessian_fderiv_eqZero_off_jointGraph`
    (J4-887/888).  NO gate hypothesis, ANY `S`.  NOT `a₁ = R/6`. -/
theorem censusTauDeriv_eqZero_offGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (z : Point n) (τ : ℝ) (hoff : z ∉ K ∨ (0 : Point n) ∉ S z) :
    deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ = 0 := by
  have hzero : (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) = fun _ => (0 : ℝ) := by
    funext u
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ u 0 z hoff
  rw [hzero]; simp

/-- **★★ `censusTauDeriv_gateSplit` — THE CENSUS-SLICE `∂_τ` EVERYWHERE IDENTITY (piece (1) DISCHARGED).**
    For the concrete gated van-Vleck witness at the fixed field point `0`, the raw `∂_τ` kernel equals a
    three-way-dichotomy representative that is GATED on the FULL census gate `z ∈ K ∧ 0 ∈ S z`:
      • ON the gate the CoV-transportable BASE-slot closed form
        `(∑ᵢ ((W z 0)ᵢ²/(4τ²) − 1/(2τ)))·G_τ(W z 0)·A(τ) + G_τ(W z 0)·(∂_τA)`, `W = uniformInverseChart`,
        `A = chartFieldAmp … τ z 0`, `∂_τA = censusAmpTauDeriv` (the affine slope);
      • OFF the gate (`z ∉ K` or `0 ∉ S z`) both sides are `0`.
    The GATE-MEMBERSHIP conjunct of J4-217's `hgate` is discharged by the OFF-GATE SPLIT (no `S = univ`),
    the analytic `HasDerivAt` conjunct by the banked, UNCONDITIONAL
    `OnGateJets.chartFieldAmp_hasDerivAt_tau`.  Hence NO `hgate` carry and ANY `S`.  Every term carries a
    `G_τ(W z 0)` factor, so the on-gate value is `0` for `τ ≤ 0` too — matching the vanishing `deriv`.
    NOT `a₁ = R/6`. -/
theorem censusTauDeriv_gateSplit (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (z : Point n) (τ : ℝ) :
    deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ
      = if z ∈ K ∧ (0 : Point n) ∈ S z then
          ((∑ i, ((uniformInverseChart g gi hC hK z 0 i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)))
                * gaussDdim τ (uniformInverseChart g gi hC hK z 0))
              * chartFieldAmp g gi hC hK a b τ z 0
            + gaussDdim τ (uniformInverseChart g gi hC hK z 0)
                * censusAmpTauDeriv g gi hC hK a b z
        else 0 := by
  by_cases hgate : z ∈ K ∧ (0 : Point n) ∈ S z
  · obtain ⟨hzK, h0S⟩ := hgate
    rw [if_pos ⟨hzK, h0S⟩]
    set v := uniformInverseChart g gi hC hK z 0 with hvdef
    by_cases hτ : 0 < τ
    · -- ON GATE, τ > 0: the funext factorisation + product rule.
      have hamp : HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u z 0)
          (censusAmpTauDeriv g gi hC hK a b z) τ :=
        QIQTH.OnGateJets.chartFieldAmp_hasDerivAt_tau g gi hC hK a b z 0 τ
      have hfe : (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z)
          = (fun u => gaussDdim u v * chartFieldAmp g gi hC hK a b u z 0) := by
        funext u
        rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK h0S]
        simp only [chartFieldAmp, hvdef]
        ring
      have hgauss_deriv_eq : deriv (fun u => gaussDdim u v) τ
          = (∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ v := by
        rw [gaussDdim_heat_eqn τ hτ v, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i τ hτ v i)
      have hgd : DifferentiableAt ℝ (fun u => gaussDdim u v) τ := by
        have h := HasDerivAt.fun_finsetProd
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => heatKernel1D_hasDerivAt_t τ (v i) hτ)
        simpa only [gaussDdim] using h.differentiableAt
      have hg : HasDerivAt (fun u => gaussDdim u v)
          ((∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ v) τ := by
        have h0 := hgd.hasDerivAt
        rwa [hgauss_deriv_eq] at h0
      rw [hfe]
      exact (hg.mul hamp).deriv
    · -- ON GATE, τ ≤ 0: both sides `0` (shared `gaussDdim τ v` factor vanishes).
      rw [not_lt] at hτ
      have hzero_le : ∀ u : ℝ, u ≤ 0 →
          vanVleckGatedWitness g gi hC hK S a b u 0 z = 0 := by
        intro u hu
        rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b u hzK h0S,
            gaussDdim_eq_zero_of_nonpos hn u v hu]
        ring
      have hDW : HasDerivWithinAt
          (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) 0 (Set.Iic τ) τ := by
        refine (hasDerivAt_const τ (0 : ℝ)).hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
        · exact eventuallyEq_of_mem self_mem_nhdsWithin
            (fun u hu => hzero_le u (le_trans (Set.mem_Iic.mp hu) hτ))
        · exact hzero_le τ hτ
      have hderiv0 : deriv (fun u => vanVleckGatedWitness g gi hC hK S a b u 0 z) τ = 0 :=
        hDW.deriv_eq_zero (uniqueDiffWithinAt_Iic τ)
      rw [hderiv0, gaussDdim_eq_zero_of_nonpos hn τ v hτ]
      ring
  · -- OFF the joint gate: both sides `0`.
    rw [if_neg hgate]
    refine censusTauDeriv_eqZero_offGate g gi hC hK S a b z τ ?_
    by_cases hzK : z ∈ K
    · exact Or.inr (fun h0S => hgate ⟨hzK, h0S⟩)
    · exact Or.inl hzK

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/

#print axioms censusTauDeriv_eqZero_offGate
#print axioms censusTauDeriv_gateSplit

end QIQTH.CensusTauDerivGateSplit
