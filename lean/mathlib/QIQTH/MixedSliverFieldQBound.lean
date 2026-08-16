/-
  MixedSliverFieldQBound — the CONCRETE per-point (ball) supplier for the mixed sliver's `hJ3Q` at the
  van-Vleck inverse chart, via the FIELD-POINT (not base-point) second-jet Hessian contraction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is one
  geometry-layer analytic brick of the a₁=R/6 mixed-sliver campaign's chart-surface residue.

  ── WHAT IT CORRECTS.  J4-798 supplied `chartW0_secondJet_bound`, an operator-norm Hessian bound of the
  inverse chart at the ORIGIN field point, with the BASE point `z` varying — flagged (J4-800(c)) as "one
  contraction away" from the sliver's vector `Q`.  But the mixed sliver
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` carries `hJ3Q : ∀ z, ‖Q z‖ ≤ C_Q` where `z` is the
  INTEGRATION (field) variable and `Q z` is the concrete mixed second field-partial
  `∂ᵢ∂ⱼ (uniformInverseChart … 0)(z)` of the FIXED base-`0` chart at the VARYING field point `z`
  (`ChartJetHessianMixed.gatedMixed2RepProd`'s `Qfield 0 z` slot: the `HasDerivAt`-derivative of the first
  jet `Pjfield` in the `i`-direction).  That is the field-varying Hessian of the fixed chart — NOT the
  base-varying, origin-evaluated object `chartW0_secondJet_bound` bounds.  So (c) is not "one contraction
  away" from that lemma; it needs the field-point Hessian, supplied here.

  ── WHAT LANDS (all DERIVED; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * (A) `hessianContract_bounded_on_ball` — the reusable PURE brick: for `φ : E → F'` with
      `ContDiffAt ℝ 2 φ x₀` and any `u v : E`, the once-contracted second Fréchet derivative
      `z ↦ (fderiv (fderiv φ) z) u v` is bounded on a ball around `x₀`:
          `∃ r > 0, ∃ C ≥ 0, ∀ z ∈ ball x₀ r, ‖(fderiv (fderiv φ) z) u v‖ ≤ C`.
      Proof: `ContDiffAt 2` ⟹ `fderiv (fderiv φ)` continuous at `x₀`; CLM-evaluation `L ↦ L u v` is
      continuous, so the F'-valued map `z ↦ (fderiv (fderiv φ) z) u v` is continuous at `x₀`; its norm is
      then `≤ ‖·(x₀)‖ + 1` on a neighborhood.
    * (B) `chartField_secondJet_contract_ball` — the CONCRETE discharge for the van-Vleck inverse chart:
      an explicit `r > 0`, `C_Q ≥ 0` with, for every field point `z ∈ ball 0 r`,
          `‖(fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK 0) y) z) (unitVec i) (unitVec j)‖ ≤ C_Q`,
      the `Point n`-vector whose `k`-component is the concrete `Qfield 0 z k = ∂ᵢ∂ⱼ(inverse chart)_k(z)`.
      Assembles (A) with the base-`0` chart's field-slot `C²` at `0`
      (`ChartFieldC2General.chartField_contDiffAt_basePoint_viaIFT`, needing `0 ∈ K`).

  ── HONEST SCOPE.  Like `chartW0_secondJet_bound` / `chartW0_firstJet_gap`, this is per-point on a BALL,
  not the GLOBAL `∀ z` form; the global form is obtained by the already-built gating layer
  (`MixedSliverGatedEstimates.gateQ_bound_global`, setting `Q := 0` off the ball).  Every hypothesis is
  satisfiable and non-vacuous (`φ` any `C²` map; `0 ∈ K` genuine), and none equals the conclusion.  NOT
  `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartFieldC2General
import QIQTH.SliverAssembly

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.ChartFieldC2General
open scoped Topology

/-! ############################################################################
    ### (A) The pure reusable brick — second-jet contraction bounded on a ball.
    ############################################################################ -/

namespace QIQTH.MixedSliverFieldQBound

/-- **★ (A) `hessianContract_bounded_on_ball`.**  For `φ : E → F'` with `ContDiffAt ℝ 2 φ x₀` and any
    directions `u v : E`, the once-contracted second Fréchet derivative
    `z ↦ (fderiv ℝ (fderiv ℝ φ) z) u v` is bounded on a ball around `x₀`.  Proof: `ContDiffAt 2` gives
    continuity of `fderiv (fderiv φ)` at `x₀`; CLM-evaluation `L ↦ L u v` is continuous, so the
    `F'`-valued map `z ↦ (fderiv (fderiv φ) z) u v` is continuous at `x₀`, hence its norm stays
    `≤ ‖·(x₀)‖ + 1` on a neighborhood.  ⚠ NOT `a₁ = R/6`. -/
theorem hessianContract_bounded_on_ball
    {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (φ : E → F') (x₀ : E) (hφ : ContDiffAt ℝ 2 φ x₀) (u v : E) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ z ∈ Metric.ball x₀ r,
      ‖(fderiv ℝ (fun y => fderiv ℝ φ y) z) u v‖ ≤ C := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x₀ := hφ.fderiv_right (by norm_num)
  have hcont : ContinuousAt (fun y => fderiv ℝ (fderiv ℝ φ) y) x₀ :=
    h1.continuousAt_fderiv (by norm_num)
  -- The `F'`-valued evaluation `z ↦ (fderiv (fderiv φ) z) u v` is continuous at `x₀`
  -- (CLM evaluation composed with `hcont`); hence so is its scalar norm.
  have e1 := (ContinuousLinearMap.apply ℝ (E →L[ℝ] F') u).continuous
  have e2 := (ContinuousLinearMap.apply ℝ F' v).continuous
  have hev2 : ContinuousAt (fun z => (fderiv ℝ (fderiv ℝ φ) z) u v) x₀ :=
    ((e2.comp e1).continuousAt).comp hcont
  have hgc : ContinuousAt (fun z => ‖(fderiv ℝ (fderiv ℝ φ) z) u v‖) x₀ := hev2.norm
  set C : ℝ := ‖(fderiv ℝ (fderiv ℝ φ) x₀) u v‖ + 1 with hCdef
  have hClt : ‖(fderiv ℝ (fderiv ℝ φ) x₀) u v‖ < C := by rw [hCdef]; linarith
  have hev : ∀ᶠ z in 𝓝 x₀, ‖(fderiv ℝ (fderiv ℝ φ) z) u v‖ ≤ C :=
    (hgc.eventually_lt_const hClt).mono (fun z hz => le_of_lt hz)
  obtain ⟨r, hr0, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr0, C, by positivity, fun z hz => ?_⟩
  exact hball (Metric.mem_ball.mp hz)

end QIQTH.MixedSliverFieldQBound

/-! ############################################################################
    ### (B) The concrete van-Vleck field-point discharge.
    ############################################################################ -/

namespace QIQTH.HeatResidualBound

open QIQTH.MixedSliverFieldQBound

variable {n : ℕ}

/-- **★ (B) `chartField_secondJet_contract_ball` — the mixed-sliver `hJ3Q` shape for the CONCRETE
    van-Vleck inverse chart at the FIELD point, per-point on a ball.**  For the fixed base-`0` chart
    (`0 ∈ K`), there is `r > 0` and `C_Q ≥ 0` such that for every FIELD point `z ∈ ball 0 r` the mixed
    second field-jet contraction is uniformly bounded:
        `‖(fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK 0) y) z) (unitVec i) (unitVec j)‖ ≤ C_Q`.
    This is the `Point n`-vector whose `k`-component is the concrete `Qfield 0 z k = ∂ᵢ∂ⱼ(chart)_k(z)`
    that the mixed sliver carries in its `hJ3Q` slot.  Proof: the base-`0` chart is field-slot `C²` at
    `0` (`chartField_contDiffAt_basePoint_viaIFT`); feed it to the pure brick
    `hessianContract_bounded_on_ball` with `u = eᵢ`, `v = eⱼ`.  ⚠ NOT `a₁ = R/6` — the GLOBAL `∀ z` form
    needs the gating layer (`MixedSliverGatedEstimates.gateQ_bound_global`). -/
theorem chartField_secondJet_contract_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) (i j : Fin n) :
    ∃ r > (0 : ℝ), ∃ C_Q : ℝ, 0 ≤ C_Q ∧ ∀ z ∈ Metric.ball (0 : Point n) r,
      ‖(fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK 0) y) z)
          (unitVec i) (unitVec j)‖ ≤ C_Q := by
  have hφ : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK 0) (0 : Point n) :=
    chartField_contDiffAt_basePoint_viaIFT g gi hC hK 0 hK0
  obtain ⟨r, hr0, C, hC0, hbound⟩ :=
    hessianContract_bounded_on_ball (uniformInverseChart g gi hC hK 0) (0 : Point n) hφ
      (unitVec i) (unitVec j)
  exact ⟨r, hr0, C, hC0, hbound⟩

end QIQTH.HeatResidualBound

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverFieldQBound QIQTH.HeatResidualBound
#print axioms hessianContract_bounded_on_ball
#print axioms chartField_secondJet_contract_ball
end AxiomChecks
