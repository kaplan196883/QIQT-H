/-
  BoundaryIntegralChartImageConcreteCoV — J4-1009: Layer A ∘ B(concrete) — wiring J4-1008's base-slot
  M1–M4 CoV bundle directly into J4-271's already-banked Layer A ∘ B(abstract) composition, producing
  the FIRST literal (non-abstract-CoV-data) chart-image rewrite of the boundary witness integral.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ORIENTATION CORRECTION (load-bearing).  J4-1008's own report (`BaseSlotM1M4Assembly.lean`)
  claimed "Layer A (the set-integral rewrite onto the gate, factoring `Wit τ 0 z` as
  `gaussDdim τ (W₀ z) · A τ z`) remains a SEPARATE, unstarted brick."  This is FALSE — Layer A was
  banked back in J4-271 (`ChartImageAIConcrete.boundary_integral_eq_gate_integral`, "★ LAYER A, CONCRETE
  & FULLY DISCHARGED") and Layer A ∘ B(abstract) was ALSO already banked there
  (`ChartImageAIConcrete.boundary_integral_eq_chartImage_integral`), for the BASE-VARYING chart
  `Wbv : z ↦ uniformInverseChart g gi hC hK z 0`.  What THAT file's own "ORIENTATION VERDICT" flagged
  as missing was the CONCRETE M1–M4 change-of-variables bundle *for `Wbv` specifically* (J4-270's
  `ChartIFTPackage` was for the field-varying `Wfv`, the wrong orientation).  J4-1008
  (`BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK`) builds EXACTLY that missing
  bundle for the general base-slot map `W p := uniformInverseChart g gi hC hK p q₀` — and at `q₀ = 0`
  this `W` IS `Wbv` on the nose.  So the two already-banked bricks compose directly; THIS FILE performs
  that composition, closing the gap J4-1008 itself misdiagnosed as unstarted.

  ## WHAT LANDS.
    • `boundary_integral_eq_chartImage_integral_concreteCoV` — ★★★★ THE PAYOFF.  For any compact `K`
      with `0 ∈ interior K`, any gate family `S`, any `a b τ f`, there is a CONCRETE radius `ρ > 0` and
      a CONCRETE left inverse `V` (both extracted from J4-1008's IFT-built open set `S'`, via
      `Metric.isOpen_iff` to shrink `S'` to a ball around `0`) such that — GIVEN the honest gate-
      activation and off-ball-support facts for that `ρ` (the only remaining hypotheses; they are the
      genuine non-analytic "which points are gated" input, not analytic CoV data) —
        `∫ z, Wit τ 0 z · f z
           = ∫ w in Wbv '' (ball 0 ρ), gaussDdim τ w · (chartFieldAmp … τ (V w) 0 · f (V w) / |det|)`.
      Unlike `ChartImageAIConcrete.boundary_integral_eq_chartImage_integral`, the CoV data
      (`f'`, `hfd`, `hinj`, `V`, `hV`, `hJpos`) is NO LONGER carried as free hypotheses of the caller —
      it is CONSTRUCTED here from the IFT package, so the only residual inputs are the gate-activation
      facts, which are honest, satisfiable, non-analytic bookkeeping (not the CoV data itself).
    Route: `BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK` at `q₀ := 0` gives an open
    `S' ∋ 0` with M1–M4; `Metric.isOpen_iff` extracts a ball `ball 0 ρ ⊆ S'`; `HasFDerivWithinAt.mono`
    / `Set.InjOn.mono` / direct weakening restrict M1/M2/M4 (and M3 trivially) from `S'` to the ball;
    feeding this into `ChartImageAIConcrete.boundary_integral_eq_chartImage_integral` gives the result.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  This file does NOT touch `nb`/`hcomp`/
  `hCConv`/`kPrime` — the boundary witness `vanVleckGatedWitness … τ 0 z` composed against a TEST
  function `f` is a DIFFERENT object from `HCompNearFarSplit`'s per-direction sliver integral of
  `kPrime`; the two threads remain SEPARATE (see the W1-wall vs R1/hcomp distinction below).  The
  Layer-C moving-integrand inputs (`hmeas`/`hbound`/`hlocal` of `chartImage_approx_identity_conditional`)
  and the gate-activation/support facts (`hGgate`/`hSupp`, still genuinely required, now at the
  CONCRETE `ρ` this file produces) remain OPEN for the W1-wall boundary-witness thread.  No `sorry`,
  no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.BaseSlotM1M4Assembly
import QIQTH.ChartImageAIConcrete

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.BoundaryIntegralChartImageConcreteCoV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★★ `boundary_integral_eq_chartImage_integral_concreteCoV`.**  THE PAYOFF: Layer A ∘ B(concrete)
for the boundary witness at a CONCRETE radius `ρ` and CONCRETE left inverse `V`, both produced from
J4-1008's IFT-built base-slot M1–M4 bundle (at `q₀ = 0`) restricted to a ball inside the open set it
supplies.  Given the gate-activation (`hGgate`) and off-ball support (`hSupp`) facts for that `ρ`, the
boundary integral against a fixed test function `f` equals the chart-image Gaussian integral over
`Wbv '' (ball 0 ρ)`.  NOT `a₁ = R/6`. -/
theorem boundary_integral_eq_chartImage_integral_concreteCoV
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ interior K)
    (S : Point n → Set (Point n)) (a b : ℝ) (τ : ℝ) (f : Point n → ℝ) :
    ∃ (ρ : ℝ) (V : Point n → Point n), 0 < ρ ∧
      ∀ (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z)
        (hSupp : ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
          vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z = 0),
      (∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w
              * (chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w)
                  / |(fderiv ℝ (fun p => uniformInverseChart g gi hC hK p 0) (V w)).det|) := by
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos⟩ :=
    QIQTH.BaseSlotM1M4Assembly.uniformInverseChart_baseSlot_M1M4_generalK g gi hC hK hK0
  obtain ⟨ρ, hρpos, hballSub⟩ := Metric.isOpen_iff.mp hS'open 0 hq0S'
  refine ⟨ρ, V, hρpos, fun hGgate hSupp => ?_⟩
  exact QIQTH.ChartImageAIConcrete.boundary_integral_eq_chartImage_integral g gi hC hK S a b τ f ρ V
    (fun z => fderiv ℝ (fun p => uniformInverseChart g gi hC hK p 0) z)
    (fun z hz => (hfd z (hballSub hz)).mono hballSub)
    (hinj.mono hballSub)
    (fun z hz => hV z (hballSub hz))
    (fun z hz => hJpos z (hballSub hz))
    hGgate hSupp

end QIQTH.BoundaryIntegralChartImageConcreteCoV

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BoundaryIntegralChartImageConcreteCoV
#print axioms boundary_integral_eq_chartImage_integral_concreteCoV
end AxiomChecks
