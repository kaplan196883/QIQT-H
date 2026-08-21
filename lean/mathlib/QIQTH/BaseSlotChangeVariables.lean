/-
  BaseSlotChangeVariables — J4-930: the BASE-slot Gaussian change-of-variables, discharging
  obstruction (i) of the `hCensusBound` wall (J4-929) — modulo the honest base-slot regularity
  residual `hbaseC2` / `hT0`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick: the base-slot mirror of J4-270's field-slot CoV.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypothesis, no
  existing banked file edited.

  ## THE WALL THIS ADDRESSES.  J4-929 (`HCrossDerivEngineWired`) localized the entire live `hCross`
  binder (h,k>0) to a SINGLE scalar census inequality `hCensusBound`, whose sole opaque residue was
  the chart change-of-variables.  gpt-5.6-sol's NO-GO audit named THREE obstructions:
    (i)   a base-slot vs field-slot CoV MISMATCH — the census integrates the BASE slot
          `uniformInverseChart g gi hC hK z 0` (base = integration var `z`, field fixed at `0`), but
          the only banked CoV `ChartIFTPackage.chart_gaussian_change_variables_concrete` (J4-270) is
          for the FIELD slot `uniformInverseChart g gi hC hK 0 z` — and the two are NOT related by
          literal negation (`GeodesicReversalRoute.baseSlot_eventuallyEq_neg_terminalVel`:
          `U z 0 =ᶠ[𝓝 0] -T₀(U 0 z)`, geodesic reversal + terminal velocity, NOT `-U 0 z`);
    (ii)  the CoV is over `ball 0 ρ`, the census over `ℝⁿ` (tail residue);
    (iii) the concrete transformed weights are unverified bounded + center-Lipschitz.

  ## WHAT THIS FILE DOES — obstruction (i) ONLY.  There is NO clean literal symmetry (confirmed: the
  base↔field swap is geodesic reversal + parallel transport, not negation).  The HONEST route is the
  base-varying IFT that the campaign ALREADY built: `BaseVaryingIFTPackage.baseVaryingIFTPackage`
  (J4-272) supplies the EXACT M1–M4 change-of-variables bundle for the base-varying chart
  `Wbv = fun z => uniformInverseChart g gi hC hK z 0`, CONDITIONAL on the single honest regularity
  input `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` — with centre-derivative invertibility supplied
  UNCONDITIONALLY by the banked quadratic displacement bound (`fderiv Wbv 0 = -id`).  That bundle is
  precisely the input the ABSTRACT `ChartGaussianChangeVar.chart_gaussian_change_variables` consumes.
  So the base-slot CoV is a DIRECT MIRROR of J4-270's `chart_gaussian_change_variables_concrete`,
  feeding the base-varying bundle instead of the field-slot bundle.

  ## WHAT LANDS.
    • `base_slot_gaussian_change_variables_of_hbaseC2` — ★★ the BASE-slot CoV, CONDITIONAL on
      `hbaseC2`:  `∫ z in ball 0 ρ, gaussDdim τ (U z 0) · B z
                    = ∫ w in Wbv''(ball 0 ρ), gaussDdim τ w · (B(V w) / |det f'(V w)|)`.
    • `base_slot_gaussian_change_variables_of_terminalVel` — ★ the same CoV, further reduced to the
      MORE FUNDAMENTAL residual `hT0 : ContDiffAt ℝ 2 (terminalVel0 …) 0` via
      `GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt`.

  ## HONEST STATUS.  This discharges obstruction (i) ONLY — the base-slot CoV is now BANKED (as a
  reusable API brick), modulo the honest, geometrically-true, separately-bankable residual
  `hbaseC2` (⟸ `hT0`).  Obstructions (ii) (`ball 0 ρ` vs `ℝⁿ` tail) and (iii) (concrete transformed
  weights bounded + center-Lipschitz) REMAIN, so `hCensusBound` / `hCross` are NOT closed.
  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6` remains CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseVaryingIFTPackage
import QIQTH.ChartGaussianChangeVar
import QIQTH.GeodesicReversalRoute

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.BaseSlotChangeVariables

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- **★★ `base_slot_gaussian_change_variables_of_hbaseC2` — the BASE-slot Gaussian change of
    variables, CONDITIONAL on `hbaseC2`.**  For the BASE-varying chart
    `Wbv = fun z => uniformInverseChart g gi hC hK z 0` (base slot varying, field fixed `0`), given the
    single honest regularity input `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, there is a radius `ρ > 0`, a left
    inverse `V`, and a derivative field `f'` with, for any `τ` and weight `B`:

        `∫ z in ball 0 ρ, gaussDdim τ (uniformInverseChart g gi hC hK z 0) · B z`
          = `∫ w in Wbv '' (ball 0 ρ), gaussDdim τ w · (B (V w) / |(f' (V w)).det|)`.

    This is the BASE-slot mirror of J4-270's `chart_gaussian_change_variables_concrete`: the M1–M4
    bundle is supplied by `BaseVaryingIFTPackage.baseVaryingIFTPackage` (whose centre-derivative
    invertibility, `fderiv Wbv 0 = -id`, is UNCONDITIONAL from the banked displacement bound), fed
    into the abstract `ChartGaussianChangeVar.chart_gaussian_change_variables`.  Discharges obstruction
    (i) of the `hCensusBound` wall — modulo the honest residual `hbaseC2`.  NOT `a₁ = R/6`. -/
theorem base_slot_gaussian_change_variables_of_hbaseC2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball (0 : Point n) ρ,
          gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w * (B (V w) / |(f' (V w)).det|) := by
  obtain ⟨ρ, hρ, V, f', hS, hfd, hinj, hV, hJpos, _⟩ :=
    QIQTH.BaseVaryingIFTPackage.baseVaryingIFTPackage g gi hC hK h0Kmem hbaseC2
  refine ⟨ρ, hρ, V, f', ?_⟩
  exact QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
    τ (Metric.ball (0 : Point n) ρ) (fun z => uniformInverseChart g gi hC hK z 0) V f'
    (fun z => |(f' z).det|) B hS hfd hinj hV (fun _ _ => rfl) hJpos

/-- **★ `base_slot_gaussian_change_variables_of_terminalVel` — the BASE-slot CoV, reduced to the
    fundamental residual `hT0`.**  The same base-slot change of variables, with the base-slot
    regularity input `hbaseC2` further reduced (via `GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt`,
    i.e. the geodesic-reversal identity `U z 0 = -T₀(U 0 z)`) to the fixed-base velocity-endpoint `C²`
    residual `hT0 : ContDiffAt ℝ 2 (terminalVel0 g gi hC hK) 0`.  NOT `a₁ = R/6`. -/
theorem base_slot_gaussian_change_variables_of_terminalVel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hT0 : ContDiffAt ℝ 2 (QIQTH.GeodesicReversalRoute.terminalVel0 g gi hC hK) (0 : Point n))
    (τ : ℝ) (B : Point n → ℝ) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      (∫ z in Metric.ball (0 : Point n) ρ,
          gaussDdim τ (uniformInverseChart g gi hC hK z 0) * B z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w * (B (V w) / |(f' (V w)).det|) :=
  base_slot_gaussian_change_variables_of_hbaseC2 g gi hC hK h0Kmem
    (QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem hT0) τ B

end QIQTH.BaseSlotChangeVariables

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseSlotChangeVariables
#print axioms base_slot_gaussian_change_variables_of_hbaseC2
#print axioms base_slot_gaussian_change_variables_of_terminalVel
end AxiomChecks
