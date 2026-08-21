/-
  BaseSlotIFTOpenSuperset — J4-935: the IFT OPEN-MAP SUPERSET `Wbv '' (ball 0 ρ) ⊇ ball 0 r`,
  junction piece (4) of J4-933's `hCensusBound` re-audit.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── ★ THE CONSUMER REQUIREMENT. ──
    The base-slot change of variables (`BaseSlotChangeVariables`, J4-930) transports the census over
    the base ball `ball 0 ρ` into an integral in the IMAGE variable `w`, ranging over the CoV image
    `Wbv '' (ball 0 ρ)` where `Wbv z = uniformInverseChart g gi hC hK z 0`.  The J4-922/923 flat
    trace-cancellation machinery (`gaussian_hessian_cancel_trace_on_superset` and its
    center-Lipschitz strengthening) fires on ANY measurable `Ω ⊇ ball 0 r` (`r > 0`).  To hand the
    transported census to that machinery one needs the CoV image to CONTAIN a ball around the centre,
    i.e. the IFT open-map superset `Wbv '' (ball 0 ρ) ⊇ ball 0 r` for some `r > 0`.

  ── ★★ IT IS IMMEDIATE FROM THE BANKED IMAGE-NEIGHBOURHOOD FACT. ──
    The base-varying IFT/CoV bundle (`BaseVaryingIFTPackage.baseVaryingIFTPackage`, J4-272, re-exported
    with the weight-matching identity by `BaseSlotInverseWeightMatch.baseVaryingIFT_weightMatch`,
    J4-934) already banks `himg : Wbv '' (ball 0 ρ) ∈ 𝓝 (0 : Point n)` — the image is a NEIGHBOURHOOD
    of the centre (proved there from `OpenPartialHomeomorph.isOpen_image_of_subset_source` + the
    centre value `Wbv 0 = 0`).  `Metric.mem_nhds_iff` turns "neighbourhood of `0`" into "contains a
    metric ball around `0`": `s ∈ 𝓝 0 ↔ ∃ r > 0, ball 0 r ⊆ s`.  So the superset is a two-line
    extraction — NO new IFT, NO fresh open-map export, NO extra regularity input.

  ── WHAT IS PROVEN (conditional on the SAME single honest residual as J4-272/930/931/932/934).
    Everything here is CONDITIONAL only on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` (the geometrically-true,
    separately-bankable base-slot regularity input), inherited verbatim by CONSUMING
    `baseVaryingIFT_weightMatch`.  This file adds NO new regularity assumption.

    • `baseVaryingIFT_openSuperset` (★★): re-exports the FULL M1–M4 bundle + the weight-matching
      identity of `baseVaryingIFT_weightMatch`, AND adds the open-map superset
          `∃ r > 0, ball 0 r ⊆ Wbv '' (ball 0 ρ)`.
    • `baseVaryingIFT_imageBallSubset` (★): the lean-and-mean form — just the radii `ρ, r > 0` and the
      inclusion `ball 0 r ⊆ Wbv '' (ball 0 ρ)`, for consumers that only need the superset.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  The superset is an EXACT
  consequence of the banked image-neighbourhood fact `himg` (`Metric.mem_nhds_iff`), strictly weaker
  than and orthogonal to the CoV/`R/6` conclusion.  Non-vacuous: `himg ∈ 𝓝 0` genuinely furnishes a
  positive radius `r > 0` with an inhabited ball (`0 ∈ ball 0 r`).  No existing banked file is edited —
  this file only CONSUMES `baseVaryingIFT_weightMatch`.
-/
import Mathlib
import QIQTH.BaseSlotInverseWeightMatch

open MeasureTheory Filter Asymptotics
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.BaseVaryingIFTPackage QIQTH.BaseSlotInverseWeightMatch
open scoped Topology

namespace QIQTH.BaseSlotIFTOpenSuperset

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `baseVaryingIFT_openSuperset` — the base-varying IFT/CoV bundle PLUS the weight-matching
    identity PLUS the open-map superset `ball 0 r ⊆ Wbv '' (ball 0 ρ)`.**

    Consumes `BaseSlotInverseWeightMatch.baseVaryingIFT_weightMatch` verbatim (same hypotheses, same
    single honest residual `hbaseC2`), re-exporting its full M1–M4 bundle, the image neighbourhood, the
    exact left-inverse weight-matching identity, and — the new content — the open-map superset
        `∃ r > 0, ball 0 r ⊆ (· ↦ uic · 0) '' (ball 0 ρ)`.
    The superset is EXACT (`Metric.mem_nhds_iff` applied to the banked `himg : Wbv '' (ball 0 ρ) ∈ 𝓝 0`),
    NOT approximate.  This is junction piece (4) of J4-933's `hCensusBound` re-audit.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFT_openSuperset (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n)),
      MeasurableSet (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          HasFDerivWithinAt (fun z => uniformInverseChart g gi hC hK z 0) (f' z)
            (Metric.ball (0 : Point n) ρ) z)
      ∧ Set.InjOn (fun z => uniformInverseChart g gi hC hK z 0) (Metric.ball (0 : Point n) ρ)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ,
          V (uniformInverseChart g gi hC hK z 0) = z)
      ∧ (∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
      ∧ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n)
      ∧ (∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
          uniformInverseChart g gi hC hK (V w) 0 = w)
      -- ★ the IFT open-map superset (junction piece (4)):
      ∧ ∃ r > (0 : ℝ),
          Metric.ball (0 : Point n) r
            ⊆ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ) := by
  obtain ⟨ρ, hρ, V, f', hmeas, hM1, hM2, hM3, hM4, himg, hwm⟩ :=
    baseVaryingIFT_weightMatch g gi hC hK h0Kmem hbaseC2
  -- The banked image neighbourhood `himg ∈ 𝓝 0` contains a metric ball around `0`.
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp himg
  exact ⟨ρ, hρ, V, f', hmeas, hM1, hM2, hM3, hM4, himg, hwm, r, hr, hrsub⟩

/-- **★ `baseVaryingIFT_imageBallSubset` — the lean open-map superset alone.**  Just the base radius
    `ρ > 0` (defining the CoV domain `ball 0 ρ`), the inverse `V`, an image radius `r > 0`, and the
    inclusion `ball 0 r ⊆ Wbv '' (ball 0 ρ)`.  A convenience projection of `baseVaryingIFT_openSuperset`
    for consumers that only need the superset (e.g. to feed a measurable `Ω ⊇ ball 0 r` to J4-922/923's
    `gaussian_hessian_cancel_trace_on_superset`).  NOT `a₁ = R/6`. -/
theorem baseVaryingIFT_imageBallSubset (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ r > (0 : ℝ),
      Metric.ball (0 : Point n) r
        ⊆ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ) := by
  obtain ⟨ρ, hρ, V, f', _, _, _, _, _, _, _, r, hr, hrsub⟩ :=
    baseVaryingIFT_openSuperset g gi hC hK h0Kmem hbaseC2
  exact ⟨ρ, hρ, r, hr, hrsub⟩

end QIQTH.BaseSlotIFTOpenSuperset

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotIFTOpenSuperset
#print axioms baseVaryingIFT_openSuperset
#print axioms baseVaryingIFT_imageBallSubset
end AxiomChecks
