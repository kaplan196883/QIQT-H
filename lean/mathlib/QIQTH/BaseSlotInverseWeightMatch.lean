/-
  BaseSlotInverseWeightMatch — J4-934: the CoV LEFT-INVERSE WEIGHT-MATCHING identity
  `uic (V w) 0 = w` (EXACTLY), the junction piece (2) that gpt-5.6-sol's J4-933 re-audit flagged
  as required — beyond {base-slot CoV, det/ratio, V-transport, tail} — for the literal assembly of
  `hCensusBound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── ★ THE EXACT IDENTITY (NOT first-order). ──
    The base-varying IFT bundle (`BaseVaryingIFTPackage.baseVaryingIFTPackage`, J4-272) returns a
    left inverse `V` with M3: `∀ z ∈ ball 0 ρ, V (Wbv z) = z`, where `Wbv z = uic z 0`.  The
    downstream census, AFTER the change of variables, integrates over the IMAGE variable
    `w ∈ Wbv '' (ball 0 ρ)`, and needs the transported base-slot trace factor
    `∑ᵢ ((uic (V w) 0)ᵢ² / (4τ²) − 1/(2τ))` to collapse to the FLAT `∑ᵢ (wᵢ²/(4τ²) − 1/(2τ))`.
    That collapse holds iff `uic (V w) 0 = w` EXACTLY (Sol: else a coordinate-error term appears).

    ★ IT HOLDS EXACTLY, with NO Taylor/first-order residual, because `V` is the genuine topological
    local inverse `Φ.symm` (from `ContDiffAt.toOpenPartialHomeomorph`), NOT an approximate/linearized
    inverse.  The proof needs nothing beyond the banked M3: for `w = Wbv z` with `z ∈ ball 0 ρ`,
        `uic (V w) 0 = Wbv (V w) = Wbv (V (Wbv z)) = Wbv z = w`,
    using `V (Wbv z) = z` (M3) at the middle step.  No `Φ.right_inv` incantation is even required —
    the left inverse alone, evaluated on the image set, yields the right-inverse-on-image identity.
    gpt-5.6-sol (high) verified: exact, non-vacuous, no coordinate-error residual, provided the
    census `w` stays in `Wbv '' (ball 0 ρ)` (which it does — it IS the CoV image).

  ── WHAT IS PROVEN (conditional on the SAME single honest residual as J4-272/930/931/932).
    Everything here is CONDITIONAL only on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0` (the geometrically-true,
    separately-bankable base-slot regularity input `⟸ hT0`), inherited verbatim by CONSUMING
    `baseVaryingIFTPackage`.  This file adds NO new regularity assumption.

    • `baseVaryingIFT_weightMatch` (★★): re-exports the FULL M1–M4 bundle of `baseVaryingIFTPackage`
      AND the extra weight-matching identity `∀ w ∈ Wbv '' (ball 0 ρ), uic (V w) 0 = w`.
    • `baseVaryingIFT_rightInvOn` (★): the same identity in `Set.RightInvOn` form.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  The identity is a
  genuine EXACT consequence of the banked M3 (the census image variable lies in `Wbv '' (ball 0 ρ)`),
  strictly weaker than and orthogonal to the CoV/`R/6` conclusion.  Non-vacuous: the image set is a
  neighbourhood of `0` (banked `himg`), so the `∀` domain is inhabited.  No existing banked file is
  edited — this file only CONSUMES `baseVaryingIFTPackage`.
-/
import Mathlib
import QIQTH.BaseVaryingIFTPackage

open MeasureTheory Filter Asymptotics
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.BaseVaryingIFTPackage
open scoped Topology

namespace QIQTH.BaseSlotInverseWeightMatch

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `baseVaryingIFT_weightMatch` — the base-varying IFT/CoV bundle PLUS the exact left-inverse
    weight-matching identity `uic (V w) 0 = w` on the change-of-variables image set.**

    Consumes `BaseVaryingIFTPackage.baseVaryingIFTPackage` verbatim (same hypotheses, same single
    honest residual `hbaseC2`), re-exporting its full M1–M4 bundle and adding the identity
        `∀ w ∈ Wbv '' (ball 0 ρ), uniformInverseChart g gi hC hK (V w) 0 = w`
    where `Wbv z = uniformInverseChart g gi hC hK z 0`.  EXACT (not first-order): follows from M3
    (`V (Wbv z) = z`) evaluated on the image `w = Wbv z`.  This is junction piece (2) of J4-933's
    `hCensusBound` re-audit.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFT_weightMatch (g gi : Point n → Fin n → Fin n → ℝ)
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
      -- ★ the exact weight-matching identity on the CoV image set:
      ∧ (∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
          uniformInverseChart g gi hC hK (V w) 0 = w) := by
  obtain ⟨ρ, hρ, V, f', hmeas, hM1, hM2, hM3, hM4, himg⟩ :=
    baseVaryingIFTPackage g gi hC hK h0Kmem hbaseC2
  refine ⟨ρ, hρ, V, f', hmeas, hM1, hM2, hM3, hM4, himg, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  -- goal: uic (V (uic z 0)) 0 = uic z 0.  M3 gives V (uic z 0) = z, then rfl.
  rw [hM3 z hz]

/-- **★ `baseVaryingIFT_rightInvOn` — the weight-matching identity in `Set.RightInvOn` form.**
    States that `V` is a right inverse of `Wbv = (· ↦ uic · 0)` on the CoV image set
    `Wbv '' (ball 0 ρ)` (i.e. `Wbv ∘ V = id` there), together with the underlying bundle radius.
    A convenience repackaging of `baseVaryingIFT_weightMatch`.  NOT `a₁ = R/6`. -/
theorem baseVaryingIFT_rightInvOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ ρ > (0 : ℝ), ∃ (V : Point n → Point n),
      (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)
          ∈ 𝓝 (0 : Point n)
      ∧ Set.RightInvOn V (fun z => uniformInverseChart g gi hC hK z 0)
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) := by
  obtain ⟨ρ, hρ, V, f', _, _, _, _, _, himg, hwm⟩ :=
    baseVaryingIFT_weightMatch g gi hC hK h0Kmem hbaseC2
  exact ⟨ρ, hρ, V, himg, fun w hw => hwm w hw⟩

end QIQTH.BaseSlotInverseWeightMatch

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotInverseWeightMatch
#print axioms baseVaryingIFT_weightMatch
#print axioms baseVaryingIFT_rightInvOn
end AxiomChecks
