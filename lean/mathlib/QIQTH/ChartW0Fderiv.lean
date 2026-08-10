/-
  ChartW0Fderiv — J4-516: the base-slot chart centre derivative `fderiv W₀ 0 = -id` and its
  unit-modulus Jacobian `|det (fderiv W₀ 0)| = 1` (M4), as STANDALONE pinnable lemmas.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ★ DON'T-UNDERCREDIT VERDICT (J4-516).  The J4-515 note claimed M4 (`|det DW₀(0)| = 1`) was
  BLOCKED because the base-point derivative `fderiv (z ↦ W₀ z) 0` was "unbanked" (the `.choose`-built
  chart; the displacement bound `chartW0_displacement` "only for z ∈ K").  That is STALE.  The
  J4-272 / J4-278 line (`BaseVaryingIFTPackage` / `EnrichedChartBundle`) had ALREADY executed exactly
  the KEY INSIGHT the J4-516 mission proposed to test:
    • `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center` derives `HasFDerivAt W₀ (-id) 0`
      UNCONDITIONALLY (given `K ∈ 𝓝 0`) from the banked quadratic displacement bound
      `‖W₀ z + z‖ ≤ C_W‖z‖²` (`chartW0_displacement`) — the compact-`K` bound is upgraded to the
      eventual-near-0 little-o form by `filter_upwards` against `K ∈ 𝓝 0`, precisely the mission's
      proposal.  It is NOT faked from a compact-only bound: the genuine neighbourhood is the honest
      interior-basepoint hypothesis `K ∈ 𝓝 0`.
    • `EnrichedChartBundle.enrichedChartBundle` already CONTAINS the conjunct
      `|det (fderiv W₀ 0)| = 1` (proven via `det(-id) = (-1)ⁿ`, `|(-1)ⁿ| = 1`; AxiomAudit-pinned).

  This file simply EXTRACTS the two facts as standalone, directly-consumable, pinnable lemmas (they
  were previously only available buried inside the 13-way `enrichedChartBundle` conjunction), reusing
  `baseVaryingChart_hasFDerivAt_center`.  No new mathematics; NO `sorry`, no new axioms, no `:= True`.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  M4 is DIMENSION-ONLY
  (`|det(-I)| = |(-1)ⁿ| = 1`), curved-generic — the displacement bound is curved-generic and no
  `hframeK` / `g = δ` enters.  M4 is ONE ingredient of the concrete change-of-variables, not the
  curved witness.
-/
import Mathlib
import QIQTH.BaseVaryingIFTPackage

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.ChartW0Fderiv

variable {n : ℕ}

/-- **★ `chartW0_hasFDerivAt_zero` — the base-slot chart centre derivative is `-id`.**  Restates
    `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center` with the derivative in the plain
    `-ContinuousLinearMap.id` form.  DERIVED from the banked quadratic displacement bound
    `‖W₀ z + z‖ ≤ C_W‖z‖²` (`chartW0_displacement`) together with `K ∈ 𝓝 0` — the compact-`K` bound
    upgraded to the eventual-near-0 little-o form; NOT faked from a compact-only bound.
    ⚠ NOT `a₁ = R/6`. -/
theorem chartW0_hasFDerivAt_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    HasFDerivAt (fun z => uniformInverseChart g gi hC hK z 0)
      (-ContinuousLinearMap.id ℝ (Point n)) (0 : Point n) := by
  have h := QIQTH.BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center g gi hC hK h0Kmem
  have hcoe : ((ContinuousLinearEquiv.neg ℝ : Point n ≃L[ℝ] Point n) : Point n →L[ℝ] Point n)
      = -ContinuousLinearMap.id ℝ (Point n) := by ext x; simp
  rwa [hcoe] at h

/-- **★ `chartW0_fderiv_zero` — `fderiv W₀ 0 = -id`.**  Immediate from the centre derivative
    (`HasFDerivAt.fderiv`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartW0_fderiv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)
      = -ContinuousLinearMap.id ℝ (Point n) :=
  (chartW0_hasFDerivAt_zero g gi hC hK h0Kmem).fderiv

/-- **★★ `chartW0_absdet_fderiv_zero` — M4, STANDALONE: `|det (fderiv W₀ 0)| = 1`.**  The centre
    derivative is `-id`, whose determinant is `(-1)ⁿ`, of modulus `1`.  DIMENSION-ONLY,
    curved-generic (no `hframeK`, no `g = δ`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartW0_absdet_fderiv_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n)).det| = 1 := by
  rw [chartW0_fderiv_zero g gi hC hK h0Kmem]
  have hL : (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
      Point n →ₗ[ℝ] Point n) = (-1 : ℝ) • LinearMap.id := by ext x; simp
  show |LinearMap.det (((-ContinuousLinearMap.id ℝ (Point n)) : Point n →L[ℝ] Point n) :
      Point n →ₗ[ℝ] Point n)| = 1
  rw [hL, LinearMap.det_smul, LinearMap.det_id, mul_one, abs_pow]
  norm_num

end QIQTH.ChartW0Fderiv

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.ChartW0Fderiv.chartW0_hasFDerivAt_zero
#print axioms QIQTH.ChartW0Fderiv.chartW0_fderiv_zero
#print axioms QIQTH.ChartW0Fderiv.chartW0_absdet_fderiv_zero
