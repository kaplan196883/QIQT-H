/-
  §6c — the concrete NON-VACUITY witness, sealing the localized covariant μ∞.

  `localized_typicality_boost_invariant` (LocalizedCovariance.lean) takes a *pairwise-spacelike* region
  family as a hypothesis.  Here we exhibit a CONCRETE such family with ≥ 2 genuinely spacelike-separated
  regions — smooth, compactly-supported real bumps at spatially separated locations — and discharge every
  analytic hypothesis (`Krep ∈ L²` via `schwartz_Krep_memLp`, the convergence `hKint` via Cauchy–Schwarz),
  so the microcausality / boost-covariance theorems are non-vacuously instantiated.  Axiom-free.

  The 2D bump on `V = Fin 2 → ℝ` (sup norm — not an inner product space, so no direct `ContDiffBump`) is
  built as a PRODUCT of two 1D `ContDiffBump`s (ℝ has the instance).
-/
import QIQTH.Fock.LocalizedCovariance
import QIQTH.Fock.SchwartzDecay
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option linter.unusedSectionVars false

namespace QIQTH.Fock.Localization

open MeasureTheory Metric
open scoped ContDiff InnerProductSpace

/-- A fixed 1D smooth bump centered at `c`, supported in `[c−2, c+2]` (`rOut = 2`). -/
noncomputable def bump1 (c : ℝ) : ContDiffBump c := ⟨1, 2, one_pos, one_lt_two⟩

/-- The 2D real bump centered at `(cT, cX)` — a product of 1D time/space bumps. -/
noncomputable def bumpReal (cT cX : ℝ) : V → ℝ := fun x => bump1 cT (x 0) * bump1 cX (x 1)

/-- The 2D real bump as a (real-valued) complex test function. -/
noncomputable def bumpC (cT cX : ℝ) : V → ℂ := fun x => ((bumpReal cT cX x : ℝ) : ℂ)

theorem bumpReal_contDiff (cT cX : ℝ) : ContDiff ℝ ∞ (bumpReal cT cX) := by
  have h0 : ContDiff ℝ ∞ (fun x : V => bump1 cT (x 0)) :=
    (bump1 cT).contDiff.comp (contDiff_apply ℝ ℝ 0)
  have h1 : ContDiff ℝ ∞ (fun x : V => bump1 cX (x 1)) :=
    (bump1 cX).contDiff.comp (contDiff_apply ℝ ℝ 1)
  exact h0.mul h1

theorem bumpC_contDiff (cT cX : ℝ) : ContDiff ℝ ∞ (bumpC cT cX) :=
  Complex.ofRealCLM.contDiff.comp (bumpReal_contDiff cT cX)

theorem bumpC_continuous (cT cX : ℝ) : Continuous (bumpC cT cX) :=
  (bumpC_contDiff cT cX).continuous

theorem bumpC_real (cT cX : ℝ) (x : V) : (starRingEnd ℂ) (bumpC cT cX x) = bumpC cT cX x := by
  simp [bumpC]

/-- The support of the 2D bump is contained in the sup-norm "box" of half-width `2` around `(cT, cX)`. -/
theorem bumpReal_support_subset (cT cX : ℝ) :
    Function.support (bumpReal cT cX) ⊆ {x : V | |x 0 - cT| ≤ 2 ∧ |x 1 - cX| ≤ 2} := by
  intro x hx
  simp only [Function.mem_support, bumpReal, mul_ne_zero_iff] at hx
  obtain ⟨h0, h1⟩ := hx
  have hb0 : x 0 ∈ ball cT (bump1 cT).rOut :=
    (bump1 cT).support_eq ▸ Function.mem_support.mpr h0
  have hb1 : x 1 ∈ ball cX (bump1 cX).rOut :=
    (bump1 cX).support_eq ▸ Function.mem_support.mpr h1
  rw [mem_ball, Real.dist_eq] at hb0 hb1
  exact ⟨hb0.le, hb1.le⟩

theorem bumpC_hasCompactSupport (cT cX : ℝ) : HasCompactSupport (bumpC cT cX) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (|cT| + |cX| + 4)) (fun x hx => ?_)
  simp only [bumpC, Complex.ofReal_eq_zero]
  by_contra h
  obtain ⟨hT, hX⟩ := bumpReal_support_subset cT cX (Function.mem_support.mpr h)
  apply hx
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (x 0) cT
    linarith [hT, abs_nonneg cX, abs_nonneg cT]
  · rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (x 1) cX
    linarith [hX, abs_nonneg cX, abs_nonneg cT]

/-- The localized amplitude of a bump is in `L²(ℝ)` (smooth compact support ⊂ Schwartz). -/
theorem bumpC_Krep_memLp (m cT cX : ℝ) (hm : m ≠ 0) :
    MemLp (Krep m (bumpC cT cX)) 2 (volume : Measure ℝ) :=
  schwartz_Krep_memLp ((bumpC_hasCompactSupport cT cX).toSchwartzMap (bumpC_contDiff cT cX)) hm

/-- The bump as a genuine (non-zero, compactly supported) localizable test. -/
noncomputable def bumpLocalTest (m cT cX : ℝ) (hm : m ≠ 0) : LocalTest m where
  f := bumpC cT cX
  memLp := bumpC_Krep_memLp m cT cX hm

/-- **Convergence (`hKint`) for two bumps** via Cauchy–Schwarz: the product of two `L²` localized
amplitudes is `L¹`. -/
theorem bumpC_hKint (m cT1 cX1 cT2 cX2 : ℝ) (hm : m ≠ 0) :
    Integrable (fun θ => (starRingEnd ℂ) (Krep m (bumpC cT1 cX1) θ) * Krep m (bumpC cT2 cX2) θ) := by
  have h1 : MemLp (Krep m (bumpC cT1 cX1)) 2 volume := bumpC_Krep_memLp m cT1 cX1 hm
  have h2 : MemLp (Krep m (bumpC cT2 cX2)) 2 volume := bumpC_Krep_memLp m cT2 cX2 hm
  have := h1.star.integrable_mul h2
  simpa only [Pi.mul_apply, Pi.star_apply, RCLike.star_def] using this

/-- The closed support of the bump lies in the sup-norm box around its center. -/
theorem bumpC_tsupport_subset (cT cX : ℝ) :
    tsupport (bumpC cT cX) ⊆ {x : V | |x 0 - cT| ≤ 2 ∧ |x 1 - cX| ≤ 2} := by
  have hclosed : IsClosed {x : V | |x 0 - cT| ≤ 2 ∧ |x 1 - cX| ≤ 2} :=
    (isClosed_le (((continuous_apply 0).sub continuous_const).abs) continuous_const).inter
      (isClosed_le (((continuous_apply 1).sub continuous_const).abs) continuous_const)
  refine closure_minimal (fun x hx => bumpReal_support_subset cT cX ?_) hclosed
  simpa only [Function.mem_support, bumpC, Complex.ofReal_ne_zero] using hx

/-- **The two record regions are GENUINELY spacelike separated.**  Bumps centered at `(0,5)` and `(0,−5)`
have supports in boxes around `(0,±5)`, whose every pair of points has `(Δx)² ≥ 36 > 16 ≥ (Δt)²`. -/
theorem bumps_spacelike :
    ∀ x ∈ tsupport (bumpC 0 5), ∀ y ∈ tsupport (bumpC 0 (-5)), Spacelike (x - y) := by
  intro x hx y hy
  obtain ⟨hx0, hx1⟩ := bumpC_tsupport_subset 0 5 hx
  obtain ⟨hy0, hy1⟩ := bumpC_tsupport_subset 0 (-5) hy
  simp only [sub_zero] at hx0 hy0
  rw [abs_le] at hx0 hx1 hy0 hy1
  simp only [Spacelike, Pi.sub_apply]
  nlinarith [hx0.1, hx0.2, hx1.1, hx1.2, hy0.1, hy0.2, hy1.1, hy1.2]

/-- **★★★ NON-VACUITY of the localized microcausality.**  For `m ≠ 0`, two GENUINELY spacelike-separated
localizable tests (smooth compactly-supported real bumps at `(0,±5)`) have symplectically-orthogonal
localizations: `Im⟪K Lf, K Lg⟫ = 0` — a *non-vacuous* instance of the `pauli_jordan` field (NOT the
degenerate `f = 0`).  Every analytic hypothesis (`Krep ∈ L²`, the convergence `hKint`, spacelike supports)
is discharged concretely, so the whole localized boost-covariant typicality construction is non-vacuously
realized.  Axiom-free. -/
theorem localized_microcausality_nonvacuous (m : ℝ) (hm : m ≠ 0) :
    Complex.im ⟪K m (bumpLocalTest m 0 5 hm), K m (bumpLocalTest m 0 (-5) hm)⟫_ℂ = 0 :=
  K_im_inner_eq_zero_of_spacelike m hm (bumpLocalTest m 0 5 hm) (bumpLocalTest m 0 (-5) hm)
    (bumpC_continuous 0 5) (bumpC_hasCompactSupport 0 5)
    (bumpC_continuous 0 (-5)) (bumpC_hasCompactSupport 0 (-5))
    (bumpC_real 0 5) (bumpC_real 0 (-5))
    bumps_spacelike (bumpC_hKint m 0 5 0 (-5) hm)

end QIQTH.Fock.Localization
