/-
  MixedHessianBracketBound — J4-782: the OFF-DIAGONAL (mixed-index `∂ᵢ∂ⱼ`, `i ≠ j`) analogue of the
  diagonal `HessianSliceBound.polyChartDiff_abs_bound` / `RemainderIntegration.tE2_bracket_poly` — the
  POINTWISE polynomial bound on the mixed Hessian bracket MINUS its parity-cancellable leading term.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT (where this sits in the a₁=R/6 assembly).

  The `hcomp` slot of `KPrimeOpNormSliver.kPrime_opNorm_sliver_bound` needs, for EACH direction `j`, a
  scalar per-component sliver bound.  For the DIAGONAL component `j = i` that is the banked
  `XUniformSliverFull.witness_sliver2_xuniform`, whose Hessian slice is discharged through
  `tE2_bracket_poly` (the diagonal chart-jet remainder bound) + the diagonal Hermite cancellation
  `GaussianHessianCancel.gaussian_hessian_cancel`.

  For an OFF-DIAGONAL component `j ≠ i` the concrete kernel is the MIXED second field partial whose exact
  on-gate normal form (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`) has Hessian coefficient
      `⟨V,Pi⟩·⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩ + ⟨V,Q⟩)/(2τ)`
  (a PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩`, not a square, and `⟨Pi,Pj⟩` in place of the diagonal `⟨P,P⟩`).  J4-781
  (`GaussianHessianCancelMixed.gaussian_hessian_cancel_mixed`) proved the LEADING term
  `∫ (zᵢ·zⱼ)/(4τ²)·G_t·q = 0` by PARITY (the genuinely-new analytic content), leaving the SUBLEADING
  remainder — the difference `⟨V,Pi⟩·⟨V,Pj⟩ − zᵢ·zⱼ` plus the `⟨Pi,Pj⟩` and `⟨V,Q⟩` terms — which J4-781
  flagged as "higher-order, magnitude-boundable, goes through the existing moment-domination bricks with
  the coordinate-aligned `hJ3` for `Pi` and `Pj` INDIVIDUALLY".

  THIS FILE supplies exactly that pointwise polynomial bound.  A clean structural fact makes it a verbatim
  reuse of the diagonal polynomial envelope:
    • `innerYP_mul_sub_zizj_bound` — the mixed PRODUCT bridge `|⟨Y,Pi⟩·⟨Y,Pj⟩ − zᵢ·zⱼ| ≤ Δ·(Δ+2‖z‖)`,
      the SAME shape as the diagonal square bridge `innerYP_sq_sub_zi_sq_bound` (`|⟨Y,P⟩²−zᵢ²|`).
    • `innerPiPj_offdiag_bound` — the off-diagonal `|⟨Pi,Pj⟩| ≤ n·γ² + 2·γ`, the SAME numeric envelope as
      the diagonal `innerPP_sub_one_bound` (`|⟨P,P⟩−1|`).
  Hence `mixedBracket_abs_bound` has the IDENTICAL polynomial RHS as `polyChartDiff_abs_bound`, so every
  downstream moment-integration step (`tE2_slice_abstract`, `tE2RateConst`) transfers with the same
  constant — the mixed E2 remainder inherits the diagonal rate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  reusable POINTWISE ALGEBRAIC brick: the mixed-index analogue of the banked diagonal chart-jet remainder
  bound, with the parity-cancellable leading term `zᵢ·zⱼ/(4τ²)` subtracted (the term
  `gaussian_hessian_cancel_mixed` handles).  The jet-gap hypotheses (`hΔi`/`hΔj` = the individual
  coordinate-aligned first-jet gaps, `hP₁`/`hQ₁` = the second-moment / center-jet bounds) are genuine,
  load-bearing, non-vacuous (at the model `Y = −id`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0` they hold with `Δ = 0`,
  `⟨Pi,Pj⟩ = 0`, `⟨Y,Q⟩ = 0`, and the bound holds; it FAILS without them); `i ≠ j` is load-bearing (at
  `i = j` the parity term becomes the diagonal Hermite `(zᵢ²−2τ)/(4τ²)`, a DIFFERENT subtraction).  This
  brick does NOT by itself supply the mixed √ε SLIVER: it is the pointwise integrand bound; the
  moment-integration + Gaussian-replacement + full-slice reassembly + the wiring of the abstract
  `kPrime … eⱼ` to this concrete normal form remain the assembly's downstream work.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing
  file edited.  `a₁ = R/6` remains CONDITIONAL.
-/
import Mathlib
import QIQTH.HessianSliceBound

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★ The mixed PRODUCT bridge — `⟨Y,Pi⟩·⟨Y,Pj⟩ ≈ zᵢ·zⱼ`.
    ############################################################################### -/

/-- **★ Mixed product bridge — `⟨Y,Pi⟩·⟨Y,Pj⟩ ≈ zᵢ·zⱼ`.**  The off-diagonal analogue of the diagonal
    cubic bridge `innerYP_sq_sub_zi_sq_bound`.  From the two INDIVIDUAL first-jet gaps
    `|⟨Y,Pi⟩ + zᵢ| ≤ Δ` and `|⟨Y,Pj⟩ + zⱼ| ≤ Δ` (each the coordinate-aligned `hJ3` for `Pi`/`Pj`
    separately — so `⟨Y,Pi⟩ ≈ −zᵢ`, `⟨Y,Pj⟩ ≈ −zⱼ`, product `≈ zᵢ·zⱼ`),
      `|⟨Y,Pi⟩·⟨Y,Pj⟩ − zᵢ·zⱼ| ≤ Δ·(Δ + 2‖z‖)`.
    (Product split `SᵢSⱼ − zᵢzⱼ = Sᵢ(Sⱼ+zⱼ) − zⱼ(Sᵢ+zᵢ)`; `|Sᵢ| ≤ Δ + ‖z‖`, `|zⱼ| ≤ ‖z‖`.)  With
    `Δ ~ C‖z‖²` this is the CUBIC gain feeding `∫‖z‖³·G/τ² ~ τ^{−1/2}` — exactly the diagonal shape.
    NOT `a₁ = R/6`. -/
theorem innerYP_mul_sub_zizj_bound (Y z Pi Pj : Point n) (i j : Fin n) (Δ : ℝ)
    (hΔi : |(∑ k, Y k * Pi k) + z i| ≤ Δ)
    (hΔj : |(∑ k, Y k * Pj k) + z j| ≤ Δ) :
    |(∑ k, Y k * Pi k) * (∑ k, Y k * Pj k) - z i * z j| ≤ Δ * (Δ + 2 * ‖z‖) := by
  set Si : ℝ := ∑ k, Y k * Pi k with hSi
  set Sj : ℝ := ∑ k, Y k * Pj k with hSj
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hΔi
  have hzi : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
  have hzj : |z j| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z j
  -- `|Sᵢ| ≤ Δ + ‖z‖`.
  have hSieq : (Si + z i) - z i = Si := by ring
  have hSiabs : |Si| ≤ Δ + ‖z‖ := by
    rw [← hSieq]
    calc |(Si + z i) - z i| = |(Si + z i) + (-(z i))| := by rw [sub_eq_add_neg]
      _ ≤ |Si + z i| + |(-(z i))| := abs_add_le _ _
      _ = |Si + z i| + |z i| := by rw [abs_neg]
      _ ≤ Δ + ‖z‖ := by linarith [hΔi, hzi]
  -- product split.
  have hfac : Si * Sj - z i * z j = Si * (Sj + z j) - z j * (Si + z i) := by ring
  rw [hfac]
  calc |Si * (Sj + z j) - z j * (Si + z i)|
      = |Si * (Sj + z j) + (-(z j * (Si + z i)))| := by rw [sub_eq_add_neg]
    _ ≤ |Si * (Sj + z j)| + |(-(z j * (Si + z i)))| := abs_add_le _ _
    _ = |Si| * |Sj + z j| + |z j| * |Si + z i| := by rw [abs_neg, abs_mul, abs_mul]
    _ ≤ (Δ + ‖z‖) * Δ + ‖z‖ * Δ :=
        add_le_add
          (mul_le_mul hSiabs hΔj (abs_nonneg _) (by linarith [hΔ0, norm_nonneg z]))
          (mul_le_mul hzj hΔi (abs_nonneg _) (norm_nonneg z))
    _ = Δ * (Δ + 2 * ‖z‖) := by ring

/-! ###############################################################################
    ★ The off-diagonal second-moment bound — `⟨Pi,Pj⟩ ≈ 0`.
    ############################################################################### -/

/-- `∑ₖ (eᵢ)ₖ·(eⱼ)ₖ = 0` for `i ≠ j` (orthogonality of distinct standard units). -/
theorem sum_single_mul_single_offdiag (i j : Fin n) (hij : i ≠ j) :
    ∑ k, unitVec i k * unitVec j k = 0 := by
  rw [sum_mul_single_eq (unitVec i) j]
  simp only [unitVec, Pi.single_eq_of_ne (Ne.symm hij)]

/-- **★ Off-diagonal second-moment bound — `⟨Pi,Pj⟩ ≈ 0`.**  The off-diagonal analogue of the diagonal
    coercive bridge `innerPP_sub_one_bound`.  With the two individual first-jet gaps `‖Pi − eᵢ‖ ≤ γ`,
    `‖Pj − eⱼ‖ ≤ γ` (`hJ3` for `Pi`/`Pj`) and `i ≠ j` (so `⟨eᵢ,eⱼ⟩ = 0`),
      `|⟨Pi,Pj⟩| ≤ n·γ² + 2·γ`.
    (`cᵢ := Pi−eᵢ`, `cⱼ := Pj−eⱼ`; `⟨Pi,Pj⟩ = ⟨cᵢ,cⱼ⟩ + cᵢ(j) + cⱼ(i)`; `⟨cᵢ,cⱼ⟩ ≤ nγ²`, each
    center term `≤ γ`.)  The SAME numeric envelope `nγ² + 2γ` as the diagonal `|⟨P,P⟩−1|`.  On the ball
    this is the LINEAR gain feeding `∫‖z‖·G/τ ~ τ^{−1/2}`.  NOT `a₁ = R/6`. -/
theorem innerPiPj_offdiag_bound (Pi Pj : Point n) (i j : Fin n) (hij : i ≠ j) (γ : ℝ)
    (hci : ‖Pi - unitVec i‖ ≤ γ) (hcj : ‖Pj - unitVec j‖ ≤ γ) :
    |∑ k, Pi k * Pj k| ≤ (n : ℝ) * γ ^ 2 + 2 * γ := by
  have hγ0 : 0 ≤ γ := le_trans (norm_nonneg _) hci
  set ci : Point n := Pi - unitVec i with hcidef
  set cj : Point n := Pj - unitVec j with hcjdef
  have hPieq : Pi = ci + unitVec i := by rw [hcidef]; abel
  have hPjeq : Pj = cj + unitVec j := by rw [hcjdef]; abel
  -- expand the product ⟨Pi,Pj⟩ = ⟨cᵢ,cⱼ⟩ + ⟨cᵢ,eⱼ⟩ + ⟨eᵢ,cⱼ⟩ + ⟨eᵢ,eⱼ⟩.
  have hexp : (∑ k, Pi k * Pj k)
      = (∑ k, ci k * cj k) + (∑ k, ci k * unitVec j k)
        + (∑ k, unitVec i k * cj k) + (∑ k, unitVec i k * unitVec j k) := by
    rw [hPieq, hPjeq]
    have hpt : ∀ k, (ci + unitVec i) k * (cj + unitVec j) k
        = ci k * cj k + ci k * unitVec j k + unitVec i k * cj k
          + unitVec i k * unitVec j k := by
      intro k; simp only [_root_.Pi.add_apply]; ring
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
  -- evaluate the single-index sums.
  have hcomm : (∑ k, unitVec i k * cj k) = cj i := by
    rw [Finset.sum_congr rfl (fun k _ => mul_comm (unitVec i k) (cj k))]
    exact sum_mul_single_eq cj i
  rw [hexp, sum_mul_single_eq ci j, sum_single_mul_single_offdiag i j hij, hcomm, add_zero]
  -- norm bounds on the center pieces.
  have hcinorm : ‖ci‖ ≤ γ := by rw [hcidef]; exact hci
  have hcjnorm : ‖cj‖ ≤ γ := by rw [hcjdef]; exact hcj
  have hcij : |ci j| ≤ γ := le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm ci j) hcinorm
  have hcji : |cj i| ≤ γ := le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm cj i) hcjnorm
  have hinner : |∑ k, ci k * cj k| ≤ (n : ℝ) * γ ^ 2 := by
    refine (abs_inner_le ci cj).trans ?_
    have h : (n : ℝ) * ‖ci‖ * ‖cj‖ ≤ (n : ℝ) * γ * γ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcinorm (Nat.cast_nonneg n)) hcjnorm (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg n) hγ0)
    nlinarith [h]
  -- triangle over the three surviving pieces.
  calc |(∑ k, ci k * cj k) + ci j + cj i|
      ≤ |(∑ k, ci k * cj k) + ci j| + |cj i| := abs_add_le _ _
    _ ≤ (|∑ k, ci k * cj k| + |ci j|) + |cj i| := add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (n : ℝ) * γ ^ 2 + 2 * γ := by linarith [hinner, hcij, hcji]

/-! ###############################################################################
    ★★ The mixed Hessian bracket bound (mixed analogue of `polyChartDiff_abs_bound`).
    ############################################################################### -/

/-- **★★ THE MIXED HESSIAN BRACKET BOUND.**  The off-diagonal (`i ≠ j`) analogue of
    `HessianSliceBound.polyChartDiff_abs_bound`: the mixed Hessian bracket, with its parity-cancellable
    leading term `zᵢ·zⱼ/(4τ²)` subtracted, obeys the SAME explicit polynomial bound as the diagonal
    chart-jet remainder,
      `|(⟨Y,Pi⟩·⟨Y,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨Y,Q⟩)/(2τ)) − zᵢ·zⱼ/(4τ²)|
          ≤ Δ·(Δ+2‖z‖)/(4τ²) + P₁/(2τ) + Q₁/(2τ)`
    given the individual first-jet gaps `hΔi`/`hΔj` (`⟨Y,Pi⟩ ≈ −zᵢ`, `⟨Y,Pj⟩ ≈ −zⱼ`, via
    `innerYP_mul_sub_zizj_bound`), the off-diagonal second-moment bound `hP₁` (`|⟨Pi,Pj⟩| ≤ P₁`, via
    `innerPiPj_offdiag_bound`), and the center-jet bound `hQ₁` (`|⟨Y,Q⟩| ≤ Q₁`).  Route: the exact
    rearrangement `(SᵢSⱼ/(4τ²) − (PP+YQ)/(2τ)) − zᵢzⱼ/(4τ²) = (SᵢSⱼ − zᵢzⱼ)/(4τ²) − PP/(2τ) − YQ/(2τ)`,
    then triangle + the three per-term bounds.  IDENTICAL RHS to the diagonal — so the diagonal moment
    tower transfers verbatim to the mixed E2 remainder.  NOT `a₁ = R/6`. -/
theorem mixedBracket_abs_bound (Y Pi Pj Q : Point n) (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (Δ P₁ Q₁ : ℝ)
    (hΔi : |(∑ k, Y k * Pi k) + z i| ≤ Δ)
    (hΔj : |(∑ k, Y k * Pj k) + z j| ≤ Δ)
    (hP₁ : |∑ k, Pi k * Pj k| ≤ P₁)
    (hQ₁ : |∑ k, Y k * Q k| ≤ Q₁) :
    |((∑ k, Y k * Pi k) * (∑ k, Y k * Pj k) / (4 * τ ^ 2)
          - ((∑ k, Pi k * Pj k) + (∑ k, Y k * Q k)) / (2 * τ))
        - (z i * z j) / (4 * τ ^ 2)|
      ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) + P₁ / (2 * τ) + Q₁ / (2 * τ) := by
  have hτne : τ ≠ 0 := hτ.ne'
  have h4τ : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  set Si : ℝ := ∑ k, Y k * Pi k with hSi
  set Sj : ℝ := ∑ k, Y k * Pj k with hSj
  set PP : ℝ := ∑ k, Pi k * Pj k with hPP
  set YQ : ℝ := ∑ k, Y k * Q k with hYQ
  -- exact rearrangement.
  have hrw : (Si * Sj / (4 * τ ^ 2) - (PP + YQ) / (2 * τ)) - (z i * z j) / (4 * τ ^ 2)
      = (Si * Sj - z i * z j) / (4 * τ ^ 2) - PP / (2 * τ) - YQ / (2 * τ) := by
    field_simp; ring
  rw [hrw]
  -- per-term bounds.
  have hA : |(Si * Sj - z i * z j) / (4 * τ ^ 2)| ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) := by
    rw [abs_div, abs_of_pos h4τ]; gcongr
    exact innerYP_mul_sub_zizj_bound Y z Pi Pj i j Δ hΔi hΔj
  have hB : |PP / (2 * τ)| ≤ P₁ / (2 * τ) := by
    rw [abs_div, abs_of_pos h2τ]; gcongr
  have hC : |YQ / (2 * τ)| ≤ Q₁ / (2 * τ) := by
    rw [abs_div, abs_of_pos h2τ]; gcongr
  have tri3 : ∀ a b c : ℝ, |a - b - c| ≤ |a| + |b| + |c| := fun a b c => by
    have h1 : |a - b - c| ≤ |a - b| + |c| := by
      calc |a - b - c| = |(a - b) + (-c)| := by rw [sub_eq_add_neg]
        _ ≤ |a - b| + |(-c)| := abs_add_le _ _
        _ = |a - b| + |c| := by rw [abs_neg]
    have h2 : |a - b| ≤ |a| + |b| := by
      calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
        _ ≤ |a| + |(-b)| := abs_add_le _ _
        _ = |a| + |b| := by rw [abs_neg]
    linarith
  calc |(Si * Sj - z i * z j) / (4 * τ ^ 2) - PP / (2 * τ) - YQ / (2 * τ)|
      ≤ |(Si * Sj - z i * z j) / (4 * τ ^ 2)| + |PP / (2 * τ)| + |YQ / (2 * τ)| := tri3 _ _ _
    _ ≤ Δ * (Δ + 2 * ‖z‖) / (4 * τ ^ 2) + P₁ / (2 * τ) + Q₁ / (2 * τ) := by
        linarith [hA, hB, hC]

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms innerYP_mul_sub_zizj_bound
#print axioms innerPiPj_offdiag_bound
#print axioms mixedBracket_abs_bound
end AxiomChecks
