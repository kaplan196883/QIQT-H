/-
  GaussTauTraceCancellation — the n-D `∂_τ`-TRACE moment-cancellation Lipschitz bound: the
  `hCross` sub-campaign's flat-coordinate assembly of the banked per-coordinate Hessian cancellation
  (J4-124 `gaussian_hessian_cancel`) into the EXACT multiplier form appearing in the concrete
  witness `∂_τ` representative (`GatedTauDerivRep.gatedTauRepProd`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the flat/chart-coordinate `∂_τ`-trace analogue of the banked
  1-D core (J4-919 `integral_DtauG_mul_lipschitz`), decoupled from `H`'s amplitude, from the Levi
  series `F`, from the census, and from the global `∀ h, k` range of `hCross`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS BRICK.  The concrete census kernel is n-DIMENSIONAL: the integration variable is a
  field point `z : Point n`, and the `∂_τ` of the van-Vleck witness (banked `gatedTauRepProd`) carries
  the multiplier
        `∑ᵢ ((vᵢ)²/(4τ²) − 1/(2τ))`      (`v` the chart image of `z`)
  against the Gaussian `gaussDdim τ v`.  By the flat heat equation `∂_τ G = ΔG = ∑ᵢ ∂ᵢ²G`
  (`gaussDdim_heat_eqn`), this multiplier is EXACTLY the trace of the per-coordinate Hessian factors
  `∂ᵢ²G / G = ((zᵢ)²−2τ)/(4τ²)`.  The J4-919 core was 1-D; the census needs the n-D trace form.  The
  n-D PER-COORDINATE cancellation is ALREADY banked (J4-124 `gaussian_hessian_cancel`,
  `|∫ ((zᵢ)²−2τ)/(4τ²)·G·q| ≤ L·(15/2·n)/√τ`); this file assembles the TRACE (sum over `i`) — the
  flat-coordinate form of piece (i) of the `hCross` route.

  ## WHAT LANDS.
    • `gaussian_hessian_cancel_trace` — for `τ>0`, `q` Lipschitz (const `L≥0`, bounded, measurable),
        `|∫_{z:Point n} (∑ᵢ ((zᵢ)²/(4τ²) − 1/(2τ)))·gaussDdim τ z·q(z)| ≤ L·(15/2·n²)/√τ` ,
      stated in the SYNTACTICALLY EXACT multiplier form `∑ᵢ ((zᵢ)²/(4τ²) − 1/(2τ))` of
      `gatedTauRepProd`.  Route: the trace multiplier factors the integrand into the finite sum
      `∑ᵢ ((zᵢ)²−2τ)/(4τ²)·G·q`; `integral_finsetSum` + triangle + `gaussian_hessian_cancel` per
      coordinate collapses the `τ`-powers to the `τ^{−1/2}` (integrable) singularity, `n` coordinates
      each `≤ L·(15/2·n)/√τ` ⟹ `L·(15/2·n²)/√τ`.
    • `gaussian_hessian_cancel_trace_hyp_satisfiable` — non-vacuity EXHIBITED at a genuine NONCONSTANT
      bounded Lipschitz weight `q z := cos (dist z 0)` (`|q|≤1`, `L=1`), so the bound fires on a real
      weight, not an empty/unsatisfiable bundle.

  ⚠  STILL NOT `a₁ = R/6`.  The CONCRETE-census bridge (`|∂_x g(x,s)| ≲ (x−s)^{−1/2}` for the actual
  chart-COMPOSED Gaussian `gaussDdim τ (W z)` against the resolvent weight `F s z 0`) remains an open
  downstream wall: the exact moment cancellation ∫∂_τG=0 holds in the Gaussian's OWN coordinate `v`,
  but the census integrates `dz` with `v = W(z)` a NONLINEAR chart map, so the Jacobian `|det DW|`
  breaks the exact cancellation unless `W` is affine (RNC center-only gauge).  Wiring this trace bound
  through the change of variables (transformed-weight Lipschitz/Jacobian remainder) is NOT done here.
  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, none equal to the conclusion, no
  existing file edited.
-/
import Mathlib
import QIQTH.GaussianHessianCancel

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianPolyBound QIQTH.GaussianConvolution

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- Per-coordinate integrability of the Hessian-weighted Gaussian against a bounded measurable weight
    `q` (reconstructed exactly as inside `gaussian_hessian_cancel`). -/
theorem hess_coord_gaussDdim_q_integrable (t : ℝ) (ht : 0 < t) (i : Fin n)
    (q : Point n → ℝ) (hqmeas : AEStronglyMeasurable q volume) (M : ℝ) (hM : ∀ z, |q z| ≤ M) :
    Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z) volume := by
  have hHessG_int : Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z) volume := by
    have heq : (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z)
        = fun z => (4 * t ^ 2)⁻¹ * ((z i) ^ 2 * gaussDdim t z)
            - (4 * t ^ 2)⁻¹ * (2 * t) * gaussDdim t z := by
      funext z; rw [div_eq_mul_inv]; ring
    rw [heq]
    exact ((coordSq_gaussDdim_integrable t ht i).const_mul _).sub
      ((gaussDdim_integrable' t ht).const_mul _)
  exact hHessG_int.mul_bdd hqmeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hM z))

/-- **★★★ `gaussian_hessian_cancel_trace` — THE n-D `∂_τ`-TRACE MOMENT-CANCELLATION BOUND.**  For
    `t>0`, `i`-trace multiplier `∑ᵢ ((zᵢ)²/(4t²) − 1/(2t))` (`= ∂_τ gaussDdim / gaussDdim` by the flat
    heat equation), and `q` Lipschitz (const `L≥0`, bounded, measurable),
        `|∫_{z:Point n} (∑ᵢ ((zᵢ)²/(4t²) − 1/(2t)))·gaussDdim t z·q(z)| ≤ L·(15/2·n²)/√t` .
    The trace multiplier splits the integrand into `∑ᵢ ((zᵢ)²−2t)/(4t²)·G·q`; `integral_finsetSum`
    + triangle + the banked per-coordinate `gaussian_hessian_cancel` (each `≤ L·(15/2·n)/√t`) over the
    `n` coordinates gives `L·(15/2·n²)/√t`.  Stated in the EXACT multiplier shape of `gatedTauRepProd`.
    NOT `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace (t : ℝ) (ht : 0 < t) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hq : ∀ z w, |q z - q w| ≤ L * dist z w)
    (hqmeas : AEStronglyMeasurable q volume) (hqbdd : ∃ M, ∀ z, |q z| ≤ M) :
    |∫ z : Point n, (∑ i, ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * gaussDdim t z * q z|
      ≤ L * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt t := by
  obtain ⟨M, hM⟩ := hqbdd
  have htne : t ≠ 0 := ht.ne'
  -- The trace multiplier factors the integrand into the finite sum over coordinates.
  have hpt : ∀ z : Point n,
      (∑ i, ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * gaussDdim t z * q z
        = ∑ i, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z := by
    intro z
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : (z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t) = ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) := by
      field_simp; ring
    rw [hc]
  have hint : ∀ i : Fin n, Integrable
      (fun z : Point n => ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z) volume :=
    fun i => hess_coord_gaussDdim_q_integrable t ht i q hqmeas M hM
  calc |∫ z : Point n, (∑ i, ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) * gaussDdim t z * q z|
      = |∫ z : Point n, ∑ i, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z| := by
        rw [integral_congr_ae (ae_of_all _ hpt)]
    _ = |∑ i, ∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z| := by
        rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    _ ≤ ∑ i, |∫ z : Point n, ((z i) ^ 2 - 2 * t) / (4 * t ^ 2) * gaussDdim t z * q z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, L * (15 / 2 * (n : ℝ)) / Real.sqrt t :=
        Finset.sum_le_sum
          (fun i _ => gaussian_hessian_cancel t ht i q L hL hq hqmeas ⟨M, hM⟩)
    _ = L * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Non-vacuity witness.**  The hypothesis bundle of `gaussian_hessian_cancel_trace` is jointly
    satisfiable by a genuine NONCONSTANT bounded Lipschitz weight: `q z := cos (dist z 0)` has
    `|q z − q w| ≤ 1·dist z w` (`cos` 1-Lipschitz ∘ 1-Lipschitz `dist(·,0)`), `|q z| ≤ 1`, and is
    continuous (hence measurable).  So the bound fires on a real weight, not an empty bundle.  NOT
    `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace_hyp_satisfiable :
    ∃ (L : ℝ) (q : Point n → ℝ), 0 ≤ L ∧ (∀ z w, |q z - q w| ≤ L * dist z w) ∧
      AEStronglyMeasurable q (volume : Measure (Point n)) ∧ (∃ M, ∀ z, |q z| ≤ M) := by
  refine ⟨1, fun z => Real.cos (dist z (0 : Point n)), zero_le_one, ?_, ?_, ⟨1, ?_⟩⟩
  · intro z w
    show |Real.cos (dist z (0 : Point n)) - Real.cos (dist w (0 : Point n))| ≤ 1 * dist z w
    rw [one_mul]
    exact (Real.abs_cos_sub_cos_le _ _).trans (abs_dist_sub_le z w (0 : Point n))
  · exact (Real.continuous_cos.comp (continuous_id.dist continuous_const)).aestronglyMeasurable
  · intro z; exact Real.abs_cos_le_one _

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms hess_coord_gaussDdim_q_integrable
#print axioms gaussian_hessian_cancel_trace
#print axioms gaussian_hessian_cancel_trace_hyp_satisfiable
end AxiomChecks
