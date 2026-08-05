/-
  ChartGaussianChangeVar — J4-269: the chart change-of-variables (Layer B) of the
  chart-image approximate-identity plan.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  After pushing the heat integrand through a
  normal chart, the remaining obstruction is the *chart-image approximate identity*.  An external
  architecture consult split it into three layers:

    • LAYER A — a *set-integral rewrite* of the concrete boundary witness onto the gate `S`, using
      the on-gate factorization `Wit τ 0 z = gaussDdim τ (W₀ z) · A τ z` and off-gate vanishing.
    • LAYER B — the *change of variables* `w = W z` turning the gate integral over `S` into a
      genuine `∫ w in Ω, gaussDdim τ w · (…)` over the chart image `Ω := W '' S`.  ★ THIS FILE. ★
    • LAYER C — the chart-free generic MOVING approximate identity for the flat Gaussian, landed
      in `QIQTH.ChartImageApproxIdentity` (J4-268).

  WHAT LANDS (Layer B, ABSTRACT — for any C¹ chart, not tied to the concrete normal chart).
    `chart_gaussian_change_variables` — for `W : Point n → Point n` a map that is differentiable
    (`HasFDerivWithinAt W (f' z) S z`) and injective on a measurable set `S`, with a left inverse
    `V` on `S` (`V (W z) = z`) and everywhere-invertible Jacobian on `S` (`J z = |det (f' z)| > 0`):

        ∫ z in S, gaussDdim τ (W z) · B z  =  ∫ w in (W '' S), gaussDdim τ w · (B (V w) / J (V w)).

    This is exactly the shape Layer C (`gaussDdim_set_approx_identity_moving`) consumes, with
    `Ω := W '' S` and moving integrand `g τ w := B (V w) / J (V w)`.  The proof is a direct
    application of Mathlib's Bochner change-of-variables
    `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` (which is an UNCONDITIONAL
    identity — no integrability side conditions), followed by an on-`S` pointwise cancellation
    `|det (f' z)| · (gaussDdim · (B z / J z)) = gaussDdim · B z` using `J z = |det (f' z)| > 0`.

  MISSING-FACT LIST for the CONCRETE instantiation `W₀ := uniformInverseChart g gi hC hK 0`
  (bankable intel — the concrete corollary is NOT attempted here because these are not yet banked
  as a coherent bundle over a fixed gate `S`):
    (M1) `HasFDerivWithinAt W₀ (f' z) S z` for a concrete `f'` on a fixed gate `S`.  The chart bank
         (`AmplitudeFamilyDischarge`, `InverseChartNormalJets`) supplies `ContDiffAt ℝ 2 W₀ 0` at
         the CENTRE `0` only, not a `HasFDerivWithinAt` field over a whole gate `S`.
    (M2) `Set.InjOn W₀ S` on that gate — the chart is `.choose`-defined and only *locally* injective
         near `0`; a concrete radius on which injectivity holds must be extracted (do NOT carry an
         `InjOn`-on-all-of-`S` beyond the honest local ball).
    (M3) a left inverse `V` with `V (W₀ z) = z` on `S` (the forward normal chart / `expMap`⁻¹).
    (M4) `0 < |det (f' z)|` on `S` — near `0` the Jacobian is `≈ 1` (`J(0) = 1`); a uniform
         positive lower bound over the shrunk gate is needed.
    All four should come from a *uniform local inverse-function* package for `uniformInverseChart`
    over a single small ball, which is itself downstream of the `expMap` C² regularity.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`.  This is ONE analytic brick (the Layer B change of variables),
  abstract over the chart.  No `sorry`, no new axioms, no `:= True`, no vacuous or conclusion-in-
  disguise hypotheses: `hfd`/`hinj`/`hV`/`hJ`/`hJpos` are the standard change-of-variables data and
  are all simultaneously satisfiable by any genuine C¹ diffeomorphism onto its image (e.g. an
  affine map), so the hypothesis set is non-vacuous.  RESIDUAL: the concrete corollary (M1–M4) and
  Layer A remain separate, later bricks.
-/
import Mathlib
import QIQTH.FlatHeatEquation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open scoped Topology

namespace QIQTH.ChartGaussianChangeVar

variable {n : ℕ}

/-- **LAYER B — the chart change of variables.**  For a map `W : Point n → Point n` that is
differentiable with derivative `f' z` and injective on a measurable set `S`, with left inverse `V`
on `S` and everywhere-positive Jacobian `J z = |det (f' z)|` on `S`, the Gaussian gate integral
over `S` equals the Gaussian integral over the chart image `Ω := W '' S`:

    `∫ z in S, gaussDdim τ (W z) · B z = ∫ w in W '' S, gaussDdim τ w · (B (V w) / J (V w))`.

Proof: Mathlib's unconditional Bochner change-of-variables rewrites the RHS
(`W '' S` integral) into `∫ z in S, |det (f' z)| • (gaussDdim τ (W z) · (B (V (W z)) / J (V (W z))))`;
on `S`, `V (W z) = z` and `J z = |det (f' z)| > 0` cancels to `gaussDdim τ (W z) · B z`.  NOT
`a₁ = R/6`. -/
theorem chart_gaussian_change_variables
    (τ : ℝ) (S : Set (Point n)) (W V : Point n → Point n)
    (f' : Point n → (Point n →L[ℝ] Point n)) (J B : Point n → ℝ)
    (hS : MeasurableSet S)
    (hfd : ∀ z ∈ S, HasFDerivWithinAt W (f' z) S z)
    (hinj : Set.InjOn W S)
    (hV : ∀ z ∈ S, V (W z) = z)
    (hJ : ∀ z ∈ S, J z = |(f' z).det|)
    (hJpos : ∀ z ∈ S, 0 < J z) :
    (∫ z in S, gaussDdim τ (W z) * B z)
      = ∫ w in W '' S, gaussDdim τ w * (B (V w) / J (V w)) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul
        (volume) hS hfd hinj (fun w => gaussDdim τ w * (B (V w) / J (V w)))]
  refine setIntegral_congr_fun hS (fun z hz => ?_)
  simp only [smul_eq_mul]
  rw [hV z hz, hJ z hz]
  have hdpos : 0 < |(f' z).det| := by rw [← hJ z hz]; exact hJpos z hz
  have hd : |(f' z).det| ≠ 0 := ne_of_gt hdpos
  field_simp

end QIQTH.ChartGaussianChangeVar
