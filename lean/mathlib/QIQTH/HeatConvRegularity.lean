/-
  HeatConvRegularity — the DIFFERENTIATION-UNDER-THE-INTEGRAL package for the space-time Duhamel
  convolution `heatConv` (J4-111, the hDuhamel campaign opener).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS.

  The restricted `a₁ = R/6` capstone
  (`HeatResidualBound.trueKernel_diagonal_a1_eq_R6_residual_restricted`, RestrictedEboundW.lean)
  still carries, beyond the landed residual/summability inputs, the four REGULARITY carries
      • `hDConv : DifferentiableAt ℝ (fun u => heatConv H F u 0 0) t`   (t-differentiability),
      • `hCConv : ContDiff ℝ ⊤ (fun p => heatConv H F t p 0)`           (space-smoothness),
      • plus the continuity `hcont` that `HeatDuhamel.heatConv_hasDerivAt_upper` needs to fire.
  These are the "differentiate under the `∫ s`/`∫ z`" facts.  This file builds the ABSTRACT engine
  for them, parametric in the two kernels `A B : ℝ → Point n → Point n → ℝ`, carrying the genuine
  regularity + Gaussian-domination hypotheses the underlying Mathlib parametric-integral lemmas
  demand (each fails without its hypothesis; none is the conclusion).

  Recall (HeatDuhamel):
      `heatConv A B t x y = ∫ s in (0)..t, (∫ z, A (t - s) x z * B s z y)`,
  outer an `intervalIntegral` on `[0,t]`, inner the Lebesgue (`volume`) integral on `Point n`.

  WHAT LANDS HERE (the GREEN PREFIX).

    (C1) INTEGRABILITY of the spatial integrand `z ↦ A(t−s) x z · B s z y`:
         • `heatConvIntegrand_integrable` — abstract (dominated by any integrable `bound`);
         • `heatConvIntegrand_gaussianDominated` — concrete, via the model
           `gaussDdim_mul_integrable` when `|A|,|B|` are Gaussian-dominated.
    (C2) CONTINUITY of the inner `s`-integrand `s ↦ ∫ z, A(t−s) x z · B s z y`
         (`heatConv_inner_continuous`, via `MeasureTheory.continuous_of_dominated`), and its
         payoff `heatConvFrozen_hasDerivAt_upper_of_dominated`: it DISCHARGES the `hcont` of
         `HeatDuhamel.heatConv_hasDerivAt_upper`, giving the FTC upper-limit derivative outright.
    (C3z) t-DIFFERENTIATION UNDER THE `z`-INTEGRAL (`heatConvInner_hasDerivAt`, via
         `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`):
             `d/du ∫ z, A(u−s) x z · B s z y = ∫ z, ∂_uA(u−s) x z · B s z y`.
    (C3ε) the ε-TRUNCATED under-integral LEIBNIZ RULE (`heatConv_hasDerivAt_underIntegral`, via
         `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`): with the outer upper
         limit FROZEN at a fixed `b` (`b < t` ⟹ inner times `u−s ≥ t−b > 0`, no boundary
         singularity — Sol's ε-truncation step 3),
             `d/du ∫ s in (0)..b, ∫ z, A(u−s) x z · B s z y
                = ∫ s in (0)..b, ∫ z, ∂_uA(u−s) x z · B s z y`.
    (C4p) SPACE (`p`) DIFFERENTIATION UNDER THE `z`-INTEGRAL, first rung / `C¹`
         (`heatConvInner_hasFDerivAt_space`, via
         `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le`):
             `D_p ∫ z, A t p z · B s z y = ∫ z, (D_p A t · z) p₀ · B s z y`.

  ⚠ HONEST SCOPE (firewall).  This is the ABSTRACT differentiation package.  It does NOT
  by itself discharge the capstone carries: (i) `hDConv` needs the FTC-upper (C2) and the
  under-integral (C3ε) COMBINED at the MOVING diagonal `u = t` (a multivariable chain-rule
  assembly at the boundary `s = t`, where the ε-truncation must be removed by a domination
  ε→0 limit — Sol's steps 4–5, NOT done here); (ii) `hCConv = ContDiff ℝ ⊤` needs the C4p rung
  ITERATED to all orders (the polynomial×Gaussian induction — Sol's C4 induction, NOT done here);
  (iii) the Gaussian-domination hypotheses on the ACTUAL `H`/`leviSeries E` are the far-field /
  Levi-bound wall, carried elsewhere.  These are the remaining bricks of the multi-brick campaign,
  mapped in the closing comment.  NO `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ModelIntegrableW
import QIQTH.TrueHeatKernel

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### C1. Integrability of the spatial integrand. -/

/-- **(C1a) Abstract integrability of the `heatConv` spatial integrand.**  The `z`-integrand
    `z ↦ A(t−s) x z · B s z y` is Lebesgue integrable on `Point n` whenever it is
    `AEStronglyMeasurable` and dominated a.e. by an integrable `bound`.  (`Integrable.mono'`.)
    This is the shape of the residual-side conjuncts of `IterConvIntegrableW`. -/
theorem heatConvIntegrand_integrable (A B : ℝ → Point n → Point n → ℝ) (t s : ℝ) (x y : Point n)
    (hmeas : AEStronglyMeasurable (fun z => A (t - s) x z * B s z y) volume)
    (bound : Point n → ℝ) (hbound : Integrable bound volume)
    (hle : ∀ᵐ z ∂volume, ‖A (t - s) x z * B s z y‖ ≤ bound z) :
    Integrable (fun z => A (t - s) x z * B s z y) volume :=
  Integrable.mono' hbound hmeas hle

/-- **(C1b) Gaussian-dominated integrability of the `heatConv` spatial integrand.**  If the two
    kernel slices are Gaussian-dominated pointwise,
        `|A(t−s) x z| ≤ Ca·gaussDdim a (x−z)`,  `|B s z y| ≤ Cb·gaussDdim b (z−y)`,
    then `z ↦ A(t−s) x z · B s z y` is integrable, by domination against the model product
    `gaussDdim_mul_integrable`.  (`Ca, Cb ≥ 0` are FORCED by the bounds; not assumed.) -/
theorem heatConvIntegrand_gaussianDominated (A B : ℝ → Point n → Point n → ℝ)
    (t s : ℝ) (x y : Point n) (a b Ca Cb : ℝ)
    (hmeas : AEStronglyMeasurable (fun z => A (t - s) x z * B s z y) volume)
    (hA : ∀ z, |A (t - s) x z| ≤ Ca * gaussDdim a (x - z))
    (hB : ∀ z, |B s z y| ≤ Cb * gaussDdim b (z - y)) :
    Integrable (fun z => A (t - s) x z * B s z y) volume := by
  refine Integrable.mono' ((gaussDdim_mul_integrable a b x y).const_mul (Ca * Cb)) hmeas
    (ae_of_all _ (fun z => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  calc |A (t - s) x z| * |B s z y|
      ≤ Ca * gaussDdim a (x - z) * (Cb * gaussDdim b (z - y)) :=
        mul_le_mul (hA z) (hB z) (abs_nonneg _) (le_trans (abs_nonneg _) (hA z))
    _ = Ca * Cb * (gaussDdim a (x - z) * gaussDdim b (z - y)) := by ring

/-! ### C2. Continuity of the inner `s`-integrand (feeds the FTC upper-limit derivative). -/

/-- **(C2) Continuity of the inner `s`-integrand of `heatConv`.**  For a uniform (in `s`) integrable
    dominator `bound`, `AEStronglyMeasurable` slices, and a.e.-in-`z` continuity of
    `s ↦ A(τ₀−s) x z · B s z y`, the map `s ↦ ∫ z, A(τ₀−s) x z · B s z y` is continuous.
    (`MeasureTheory.continuous_of_dominated`.)  This is EXACTLY the `hcont` hypothesis of
    `HeatDuhamel.heatConv_hasDerivAt_upper`. -/
theorem heatConv_inner_continuous (A B : ℝ → Point n → Point n → ℝ) (τ₀ : ℝ) (x y : Point n)
    (bound : Point n → ℝ) (hbound : Integrable bound volume)
    (hmeas : ∀ s, AEStronglyMeasurable (fun z => A (τ₀ - s) x z * B s z y) volume)
    (hle : ∀ s, ∀ᵐ z ∂volume, ‖A (τ₀ - s) x z * B s z y‖ ≤ bound z)
    (hcont : ∀ᵐ z ∂volume, Continuous (fun s => A (τ₀ - s) x z * B s z y)) :
    Continuous (fun s => ∫ z, A (τ₀ - s) x z * B s z y) :=
  continuous_of_dominated hmeas hle hbound hcont

/-- **(C2 payoff) FTC upper-limit derivative of the frozen convolution, from domination.**  Plugging
    `heatConv_inner_continuous` into `HeatDuhamel.heatConv_hasDerivAt_upper`: with the outer `t`
    inside `A` FROZEN at `τ₀`, the frozen convolution `u ↦ heatConvFrozen A B τ₀ u x y` has
    derivative the boundary integrand `∫ z, A(τ₀−t) x z · B t z y` at `t`.  Discharges the
    continuity hypothesis via the C2 domination package. -/
theorem heatConvFrozen_hasDerivAt_upper_of_dominated (A B : ℝ → Point n → Point n → ℝ)
    (τ₀ t : ℝ) (x y : Point n)
    (bound : Point n → ℝ) (hbound : Integrable bound volume)
    (hmeas : ∀ s, AEStronglyMeasurable (fun z => A (τ₀ - s) x z * B s z y) volume)
    (hle : ∀ s, ∀ᵐ z ∂volume, ‖A (τ₀ - s) x z * B s z y‖ ≤ bound z)
    (hcont : ∀ᵐ z ∂volume, Continuous (fun s => A (τ₀ - s) x z * B s z y)) :
    HasDerivAt (fun u => heatConvFrozen A B τ₀ u x y)
      (∫ z, A (τ₀ - t) x z * B t z y) t :=
  heatConv_hasDerivAt_upper A B τ₀ t x y
    (heatConv_inner_continuous A B τ₀ x y bound hbound hmeas hle hcont)

/-! ### C3z. `t`-differentiation under the `z`-integral. -/

/-- **(C3z) `t`-DERIVATIVE UNDER THE `z`-INTEGRAL.**  Fix `s`.  The map
    `u ↦ ∫ z, A(u−s) x z · B s z y` is differentiable at `u₀` with derivative obtained by moving the
    `∂_u` inside the `z`-integral:
        `d/du ∫ z, A(u−s) x z · B s z y = ∫ z, dAu(u−s) x z · B s z y`,
    where `dAu(u−s) x z · B s z y` is the pointwise `u`-derivative of the integrand.  Via
    `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, carrying exactly its genuine
    inputs: a neighborhood `nb` of `u₀`, `AEStronglyMeasurable` slices, integrability of the base
    integrand at `u₀` and of the derivative integrand at `u₀`, a uniform-on-`nb` integrable
    derivative bound, and the pointwise `HasDerivAt` family (which encodes the differentiability of
    `A`). -/
theorem heatConvInner_hasDerivAt (A dAu B : ℝ → Point n → Point n → ℝ) (s u₀ : ℝ) (x y : Point n)
    (nb : Set ℝ) (hnb : nb ∈ 𝓝 u₀)
    (hFmeas : ∀ u, AEStronglyMeasurable (fun z => A (u - s) x z * B s z y) volume)
    (hFint : Integrable (fun z => A (u₀ - s) x z * B s z y) volume)
    (hF'meas : AEStronglyMeasurable (fun z => dAu (u₀ - s) x z * B s z y) volume)
    (bound : Point n → ℝ) (hbdd : Integrable bound volume)
    (hbound : ∀ᵐ z ∂volume, ∀ u ∈ nb, ‖dAu (u - s) x z * B s z y‖ ≤ bound z)
    (hdiff : ∀ᵐ z ∂volume, ∀ u ∈ nb,
      HasDerivAt (fun u => A (u - s) x z * B s z y) (dAu (u - s) x z * B s z y) u) :
    HasDerivAt (fun u => ∫ z, A (u - s) x z * B s z y)
      (∫ z, dAu (u₀ - s) x z * B s z y) u₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hnb
    (Filter.Eventually.of_forall hFmeas) hFint hF'meas hbound hbdd hdiff).2

/-! ### C3ε. The ε-truncated under-integral Leibniz rule. -/

/-- **(C3ε) THE ε-TRUNCATED UNDER-INTEGRAL LEIBNIZ RULE.**  With the outer upper limit FROZEN at a
    fixed `b` (the ε-truncation: taking `b < t` keeps all inner times `u−s ≥ t−b > 0`, away from the
    `s = t` boundary singularity), the `u`-derivative of the frozen-argument convolution passes under
    BOTH integrals:
        `d/du ∫ s in (0)..b, ∫ z, A(u−s) x z · B s z y
           = ∫ s in (0)..b, ∫ z, dAu(u−s) x z · B s z y`.
    Via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, carrying its genuine
    inputs on the OUTER `s`-integral (the inner `z`-derivative family `hdiff` is exactly the C3z
    conclusion at each `s`, dischargeable by `heatConvInner_hasDerivAt`).  This is Sol's step 3 — the
    engine of the eventual full diagonal Leibniz once the ε→0 domination limit (steps 4–5) is added. -/
theorem heatConv_hasDerivAt_underIntegral (A dAu B : ℝ → Point n → Point n → ℝ)
    (τ₀ b : ℝ) (x y : Point n) (nb : Set ℝ) (hnb : nb ∈ 𝓝 τ₀)
    (hFmeas : ∀ u, AEStronglyMeasurable
      (fun s => ∫ z, A (u - s) x z * B s z y) (volume.restrict (Set.uIoc 0 b)))
    (hFint : IntervalIntegrable (fun s => ∫ z, A (τ₀ - s) x z * B s z y) volume 0 b)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dAu (τ₀ - s) x z * B s z y) (volume.restrict (Set.uIoc 0 b)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 b)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ u ∈ nb,
      ‖∫ z, dAu (u - s) x z * B s z y‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 b → ∀ u ∈ nb,
      HasDerivAt (fun u => ∫ z, A (u - s) x z * B s z y)
        (∫ z, dAu (u - s) x z * B s z y) u) :
    HasDerivAt (fun u => ∫ s in (0)..b, ∫ z, A (u - s) x z * B s z y)
      (∫ s in (0)..b, ∫ z, dAu (τ₀ - s) x z * B s z y) τ₀ :=
  (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hnb
    (Filter.Eventually.of_forall hFmeas) hFint hF'meas hbound hbdd hdiff).2

/-! ### C4p. Space (`p`) differentiation under the `z`-integral (first rung / `C¹`). -/

/-- **(C4p) SPACE-DERIVATIVE UNDER THE `z`-INTEGRAL (first rung).**  Fix `t, s`.  The map
    `p ↦ ∫ z, A t p z · B s z y` is Fréchet-differentiable at `p₀ : Point n`, with derivative the
    `z`-integral of the pointwise Fréchet derivative kernel `Fp'`:
        `D_p ∫ z, A t p z · B s z y = ∫ z, Fp' p₀ z`,
    where `Fp' p z : Point n →L[ℝ] ℝ` is the `p`-Fréchet-derivative of `p ↦ A t p z · B s z y`.
    Via `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le`, carrying its genuine inputs
    (neighborhood, `AEStronglyMeasurable` slices, base/derivative integrability, uniform integrable
    operator-norm bound, pointwise `HasFDerivAt` family).  This is the `k = 1` rung of the
    `ContDiff ℝ ⊤` induction (Sol's C4) that `hCConv` ultimately needs. -/
theorem heatConvInner_hasFDerivAt_space (A B : ℝ → Point n → Point n → ℝ)
    (t s : ℝ) (y : Point n) (p₀ : Point n)
    (Fp' : Point n → Point n → (Point n →L[ℝ] ℝ))
    (nb : Set (Point n)) (hnb : nb ∈ 𝓝 p₀)
    (hFmeas : ∀ p, AEStronglyMeasurable (fun z => A t p z * B s z y) volume)
    (hFint : Integrable (fun z => A t p₀ z * B s z y) volume)
    (hF'meas : AEStronglyMeasurable (Fp' p₀) volume)
    (bound : Point n → ℝ) (hbdd : Integrable bound volume)
    (hbound : ∀ᵐ z ∂volume, ∀ p ∈ nb, ‖Fp' p z‖ ≤ bound z)
    (hdiff : ∀ᵐ z ∂volume, ∀ p ∈ nb,
      HasFDerivAt (fun p => A t p z * B s z y) (Fp' p z) p) :
    HasFDerivAt (fun p => ∫ z, A t p z * B s z y) (∫ z, Fp' p₀ z) p₀ :=
  hasFDerivAt_integral_of_dominated_of_fderiv_le hnb
    (Filter.Eventually.of_forall hFmeas) hFint hF'meas hbound hbdd hdiff

/-! ### Campaign map — the remaining bricks toward `hDConv` / `hCConv`.

    This file lands the ABSTRACT differentiation engine (C1, C2, C3z, C3ε, C4p).  The remaining
    bricks of the hDuhamel campaign, in dependency order:

    ▸ B1 (diagonal `t`-Leibniz = `hDConv`).  Combine `heatConvFrozen_hasDerivAt_upper_of_dominated`
      (FTC upper-limit, C2) with the ε→0 limit of `heatConv_hasDerivAt_underIntegral` (C3ε) at the
      MOVING diagonal `u = t`.  Needs: the ε-removal by dominated convergence (Sol steps 4–5) and the
      two-variable chain rule `heatConvFrozen A B u u = heatConv A B u` (the diagonal of the frozen
      object, `HeatDuhamel.heatConvFrozen_diag`).  Output shape: `DifferentiableAt ℝ (fun u =>
      heatConv H F u 0 0) t`.

    ▸ B2 (space `ContDiff ⊤` = `hCConv`).  Iterate `heatConvInner_hasFDerivAt_space` (C4p) to all
      orders with the polynomial×Gaussian domination invariant (Sol's C4 induction), then lift
      through the outer `∫ s` (continuity of each order's integral-valued derivative via
      `continuous_of_dominated` in the iterated-CLM space).  Output shape: `ContDiff ℝ ⊤ (fun p =>
      heatConv H F t p 0)`.

    ▸ B3 (concrete domination of `H` / `leviSeries E`).  Supply the Gaussian-domination and
      pointwise-derivative hypotheses of C1–C4 for the ACTUAL parametrix `H` and Levi series
      `leviSeries (heatOp g gi H)` (the latter from the width-2 engine's summable bounds,
      `scaledIterKernelW_summable` / `iterConvW_bound`).  This is the far-field / Levi-bound wall.

    None of B1–B3 is attempted here; each is a genuine, separately-labeled brick. -/

end QIQTH.HeatResidualBound
