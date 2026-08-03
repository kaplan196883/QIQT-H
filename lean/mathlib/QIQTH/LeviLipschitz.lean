/-
  # J4-144 — the `hFLocLip`/`hqLip` discharge via the resolvent (Volterra) equation.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  The Duhamel-residue consumers (`HessianSliceBound`/`RemainderIntegration`/
  `GaussReplaceSlice`) carry, per positive-time slice `s`, the multiplier hypothesis

      `hqLip :  z ↦ A₀ (u−s) z · F s z 0`  is (globally) `L`-Lipschitz, bounded, and
                                            `AEStronglyMeasurable`

  where `F = leviSeries E` is the signed Levi series.  This file discharges that hypothesis to its
  genuinely-new analytic root — the *spatial Lipschitz continuity of the Levi kernel* `z ↦ F s z 0`
  on positive-time slices — via the **resolvent / Volterra identity**

      `F = −E − E∗F`      (`TrueHeatKernel.leviSeries_volterra`; PROVED-reduction output, carried
                            here as `hVol`).

  Differentiating the FIXED-POINT identity (NOT the Levi series termwise) gives the spatial modulus:
    • the `−E` term from an `E`-spatial-difference bound (`hE1`, producible via the segment MVT
      `norm_sub_le_of_fderiv_bound`);
    • the `−E∗F` term from the SAME difference bound integrated — the `(s−r)^{−1/2}` residual
      singularity integrates to `2√s` (`sliver_rpow_sub`).  This is the genuine content of
      `heatConv_diff_bound`.

  ── HONEST FIREWALL ──────────────────────────────────────────────────────────────────────────
  CONDITIONAL.  `hVol` is the Volterra identity (proved reduction, `leviSeries_volterra`); `hE1`
  (the `E`-slice difference) and `hSlice` (the per-`r` inner-`ζ`-integral difference bound, i.e. the
  Gaussian-collapse of the `E`-spatial-difference against the width-2 `F`-domination) are the two
  labelled analytic carries — SATISFIABLE and non-vacuous (they hold for the true parametrix `E` on
  positive-time slices; the `ζ`-collapse into the `(s−r)^{−1/2}` weight is the deferred Gaussian
  bookkeeping), NEVER the conclusion.  This file DERIVES the resolvent Lipschitz bound and the exact
  consumer `hqLip` triple from those carries; it does NOT assert `a₁ = R/6`, nor the unconditional
  existence of the true kernel.  No `sorry`, no new axioms, no `expRho` in statements.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatDuhamel
import QIQTH.BoundaryAssembly
import QIQTH.SliverEstimates

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel MeasureTheory
open scoped Interval

namespace QIQTH.HeatResidualBound

set_option maxHeartbeats 800000

variable {n : ℕ}

/-! ### F1a — the segment (mean-value) Lipschitz lemma. -/

/-- **F1a — the segment mean-value bound (parametric, reusable).**  For a scalar field
    `f : Point n → ℝ` differentiable on the segment `[z, z']` with `‖∇f‖ ≤ M` there, the increment
    is controlled linearly by the displacement:
        `|f z − f z'| ≤ M · dist z z'`.
    This is the tool that manufactures the `E`-spatial-difference bound `hE1` from a carried
    gradient bound on `z ↦ E s z 0`.  Pure `Convex.norm_image_sub_le_of_norm_fderiv_le` on the
    convex segment; genuine hypotheses (fail for non-differentiable `f` / unbounded gradient), never
    the conclusion. -/
theorem norm_sub_le_of_fderiv_bound (f : Point n → ℝ) (M : ℝ) (z z' : Point n)
    (hdiff : ∀ ζ ∈ segment ℝ z z', DifferentiableAt ℝ f ζ)
    (hbnd : ∀ ζ ∈ segment ℝ z z', ‖fderiv ℝ f ζ‖ ≤ M) :
    |f z - f z'| ≤ M * dist z z' := by
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbnd (convex_segment z z')
    (left_mem_segment ℝ z z') (right_mem_segment ℝ z z')
  rw [Real.norm_eq_abs] at h
  rw [abs_sub_comm, dist_eq_norm, norm_sub_rev]
  exact h

/-- **F1b (light corollary) — the `E`-slice spatial-difference bound.**  Specialisation of `F1a` to
    `f = z ↦ E s z 0`: a carried gradient bound on the `E`-slice yields the `hE1` first-term modulus
        `|E s z 0 − E s z' 0| ≤ M · dist z z'`
    consumed by the resolvent Lipschitz assembly below. -/
theorem E_slice_lipschitz (E : ℝ → Point n → Point n → ℝ) (s M : ℝ) (z z' : Point n)
    (hdiff : ∀ ζ ∈ segment ℝ z z', DifferentiableAt ℝ (fun p => E s p 0) ζ)
    (hbnd : ∀ ζ ∈ segment ℝ z z', ‖fderiv ℝ (fun p => E s p 0) ζ‖ ≤ M) :
    |E s z 0 - E s z' 0| ≤ M * dist z z' :=
  norm_sub_le_of_fderiv_bound (fun p => E s p 0) M z z' hdiff hbnd

/-! ### F2a — the `E∗F` convolution spatial-difference bound (the `2√s` integration). -/

/-- **F2a — the resolvent convolution difference bound (the genuine `(s−r)^{−1/2} → 2√s`).**
    Given the per-slice inner-integral difference carry
        `hSlice :  |∫ζ E(s−r) z ζ·F r ζ 0 − ∫ζ E(s−r) z' ζ·F r ζ 0| ≤ K·dist z z'·(s−r)^{−1/2}`
    (`r ∈ Ioo 0 s`; this is the Gaussian-collapse of the `E`-spatial difference against the `F`
    domination — the deferred Gaussian bookkeeping, carried) and interval-integrability of each
    inner integral, the space-time convolution difference obeys
        `|heatConv E F s z 0 − heatConv E F s z' 0| ≤ K·dist z z'·(2√s)`.
    The `(s−r)^{−1/2}` residual singularity at `r = s` is genuinely integrated to `2√s`
    (`sliver_rpow_sub`, endpoint excluded a.e. by `ae_ne_point`).  NOT `a₁ = R/6`. -/
theorem heatConv_diff_bound (E F : ℝ → Point n → Point n → ℝ) (s K : ℝ) (z z' : Point n)
    (hs : 0 < s) (hK : 0 ≤ K)
    (hIz : IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s)
    (hIz' : IntervalIntegrable (fun r => ∫ ζ, E (s - r) z' ζ * F r ζ 0) volume 0 s)
    (hSlice : ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ K * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    |heatConv E F s z 0 - heatConv E F s z' 0| ≤ K * dist z z' * (2 * Real.sqrt s) := by
  -- Move the difference under a single interval integral (linearity of the outer `s`-integral).
  have hconv : heatConv E F s z 0 - heatConv E F s z' 0
      = ∫ r in (0 : ℝ)..s, ((∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)) := by
    show (∫ r in (0 : ℝ)..s, ∫ ζ, E (s - r) z ζ * F r ζ 0)
        - (∫ r in (0 : ℝ)..s, ∫ ζ, E (s - r) z' ζ * F r ζ 0) = _
    rw [← intervalIntegral.integral_sub hIz hIz']
  rw [hconv]
  -- The reflected sliver value and its integrability.
  have hsl : ∫ r in (0 : ℝ)..s, (s - r) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt s := by
    have h := sliver_rpow_sub s s (le_of_lt hs); rwa [sub_self] at h
  have hgii : IntervalIntegrable (fun r => (s - r) ^ (-(1 : ℝ) / 2)) volume 0 s := by
    have h := rpow_sub_intervalIntegrable s s (le_of_lt hs); rwa [sub_self] at h
  rw [← Real.norm_eq_abs]
  calc ‖∫ r in (0 : ℝ)..s,
            ((∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0))‖
      ≤ ∫ r in (0 : ℝ)..s, K * dist z z' * (s - r) ^ (-(1 : ℝ) / 2) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (le_of_lt hs) ?_
          (hgii.const_mul (K * dist z z'))
        filter_upwards [ae_ne_point s] with r hrs hrmem
        have hmem : r ∈ Set.Ioo (0 : ℝ) s := ⟨hrmem.1, lt_of_le_of_ne hrmem.2 hrs⟩
        rw [Real.norm_eq_abs]
        exact hSlice r hmem
    _ = K * dist z z' * (2 * Real.sqrt s) := by
        rw [intervalIntegral.integral_const_mul, hsl]

/-! ### F2 — the resolvent Lipschitz bound (the prize). -/

/-- **★ F2 — the resolvent (Volterra) Lipschitz bound.**  Differentiating the fixed-point identity
    `F = −E − E∗F` in the spatial argument, the Levi kernel `z ↦ F s z 0` is spatially Lipschitz on
    a positive-time slice:
        `|F s z 0 − F s z' 0| ≤ (L_E + K·2√s) · dist z z'`.
    The `−E` term contributes `L_E` (`hE1`, the `E`-slice difference from `E_slice_lipschitz`); the
    `−E∗F` term contributes `K·2√s` (`heatConv_diff_bound`).  Route = the resolvent identity, NOT
    termwise differentiation of the Levi series.  Genuine carries (`hVol`/`hVol'` the Volterra
    identity, `hE1`, `hSlice`, integrabilities); none is the conclusion.  NOT `a₁ = R/6`. -/
theorem resolvent_lipschitz_pointwise (E F : ℝ → Point n → Point n → ℝ) (s K L_E : ℝ) (z z' : Point n)
    (hs : 0 < s) (hK : 0 ≤ K)
    (hVol : F s z 0 = - E s z 0 - heatConv E F s z 0)
    (hVol' : F s z' 0 = - E s z' 0 - heatConv E F s z' 0)
    (hE1 : |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s)
    (hIz' : IntervalIntegrable (fun r => ∫ ζ, E (s - r) z' ζ * F r ζ 0) volume 0 s)
    (hSlice : ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ K * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    |F s z 0 - F s z' 0| ≤ (L_E + K * (2 * Real.sqrt s)) * dist z z' := by
  have hconv := heatConv_diff_bound E F s K z z' hs hK hIz hIz' hSlice
  rw [hVol, hVol']
  have hsplit : (- E s z 0 - heatConv E F s z 0) - (- E s z' 0 - heatConv E F s z' 0)
      = -(E s z 0 - E s z' 0) + -(heatConv E F s z 0 - heatConv E F s z' 0) := by ring
  rw [hsplit]
  calc |-(E s z 0 - E s z' 0) + -(heatConv E F s z 0 - heatConv E F s z' 0)|
      ≤ |-(E s z 0 - E s z' 0)| + |-(heatConv E F s z 0 - heatConv E F s z' 0)| := abs_add_le _ _
    _ = |E s z 0 - E s z' 0| + |heatConv E F s z 0 - heatConv E F s z' 0| := by
        rw [abs_neg, abs_neg]
    _ ≤ L_E * dist z z' + K * dist z z' * (2 * Real.sqrt s) := add_le_add hE1 hconv
    _ = (L_E + K * (2 * Real.sqrt s)) * dist z z' := by ring

/-! ### F2b — the width-2 `F`-domination collapses to a sup bound (for the `hqLip` boundedness). -/

/-- **F2b — the sup bound of the Levi kernel from its width-2 domination.**  The peak bound
    `gaussDdim (2s) v ≤ gaussDdim (2s) 0` turns the width-2 `F`-domination into the uniform sup
    bound `|F s z 0| ≤ C_L · gaussDdim (2s) 0` used for the `hqLip` boundedness clause. -/
theorem abs_F_le_diagonal (F : ℝ → Point n → Point n → ℝ) (C_L s : ℝ) (hs : 0 < s) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ z : Point n, |F s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0)) (z : Point n) :
    |F s z 0| ≤ C_L * gaussDdim (2 * s) (0 : Point n) := by
  have h2s : 0 < 2 * s := by linarith
  calc |F s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0) := hFdom z
    _ ≤ C_L * gaussDdim (2 * s) (0 : Point n) := by
        apply mul_le_mul_of_nonneg_left _ hC_L
        rw [sub_zero]; exact gaussDdim_le_diagonal h2s z

/-! ### F2c — the consumer `hqLip` triple (product Lipschitz + bounded + measurable). -/

/-- **★ F2c — the `hqLip_discharge`.**  From the per-slice resolvent Lipschitz bound (`hFLip`,
    output of `resolvent_lipschitz_pointwise`), the `F`-sup bound (`hFbnd`, output of
    `abs_F_le_diagonal`), the amplitude Lipschitz/sup bounds (`hALip`/`hAbnd`, smooth-composite
    carries) and the per-slice measurability (`hmeas`), the multiplier
        `q z := A₀ (u−s) z · F s z 0`
    satisfies the EXACT consumer `hqLip` triple — `(M_A·L_F + M_F·L_A)`-Lipschitz, bounded by
    `M_A·M_F`, and `AEStronglyMeasurable` — for every slice `s ∈ Ioo (u−ε) u`.  Product rule for
    Lipschitz/boundedness (`add-and-subtract` + `abs_mul`).  This is precisely the hypothesis the
    `hInner0_discharge`/`gaussHessianCancel` consumers require.  NOT `a₁ = R/6`. -/
theorem hqLip_discharge (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε L_F M_F L_A M_A : ℝ) (hM_F : 0 ≤ M_F) (hM_A : 0 ≤ M_A)
    (hFLip : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (hFbnd : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |F s z 0| ≤ M_F)
    (hALip : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n,
        |A0 (u - s) z - A0 (u - s) w| ≤ L_A * dist z w)
    (hAbnd : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |A0 (u - s) z| ≤ M_A)
    (hmeas : ∀ s ∈ Set.Ioo (u - ε) u,
        AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume) :
    ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0|
            ≤ (M_A * L_F + M_F * L_A) * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z 0) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z 0| ≤ M := by
  intro s hs
  refine ⟨?_, hmeas s hs, ⟨M_A * M_F, ?_⟩⟩
  · -- product Lipschitz.
    intro z w
    have key : A0 (u - s) z * F s z 0 - A0 (u - s) w * F s w 0
        = A0 (u - s) z * (F s z 0 - F s w 0) + F s w 0 * (A0 (u - s) z - A0 (u - s) w) := by ring
    rw [key]
    calc |A0 (u - s) z * (F s z 0 - F s w 0) + F s w 0 * (A0 (u - s) z - A0 (u - s) w)|
        ≤ |A0 (u - s) z * (F s z 0 - F s w 0)|
            + |F s w 0 * (A0 (u - s) z - A0 (u - s) w)| := abs_add_le _ _
      _ = |A0 (u - s) z| * |F s z 0 - F s w 0|
            + |F s w 0| * |A0 (u - s) z - A0 (u - s) w| := by rw [abs_mul, abs_mul]
      _ ≤ M_A * (L_F * dist z w) + M_F * (L_A * dist z w) := by
          apply add_le_add
          · exact mul_le_mul (hAbnd s hs z) (hFLip s hs z w) (abs_nonneg _) hM_A
          · exact mul_le_mul (hFbnd s hs w) (hALip s hs z w) (abs_nonneg _) hM_F
      _ = (M_A * L_F + M_F * L_A) * dist z w := by ring
  · -- uniform boundedness.
    intro z
    calc |A0 (u - s) z * F s z 0| = |A0 (u - s) z| * |F s z 0| := abs_mul _ _
      _ ≤ M_A * M_F := mul_le_mul (hAbnd s hs z) (hFbnd s hs z) (abs_nonneg _) hM_A

/-! ### Axiom audit. -/

#print axioms norm_sub_le_of_fderiv_bound
#print axioms heatConv_diff_bound
#print axioms resolvent_lipschitz_pointwise
#print axioms abs_F_le_diagonal
#print axioms hqLip_discharge

end QIQTH.HeatResidualBound
