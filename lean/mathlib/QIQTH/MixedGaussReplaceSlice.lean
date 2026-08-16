/-
  MixedGaussReplaceSlice — J4-785: the OFF-DIAGONAL (`∂ᵢ∂ⱼ`, `i ≠ j`) mixed E1 Gaussian-replacement
  SLICE bound — the mixed analogue of `XUniformSliver.tE1_slice_abstract` / `HeatResidualBound.tE1_slice_bound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign — the mixed Gaussian-replacement (`G_τ(V z) → G_τ(z)`) half of
  the mixed-Hessian inner bound (`hInner0` of `MixedSliverAssembly.witness_sliver2_assembly_mixed`).

  ## THE OBSTRUCTION THIS CLOSES (scoped J4-783/J4-784).
  The mixed Hessian normal-form term `mTerm0` uses the CHART Gaussian `G_τ(V z)`.  The banked mixed slice
  `MixedTE2Slice.mixedHessianSlice_plain_bound` is the PLAIN-Gaussian (`G_τ(z)`) half only.  To bridge the
  two, one needs the mixed E1 Gaussian-replacement port: the bound on the DIFFERENCE integral
    `∫ z, (G_τ(V z) − G_τ(z))·[mixed Hessian bracket]·(A₀·g)`.
  The diagonal case gets this from `HeatResidualBound.tE1_slice_bound` / `XUniformSliver.tE1_slice_abstract`
  (whose E1 leg feeds `XUniformSliverFull.hRem_xuniform`); no mixed off-diagonal E1 leg existed yet.

  ## WHY THIS IS THE MECHANICAL WALL (task hypothesis, CONFIRMED).
  The Gaussian-difference factor `|G_τ(V z) − G_τ(z)| ≤ (2n·C_W‖z‖³+n·C_W²‖z‖⁴)/(4τ)·(√2)ⁿ·G_{2τ}(z)`
  (`gaussReplace_E1_bound`) is GENERIC in the coefficient — it depends ONLY on the displacement map `V`'s
  coercivity (`hco`) and quadratic displacement (`hVdisp`), NOT on which Hessian polynomial multiplies it.
  So the ONLY coefficient-specific link is the bracket cap.  And the mixed bracket cap is SYNTACTICALLY the
  SAME polynomial RHS as the diagonal `HeatResidualBound.polyChart_abs_bound`:
    • the mixed second-moment is the PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩`, each factor capped by the SAME
      `n(‖z‖+C_W‖z‖²)(1+C_P‖z‖)` the diagonal `⟨Y,P⟩` gets — so the product caps to the SAME
      `n²(…)²(…)²` the diagonal SQUARE `⟨Y,P⟩²` gets (`i ≠ j` is NOT needed — no parity cancellation);
    • the cross-jet `⟨Pi,Pj⟩` caps by `n(1+C_P‖z‖)²`, exactly the diagonal `⟨P,P⟩` cap;
    • the center-jet `⟨V,Q⟩` caps by `n(‖z‖+C_W‖z‖²)C_Q`, exactly the diagonal `⟨Y,Q⟩` cap.
  Because the RHS is identical, the ENTIRE downstream moment tower (the eight `τ`-coefficients `c3..c10`,
  the width-`2τ` moment envelope, the `w=√τ` fold) transfers UNCHANGED and delivers the SAME explicit
  constant `XUniformSliver.sliverRateConst`.

  ## WHAT THIS DELIVERS.
    • `polyChartMixed_abs_bound` — ★ the mixed Hessian bracket cap, with RHS SYNTACTICALLY the diagonal
        `HeatResidualBound.polyChart_abs_bound` RHS.
    • `tE1_slice_abstract_mixed` — ★★ the mixed E1 per-slice bound (field slice `g`), delivering the SAME
        `sliverRateConst`; the mixed twin of `XUniformSliver.tE1_slice_abstract`.
    • `mixedHessianSlice_chart_bound` — ★★★ the CHART-Gaussian mixed Hessian slice bound: the E1 port
        (this file) COMBINED with the plain half (`MixedTE2Slice.mixedHessianSlice_plain_bound`), via the
        add-and-subtract split `G_τ(V z)·bracket = (G_τ(V z)−G_τ(z))·bracket + G_τ(z)·bracket`, giving the
        `hInner0`-shaped bound `≤ (sliverRateConst + (tE2RateConst + L·n))·τ^{−1/2}` on
        `∫ z, G_τ(V z)·[mixed bracket]·(A₀·g)`.  This is exactly the mixed Hessian inner bound the
        four-term `MixedSliverAssembly.witness_sliver2_assembly_mixed` carries as `hInner0`.

  ## WHAT THIS DOES NOT DO (honest scope).
  The two mixed gradient inner bounds (`hInner1i`/`hInner1j`) still need the x-uniform mixed gradient
  slice; this file does the Hessian (`hInner0`) piece only.  The `hInner0`-shaped bound here carries its
  per-slice integrabilities as hypotheses (exactly as the diagonal `hRem_xuniform` does).  NOT `a₁ = R/6`.

  Every hypothesis is satisfiable and non-vacuous (`V = −id`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0`, `A₀`
  bounded, `g` a width-2 Gaussian bump satisfies all; for that model `G_τ(−z) = G_τ(z)` makes the E1
  difference `≡ 0`), and none equals the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedTE2Slice

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull QIQTH.MixedTE2Slice
open scoped Interval Topology

namespace QIQTH.MixedGaussReplaceSlice

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ★ The mixed Hessian bracket cap (same polynomial RHS as the diagonal `polyChart_abs_bound`).
    ############################################################################### -/

/-- **★ THE MIXED HESSIAN BRACKET CAP.**  The off-diagonal analogue of
    `HeatResidualBound.polyChart_abs_bound`.  The mixed Hessian coefficient
    `⟨V,Pi⟩⟨V,Pj⟩/(4τ²) − (⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ)` is bounded, via `abs_inner_le`/`normY_le`/`normP_le` fed
    the geometric inputs, by the polynomial that is SYNTACTICALLY the diagonal RHS:
      `≤ n²(‖z‖+C_W‖z‖²)²(1+C_P‖z‖)²/(4τ²) + (n(1+C_P‖z‖)²+n(‖z‖+C_W‖z‖²)C_Q)/(2τ)`.
    The mixed second-moment is the PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩` of two DISTINCT first-moment factors — each
    capped by the SAME `n(‖z‖+C_W‖z‖²)(1+C_P‖z‖)` the diagonal `⟨Y,P⟩` gets — so the product caps to the
    SAME `n²(…)²(…)²` the diagonal SQUARE gets.  `i ≠ j` is NOT needed (no parity cancellation on the E1
    leg).  NOT `a₁ = R/6`. -/
theorem polyChartMixed_abs_bound (V Pi Pj Q : Point n → Point n) (i j : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (C_W C_P C_Q : ℝ) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (_hC_Q : 0 ≤ C_Q)
    (hVd : ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2) (hJi : ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJj : ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖) (hQ : ‖Q z‖ ≤ C_Q) :
    |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
        - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)|
      ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
        + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) := by
  have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hVn : ‖V z‖ ≤ C_W * ‖z‖ ^ 2 + ‖z‖ := normY_le (V z) z (C_W * ‖z‖ ^ 2) hVd
  have hVn' : ‖V z‖ ≤ ‖z‖ + C_W * ‖z‖ ^ 2 := by linarith [hVn]
  have hPin : ‖Pi z‖ ≤ 1 + C_P * ‖z‖ := normP_le (Pi z) i C_P ‖z‖ hJi
  have hPjn : ‖Pj z‖ ≤ 1 + C_P * ‖z‖ := normP_le (Pj z) j C_P ‖z‖ hJj
  -- the four inner-product caps.
  have hVPi : |∑ k, V z k * Pi z k| ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) := by
    calc |∑ k, V z k * Pi z k| ≤ (n : ℝ) * ‖V z‖ * ‖Pi z‖ := abs_inner_le (V z) (Pi z)
      _ ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVn' hcast) hPin (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
  have hVPj : |∑ k, V z k * Pj z k| ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) := by
    calc |∑ k, V z k * Pj z k| ≤ (n : ℝ) * ‖V z‖ * ‖Pj z‖ := abs_inner_le (V z) (Pj z)
      _ ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVn' hcast) hPjn (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
  have hPiPj : |∑ k, Pi z k * Pj z k| ≤ (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 := by
    calc |∑ k, Pi z k * Pj z k| ≤ (n : ℝ) * ‖Pi z‖ * ‖Pj z‖ := abs_inner_le (Pi z) (Pj z)
      _ ≤ (n : ℝ) * (1 + C_P * ‖z‖) * (1 + C_P * ‖z‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hPin hcast) hPjn (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
      _ = (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 := by ring
  have hVQ : |∑ k, V z k * Q z k| ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q := by
    calc |∑ k, V z k * Q z k| ≤ (n : ℝ) * ‖V z‖ * ‖Q z‖ := abs_inner_le (V z) (Q z)
      _ ≤ (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q :=
          mul_le_mul (mul_le_mul_of_nonneg_left hVn' hcast) hQ (norm_nonneg _)
            (mul_nonneg hcast (by positivity))
  -- numerator caps: the PRODUCT caps to the SAME `n²(…)²(…)²` the diagonal square gets.
  have hPcap : |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k)|
      ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 := by
    rw [abs_mul]
    calc |∑ k, V z k * Pi z k| * |∑ k, V z k * Pj z k|
        ≤ ((n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖))
            * ((n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * (1 + C_P * ‖z‖)) :=
          mul_le_mul hVPi hVPj (abs_nonneg _)
            (mul_nonneg (mul_nonneg hcast (by positivity)) (by positivity))
      _ = (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 := by ring
  have hYb : |(∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)|
      ≤ (n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q :=
    (abs_add_le _ _).trans (add_le_add hPiPj hVQ)
  have h4 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have h2p : (0 : ℝ) < 2 * τ := by linarith
  have habs2 : |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
        - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)|
      ≤ |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)|
        + |((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)| := by
    have := abs_add_le ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2))
      (-(((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)))
    rwa [← sub_eq_add_neg, abs_neg] at this
  calc |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
          - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)|
      ≤ |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)|
        + |((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)| := habs2
    _ = |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k)| / (4 * τ ^ 2)
        + |(∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)| / (2 * τ) := by
        rw [abs_div, abs_div, abs_of_pos h4, abs_of_pos h2p]
    _ ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
        + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) :=
        add_le_add ((div_le_div_iff_of_pos_right h4).mpr hPcap)
          ((div_le_div_iff_of_pos_right h2p).mpr hYb)

/-! ###############################################################################
    ★★ The mixed E1 per-slice Gaussian-replacement bound (field slice `g`).
    ############################################################################### -/

/-- **★★ THE MIXED E1 PER-SLICE BOUND.**  The off-diagonal analogue of
    `XUniformSliver.tE1_slice_abstract`.  The Gaussian-replacement difference `G_τ(V z) − G_τ(z)` times
    the MIXED Hessian bracket times the abstract field slice `A₀·g` (carrying only `|g s z| ≤ C_F`) has
    the `τ^{−1/2}` rate with the SAME explicit constant `sliverRateConst`:
      `|∫ z, (G_τ(V z)−G_τ(z))·[⟨V,Pi⟩⟨V,Pj⟩/(4τ²)−(⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ)]·(A₀·g)| ≤ sliverRateConst·τ^{−1/2}`.
    Route: `gaussReplace_E1_bound` (the coefficient-GENERIC Gaussian-difference bound, applied to `V`) ×
    `polyChartMixed_abs_bound` (the mixed bracket cap, SAME RHS as diagonal) × amplitude/field caps gives
    the pointwise domination by `K·Σ_{k=3}^{10} c_k·‖z‖^k·G_{2τ}` with the IDENTICAL coefficients of the
    diagonal `tE1_slice_abstract`; every downstream moment step is the diagonal one verbatim.  NOT
    `a₁ = R/6`. -/
theorem tE1_slice_abstract_mixed
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i j : Fin n) (M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z))
    (hVdisp : ∀ z : Point n, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i : ∀ z : Point n, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j : ∀ z : Point n, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * g s z)|
        ≤ sliverRateConst n M₀ C_F C_W C_P C_Q τ₀ * (u - s) ^ (-(1 : ℝ) / 2) := by
  set K : ℝ := (Real.sqrt 2) ^ n * (M₀ * C_F) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; exact mul_nonneg (by positivity) (mul_nonneg hM₀ hC_F)
  intro s hsmem
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hττ₀ : u - s ≤ τ₀ := by linarith [hsmem.1, hετ₀]
  set τ : ℝ := u - s with hτ_def
  have hτne : τ ≠ 0 := hτpos.ne'
  have h2τ : (0 : ℝ) < 2 * τ := by linarith
  have hFcap : ∀ z : Point n, |g s z| ≤ C_F := hgcap s hsmem
  -- the eight τ-coefficients of the product polynomial (E·polyChart-cap, collected by degree).
  set c3 : ℝ := (n : ℝ) ^ 2 * C_W / (4 * τ ^ 2) with hc3
  set c4 : ℝ := C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / (8 * τ ^ 2) with hc4
  set c5 : ℝ := (n : ℝ) ^ 3 * C_W / (8 * τ ^ 3)
      + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / (8 * τ ^ 2) with hc5
  set c6 : ℝ := C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / (16 * τ ^ 3)
      + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / (8 * τ ^ 2) with hc6
  set c7 : ℝ := C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / (8 * τ ^ 3) with hc7
  set c8 : ℝ := C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / (16 * τ ^ 3) with hc8
  set c9 : ℝ := C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / (8 * τ ^ 3) with hc9
  set c10 : ℝ := C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / (16 * τ ^ 3) with hc10
  have hc3nn : 0 ≤ c3 := by rw [hc3]; positivity
  have hc4nn : 0 ≤ c4 := by rw [hc4]; positivity
  have hc5nn : 0 ≤ c5 := by rw [hc5]; positivity
  have hc6nn : 0 ≤ c6 := by rw [hc6]; positivity
  have hc7nn : 0 ≤ c7 := by rw [hc7]; positivity
  have hc8nn : 0 ≤ c8 := by rw [hc8]; positivity
  have hc9nn : 0 ≤ c9 := by rw [hc9]; positivity
  have hc10nn : 0 ≤ c10 := by rw [hc10]; positivity
  -- pointwise domination by the dominating (poly × width-2τ Gaussian) function.
  have hpt : ∀ z : Point n,
      ‖(gaussDdim τ (V z) - gaussDdim τ z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z)‖
        ≤ K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
    intro z
    have hG2nn : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg' (2 * τ) z
    have hGd := gaussReplace_E1_bound τ hτpos V z C_W hC_W (hVdisp z) (hco z)
    have hpc := polyChartMixed_abs_bound V Pi Pj Q i j τ hτpos z C_W C_P C_Q hC_W hC_P hC_Q
      (hVdisp z) (hJ3i z) (hJ3j z) (hJ3Q z)
    have hAF : |A0 τ z * g s z| ≤ M₀ * C_F := by
      rw [abs_mul]; exact mul_le_mul (hA0bdd τ z) (hFcap z) (abs_nonneg _) hM₀
    have hEnn : (0 : ℝ) ≤ (2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4) / (4 * τ)
        * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z :=
      mul_nonneg (mul_nonneg (by positivity) (by positivity)) hG2nn
    have hPCnn : (0 : ℝ)
        ≤ (n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
          + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ) := by
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |gaussDdim τ (V z) - gaussDdim τ z|
            * |(∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ)|
            * |A0 τ z * g s z|
        ≤ ((2 * (n : ℝ) * C_W * ‖z‖ ^ 3 + (n : ℝ) * C_W ^ 2 * ‖z‖ ^ 4) / (4 * τ)
              * (Real.sqrt 2) ^ n * gaussDdim (2 * τ) z)
            * ((n : ℝ) ^ 2 * (‖z‖ + C_W * ‖z‖ ^ 2) ^ 2 * (1 + C_P * ‖z‖) ^ 2 / (4 * τ ^ 2)
              + ((n : ℝ) * (1 + C_P * ‖z‖) ^ 2 + (n : ℝ) * (‖z‖ + C_W * ‖z‖ ^ 2) * C_Q) / (2 * τ))
            * (M₀ * C_F) :=
          mul_le_mul (mul_le_mul hGd hpc (abs_nonneg _) hEnn) hAF (abs_nonneg _)
            (mul_nonneg hEnn hPCnn)
      _ = K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
          rw [hKdef, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
          field_simp
          ring
  -- integrability of each monomial × Gaussian and of the dominating function.
  have hi3 := (normPow_gauss_integrable 3 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c3
  have hi4 := (normPow_gauss_integrable 4 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c4
  have hi5 := (normPow_gauss_integrable 5 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c5
  have hi6 := (normPow_gauss_integrable 6 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c6
  have hi7 := (normPow_gauss_integrable 7 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c7
  have hi8 := (normPow_gauss_integrable 8 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c8
  have hi9 := (normPow_gauss_integrable 9 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c9
  have hi10 := (normPow_gauss_integrable 10 (by norm_num) (2 * τ) h2τ (n := n)).const_mul c10
  have hdom_int : Integrable (fun z : Point n =>
      K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
        + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
        + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
        + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))) volume :=
    (((((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8).add hi9).add hi10).const_mul K
  -- the width-2τ moment values (κ = 2).
  have hm3 : ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3 :=
    pow_norm_mul_gauss_integral 3 (by norm_num) 2 (by norm_num) τ hτpos (64 * Real.sqrt 2 + 1)
      (by positivity) (oneD_absMoment3 (2 * τ) h2τ)
  have hm4 : ∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4 :=
    pow_norm_mul_gauss_integral 4 (by norm_num) 2 (by norm_num) τ hτpos (128 * Real.sqrt 2)
      (by positivity) (oneD_absMoment4 (2 * τ) h2τ)
  have hm5 : ∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5 :=
    pow_norm_mul_gauss_integral 5 (by norm_num) 2 (by norm_num) τ hτpos (1600 * Real.sqrt 2)
      (by positivity) (oneD_absMoment5 (2 * τ) h2τ)
  have hm6 : ∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6 :=
    pow_norm_mul_gauss_integral 6 (by norm_num) 2 (by norm_num) τ hτpos (3072 * Real.sqrt 2)
      (by positivity) (oneD_absMoment6 (2 * τ) h2τ)
  have hm7 : ∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7 :=
    pow_norm_mul_gauss_integral 7 (by norm_num) 2 (by norm_num) τ hτpos (50688 * Real.sqrt 2)
      (by positivity) (oneD_absMoment7 (2 * τ) h2τ)
  have hm8 : ∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8 :=
    pow_norm_mul_gauss_integral 8 (by norm_num) 2 (by norm_num) τ hτpos (98304 * Real.sqrt 2)
      (by positivity) (oneD_absMoment8 (2 * τ) h2τ)
  have hm9 : ∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9 :=
    pow_norm_mul_gauss_integral 9 (by norm_num) 2 (by norm_num) τ hτpos (2015232 * Real.sqrt 2)
      (by positivity) (oneD_absMoment9 (2 * τ) h2τ)
  have hm10 : ∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z
      ≤ (n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10 :=
    pow_norm_mul_gauss_integral 10 (by norm_num) 2 (by norm_num) τ hτpos (3932160 * Real.sqrt 2)
      (by positivity) (oneD_absMoment10 (2 * τ) h2τ)
  -- the integral of the dominating function.
  have e1 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) := integral_add hi3 hi4
  have e2 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) := integral_add (hi3.add hi4) hi5
  have e3 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) :=
    integral_add ((hi3.add hi4).add hi5) hi6
  have e4 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) :=
    integral_add (((hi3.add hi4).add hi5).add hi6) hi7
  have e5 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) :=
    integral_add ((((hi3.add hi4).add hi5).add hi6).add hi7) hi8
  have e6 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) :=
    integral_add (((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8) hi9
  have e7 : (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z)
        + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))
      = (∫ z : Point n, c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z))
        + ∫ z : Point n, c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z) :=
    integral_add ((((((hi3.add hi4).add hi5).add hi6).add hi7).add hi8).add hi9) hi10
  have hDval : ∫ z : Point n, K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z)
        + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z) + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z)
        + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z) + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z)
        + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z) + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z)
        + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z))
      = K * (c3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
          + c4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z)
          + c5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
          + c6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z)
          + c7 * (∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z)
          + c8 * (∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z)
          + c9 * (∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z)
          + c10 * (∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
    rw [integral_const_mul, e7, e6, e5, e4, e3, e2, e1, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul, integral_const_mul]
  -- main inequality: |∫ T_E1| ≤ (moment upper bounds).
  have hmain : |∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z)|
      ≤ K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
          + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4)
          + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
          + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6)
          + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7)
          + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8)
          + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9)
          + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10)) := by
    calc |∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z)|
        = ‖∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖(gaussDdim τ (V z) - gaussDdim τ z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) :=
          integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hdom_int (ae_of_all _ hpt)
      _ = K * (c3 * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim (2 * τ) z)
            + c4 * (∫ z : Point n, ‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (∫ z : Point n, ‖z‖ ^ 5 * gaussDdim (2 * τ) z)
            + c6 * (∫ z : Point n, ‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (∫ z : Point n, ‖z‖ ^ 7 * gaussDdim (2 * τ) z)
            + c8 * (∫ z : Point n, ‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (∫ z : Point n, ‖z‖ ^ 9 * gaussDdim (2 * τ) z)
            + c10 * (∫ z : Point n, ‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := hDval
      _ ≤ K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
            + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4)
            + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
            + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6)
            + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7)
            + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8)
            + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9)
            + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKnn
          exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hm3 hc3nn) (mul_le_mul_of_nonneg_left hm4 hc4nn))
            (mul_le_mul_of_nonneg_left hm5 hc5nn)) (mul_le_mul_of_nonneg_left hm6 hc6nn))
            (mul_le_mul_of_nonneg_left hm7 hc7nn)) (mul_le_mul_of_nonneg_left hm8 hc8nn))
            (mul_le_mul_of_nonneg_left hm9 hc9nn)) (mul_le_mul_of_nonneg_left hm10 hc10nn)
  refine le_trans hmain ?_
  -- expose the explicit constant and fold `K`.
  unfold sliverRateConst
  rw [← hKdef]
  -- the τ^{−1/2} fold: substitute `w = √τ`, cap `w ≤ √τ₀`.
  rw [← inv_sqrt_eq_rpow τ hτpos]
  have hwpos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
  have hwne : Real.sqrt τ ≠ 0 := hwpos.ne'
  have hwsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτpos.le
  have hwle : Real.sqrt τ ≤ Real.sqrt τ₀ := Real.sqrt_le_sqrt hττ₀
  set w : ℝ := Real.sqrt τ with hwdef
  -- linearise: pull out `w⁻¹`.
  have hlin : K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * w ^ 3)
          + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * w ^ 4)
          + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * w ^ 5)
          + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * w ^ 6)
          + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * w ^ 7)
          + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * w ^ 8)
          + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * w ^ 9)
          + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * w ^ 10))
      = w⁻¹ * (K * (((n : ℝ) ^ 3 * C_W / 8 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)
            + (n : ℝ) ^ 2 * C_W / 4 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3))
          + (C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / 16
                * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)
              + C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / 8
                * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4)) * w
          + (C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / 8
                * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7)
              + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / 8
                * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)) * w ^ 2
          + (C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / 16
                * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8)
              + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / 8
                * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)) * w ^ 3
          + (C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / 8
                * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9)) * w ^ 4
          + (C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / 16
                * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10)) * w ^ 5)) := by
    rw [hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, ← hwsq]
    field_simp
    try ring
  rw [hlin]
  have hwinv_nn : (0 : ℝ) ≤ w⁻¹ := inv_nonneg.mpr hwpos.le
  rw [mul_comm _ w⁻¹]
  refine mul_le_mul_of_nonneg_left ?_ hwinv_nn
  refine mul_le_mul_of_nonneg_left ?_ hKnn
  gcongr

/-! ###############################################################################
    ★★★ The full CHART-Gaussian mixed Hessian slice bound (E1 port + plain half) — the `hInner0` shape.
    ############################################################################### -/

/-- **★★★ THE CHART-GAUSSIAN MIXED HESSIAN SLICE BOUND (the `hInner0` shape).**  Combines the E1 port
    `tE1_slice_abstract_mixed` (the Gaussian-replacement difference) with the plain half
    `MixedTE2Slice.mixedHessianSlice_plain_bound` (`G_τ(z)` mixed bracket) into the CHART-Gaussian mixed
    Hessian slice:
      `|∫ z, G_τ(V z)·(⟨V,Pi⟩⟨V,Pj⟩/(4τ²)−(⟨Pi,Pj⟩+⟨V,Q⟩)/(2τ))·(A₀·g)|
         ≤ (sliverRateConst + (tE2RateConst + L·n))·τ^{−1/2}`.
    Route: the add-and-subtract split
      `G_τ(V z)·bracket·(A₀·g) = (G_τ(V z)−G_τ(z))·bracket·(A₀·g) + G_τ(z)·bracket·(A₀·g)`,
    the first bounded by `tE1_slice_abstract_mixed`, the second by `mixedHessianSlice_plain_bound`; the
    add-subtract needs the two per-slice integrabilities (the E1 difference piece and the plain full
    piece), carried exactly as the diagonal `XUniformSliverFull.hRem_xuniform` carries `hIntT1`/`hIntT2`.
    This is EXACTLY the mixed Hessian inner bound (`hInner0`) that the four-term
    `MixedSliverAssembly.witness_sliver2_assembly_mixed` carries.  NOT `a₁ = R/6`. -/
theorem mixedHessianSlice_chart_bound
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (L M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z))
    (hVdisp : ∀ z : Point n, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i : ∀ z : Point n, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j : ∀ z : Point n, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F)
    (hqLip : ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * g s z - A0 (u - s) w * g s w| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * g s z) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * g s z| ≤ M)
    (hIntE1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * g s z)) volume)
    (hIntPlain : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * g s z)) volume)
    (hIntRem : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
                - (z i * z j) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * g s z)) volume) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, gaussDdim (u - s) (V z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * g s z)|
        ≤ (sliverRateConst n M₀ C_F C_W C_P C_Q τ₀
            + (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ))) * (u - s) ^ (-(1 : ℝ) / 2) := by
  have hE1 := tE1_slice_abstract_mixed V Pi Pj Q A0 g i j M₀ C_F u ε τ₀ C_W C_P C_Q
    hM₀ hC_F hC_W hC_P hC_Q hετ₀ hco hVdisp hJ3i hJ3j hJ3Q hA0bdd hgcap
  have hPlain := mixedHessianSlice_plain_bound V Pi Pj Q A0 g i j hij L M₀ C_F u ε τ₀ C_W C_P C_Q
    hL hM₀ hC_F hC_W hC_P hC_Q hετ₀ hVdisp hJ3i hJ3j hJ3Q hA0bdd hgcap hqLip hIntRem
  intro s hs
  set τ : ℝ := u - s with hτ_def
  -- the add-and-subtract split of the chart-Gaussian mixed Hessian slice.
  have hsplit : (∫ z, gaussDdim τ (V z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z))
      = (∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z))
        + ∫ z, gaussDdim τ z
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z) := by
    rw [← integral_add (hIntE1 s hs) (hIntPlain s hs)]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
  rw [hsplit]
  calc |(∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
              * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                  - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
              * (A0 τ z * g s z))
          + ∫ z, gaussDdim τ z
              * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                  - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
              * (A0 τ z * g s z)|
      ≤ |∫ z, (gaussDdim τ (V z) - gaussDdim τ z)
              * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                  - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
              * (A0 τ z * g s z)|
          + |∫ z, gaussDdim τ z
              * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
                  - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
              * (A0 τ z * g s z)| := abs_add_le _ _
    _ ≤ sliverRateConst n M₀ C_F C_W C_P C_Q τ₀ * τ ^ (-(1 : ℝ) / 2)
          + (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ)) * τ ^ (-(1 : ℝ) / 2) :=
        add_le_add (hE1 s hs) (hPlain s hs)
    _ = (sliverRateConst n M₀ C_F C_W C_P C_Q τ₀
          + (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ))) * τ ^ (-(1 : ℝ) / 2) := by ring

end QIQTH.MixedGaussReplaceSlice

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedGaussReplaceSlice
#print axioms polyChartMixed_abs_bound
#print axioms tE1_slice_abstract_mixed
#print axioms mixedHessianSlice_chart_bound
end AxiomChecks
