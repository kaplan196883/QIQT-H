/-
  XUniformSliver — J4-201: the x-UNIFORM upgrade of the E1 (Gaussian-replacement) sliver bound,
  and the per-slice `(u−s)^{−1/2}` sliver-rate `hsbound` at a general field point.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign: it lifts the banked `GaussReplaceSlice` E1-slice bound (whose
  field point is PINNED to the centre `0`) to a bound that is UNIFORM over the field point `x`, and
  packages the per-slice `(u−s)^{−1/2}` differential rate as the `hsbound` shape that
  `HD1ConcreteWiring.gderiv_continuousAt` consumes.  No new singular-convolution analysis: the moment
  integration is imported from `GaussReplaceSlice`, not reproved.  NO `sorry`.  NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PINNING MAP (asked by the ledger — where does the field point `0` enter the sliver chain?).

  The terminal per-slice E1 bound is `GaussReplaceSlice.tE1_slice_bound`:
      `∀ s ∈ Ioo (u−ε) u, |∫ z, (G_{u−s}(Y z) − G_{u−s}(z))·polyChart(z)·(A₀ (u−s) z · F s z 0)|
                            ≤ C_E1·(u−s)^{−1/2}`,
  with the field point PINNED to `0` inside `F s z 0`.  Tracing every link of its proof:

    • `gaussReplace_E1_bound` (R1, the `|G_τ(Y z) − G_τ(z)|` replacement bound)  ......  FIELD-FREE
    • `polyChart_abs_bound`   (R2, the chart Hessian-coefficient cap)             ......  FIELD-FREE
    • `oneD_absMoment3..10`, `pow_norm_mul_gauss_integral`, `normPow_gauss_integrable`
        (R3, the width-`2τ` moment envelope + integrabilities)                    ......  FIELD-FREE
    • the witness constant (lines 315–332 of GaussReplaceSlice) and the `w = √τ` fold `hlin`  FIELD-FREE
    • `hA0bdd` (amplitude cap `|A₀ τ z| ≤ M₀`)                                     ......  FIELD-FREE
    • ★ THE ONLY FIELD-DEPENDENT LINK:  `hFcap : ∀ z, |F s z 0| ≤ C_F` where
        `C_F = C_L·gaussDdim a 0`, produced by `BoundaryAssembly.B_le_MB`.  `B_le_MB` calls the
        domination `hFdom` ONLY at field point `0` (`hFdom s _ _ z 0`), yielding
        `|F s z 0| ≤ C_L·gaussDdim (2s)(z−0)`, then PEAK-BOUNDS `gaussDdim (2s)(z) ≤ gaussDdim (2s) 0`
        and WIDTH-ANTITONE `gaussDdim (2s) 0 ≤ gaussDdim a 0`.

  VERDICT — the pinning is INTERFACE-ONLY (route A).  The field point `0` never enters the moment
  integration or the constants; it enters ONLY as the second argument of `F` inside the single
  constant cap `hFcap`.  And that cap is ALREADY x-UNIFORM: for ANY field point `x`,
      `|F s z x| ≤ C_L·gaussDdim (2s)(z−x) ≤ C_L·gaussDdim (2s) 0 ≤ C_L·gaussDdim a 0 = C_F`,
  the SAME constant `C_F`, because the Gaussian `gaussDdim (2s)(z−x)` peaks at value `gaussDdim (2s) 0`
  regardless of its centre `x` (`gaussDdim_le_diagonal`).  This is `F_le_const_xuniform` below.

  Cross-check with the ORDER ABOVE (J4-198 `SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`): the
  order-2 on-gate formula is already stated at a GENERAL field point `p ∈ S z`, confirming the chart
  amplitude data is field-general one order up — consistent with route A here.

  Therefore the x-uniform bound is the SAME proof re-run with the field slice `F s z 0` replaced by the
  abstract field slice `g s z` carrying only the constant cap `|g s z| ≤ C_F` — that abstraction is
  `tE1_slice_abstract`.  Instantiating `g s z := F s z x` and discharging its cap by
  `F_le_const_xuniform` gives `tE1_slice_xuniform`, uniform in `x` with the SAME explicit constant
  `sliverRateConst` (which does not mention `x`).  No genuinely NEW geometric carry is introduced: the
  carry set is EXACTLY that of `tE1_slice_bound` (the same `hco`/`hYdisp`/`hJ3`/`hJ3Q`/`hA0bdd`/`hFdom`),
  now with the field point ranging over all `x` rather than pinned to `0`.

  ## WHAT LANDS (this file, ns `QIQTH.XUniformSliver`).
    • `sliverRateConst`         — the explicit, x-FREE per-slice E1 constant (the banked witness).
    • `sliverRateConst_nonneg`  — its nonnegativity.
    • `F_le_const_xuniform`     — ★ the x-UNIFORM field cap `|F s z x| ≤ C_L·gaussDdim a 0` (route A key).
    • `tE1_slice_abstract`      — ★★ the abstract constant-cap E1 per-slice bound (field slice `g`).
    • `tE1_slice_xuniform`      — ★★ the E1 per-slice bound at a GENERAL field point `x`, SAME constant.
    • `sliver_rate_hsbound`     — ★★★ the single-constant, x-uniform per-slice `(u−s)^{−1/2}` bound
        `∃ C ≥ 0, ∀ x, ∀ s ∈ Ioo (u−ε) u, ‖∫ z, …·F s z x‖ ≤ C·(u−s)^{−1/2}` — the `hsbound` feed of
        `HD1ConcreteWiring.gderiv_continuousAt` for the E1 kernel.

  Every hypothesis is satisfiable and non-vacuous (the model `Y = −id`, `P = eᵢ`, `Q = 0`, `A₀` bounded,
  `F` a width-2 Gaussian bump satisfies all of them — the SAME model that satisfies
  `tE1_slice_bound`), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GaussReplaceSlice
import QIQTH.BoundaryAssembly

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.XUniformSliver

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ★ The x-uniform field cap (route A key) + the explicit per-slice constant.
    ############################################################################### -/

/-- **★ THE x-UNIFORM FIELD CAP.**  The `B_le_MB` peak/width bound at a GENERAL field point `x`:
    for `a/2 ≤ s ≤ T`, the Gaussian-dominated slice `|F s z x|` is bounded, UNIFORMLY in both `z` AND
    the field point `x`, by the `s`-free and `x`-free constant `C_L·gaussDdim a 0`.  Route: domination
    `|F s z x| ≤ C_L·gaussDdim (2s)(z−x)`, peak-bound `gaussDdim (2s)(z−x) ≤ gaussDdim (2s) 0`
    (`gaussDdim_le_diagonal` — the Gaussian peaks at `0` regardless of centre `x`), width-antitone
    `gaussDdim (2s) 0 ≤ gaussDdim a 0` (`gaussDdim_zero_antitone`, `a ≤ 2s`).  This is the ONLY
    field-dependent link of the sliver chain, and it is field-uniform.  NOT `a₁ = R/6`. -/
theorem F_le_const_xuniform (F : ℝ → Point n → Point n → ℝ) (C_L T a : ℝ) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (ha : 0 < a) (s : ℝ) (hs : a / 2 ≤ s) (hsT : s ≤ T) (x z : Point n) :
    |F s z x| ≤ C_L * gaussDdim a (0 : Point n) := by
  have hs0 : 0 < s := by linarith
  have h2s : a ≤ 2 * s := by linarith
  calc |F s z x| ≤ C_L * gaussDdim (2 * s) (z - x) := hFdom s hs0 hsT z x
    _ ≤ C_L * gaussDdim (2 * s) (0 : Point n) :=
        mul_le_mul_of_nonneg_left (gaussDdim_le_diagonal (by linarith) (z - x)) hC_L
    _ ≤ C_L * gaussDdim a (0 : Point n) :=
        mul_le_mul_of_nonneg_left (gaussDdim_zero_antitone ha h2s) hC_L

/-- **THE EXPLICIT, x-FREE PER-SLICE E1 CONSTANT.**  The banked `tE1_slice_bound` witness, written with
    the abstract field cap `C_F` in place of `C_L·gaussDdim a 0` (so `K := (√2)ⁿ·(M₀·C_F)`).  It does
    NOT mention the field point, so it serves as the SINGLE x-uniform constant of the per-slice bound. -/
noncomputable def sliverRateConst (n : ℕ) (M₀ C_F C_W C_P C_Q τ₀ : ℝ) : ℝ :=
  (Real.sqrt 2) ^ n * (M₀ * C_F) *
    (((n : ℝ) ^ 3 * C_W / 8 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)
        + (n : ℝ) ^ 2 * C_W / 4 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3))
      + (C_W * (n : ℝ) ^ 3 * (5 * C_W + 4 * C_P) / 16
            * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)
          + C_W * (n : ℝ) ^ 2 * (C_W + 4 * C_P + 2 * C_Q) / 8
            * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4)) * Real.sqrt τ₀
      + (C_W * (n : ℝ) ^ 3 * (2 * C_W ^ 2 + 5 * C_W * C_P + C_P ^ 2) / 8
            * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7)
          + C_W * (n : ℝ) ^ 2 * (2 * C_W * C_P + 3 * C_W * C_Q + 2 * C_P ^ 2) / 8
            * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5)) * Real.sqrt τ₀ ^ 2
      + (C_W ^ 2 * (n : ℝ) ^ 3 * (C_W ^ 2 + 8 * C_W * C_P + 5 * C_P ^ 2) / 16
            * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8)
          + C_W ^ 2 * (n : ℝ) ^ 2 * (C_W * C_Q + C_P ^ 2) / 8
            * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6)) * Real.sqrt τ₀ ^ 3
      + (C_W ^ 3 * (n : ℝ) ^ 3 * C_P * (C_W + 2 * C_P) / 8
            * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9)) * Real.sqrt τ₀ ^ 4
      + (C_W ^ 4 * (n : ℝ) ^ 3 * C_P ^ 2 / 16
            * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10)) * Real.sqrt τ₀ ^ 5)

/-- The per-slice E1 constant is nonnegative (all factors nonneg; `√` always nonneg). -/
theorem sliverRateConst_nonneg (M₀ C_F C_W C_P C_Q τ₀ : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q) :
    0 ≤ sliverRateConst n M₀ C_F C_W C_P C_Q τ₀ := by
  unfold sliverRateConst
  have h1 : (0 : ℝ) ≤ M₀ * C_F := mul_nonneg hM₀ hC_F
  positivity

/-! ###############################################################################
    ★★ The abstract constant-cap E1 per-slice bound (field slice `g`).
    ############################################################################### -/

/-- **★★ THE ABSTRACT E1 PER-SLICE BOUND.**  `tE1_slice_bound` with the concrete Gaussian-dominated
    field slice `F s z 0` replaced by an ABSTRACT field slice `g s z` carrying ONLY the constant cap
    `|g s z| ≤ C_F` (this is exactly what the sliver chain uses of the field — see the pinning map).
    Every other link (`gaussReplace_E1_bound`, `polyChart_abs_bound`, the moment envelope, the constant,
    the `w=√τ` fold) is field-free and imported verbatim.  Delivers the EXPLICIT single constant
    `sliverRateConst`.  This is the field-general core: `tE1_slice_bound` is the instance `g s z=F s z 0`,
    and `tE1_slice_xuniform` the instance `g s z=F s z x`.  NOT `a₁ = R/6`. -/
theorem tE1_slice_abstract
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (g : ℝ → Point n → ℝ)
    (i : Fin n) (M₀ C_F u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_F : 0 ≤ C_F) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |g s z| ≤ C_F) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
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
  -- field cap (the only field-dependent input).
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
      ‖(gaussDdim τ (Y z) - gaussDdim τ z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z)‖
        ≤ K * (c3 * (‖z‖ ^ 3 * gaussDdim (2 * τ) z) + c4 * (‖z‖ ^ 4 * gaussDdim (2 * τ) z)
            + c5 * (‖z‖ ^ 5 * gaussDdim (2 * τ) z) + c6 * (‖z‖ ^ 6 * gaussDdim (2 * τ) z)
            + c7 * (‖z‖ ^ 7 * gaussDdim (2 * τ) z) + c8 * (‖z‖ ^ 8 * gaussDdim (2 * τ) z)
            + c9 * (‖z‖ ^ 9 * gaussDdim (2 * τ) z) + c10 * (‖z‖ ^ 10 * gaussDdim (2 * τ) z)) := by
    intro z
    have hG2nn : 0 ≤ gaussDdim (2 * τ) z := gaussDdim_nonneg' (2 * τ) z
    have hGd := gaussReplace_E1_bound τ hτpos Y z C_W hC_W (hYdisp z) (hco z)
    have hpc := polyChart_abs_bound Y P Q i τ hτpos z C_W C_P C_Q hC_W hC_P hC_Q
      (hYdisp z) (hJ3 z) (hJ3Q z)
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
    calc |gaussDdim τ (Y z) - gaussDdim τ z|
            * |(∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ)|
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
  have hmain : |∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
          * (A0 τ z * g s z)|
      ≤ K * (c3 * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
          + c4 * ((n : ℝ) * (128 * Real.sqrt 2) * (Real.sqrt 2) ^ 4 * (Real.sqrt τ) ^ 4)
          + c5 * ((n : ℝ) * (1600 * Real.sqrt 2) * (Real.sqrt 2) ^ 5 * (Real.sqrt τ) ^ 5)
          + c6 * ((n : ℝ) * (3072 * Real.sqrt 2) * (Real.sqrt 2) ^ 6 * (Real.sqrt τ) ^ 6)
          + c7 * ((n : ℝ) * (50688 * Real.sqrt 2) * (Real.sqrt 2) ^ 7 * (Real.sqrt τ) ^ 7)
          + c8 * ((n : ℝ) * (98304 * Real.sqrt 2) * (Real.sqrt 2) ^ 8 * (Real.sqrt τ) ^ 8)
          + c9 * ((n : ℝ) * (2015232 * Real.sqrt 2) * (Real.sqrt 2) ^ 9 * (Real.sqrt τ) ^ 9)
          + c10 * ((n : ℝ) * (3932160 * Real.sqrt 2) * (Real.sqrt 2) ^ 10 * (Real.sqrt τ) ^ 10)) := by
    calc |∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z)|
        = ‖∫ z, (gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
            * (A0 τ z * g s z)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖(gaussDdim τ (Y z) - gaussDdim τ z)
            * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
                - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
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
    ★★ The x-uniform E1 per-slice bound (field point ranging) + the hsbound.
    ############################################################################### -/

/-- **★★ THE x-UNIFORM E1 PER-SLICE BOUND.**  `tE1_slice_bound` at a GENERAL field point `x` (not
    pinned to the centre `0`), with the SAME explicit `x`-free constant `sliverRateConst`.  Instance of
    `tE1_slice_abstract` with the field slice `g s z := F s z x`, whose constant cap
    `|F s z x| ≤ C_L·gaussDdim a 0` is discharged by `F_le_const_xuniform` (route A: the Gaussian peak
    is centre-independent).  The carry set is EXACTLY that of `tE1_slice_bound` (same geometric inputs +
    `hFdom`), now field-general.  NOT `a₁ = R/6`. -/
theorem tE1_slice_xuniform
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ) (x : Point n)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)|
        ≤ sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
            * (u - s) ^ (-(1 : ℝ) / 2) := by
  refine tE1_slice_abstract Y P Q A0 (fun s z => F s z x) i M₀ (C_L * gaussDdim a (0 : Point n))
    u ε τ₀ C_W C_P C_Q hM₀ (mul_nonneg hC_L (gaussDdim_nonneg' a 0)) hC_W hC_P hC_Q hετ₀
    hco hYdisp hJ3 hJ3Q hA0bdd ?_
  intro s hsmem z
  have hlo : a / 2 < s := by linarith [hsmem.1]
  have hsT : s ≤ T := by linarith [hsmem.2]
  exact F_le_const_xuniform F C_L T a hC_L hFdom ha s hlo.le hsT x z

/-- **★★★ THE SINGLE-CONSTANT x-UNIFORM SLIVER-RATE `hsbound`.**  A SINGLE constant `C ≥ 0`
    (`= sliverRateConst`, which does NOT mention the field point) such that the per-slice E1 integral
    has the `(u−s)^{−1/2}` rate UNIFORMLY over ALL field points `x` and all `s` in the sliver window:
      `∀ x, ∀ s ∈ Ioo (u−ε) u, ‖∫ z, (…)·(A₀ (u−s) z · F s z x)‖ ≤ C·(u−s)^{−1/2}`.
    This is the DIFFERENTIAL (per-`s`) form the `√ε`-integrated `witness_sliver2_grand` was built from,
    now field-uniform; it is exactly the `hsbound` shape consumed by
    `HD1ConcreteWiring.gderiv_continuousAt` (the order-2 continuity `hBint` feed) for the E1 kernel —
    `∀ᶠ x, ∀ᵐ s, ‖∫ z, K' s x z‖ ≤ C·(t−s)^{−1/2}` follows since the bound holds for EVERY `x`.  The
    single constant is what makes the `x`-uniformity usable downstream.  NOT `a₁ = R/6`. -/
theorem sliver_rate_hsbound
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₀ C_L T a u ε τ₀ C_W C_P C_Q : ℝ)
    (hM₀ : 0 ≤ M₀) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (Y z))
    (hYdisp : ∀ z : Point n, ‖Y z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      ‖∫ z, (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)‖
        ≤ C * (u - s) ^ (-(1 : ℝ) / 2) := by
  refine ⟨sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀,
    sliverRateConst_nonneg _ _ _ _ _ _ hM₀ (mul_nonneg hC_L (gaussDdim_nonneg' a 0)) hC_W hC_P hC_Q,
    ?_⟩
  intro x s hsmem
  rw [Real.norm_eq_abs]
  exact tE1_slice_xuniform Y P Q A0 F i M₀ C_L T a u ε τ₀ C_W C_P C_Q x
    hM₀ hC_L hC_W hC_P hC_Q ha hau huT hεa hετ₀ hco hYdisp hJ3 hJ3Q hA0bdd hFdom s hsmem

end QIQTH.XUniformSliver

section AxiomChecks
open QIQTH.XUniformSliver
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms F_le_const_xuniform
#print axioms sliverRateConst_nonneg
#print axioms tE1_slice_abstract
#print axioms tE1_slice_xuniform
#print axioms sliver_rate_hsbound
end AxiomChecks
