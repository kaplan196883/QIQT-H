/-
  GaussianWidthTolerant — the WIDTH-TOLERANCE step of M6 (attacking gap **G3 (WIDTH)** of the
  parametrix-residual ↔ Levi/Duhamel convergence wiring; see `ParametrixResidualBaseKernel.lean`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE PROBLEM (G3, verbatim from the M6-2 assessment).

  The convergence machinery's exact self-similar convolution identity
  (`GaussianConvBound.gaussTimePow_conv_beta`, iterated in `TimeSimplexBeta.iterKernel_eq`) is
  WIDTH-LOCKED to the NARROW base Gaussian `gaussDdim τ` (width `4τ`) at MATCHED time:

      heatConv (τ^a · G_τ) (σ^b · G_σ) t x y  =  t^(a+b+1)·Β(a+1,b+1) · G_t(x−y)          (★)

  The width is locked because the Gaussian's width argument is LITERALLY the convolution time: the
  proof rests on C1 (`GaussianConvolution.gaussDdim_conv (t−s) s`, "variances add") which needs the
  two inner Gaussians to sit at times `t−s` and `s` summing to the outer `t` — the SAME `t` whose
  Gaussian `G_t` appears on the right of (★).

  But the parametrix residual only supplies a bound by the WIDE Gaussian
  `gaussDdimWide t v = (√2)ⁿ · gaussDdim (2t) v` — the base Gaussian at DOUBLED time `2t`
  (`ParametrixResidualBaseKernel.gaussDdimWide_eq_scaled_gaussDdim`).  A wide Gaussian is NOT
  `≤ C·(same-time narrow gaussDdim)` (the ratio `gaussDdim(2t)/gaussDdim(t) → ∞`), so a direct
  domination into (★) FAILS.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE RESOLUTION — the Levi iteration IS SCALE-INVARIANT in a Gaussian WIDTH factor `κ > 0`.

  Convolution adds variances: `G_{κa} * G_{κb} = G_{κ(a+b)}` (C1 at rescaled times).  So running the
  ENTIRE self-similar chain with the width-`κ` base Gaussian `gaussDdim (κ·τ)` closes IDENTICALLY —
  the inner convolution `gaussDdim (κ(t−s)) * gaussDdim (κs) = gaussDdim (κt)` still lands the SAME
  outer-width Gaussian `gaussDdim (κt)`, and the TIME integral `∫₀ᵗ (t−s)^a s^b ds` (hence the whole
  Β/Γ factor) is UNTOUCHED by `κ`.  The residual's wide Gaussian is exactly the `κ = 2` case
  (`gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`), so it iterates.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS HERE.

    • `gaussDdim_conv_scaled` (F2) — the RESCALED-WIDTH convolution semigroup
          `∫ z, G_{κt}(x−z)·G_{κs}(z−y) dz = G_{κ(t+s)}(x−y)`   (`κ,t,s > 0`),
      a one-line corollary of C1 (`gaussDdim_conv (κt) (κs)`, `κt + κs = κ(t+s)`).  THE building block.

    • `gaussTimePow_conv_scaled` (F1 core) — the WIDTH-TOLERANT self-similar identity: the exact
      analogue of `gaussTimePow_conv`, with EVERY Gaussian widened by `κ`,
          heatConv (τ^a·G_{κτ}) (σ^b·G_{κσ}) t x y  =  (∫₀ᵗ (t−s)^a s^b ds) · G_{κt}(x−y).

    • `gaussTimePow_conv_beta_scaled` (F1 core) — its closed Β/Γ form
          … = t^(a+b+1) · (Γ(a+1)Γ(b+1)/Γ(a+b+2)) · G_{κt}(x−y).
      The `κ` threads through the Gaussian ONLY; the `t^(a+b+1)·Β` factor is width-independent.

    • `baseKernelW`, `iterKernelW`, `iterKernelW_eq` (F1, the full engine) — the width-`κ` base kernel
      `τ^α·G_{κτ}` and its `k`-fold convolution, with the SAME factorial (Γ) decay:
          iterKernelW κ α k t x y = (Γ(α+1)^k / Γ(k·(α+1))) · t^(k·(α+1)−1) · G_{κt}(x−y).
      This is the crux "the iteration is scale-invariant": the width-locked `TimeSimplexBeta` chain
      REBUILDS verbatim at general width `κ`, the Γ-telescoping unchanged.

    • `iterKernelW_series_summable` (F1) — the width-`κ` iterated-kernel series is summable
      (`α ≥ 0`, `t > 0`): the model coefficient is width-INDEPENDENT, so `LeviSeries.modelCoeff_summable`
      applies verbatim (the `G_{κt}` is a `k`-constant factor).

    • `gaussDdimWide_eq_scaled_baseKernelW` — the residual connection: the residual's WIDE Gaussian IS
      the width-`κ=2` base kernel, `gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`.  So the
      residual bound is a width-2 base-kernel bound, and (by the above) width-2 base kernels iterate to
      a convergent series — G3 is discharged at the model level.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FLOORS.

    • F1 (LANDED) — the width-tolerant self-similar identity + full iterated-kernel formula
      (`iterKernelW_eq`) + series summability (`iterKernelW_series_summable`).  The Levi iteration is
      PROVED scale-invariant: an `8t`-width (= `gaussDdim (2t)`, `κ = 2`) bound iterates to a
      convergent Neumann series.  **G3 is closed at the model level.**
    • F2 (LANDED) — `gaussDdim_conv_scaled`, the rescaled-width convolution semigroup building block.
    • F3 (this docstring) — precise assessment: where the width is locked (verbatim, C1's matched-time
      convolution) and why the fix is a clean rescaling.

  ⚠ WHAT G3'S RESOLUTION DOES *NOT* CLOSE (honest remaining scope).
    G3 was ONE of the three residual↔convergence mismatches.  Still open, ORTHOGONAL to width:
      (G1) GLOBAL vs LOCAL — the residual bound is `∀ᶠ v in 𝓝 0` (near the diagonal); the Levi
           convolution integrates over ALL space.  THIS IS THE DEEP GAP (far-field extension).
      (G2) ALL-`τ` vs FIXED-`t` — `hEbound` quantifies every `τ > 0` with the `τ^α` power; the residual
           bound is at a single fixed `t` (residual order `α = 0`).
    Also, WIRING the width-`κ` engine into `LeviSeries.iterConv_bound`/`leviSeries_summable`
    (currently phrased against the width-`1` `baseKernel`/`iterKernel`) is a mechanical
    re-parametrization: the domination lemmas (`heatConv_le_of_abs_le_pos`, etc.) are width-AGNOSTIC
    (any dominators `A',B'`), so `iterConv_bound` re-states verbatim with `A' = C·baseKernelW κ α`,
    `B' = C^k·iterKernelW κ α` and `iterKernelW_eq`/`iterKernelW_series_summable` as the model — no new
    analysis, only a κ-parametrized copy.  Deferred (not required to certify G3's resolution).

  This is the WIDTH-TOLERANCE step of M6.  NOT the true curved kernel, the Seeley–DeWitt recursion,
  or `a₁ = R/6`.  No axioms beyond the standard three, no `sorry`, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.TimeSimplexBeta
import QIQTH.GaussianConvBound
import QIQTH.GaussianConvolution
import QIQTH.ParametrixResidualBaseKernel

open Real MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianConvolution QIQTH.HeatDuhamel
open QIQTH.GaussianConvBound QIQTH.TimeSimplexBeta QIQTH.LeviSeries
open scoped Interval

namespace QIQTH.GaussianWidthTolerant

set_option maxHeartbeats 2400000

variable {n : ℕ}

/-! ### 1. F2 — the RESCALED-WIDTH Gaussian convolution semigroup (the building block). -/

/-- **★ THE RESCALED-WIDTH CONVOLUTION SEMIGROUP (F2).**  For a fixed width factor `κ > 0` and
    `t, s > 0`,
        `∫ z, gaussDdim (κ·t) (x − z) · gaussDdim (κ·s) (z − y) dz = gaussDdim (κ·(t+s)) (x − y)`.
    The convolution of two width-`κ` Gaussians at times `t` and `s` is the width-`κ` Gaussian at time
    `t+s`.  Proof: C1 (`gaussDdim_conv (κt) (κs)`, "variances add") plus `κ·t + κ·s = κ·(t+s)`.  This
    is the one fact that makes the whole Levi chain scale-invariant in the width. -/
theorem gaussDdim_conv_scaled (κ t s : ℝ) (hκ : 0 < κ) (ht : 0 < t) (hs : 0 < s) (x y : Point n) :
    ∫ z : Point n, gaussDdim (κ * t) (x - z) * gaussDdim (κ * s) (z - y)
      = gaussDdim (κ * (t + s)) (x - y) := by
  rw [gaussDdim_conv (κ * t) (κ * s) (mul_pos hκ ht) (mul_pos hκ hs) x y,
      show κ * t + κ * s = κ * (t + s) from by ring]

/-! ### 2. F1 core — the WIDTH-TOLERANT self-similar convolution identity. -/

/-- **★ THE WIDTH-TOLERANT SELF-SIMILAR IDENTITY (F1 core).**  The exact analogue of
    `GaussianConvBound.gaussTimePow_conv` with every Gaussian widened by the fixed factor `κ > 0`:
        `heatConv (τ^a · G_{κτ}) (σ^b · G_{κσ}) t x y = (∫₀ᵗ (t−s)^a s^b ds) · G_{κt}(x−y)`.
    Proof mirrors `gaussTimePow_conv` verbatim, EXCEPT the inner `z`-convolution closes via the
    rescaled semigroup `gaussDdim_conv (κ(t−s)) (κs)` (`κ(t−s) + κs = κt`), landing the OUTER-width
    Gaussian `G_{κt}`.  The `z`-independent scalar `(t−s)^a s^b` pulls out and the (now `s`-constant)
    Gaussian `G_{κt}(x−y)` pulls out of the `s`-interval integral — the TIME integral is untouched by
    `κ`.  Carries `κ > 0, t > 0` (genuine). -/
theorem gaussTimePow_conv_scaled (κ a b : ℝ) (hκ : 0 < κ) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    heatConv (fun τ p q => τ ^ a * gaussDdim (κ * τ) (p - q))
             (fun σ p q => σ ^ b * gaussDdim (κ * σ) (p - q)) t x y
      = (∫ s in (0)..t, (t - s) ^ a * s ^ b) * gaussDdim (κ * t) (x - y) := by
  simp only [heatConv]
  have hkey : ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.uIoc 0 t →
      (∫ z : Point n,
          ((t - s) ^ a * gaussDdim (κ * (t - s)) (x - z)) * (s ^ b * gaussDdim (κ * s) (z - y)))
        = ((t - s) ^ a * s ^ b) * gaussDdim (κ * t) (x - y) := by
    have hne : ({t} : Set ℝ)ᶜ ∈ MeasureTheory.ae volume := by
      rw [MeasureTheory.mem_ae_iff, compl_compl]
      exact MeasureTheory.measure_singleton t
    filter_upwards [hne] with s hs
    intro hmem
    rw [Set.uIoc_of_le ht.le] at hmem
    obtain ⟨hs0, hst⟩ := hmem
    have hsne : s ≠ t := by simpa using hs
    have hts : 0 < t - s := by
      have : s < t := lt_of_le_of_ne hst hsne
      linarith
    calc (∫ z : Point n,
            ((t - s) ^ a * gaussDdim (κ * (t - s)) (x - z)) * (s ^ b * gaussDdim (κ * s) (z - y)))
        = ∫ z : Point n,
            ((t - s) ^ a * s ^ b) *
              (gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
          ring
      _ = ((t - s) ^ a * s ^ b) *
            ∫ z : Point n, gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y) :=
          integral_const_mul _ _
      _ = ((t - s) ^ a * s ^ b) * gaussDdim (κ * ((t - s) + s)) (x - y) := by
          rw [gaussDdim_conv_scaled κ (t - s) s hκ hts hs0 x y]
      _ = ((t - s) ^ a * s ^ b) * gaussDdim (κ * t) (x - y) := by
          rw [show (t - s) + s = t from by ring]
  rw [intervalIntegral.integral_congr_ae hkey]
  exact intervalIntegral.integral_mul_const _ _

/-- **★ THE WIDTH-TOLERANT SELF-SIMILAR IDENTITY IN CLOSED Β/Γ FORM (F1 core).**  Combine the
    width-tolerant identity with the (width-independent) Beta time integral
    (`GaussianConvBound.betaTimeIntegral_eq`): for `κ > 0, a > −1, b > −1, t > 0`,
        `heatConv (τ^a·G_{κτ}) (σ^b·G_{κσ}) t x y
           = t^(a+b+1) · (Γ(a+1)Γ(b+1)/Γ(a+b+2)) · G_{κt}(x−y)`.
    The Β/Γ factor `t^(a+b+1)·Β(a+1,b+1)` is EXACTLY as in the narrow (`κ = 1`) case — the width `κ`
    lives entirely in the Gaussian `G_{κt}`. -/
theorem gaussTimePow_conv_beta_scaled (κ a b : ℝ) (hκ : 0 < κ) (ha : -1 < a) (hb : -1 < b)
    (t : ℝ) (ht : 0 < t) (x y : Point n) :
    heatConv (fun τ p q => τ ^ a * gaussDdim (κ * τ) (p - q))
             (fun σ p q => σ ^ b * gaussDdim (κ * σ) (p - q)) t x y
      = t ^ (a + b + 1) * (Real.Gamma (a + 1) * Real.Gamma (b + 1) / Real.Gamma (a + b + 2))
          * gaussDdim (κ * t) (x - y) := by
  rw [gaussTimePow_conv_scaled κ a b hκ t ht x y, betaTimeIntegral_eq a b ha hb t ht]

/-! ### 3. F1 — the WIDTH-TOLERANT base kernel and its iterated convolution. -/

/-- **The width-`κ` model kernel** `baseKernelW κ α τ p q = τ^α · gaussDdim (κ·τ) (p−q)` — the
    `TimeSimplexBeta.baseKernel` with the Gaussian widened by the fixed factor `κ`. -/
noncomputable def baseKernelW (κ α : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => τ ^ α * gaussDdim (κ * τ) (p - q)

/-- **The `k`-fold iterated convolution** of `baseKernelW κ α` (mirrors `TimeSimplexBeta.iterKernel`):
    `iterKernelW κ α 1 = baseKernelW κ α`, and each step left-convolves once more by the base. -/
noncomputable def iterKernelW (κ α : ℝ) : ℕ → (ℝ → Point n → Point n → ℝ)
  | 0 => baseKernelW κ α
  | 1 => baseKernelW κ α
  | (k + 2) => heatConvK (baseKernelW κ α) (iterKernelW κ α (k + 1))

/-- One base factor: `iterKernelW κ α 1 = baseKernelW κ α`. -/
theorem iterKernelW_one (κ α : ℝ) :
    (iterKernelW κ α 1 : ℝ → Point n → Point n → ℝ) = baseKernelW κ α := rfl

/-- The recursion step (for `k ≥ 1`): `iterKernelW κ α (k+1) = heatConvK (baseKernelW κ α)
    (iterKernelW κ α k)`. -/
theorem iterKernelW_succ (κ α : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (iterKernelW κ α (k + 1) : ℝ → Point n → Point n → ℝ)
      = heatConvK (baseKernelW κ α) (iterKernelW κ α k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rfl

/-- Auxiliary (∀-inside) form of `iterKernelW_eq`, so the inductive hypothesis is universally
    quantified over the convolution variables `t, x, y`. -/
theorem iterKernelW_eq_aux (κ α : ℝ) (hκ : 0 < κ) (hα : -1 < α) {k : ℕ} (hk : 1 ≤ k) :
    ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      iterKernelW κ α k t x y
        = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
            * t ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim (κ * t) (x - y) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht x y
      rw [iterKernelW_one]
      simp only [baseKernelW, Nat.cast_one, pow_one, one_mul]
      rw [div_self (ne_of_gt (Real.Gamma_pos_of_pos (by linarith : (0:ℝ) < α + 1))), one_mul,
          show (α + 1) - 1 = α from by ring]
  | succ k hk IH =>
      intro t ht x y
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hα1 : (0:ℝ) < α + 1 := by linarith
      have hkpos : (0:ℝ) < (k : ℝ) * (α + 1) := mul_pos (by linarith) hα1
      have hk1pos : (0:ℝ) < ((k : ℝ) + 1) * (α + 1) := mul_pos (by linarith) hα1
      have hbkgt : (-1:ℝ) < (k : ℝ) * (α + 1) - 1 := by linarith
      have hGk : Real.Gamma ((k : ℝ) * (α + 1)) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hkpos)
      have hGk1 : Real.Gamma (((k : ℝ) + 1) * (α + 1)) ≠ 0 :=
        ne_of_gt (Real.Gamma_pos_of_pos hk1pos)
      -- Unfold one iteration.
      rw [iterKernelW_succ κ α hk, heatConvK_apply]
      -- Rewrite `iterKernelW κ α k` a.e. in the `s`-integral into the model kernel via the IH.
      have hstep : heatConv (baseKernelW κ α) (iterKernelW κ α k) t x y
          = heatConv (baseKernelW κ α)
              (fun σ p q => (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * (σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim (κ * σ) (p - q))) t x y := by
        simp only [heatConv]
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s hmem => ?_))
        rw [Set.uIoc_of_le ht.le] at hmem
        obtain ⟨hs0, _⟩ := hmem
        refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        dsimp only
        rw [IH s hs0 z y]
        ring
      rw [hstep]
      -- Pull the constant `c_k` out of the RIGHT kernel.
      rw [show heatConv (baseKernelW κ α)
                (fun σ p q => (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                    * (σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim (κ * σ) (p - q))) t x y
              = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * heatConv (baseKernelW κ α)
                      (fun σ p q => σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim (κ * σ) (p - q)) t x y
            from heatConv_smul_right _ _ _ _ _ _]
      -- Apply the WIDTH-TOLERANT C2 self-similar identity with `a = α`, `b = k(α+1) − 1`.
      unfold baseKernelW
      rw [gaussTimePow_conv_beta_scaled κ α ((k : ℝ) * (α + 1) - 1) hκ hα hbkgt t ht x y]
      -- Γ telescoping + rpow-exponent arithmetic (verbatim as the narrow case).
      push_cast
      rw [pow_succ,
          show α + ((k : ℝ) * (α + 1) - 1) + 1 = ((k : ℝ) + 1) * (α + 1) - 1 from by ring,
          show ((k : ℝ) * (α + 1) - 1) + 1 = (k : ℝ) * (α + 1) from by ring,
          show α + ((k : ℝ) * (α + 1) - 1) + 2 = ((k : ℝ) + 1) * (α + 1) from by ring]
      field_simp

/-- **★ THE WIDTH-TOLERANT ITERATED-CONVOLUTION FORMULA (F1, the scale-invariant factorial engine).**
    For `κ > 0, α > −1, t > 0`, and `k ≥ 1`,
        `iterKernelW κ α k t x y
           = (Γ(α+1)^k / Γ(k·(α+1))) · t^(k·(α+1) − 1) · gaussDdim (κ·t) (x−y)`.
    IDENTICAL to `TimeSimplexBeta.iterKernel_eq` except the Gaussian is widened to `gaussDdim (κ·t)`:
    the width-locked `TimeSimplexBeta` chain rebuilds verbatim at general width `κ`, the Γ-telescoping
    factorial decay `1/Γ(k(α+1))` unchanged.  **This is the proof that the Levi iteration is
    scale-invariant** — the parametrix residual's `κ = 2` (doubled-time) Gaussian iterates with the
    SAME convergent factorial coefficient. -/
theorem iterKernelW_eq (κ α : ℝ) (hκ : 0 < κ) (hα : -1 < α) (t : ℝ) (ht : 0 < t) (x y : Point n)
    {k : ℕ} (hk : 1 ≤ k) :
    iterKernelW κ α k t x y
      = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
          * t ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim (κ * t) (x - y) :=
  iterKernelW_eq_aux κ α hκ hα hk t ht x y

/-! ### 4. F1 — the width-tolerant iterated-kernel series is summable. -/

/-- **★ THE WIDTH-TOLERANT SERIES CONVERGES (F1).**  For `κ > 0, α ≥ 0, t > 0`, and `x y`,
        `Summable (fun k => iterKernelW κ α (k+1) t x y)`.
    The MODEL coefficient `LeviSeries.modelCoeff α t (k+1)` is WIDTH-INDEPENDENT — the width `κ` only
    scales the `k`-constant Gaussian `gaussDdim (κ·t) (x−y)` — so each term is
    `modelCoeff α t (k+1) · gaussDdim (κ·t) (x−y)` (`iterKernelW_eq`) and
    `LeviSeries.modelCoeff_summable` applies verbatim.  The factorial (Γ) decay that drives
    convergence is UNAFFECTED by the width, so the `κ = 2` residual bound iterates to a convergent
    Neumann series — **the resolution of G3.** -/
theorem iterKernelW_series_summable (κ α t : ℝ) (hκ : 0 < κ) (hα : 0 ≤ α) (ht : 0 < t)
    (x y : Point n) :
    Summable (fun k : ℕ => iterKernelW κ α (k + 1) t x y) := by
  have heq : (fun k : ℕ => iterKernelW κ α (k + 1) t x y)
      = fun k : ℕ => modelCoeff α t (k + 1) * gaussDdim (κ * t) (x - y) := by
    funext k
    rw [iterKernelW_eq κ α hκ (by linarith) t ht x y (by omega : 1 ≤ k + 1)]
    unfold modelCoeff
    ring
  rw [heq]
  exact (modelCoeff_summable α t hα ht).mul_right _

/-! ### 5. The residual connection — the WIDE Gaussian is the width-`κ = 2` base kernel. -/

/-- **★ THE RESIDUAL CONNECTION.**  The parametrix residual's WIDE dominating Gaussian equals the
    width-`κ = 2` base kernel (order `α = 0`) at base point `0`, times `2^{n/2} = (√2)ⁿ`:
        `gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`   (`0 < t`).
    Route: `ParametrixResidualBaseKernel.gaussDdimWide_eq_scaled_gaussDdim`
    (`gaussDdimWide t v = (√2)ⁿ · gaussDdim (2·t) v`) plus `baseKernelW 2 0 t v 0 = gaussDdim (2·t) v`
    (`τ^0 = 1`, `v − 0 = v`).  Together with `iterKernelW_series_summable` (`κ = 2`), this certifies
    that the residual's wide-Gaussian bound is a width-tolerant base-kernel bound that ITERATES to a
    convergent series — G3 is closed at the model level (G1/G2 remain, orthogonal to width). -/
theorem gaussDdimWide_eq_scaled_baseKernelW {t : ℝ} (ht : 0 < t) (v : Point n) :
    QIQTH.ResidueBound.gaussDdimWide t v
      = Real.sqrt 2 ^ n * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 := by
  rw [QIQTH.HeatResidualBound.gaussDdimWide_eq_scaled_gaussDdim ht v]
  simp only [baseKernelW, Real.rpow_zero, one_mul, sub_zero]

end QIQTH.GaussianWidthTolerant
