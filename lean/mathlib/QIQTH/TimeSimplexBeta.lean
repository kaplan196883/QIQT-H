/-
  TimeSimplexBeta — the ITERATED-CONVOLUTION FACTORIAL-DECAY ENGINE (Phase C3 of the
  convergence-infrastructure campaign, docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md).

  This is the engine that makes the Levi/Duhamel Neumann series converge.  It is NOT a raw
  k-dimensional simplex Fubini: it is the ITERATION of C2's self-similar identity
  (`gaussTimePow_conv_beta`), with the Beta factors telescoping through Γ.

  WHAT LANDS HERE.

    • `baseKernel α = fun τ p q => τ^α · G_τ(p−q)` — the model kernel `τ^α G_τ` (α = the residual
      order; `^` is `Real.rpow`).

    • `iterKernel α k` — the `k`-fold left-convolution of `baseKernel α` with itself
      (`iterKernel α 1 = baseKernel α`, `iterKernel α (k+1) = heatConvK (baseKernel α) (iterKernel α k)`
      for `k ≥ 1`).

    • `iterKernel_eq` — THE deliverable: for `α > −1`, `t > 0`, `x y`, and `k ≥ 1`,
        `iterKernel α k t x y
           = (Γ(α+1)^k / Γ(k·(α+1))) · t^(k·(α+1) − 1) · G_t(x−y)`.
      This is a genuine induction (`Nat.le_induction` from `k=1`) riding on C2 plus the Γ telescoping
      `c_k · Β(α+1, k(α+1)) = Γ(α+1)^{k+1}/Γ((k+1)(α+1))`.  The `1/Γ(k(α+1))` factor IS the
      factorial (Beta-function) decay driving Neumann-series convergence.

  ⚠ HONEST SCOPE.  This is the FLAT self-similar iterated convolution.  It is NOT the true curved
  heat kernel, the Seeley–DeWitt recursion, or `a₁ = R/6` (phases C5/C6).  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.GaussianConvBound

open Real MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.GaussianConvBound QIQTH.HeatDuhamel
open scoped Interval

namespace QIQTH.TimeSimplexBeta

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ### 1. The model kernel `τ^α G_τ` and its iterated convolution. -/

/-- **The model kernel** `baseKernel α τ p q = τ^α · G_τ(p−q)` (`G = gaussDdim`, `τ^α` the
    `Real.rpow` time power, `α` the residual order). -/
noncomputable def baseKernel (α : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => τ ^ α * gaussDdim τ (p - q)

/-- **The `k`-fold iterated convolution** of `baseKernel α` (the Levi/Duhamel Neumann term).
    `iterKernel α 1 = baseKernel α`, and each step left-convolves once more by the base:
    `iterKernel α (k+1) = heatConvK (baseKernel α) (iterKernel α k)` for `k ≥ 1`.  (Index `k` counts
    the number of base factors.) -/
noncomputable def iterKernel (α : ℝ) : ℕ → (ℝ → Point n → Point n → ℝ)
  | 0 => baseKernel α
  | 1 => baseKernel α
  | (k + 2) => heatConvK (baseKernel α) (iterKernel α (k + 1))

/-- One base factor: `iterKernel α 1 = baseKernel α`. -/
theorem iterKernel_one (α : ℝ) :
    (iterKernel α 1 : ℝ → Point n → Point n → ℝ) = baseKernel α := rfl

/-- The recursion step (for `k ≥ 1`): `iterKernel α (k+1) = heatConvK (baseKernel α) (iterKernel α k)`. -/
theorem iterKernel_succ (α : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (iterKernel α (k + 1) : ℝ → Point n → Point n → ℝ)
      = heatConvK (baseKernel α) (iterKernel α k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rfl

/-! ### 2. The iterated-convolution self-similar formula (the factorial-decay engine). -/

/-- Auxiliary (∀-inside) form of `iterKernel_eq`, so the inductive hypothesis is universally
    quantified over the convolution variables `t, x, y` (needed to rewrite `iterKernel α k` inside
    the `heatConv` integrand). -/
theorem iterKernel_eq_aux (α : ℝ) (hα : -1 < α) {k : ℕ} (hk : 1 ≤ k) :
    ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      iterKernel α k t x y
        = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
            * t ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim t (x - y) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht x y
      rw [iterKernel_one]
      simp only [baseKernel, Nat.cast_one, pow_one, one_mul]
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
      -- Unfold one iteration: `iterKernel α (k+1) = heatConv (baseKernel α) (iterKernel α k)`.
      rw [iterKernel_succ α hk, heatConvK_apply]
      -- Rewrite `iterKernel α k` a.e. in the `s`-integral into the model kernel via the IH.
      have hstep : heatConv (baseKernel α) (iterKernel α k) t x y
          = heatConv (baseKernel α)
              (fun σ p q => (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * (σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim σ (p - q))) t x y := by
        simp only [heatConv]
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun s hmem => ?_))
        rw [Set.uIoc_of_le ht.le] at hmem
        obtain ⟨hs0, _⟩ := hmem
        refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
        dsimp only
        rw [IH s hs0 z y]
        ring
      rw [hstep]
      -- Pull the constant `c_k` out of the RIGHT kernel of the convolution.
      rw [show heatConv (baseKernel α)
                (fun σ p q => (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                    * (σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim σ (p - q))) t x y
              = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * heatConv (baseKernel α)
                      (fun σ p q => σ ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim σ (p - q)) t x y
            from heatConv_smul_right _ _ _ _ _ _]
      -- Apply the C2 self-similar identity with `a = α`, `b = k(α+1) − 1`.
      unfold baseKernel
      rw [gaussTimePow_conv_beta α ((k : ℝ) * (α + 1) - 1) hα hbkgt t ht x y]
      -- Γ telescoping + rpow-exponent arithmetic.
      push_cast
      rw [pow_succ,
          show α + ((k : ℝ) * (α + 1) - 1) + 1 = ((k : ℝ) + 1) * (α + 1) - 1 from by ring,
          show ((k : ℝ) * (α + 1) - 1) + 1 = (k : ℝ) * (α + 1) from by ring,
          show α + ((k : ℝ) * (α + 1) - 1) + 2 = ((k : ℝ) + 1) * (α + 1) from by ring]
      field_simp

/-- **★ THE ITERATED-CONVOLUTION SELF-SIMILAR FORMULA (Phase C3, the factorial-decay engine).**
    For `α > −1`, `t > 0`, `x y`, and `k ≥ 1`,
        `iterKernel α k t x y
           = (Γ(α+1)^k / Γ(k·(α+1))) · t^(k·(α+1) − 1) · G_t(x−y)`.
    Genuine induction on `k` (from `k=1`) riding on the C2 self-similar identity
    `gaussTimePow_conv_beta` plus the Γ telescoping
    `[Γ(α+1)^k/Γ(k(α+1))] · [Γ(α+1)Γ(k(α+1))/Γ((k+1)(α+1))] = Γ(α+1)^{k+1}/Γ((k+1)(α+1))`.
    The `1/Γ(k(α+1))` prefactor is exactly the factorial (Beta-function) decay that makes the
    Levi/Duhamel Neumann series converge. -/
theorem iterKernel_eq (α : ℝ) (hα : -1 < α) (t : ℝ) (ht : 0 < t) (x y : Point n)
    {k : ℕ} (hk : 1 ≤ k) :
    iterKernel α k t x y
      = (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
          * t ^ ((k : ℝ) * (α + 1) - 1) * gaussDdim t (x - y) :=
  iterKernel_eq_aux α hα hk t ht x y

end QIQTH.TimeSimplexBeta
