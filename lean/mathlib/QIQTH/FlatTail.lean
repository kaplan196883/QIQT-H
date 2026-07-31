/-
  FlatTail — the flat-tail estimate `t^{-k}·exp(-a/t) = O(t^N)` as `t → 0⁺` (J4-10).

  WHAT IS DERIVED HERE (the honest boundary — read it).
  This is the self-contained ANALYTIC TOOL that makes the cutoff-parametrix's FAR FIELD (the annulus
  `r/2 ≤ ‖v‖ ≤ r`, where the base Gaussian carries `exp(-c/t)`) negligible to ALL orders in `t`.  The
  single fact:

    • `exp_neg_inv_flat` — for `a > 0` and any inverse-time power `k` and target order `N`, there is a
      constant `C ≥ 0` with, for ALL `t > 0`,
          `(1/t)^k · exp(-a/t) ≤ C · t^N`,
      i.e. the exponential `exp(-a/t)` beats not merely every inverse power `(1/t)^k` (a CONSTANT
      bound, cf. `AnnulusGaussianBound.invT_pow_exp_le`) but leaves an arbitrary positive power `t^N`
      to spare.  This is the "flat tail" — smaller than any polynomial in `t` — that lets the
      parametrix be cut off LOCALLY (no global no-conjugate-points theorem needed).

    Route: set `m := k + N`, `v := a/t ≥ 0`.  Then
      `(1/t)^m · exp(-a/t) = v^m·exp(-v)/a^m ≤ m!/a^m =: C`
    by the crude single-term exp-series bound `pow_mul_exp_neg_le_factorial` (GaussianPolyBound), and
    `(1/t)^k = (1/t)^m · t^N` for `t ≠ 0`, so
      `(1/t)^k·exp(-a/t) = ((1/t)^m·exp(-a/t))·t^N ≤ C·t^N`.
    The constant `C = m!/a^m` is honest (crude, not sharp — we do not chase `m^m e^{-m}`).  All powers
    are `Nat`-powers; no `rpow`.  The bound holds for ALL `t > 0` (no upper cutoff `T` needed).

  ⚠ HONEST SCOPE.  This is the FLAT-TAIL core only.  It is NOT the annulus Gaussian bound itself (that
  wires this to `gaussDdim` in `AnnulusGaussianBound`, a separate file) and NOT the `a₁ = R/6`
  coefficient.  No axioms, no `sorry`.
-/
import Mathlib
import QIQTH.GaussianPolyBound

namespace QIQTH.HeatResidualBound

open QIQTH.GaussianPolyBound

/-- **THE FLAT-TAIL BOUND (exp beats poly, with a power to spare).**  For `a > 0` and any `k N : ℕ`
    there is `C ≥ 0` such that, for ALL `t > 0`,
        `(1/t)^k · exp(-a/t) ≤ C · t^N`.
    The exponential far-field factor `exp(-a/t)` is therefore FLAT: smaller than any power of `t` as
    `t → 0⁺`.  Route: `m := k + N`, `v := a/t`; `(1/t)^m·exp(-a/t) = v^m·exp(-v)/a^m ≤ m!/a^m` by the
    single-term exp-series bound `pow_mul_exp_neg_le_factorial`, and `(1/t)^k = (1/t)^m·t^N`.  The
    witness is `C = (k+N)!/a^(k+N)`. -/
theorem exp_neg_inv_flat (a : ℝ) (ha : 0 < a) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → (1 / t) ^ k * Real.exp (-a / t) ≤ C * t ^ N := by
  refine ⟨((k + N).factorial : ℝ) / a ^ (k + N), by positivity, ?_⟩
  intro t ht
  set m : ℕ := k + N with hm
  have htne : t ≠ 0 := ht.ne'
  have hane : a ≠ 0 := ha.ne'
  have ham : (0 : ℝ) < a ^ m := by positivity
  have hv : 0 ≤ a / t := by positivity
  -- single-term exp-series bound: `(a/t)^m · exp(-a/t) ≤ m!`
  have hfac := pow_mul_exp_neg_le_factorial hv m
  rw [← neg_div] at hfac
  -- strip the extra `t^N`: `(1/t)^m · exp(-a/t) ≤ m!/a^m`
  have hkey : (1 / t) ^ m * Real.exp (-a / t) ≤ (m.factorial : ℝ) / a ^ m := by
    rw [le_div_iff₀ ham]
    calc (1 / t) ^ m * Real.exp (-a / t) * a ^ m
        = (a / t) ^ m * Real.exp (-a / t) := by field_simp; ring
      _ ≤ (m.factorial : ℝ) := hfac
  -- `(1/t)^k = (1/t)^m · t^N` for `t ≠ 0`
  have hinv : (1 / t) ^ N * t ^ N = 1 := by
    rw [← mul_pow, one_div, inv_mul_cancel₀ htne, one_pow]
  have hsplit : (1 / t) ^ k * Real.exp (-a / t)
      = ((1 / t) ^ m * Real.exp (-a / t)) * t ^ N := by
    have hpow : (1 / t) ^ m * t ^ N = (1 / t) ^ k := by
      rw [hm, pow_add, mul_assoc, hinv, mul_one]
    rw [mul_right_comm, hpow]
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hkey (by positivity)

end QIQTH.HeatResidualBound
