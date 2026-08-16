/-  V3MathSlice.lean — V3_PLAN Phase 8: the MATH/ℝ tier taken to a PROVABLE EMITTED op.

    The honest ℝ→target story (per the gpt-5.6-sol review): a theorem over ℝ does NOT transfer to IEEE
    float. But EVAL/chibi has an EXACT rational tower, so we realise the op over `ℚ` and prove the exact
    realisation embeds into the ℝ spec — then EVAL's exact `/` computes the ℚ value with NO rounding, so
    the MATH bound (proven over ℝ) genuinely holds of the running value.

      MATH  (Mathlib, ℝ):   avg2 a b = (a+b)/2,  proven a ≤ b → a ≤ avg2 ≤ b   (convex/envelope bound)
      EXACT (ℚ):            avg2Q a b = (a+b)/2   (EVAL raw `/` = exact rational)
      TRANSFER:             ((avg2Q a b : ℚ) : ℝ) = avg2 (a:ℝ) (b:ℝ)          (Rat.cast ring hom)

    So: EVAL avg2(5,2) = 7/2 exactly = the ℚ value = the ℝ value, which lies in [a,b] by the MATH proof. -/
import Mathlib

namespace V3Math

/-! ## MATH tier — the property, over ℝ ------------------------------------------------------------ -/

noncomputable def avg2 (a b : ℝ) : ℝ := (a + b) / 2

/-- Convex/envelope lower bound: the average is ≥ the smaller endpoint. -/
theorem avg2_lb (a b : ℝ) (h : a ≤ b) : a ≤ avg2 a b := by unfold avg2; linarith
/-- Convex/envelope upper bound: the average is ≤ the larger endpoint (so `avg2 ∈ [a,b]`). -/
theorem avg2_ub (a b : ℝ) (h : a ≤ b) : avg2 a b ≤ b := by unfold avg2; linarith
/-- Monotone in the first argument. -/
theorem avg2_mono (a₁ a₂ b : ℝ) (h : a₁ ≤ a₂) : avg2 a₁ b ≤ avg2 a₂ b := by unfold avg2; linarith

/-! ## Exact realisation over ℚ + the transfer theorem ------------------------------------------- -/

/-- The EXACT rational realisation — what EVAL actually computes (its `/` is exact on rationals). -/
def avg2Q (a b : ℚ) : ℚ := (a + b) / 2

/-- **Transfer.** The exact ℚ realisation, embedded into ℝ, equals the ℝ spec. So the MATH bounds above
    hold of the running exact value — no floating error, unlike an IEEE target. -/
theorem avg2Q_cast (a b : ℚ) : ((avg2Q a b : ℚ) : ℝ) = avg2 (a : ℝ) (b : ℝ) := by
  unfold avg2Q avg2; push_cast; ring

/-- Corollary: the exact ℚ value lies in `[a,b]` (the bound, transported to the realisation). -/
theorem avg2Q_in_range (a b : ℚ) (h : a ≤ b) : a ≤ avg2Q a b ∧ avg2Q a b ≤ b := by
  constructor
  · have := avg2_lb (a : ℝ) (b : ℝ) (by exact_mod_cast h)
    rw [← avg2Q_cast] at this; exact_mod_cast this
  · have := avg2_ub (a : ℝ) (b : ℝ) (by exact_mod_cast h)
    rw [← avg2Q_cast] at this; exact_mod_cast this

end V3Math

#eval "V3 MATH tier: avg2 bounded in [a,b] over ℝ, realised EXACTLY over ℚ (avg2Q_cast) — KERNEL-CHECKED"
#print axioms V3Math.avg2_ub
#print axioms V3Math.avg2Q_cast
#print axioms V3Math.avg2Q_in_range
