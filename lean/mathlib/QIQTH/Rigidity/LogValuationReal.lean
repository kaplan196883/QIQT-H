/-
  THE DECOUPLING SHADOW DS5 (THE_DECOUPLING_SHADOW_PLAN.md) — real log-valuation rigidity.

  The classical monotone-additive Cauchy rigidity, done by hand (no ready Mathlib lemma):
  a MONOTONE ADDITIVE function `g : ℝ → ℝ` is linear (`g t = g 1 · t`), hence a monotone
  multiplicative-to-additive valuation on the positive reals is `κ·log`. This is the
  positive-real half of the FORCED WEIGHT dictionary (DS6 transports it to the finite corners).

  Route: additivity gives ℚ-linearity (ℕ by induction, ℤ by negation, ℚ by clearing
  denominators); monotonicity then squeezes the real value between rational approximants.
-/
import Mathlib

namespace QIQTH.Rigidity

/-- **Monotone additive functions on ℝ are linear** (the Cauchy rigidity): `g t = g 1 · t`. -/
theorem monotone_additive_eq_smul (g : ℝ → ℝ) (hadd : ∀ s t, g (s + t) = g s + g t)
    (hmono : Monotone g) (t : ℝ) : g t = g 1 * t := by
  have h0 : g 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    linarith
  have hnat : ∀ (n : ℕ) (s : ℝ), g (n * s) = n * g s := by
    intro n
    induction n with
    | zero => intro s; simpa using h0
    | succ k ih =>
        intro s
        rw [show ((k + 1 : ℕ) : ℝ) * s = (k : ℕ) * s + s from by push_cast; ring, hadd, ih]
        push_cast
        ring
  have hneg : ∀ s : ℝ, g (-s) = -g s := by
    intro s
    have := hadd s (-s)
    rw [add_neg_cancel, h0] at this
    linarith
  have hint : ∀ (m : ℤ) (s : ℝ), g (m * s) = m * g s := by
    intro m s
    obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
    · exact_mod_cast hnat n s
    · rw [show (((-(n : ℤ)) : ℤ) : ℝ) * s = -((n : ℕ) * s) from by push_cast; ring, hneg,
        hnat]
      push_cast
      ring
  have hrat : ∀ (p : ℚ) (s : ℝ), g ((p : ℝ) * s) = (p : ℝ) * g s := by
    intro p s
    have hden0 : (0 : ℝ) < (p.den : ℝ) := by
      exact_mod_cast p.pos
    have hq : ((p.den : ℚ)) * p = (p.num : ℚ) := by
      have h := Rat.num_div_den p
      field_simp at h ⊢
      linarith [h]
    have hmulden : ((p.den : ℝ)) * ((p : ℝ) * s) = (p.num : ℝ) * s := by
      calc ((p.den : ℝ)) * ((p : ℝ) * s) = (((p.den : ℚ) * p : ℚ) : ℝ) * s := by
            push_cast
            ring
        _ = (p.num : ℝ) * s := by rw [hq]; push_cast; ring
    have hA : ((p.den : ℝ)) * g ((p : ℝ) * s) = (p.num : ℝ) * g s := by
      have h1 := hnat p.den ((p : ℝ) * s)
      rw [hmulden] at h1
      have h2 := hint p.num s
      linarith
    have hgoal : g ((p : ℝ) * s) = ((p.num : ℝ) / (p.den : ℝ)) * g s := by
      rw [div_mul_eq_mul_div, eq_div_iff hden0.ne']
      linarith
    rw [hgoal, Rat.cast_def]
  have hg1 : 0 ≤ g 1 := by
    have := hmono (show (0 : ℝ) ≤ 1 by norm_num)
    rw [h0] at this
    exact this
  have hratval : ∀ q : ℚ, g (q : ℝ) = (q : ℝ) * g 1 := fun q => by
    have := hrat q 1
    simpa using this
  have hub : ∀ q : ℚ, t ≤ (q : ℝ) → g t ≤ (q : ℝ) * g 1 := fun q hq => by
    have := hmono hq
    rw [hratval q] at this
    exact this
  have hlb : ∀ q : ℚ, (q : ℝ) ≤ t → (q : ℝ) * g 1 ≤ g t := fun q hq => by
    have := hmono hq
    rw [hratval q] at this
    exact this
  by_cases hg1z : g 1 = 0
  · -- all rational values vanish; squeeze g t between them
    obtain ⟨qu, hqu⟩ := exists_rat_gt t
    obtain ⟨ql, hql⟩ := exists_rat_lt t
    have h1 := hub qu hqu.le
    have h2 := hlb ql hql.le
    rw [hg1z] at h1 h2 ⊢
    simp only [mul_zero, zero_mul] at h1 h2 ⊢
    linarith
  · have hg1pos : 0 < g 1 := lt_of_le_of_ne hg1 (Ne.symm hg1z)
    refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show t < t + ε / g 1 from lt_add_of_pos_right t (by positivity))
      have h1 := hub q hq1.le
      have h2 : (q : ℝ) * g 1 < (t + ε / g 1) * g 1 :=
        mul_lt_mul_of_pos_right hq2 hg1pos
      have h3 : (t + ε / g 1) * g 1 = g 1 * t + ε := by
        field_simp
      linarith
    · rw [show g 1 * t = g 1 * t from rfl]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (show t - ε / g 1 < t from sub_lt_self t (by positivity))
      have h1 := hlb q hq2.le
      have h2 : (t - ε / g 1) * g 1 < (q : ℝ) * g 1 :=
        mul_lt_mul_of_pos_right hq1 hg1pos
      have h3 : (t - ε / g 1) * g 1 = g 1 * t - ε := by
        field_simp
      linarith

/-- **DS5 CAPSTONE — the real log-valuation rigidity**: a monotone valuation on the positive
    reals turning products into sums is `κ·log` with `κ ≥ 0` — the positive-real half of the
    forced weight dictionary. -/
theorem monotone_logValuation (A : ℝ → ℝ)
    (hmul : ∀ x y, 0 < x → 0 < y → A (x * y) = A x + A y)
    (hmono : ∀ x y, 0 < x → x ≤ y → A x ≤ A y) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, 0 < x → A x = κ * Real.log x := by
  set g : ℝ → ℝ := fun s => A (Real.exp s) with hg
  have hgadd : ∀ s u, g (s + u) = g s + g u := fun s u => by
    simp only [hg, Real.exp_add]
    exact hmul _ _ (Real.exp_pos s) (Real.exp_pos u)
  have hgmono : Monotone g := fun s u hsu =>
    hmono _ _ (Real.exp_pos s) (Real.exp_le_exp.mpr hsu)
  have hlin := monotone_additive_eq_smul g hgadd hgmono
  refine ⟨g 1, ?_, fun x hx => ?_⟩
  · have hA1 : A 1 = 0 := by
      have := hmul 1 1 one_pos one_pos
      simp only [mul_one] at this
      linarith
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have := hmono 1 (Real.exp 1) one_pos h1e
    rw [hA1] at this
    exact this
  · have hxlog : Real.exp (Real.log x) = x := Real.exp_log hx
    calc A x = g (Real.log x) := by rw [hg]; simp only []; rw [hxlog]
      _ = g 1 * Real.log x := hlin _

end QIQTH.Rigidity
