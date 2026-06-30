/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# I3 — the free-dispersion Lorentz-defect bound (the cheap, known pass of the stress test)

Phase B of the QG campaign (`QG_CAMPAIGN_PLAN.md`). The lattice / quantum-cellular-automaton free dispersion is
`E_a(p)² = m² + (4/a²)·sin²(a p / 2)` (lattice spacing `a = 1/Λ`, cutoff `Λ`). Its **Lorentz defect** — the
deviation from the continuum relativistic dispersion `m² + p²` — is bounded, in the **sub-cutoff regime**
`a·p ≤ 2` (momenta below the cutoff, where an EFT statement is meaningful), by
```
|E_a(p)² − (m² + p²)| ≤ a² p⁴ / 8.
```
So the defect is `O(a² p⁴)`: it scales as `(a p)²` and, crucially, **vanishes as `a → 0` for fixed `p` — there is
no rapidity-independent floor** (`α = 2`). This is the *cheap, known* pass of GPT-5.5-pro's Lorentz-cutoff stress
test (2026-06-30): a finite lattice/QCA cutoff can carry **approximate** Lorentz invariance at low energy. It is
**not yet decisive** — the decisive test is the one-loop speed-splitting `Δc² = Z_s/Z_t − 1` (I4), which checks
whether *interactions* preserve the suppression or generate an unsuppressed floor (the CPSUV obstruction).

The optimal constant is `1/12` (from the exact `sin x > x − x³/6`); the constant proved here is `1/8`, the honest
value yielded by Mathlib's clean lower bound `Real.sin_gt_sub_cube` (`x − x³/4 < sin x` on `0 < x ≤ 1`). Both give
`α = 2` and no floor. Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace QIQTH.QG

open Real

/-- **Core trigonometric bound:** `|sin²x − x²| ≤ x⁴/2` for `0 ≤ x ≤ 1`. Upper half from `sin²x ≤ x²`; lower
half from `x − x³/4 < sin x` (`Real.sin_gt_sub_cube`), squared. -/
theorem abs_sin_sq_sub_sq_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x ^ 2 - x ^ 2| ≤ x ^ 4 / 2 := by
  have hup : Real.sin x ^ 2 ≤ x ^ 2 := Real.sin_sq_le_sq
  have hlow : x ^ 2 - x ^ 4 / 2 ≤ Real.sin x ^ 2 := by
    rcases eq_or_lt_of_le hx0 with h | h
    · rw [← h]; simp
    · have hs : x - x ^ 3 / 4 < Real.sin x := Real.sin_gt_sub_cube h hx1
      have hpos : 0 ≤ x - x ^ 3 / 4 := by
        nlinarith [h.le, hx1, mul_nonneg (mul_nonneg h.le h.le) h.le]
      have hsq : (x - x ^ 3 / 4) ^ 2 ≤ Real.sin x ^ 2 := by
        rw [pow_two, pow_two]; exact mul_self_le_mul_self hpos hs.le
      have hexp : (x - x ^ 3 / 4) ^ 2 = x ^ 2 - x ^ 4 / 2 + x ^ 6 / 16 := by ring
      rw [hexp] at hsq
      have hx6 : 0 ≤ x ^ 6 / 16 := by positivity
      linarith
  rw [abs_le]
  have hx4 : 0 ≤ x ^ 4 / 2 := by positivity
  exact ⟨by linarith, by linarith⟩

/-- The lattice / QCA free dispersion `E_a(p)² = m² + (4/a²)·sin²(a p / 2)`. -/
noncomputable def latticeDispSq (m a p : ℝ) : ℝ := m ^ 2 + (4 / a ^ 2) * Real.sin (a * p / 2) ^ 2

/-- The continuum relativistic dispersion `m² + p²`. -/
def contDispSq (m p : ℝ) : ℝ := m ^ 2 + p ^ 2

/-- **The lattice dispersion never exceeds the continuum one:** `E_a(p)² ≤ m² + p²` (the lattice underestimates
the energy), for any spacing `a ≠ 0` and any momentum. From `sin²(ap/2) ≤ (ap/2)²`. -/
theorem latticeDispSq_le_contDispSq (m p : ℝ) {a : ℝ} (ha : a ≠ 0) :
    latticeDispSq m a p ≤ contDispSq m p := by
  unfold latticeDispSq contDispSq
  have h : Real.sin (a * p / 2) ^ 2 ≤ (a * p / 2) ^ 2 := Real.sin_sq_le_sq
  have hstep : (4 / a ^ 2) * Real.sin (a * p / 2) ^ 2 ≤ (4 / a ^ 2) * (a * p / 2) ^ 2 :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have heq : (4 / a ^ 2) * (a * p / 2) ^ 2 = p ^ 2 := by field_simp; ring
  rw [heq] at hstep
  linarith

/-- **★ I3 — the free-dispersion Lorentz-defect bound.** In the sub-cutoff regime `a·p ≤ 2` (momenta below the
lattice cutoff `Λ = 1/a`), the Lorentz defect of the lattice/QCA dispersion is `O(a²p⁴)`:
`|E_a(p)² − (m² + p²)| ≤ a²p⁴/8`. The bound `→ 0` as `a → 0` for fixed `p` — there is **no rapidity-independent
floor** (`α = 2`). The cheap, known pass of the Lorentz-cutoff stress test; not yet decisive (see I4). -/
theorem latticeDisp_lorentz_defect (m : ℝ) {a p : ℝ} (ha : 0 < a) (hp : 0 ≤ p) (hcut : a * p ≤ 2) :
    |latticeDispSq m a p - contDispSq m p| ≤ a ^ 2 * p ^ 4 / 8 := by
  unfold latticeDispSq contDispSq
  set x := a * p / 2 with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by rw [hxdef]; linarith
  have hcore : |Real.sin x ^ 2 - x ^ 2| ≤ x ^ 4 / 2 := abs_sin_sq_sub_sq_le hx0 hx1
  have hp2 : p ^ 2 = (4 / a ^ 2) * x ^ 2 := by rw [hxdef]; field_simp; ring
  have key : m ^ 2 + (4 / a ^ 2) * Real.sin x ^ 2 - (m ^ 2 + p ^ 2)
      = (4 / a ^ 2) * (Real.sin x ^ 2 - x ^ 2) := by rw [hp2]; ring
  rw [key, abs_mul, abs_of_pos (show (0:ℝ) < 4 / a ^ 2 by positivity)]
  calc (4 / a ^ 2) * |Real.sin x ^ 2 - x ^ 2|
      ≤ (4 / a ^ 2) * (x ^ 4 / 2) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = a ^ 2 * p ^ 4 / 8 := by rw [hxdef]; field_simp; ring

end QIQTH.QG
