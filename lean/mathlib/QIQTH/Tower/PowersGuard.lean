/-
  THE TOWER T4 (THE_TOWER_PLAN.md) — THE POWERS GUARD: the separation theorem.

  The constant-frequency tower FAILS the fingerprint: with x_k = s for all k, every tail modular
  exponent lies in sℤ, whose closure is cyclic and NOT dense — so `AWFingerprintIII1` fails.
  This is the fingerprint of the Powers factor III_{e^{−s}} (Powers 1967 — CITED, not proved:
  no claim is made that the constant tower's algebra IS III_λ or is not III₁; only the arithmetic
  fingerprint failure is proved).

  Together with T3, this SEPARATES the predicate: it holds for two-frequency irrational towers
  and provably fails for single-frequency towers — neither vacuous nor universal.
-/
import Mathlib
import QIQTH.Tower.Centerpiece

namespace QIQTH.Tower

/-- In a constant-frequency tower every tail modular exponent is an integer multiple of `s`
    (the exponent is approximated to every accuracy by exact multiples, and `sℤ` admits a
    positive minimum distance to any non-member — the fractional-part gap). -/
theorem tail_exponent_constant_mem {D : ℕ → ℕ} {s : ℝ} (hs : 0 < s) (hD : ∀ k, 1 ≤ D k)
    {κ : ℝ} (hκ : IsTailModularExponent (fun k => gibbsEigen (D k) s) κ) :
    ∃ m : ℤ, κ = s * m := by
  by_contra hno
  push_neg at hno
  set u := κ / s with hu
  have hκu : κ = s * u := by
    rw [hu]
    field_simp
  set f := Int.fract u with hf
  have hf0 : f ≠ 0 := by
    intro h0
    apply hno ⌊u⌋
    have huf : u = (⌊u⌋ : ℝ) := by
      have hff := Int.floor_add_fract u
      rw [← hf, h0, add_zero] at hff
      linarith
    rw [hκu]
    exact congrArg (fun z => s * z) huf
  have hfpos : 0 < f := lt_of_le_of_ne (Int.fract_nonneg u) (Ne.symm hf0)
  have hf1 : f < 1 := Int.fract_lt_one u
  set c := min f (1 - f) with hc
  have hcpos : 0 < c := lt_min hfpos (by linarith)
  have hdist : ∀ m : ℤ, s * c ≤ |κ - s * m| := by
    intro m
    have hufloor : u = (⌊u⌋ : ℝ) + f := by
      have := Int.floor_add_fract u
      rw [← hf] at this
      linarith
    have hum : c ≤ |u - m| := by
      by_cases hm : (m : ℝ) ≤ (⌊u⌋ : ℝ)
      · have hstep : f ≤ u - m := by linarith
        calc c ≤ f := min_le_left _ _
          _ ≤ u - m := hstep
          _ ≤ |u - m| := le_abs_self _
      · push_neg at hm
        have hmz : ⌊u⌋ < m := by exact_mod_cast hm
        have hm1 : (⌊u⌋ : ℝ) + 1 ≤ m := by exact_mod_cast hmz
        have hstep : 1 - f ≤ m - u := by linarith
        calc c ≤ 1 - f := min_le_right _ _
          _ ≤ m - u := hstep
          _ ≤ |u - m| := by
              rw [abs_sub_comm]
              exact le_abs_self _
    calc s * c ≤ s * |u - m| := mul_le_mul_of_nonneg_left hum hs.le
      _ = |s * (u - m)| := by rw [abs_mul, abs_of_pos hs]
      _ = |κ - s * m| := by
          congr 1
          rw [hκu]
          ring
  obtain ⟨δ, hδ, hprop⟩ := hκ
  obtain ⟨k, _, i, j, _, _, happ⟩ := hprop (s * c / 2) (by positivity) 0
  have hpi : 0 < gibbsEigen (D k) s i := gibbsEigen_pos (hD k) _ _
  have hpj : 0 < gibbsEigen (D k) s j := gibbsEigen_pos (hD k) _ _
  have hlog : Real.log (gibbsEigen (D k) s i) - Real.log (gibbsEigen (D k) s j)
      = s * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ) := by
    have := kappaOf_gibbsEigen (hD k) s i j
    rw [QIQTH.TypeIITrace.kappaOf] at this
    rw [this]
    push_cast
    ring
  rw [hlog] at happ
  have hd := hdist (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))
  rw [abs_sub_comm] at hd
  have hsc : 0 < s * c := mul_pos hs hcpos
  have hle : s * c ≤ s * c / 2 := le_trans hd happ
  linarith

/-- **T4 CAPSTONE — THE POWERS GUARD (the separation theorem)**: the constant-frequency tower
    FAILS the III₁ fingerprint — with T3, the predicate is neither vacuous nor universal. This is
    the arithmetic fingerprint of the Powers factor III_{e^{−s}} (Powers 1967 — cited; no claim
    about any actual algebra's type is made or provable here). -/
theorem gibbsTower_constant_not_fingerprint {D : ℕ → ℕ} {s : ℝ} (hs : 0 < s)
    (hD : ∀ k, 1 ≤ D k) :
    ¬ AWFingerprintIII1 (fun k => gibbsEigen (D k) s) := by
  intro hdense
  have hsub : {κ | IsTailModularExponent (fun k => gibbsEigen (D k) s) κ}
      ⊆ ((AddSubgroup.zmultiples s : AddSubgroup ℝ) : Set ℝ) := by
    intro κ hκ
    obtain ⟨m, hm⟩ := tail_exponent_constant_mem hs hD hκ
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
    rw [zsmul_eq_mul, hm]
    ring
  have hle : AddSubgroup.closure
      {κ | IsTailModularExponent (fun k => gibbsEigen (D k) s) κ}
      ≤ AddSubgroup.zmultiples s :=
    (AddSubgroup.closure_le _).mpr hsub
  have hs2 : (s / 2) ∈ closure ((AddSubgroup.zmultiples s : AddSubgroup ℝ) : Set ℝ) := by
    have hx := hdense (s / 2)
    exact closure_mono (fun y hy => hle hy) hx
  rw [Metric.mem_closure_iff] at hs2
  obtain ⟨y, hy, hdy⟩ := hs2 (s / 2) (by positivity)
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
  rw [Real.dist_eq, zsmul_eq_mul] at hdy
  have hbound : s / 2 ≤ |s / 2 - (m : ℝ) * s| := by
    have h1 : (1 : ℝ) / 2 ≤ |1 / 2 - (m : ℝ)| := by
      by_cases h : (m : ℝ) ≤ 0
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · push_neg at h
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
          have : (0 : ℤ) < m := by exact_mod_cast h
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]
        linarith
    calc s / 2 = s * (1 / 2) := by ring
      _ ≤ s * |1 / 2 - (m : ℝ)| := mul_le_mul_of_nonneg_left h1 hs.le
      _ = |s * (1 / 2 - (m : ℝ))| := by rw [abs_mul, abs_of_pos hs]
      _ = |s / 2 - (m : ℝ) * s| := by
          congr 1
          ring
  linarith

end QIQTH.Tower
