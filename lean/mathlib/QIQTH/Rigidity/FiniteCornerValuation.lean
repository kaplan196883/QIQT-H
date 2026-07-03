/-
  THE DECOUPLING SHADOW DS6 (THE_DECOUPLING_SHADOW_PLAN.md) — the finite-corner valuation
  rigidity: THE FORCED WEIGHT DICTIONARY.

  The tower-rigidity theorem: an area-like valuation on finite Hilbert dimensions that is
  • MONOIDAL (additive under tensor product: `A(mn) = A(m) + A(n)`), and
  • MONOTONE under ALL isometric embeddings (`m ≤ n ⟹ A(m) ≤ A(n)`),
  is FORCED to be `κ·log n` — hence on product record corners `A = κ·Σ log D_k`: the local weight
  `log D` of the keystone/join/embedding dictionaries is no longer a CONSTRUCTED choice but the
  UNIQUE refinement-natural valuation, up to the overall normalization κ (which is where `4G`
  lives, and stays input).

  PLUS the counterexample (the binding verdict's necessity check): the 2-adic valuation ν₂ is
  additive AND divisibility-monotone but NOT proportional to log — the FULL embedding
  monotonicity is necessary; weaker refinement hypotheses do NOT force the weight.

  Proof route (the double-log squeeze): `A(n^r) = r·A(n)`; `m^r ≤ n^s ⟹ r·A(m) ≤ s·A(n)`;
  `s := ⌈r·log m/log n⌉₊` and `r → ∞` give `A(m)/log m ≤ A(n)/log n`; swap.
-/
import Mathlib
import QIQTH.Keystone

namespace QIQTH.Rigidity

/-- **THE FINITE-CORNER VALUATION RIGIDITY (the forced weight)**: a monoidal
    (`A(mn) = A(m)+A(n)`) valuation on finite dimensions, monotone under ALL isometric
    embeddings (`m ≤ n ⟹ A(m) ≤ A(n)`), is `κ·log` with `κ ≥ 0`. -/
theorem finiteCorner_valuation_rigidity (A : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → A (m * n) = A m + A n)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → A m ≤ A n) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ n : ℕ, 1 ≤ n → A n = κ * Real.log n := by
  have hA1 : A 1 = 0 := by
    have := hmul 1 1 le_rfl le_rfl
    simp only [mul_one] at this
    linarith
  have hApos : ∀ n : ℕ, 1 ≤ n → 0 ≤ A n := fun n hn => by
    have := hmono 1 n le_rfl hn
    rw [hA1] at this
    exact this
  have hpow : ∀ n : ℕ, 1 ≤ n → ∀ r : ℕ, A (n ^ r) = r * A n := by
    intro n hn r
    induction r with
    | zero => simpa using hA1
    | succ k ih =>
        rw [pow_succ, hmul _ _ (Nat.one_le_pow k n (by omega)) hn, ih]
        push_cast
        ring
  have hratio : ∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
      A m ≤ (Real.log m / Real.log n) * A n := by
    intro m n hm hn
    have hlogm : (0 : ℝ) < Real.log m := Real.log_pos (by exact_mod_cast hm)
    have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hAn := hApos n (by omega)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨r, hr⟩ := exists_nat_gt (A n / ε)
    have hr1 : 1 ≤ r := by
      have h0 : (0 : ℝ) ≤ A n / ε := div_nonneg hAn hε.le
      by_contra h
      push_neg at h
      interval_cases r
      simp only [Nat.cast_zero] at hr
      linarith
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    set s : ℕ := ⌈(r * Real.log m) / Real.log n⌉₊ with hs
    have hs_ge : (r * Real.log m) / Real.log n ≤ (s : ℝ) := Nat.le_ceil _
    have hs_lt : (s : ℝ) < (r * Real.log m) / Real.log n + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hpow_le : m ^ r ≤ n ^ s := by
      have h1 : (r : ℝ) * Real.log m ≤ (s : ℝ) * Real.log n := by
        rw [div_le_iff₀ hlogn] at hs_ge
        linarith
      have h2 : Real.log ((m : ℝ) ^ r) ≤ Real.log ((n : ℝ) ^ s) := by
        rw [Real.log_pow, Real.log_pow]
        exact_mod_cast h1
      have h3 : ((m : ℝ)) ^ r ≤ ((n : ℝ)) ^ s := by
        have hmr : (0 : ℝ) < (m : ℝ) ^ r := by positivity
        have hns : (0 : ℝ) < (n : ℝ) ^ s := by positivity
        have := Real.exp_le_exp.mpr h2
        rwa [Real.exp_log hmr, Real.exp_log hns] at this
      exact_mod_cast h3
    have hchain : (r : ℝ) * A m ≤ (s : ℝ) * A n := by
      rw [← hpow m (by omega) r, ← hpow n (by omega) s]
      exact hmono (m ^ r) (n ^ s) (Nat.one_le_pow r m (by omega)) hpow_le
    have hs_bound : (s : ℝ) * A n ≤ ((r : ℝ) * Real.log m / Real.log n + 1) * A n :=
      mul_le_mul_of_nonneg_right hs_lt.le hAn
    have final : A m ≤ (Real.log m / Real.log n) * A n + A n / r := by
      have h4 : (r : ℝ) * A m ≤ (r : ℝ) * Real.log m / Real.log n * A n + A n := by
        nlinarith
      have h5 : (r : ℝ) * ((Real.log m / Real.log n) * A n + A n / r)
          = (r : ℝ) * Real.log m / Real.log n * A n + A n := by
        field_simp
      have h6 : (r : ℝ) * A m ≤ (r : ℝ)
          * ((Real.log m / Real.log n) * A n + A n / r) := by
        rw [h5]
        exact h4
      exact le_of_mul_le_mul_left h6 hrpos
    have hAnr : A n / r < ε := by
      rw [div_lt_iff₀ hrpos]
      have := (div_lt_iff₀ hε).mp hr
      linarith
    linarith
  refine ⟨A 2 / Real.log 2, div_nonneg (hApos 2 (by omega)) (Real.log_pos one_lt_two).le,
    fun n hn => ?_⟩
  rcases eq_or_lt_of_le hn with h1 | h2
  · rw [← h1]
    simp [hA1]
  · have hn2 : 2 ≤ n := h2
    have hlogn : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hup := hratio n 2 hn2 le_rfl
    have hdown := hratio 2 n le_rfl hn2
    have hc2 : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [hc2] at hup hdown
    have hdown' : (Real.log n / Real.log 2) * A 2 ≤ A n := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hlog2]
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogn] at hdown
      linarith
    have heq : A n = (Real.log n / Real.log 2) * A 2 := le_antisymm hup hdown'
    rw [heq]
    ring

/-- **THE FORCED WEIGHT ON PRODUCT RECORDS**: on a product record corner the unique
    refinement-natural valuation is `κ·Σ_k log D_k` — the keystone/join/embedding weight
    dictionary is RIGID (the normalization κ is where `4G` lives, and stays input). -/
theorem forced_weight_product (A : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → A (m * n) = A m + A n)
    (hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → A m ≤ A n)
    {E : Type*} (L : QIQTH.Keystone.LinkDims E) (C : Finset E) :
    ∃ κ : ℝ, 0 ≤ κ ∧ A (∏ k ∈ C, L.D k) = κ * ∑ k ∈ C, Real.log (L.D k) := by
  obtain ⟨κ, hκ, hlog⟩ := finiteCorner_valuation_rigidity A hmul hmono
  refine ⟨κ, hκ, ?_⟩
  have hprod : 1 ≤ ∏ k ∈ C, L.D k :=
    Finset.one_le_prod' fun k _ => L.hD k
  rw [hlog _ hprod]
  congr 1
  rw [show ((∏ k ∈ C, L.D k : ℕ) : ℝ) = ∏ k ∈ C, ((L.D k : ℕ) : ℝ) from by push_cast; rfl,
    Real.log_prod]
  exact fun k _ => by exact_mod_cast (L.hD k).ne'

/-- **THE ν₂ COUNTEREXAMPLE (necessity of the strong hypotheses)**: the 2-adic valuation is
    additive and DIVISIBILITY-monotone, but NOT proportional to log — additivity plus
    divisibility-refinement alone does NOT force the weight; the FULL embedding monotonicity
    (`m ≤ n`) is necessary. -/
theorem nu2_counterexample :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (padicValNat 2 (m * n) : ℝ) = padicValNat 2 m + padicValNat 2 n)
    ∧ (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m ∣ n →
      (padicValNat 2 m : ℝ) ≤ padicValNat 2 n)
    ∧ ¬ ∃ κ : ℝ, ∀ n : ℕ, 1 ≤ n → (padicValNat 2 n : ℝ) = κ * Real.log n := by
  refine ⟨?_, ?_, ?_⟩
  · intro m n hm hn
    rw [padicValNat.mul (by omega) (by omega)]
    push_cast
    ring
  · intro m n hm hn hdvd
    obtain ⟨k, rfl⟩ := hdvd
    have hk : 1 ≤ k := by
      by_contra h
      push_neg at h
      interval_cases k
      omega
    rw [padicValNat.mul (by omega) (by omega)]
    push_cast
    have : (0 : ℝ) ≤ padicValNat 2 k := by positivity
    linarith
  · rintro ⟨κ, hκ⟩
    have h2 := hκ 2 (by omega)
    have h3 := hκ 3 (by omega)
    rw [padicValNat_self] at h2
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num)] at h3
    have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hκ0 : κ = 0 := by
      have h3' : κ * Real.log ((3 : ℕ) : ℝ) = 0 := by
        rw [← h3]
        norm_num
      have hc3 : Real.log ((3 : ℕ) : ℝ) = Real.log 3 := by norm_num
      rw [hc3] at h3'
      rcases mul_eq_zero.mp h3' with h | h
      · exact h
      · exact absurd h hlog3.ne'
    rw [hκ0, zero_mul] at h2
    norm_num at h2

end QIQTH.Rigidity
