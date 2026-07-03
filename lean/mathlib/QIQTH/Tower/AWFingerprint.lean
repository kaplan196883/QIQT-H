/-
  THE TOWER T1 (THE_TOWER_PLAN.md) — the Araki–Woods data + the fingerprint predicates + the
  κ-bridge.

  The code tower with its Gibbs product states is ITPFI (infinite tensor product of finite type I)
  input data in the sense of Araki–Woods. This file packages the finite arithmetic layer:
  • `gibbsEigen` — the per-mode eigenvalue lists λ(i) = e^{−x·i}/Z (positive, normalized), with
    the UNIFORM WEIGHT BOUNDS and the EXACT ratio λ₁/λ₀ = e^{−x} (the Z cancels — exact, never
    approximated);
  • `IsTailModularExponent` / `AWFingerprintIII1` — the NAMED WITNESS PREDICATES, additive in the
    modular exponent κ (per the binding verdict: NOT the verbatim Araki–Woods r∞ definition, whose
    weight-threshold constant varies across sources; a SUFFICIENT witness form whose operator
    interpretation is cited at T3). The two clauses are load-bearing:
      – the TAIL quantifier (∀ N, ∃ k ≥ N): drifting frequencies βω_k = s + 1/k generate a dense
        algebraic ratio group, but the factor is III_{e^{−s}}, not III₁ — asymptotic occurrence
        is essential;
      – the UNIFORM δ: vanishing weights λ_k = (1−ε_k, ε_k) with Σε_k < ∞ have nontrivial ratios
        in every factor, but the factor is type I∞ — weight bounded away from zero is essential;
  • the κ-BRIDGE: the fingerprint exponents ARE the held corner modular eigen-exponents —
    `kappaOf (gibbsEigen D x) i j = x·(j − i)` and `exp (kappaOf p i j) = p i / p j` (the
    FiniteCornerEigen modular frequency language).

  ⚠ HONEST SCOPE: arithmetic statements about eigenvalue lists ONLY — no von Neumann algebra, no
  ratio set of an algebra, no type classification is constructed or claimed anywhere in this file.
-/
import Mathlib
import QIQTH.Decoupling.EntropyRegimes
import QIQTH.FiniteCornerEigen

namespace QIQTH.Tower

open QIQTH.Decoupling

/-- **The Gibbs eigenvalue list of one mode**: `λ(i) = e^{−x·i}/Z_D(e^{−x})` (`x = βω`). -/
noncomputable def gibbsEigen (D : ℕ) (x : ℝ) (i : Fin D) : ℝ :=
  Real.exp (-(x * i)) / Zgeom D (Real.exp (-x))

theorem gibbsEigen_pos {D : ℕ} (hD : 1 ≤ D) (x : ℝ) (i : Fin D) :
    0 < gibbsEigen D x i :=
  div_pos (Real.exp_pos _) (Zgeom_pos hD (Real.exp_pos _).le)

/-- The eigenvalue list is normalized (a genuine probability list). -/
theorem sum_gibbsEigen {D : ℕ} (hD : 1 ≤ D) (x : ℝ) :
    ∑ i, gibbsEigen D x i = 1 := by
  simp only [gibbsEigen]
  rw [← Finset.sum_div,
    show (∑ i : Fin D, Real.exp (-(x * i))) = Zgeom D (Real.exp (-x)) from by
      rw [Zgeom, ← Fin.sum_univ_eq_sum_range (fun n => Real.exp (-x) ^ n)]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Real.exp_nat_mul]
        congr 1
        ring,
    div_self (Zgeom_pos hD (Real.exp_pos _).le).ne']

/-- The strict geometric-tail bound: `Z_D(q) < 1/(1−q)` for `0 < q < 1` (via
    `Z·(1−q) = 1 − q^D < 1`). -/
theorem Zgeom_lt_inv_one_sub {D : ℕ} (hD : 1 ≤ D) {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    Zgeom D q < (1 - q)⁻¹ := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hgeom : Zgeom D q * (1 - q) = 1 - q ^ D := by
    have hg := geom_sum_mul q D
    have h2 : Zgeom D q * (1 - q) = -(Zgeom D q * (q - 1)) := by ring
    rw [h2, show Zgeom D q * (q - 1) = q ^ D - 1 from hg]
    ring
  have hqD : (0 : ℝ) < q ^ D := by positivity
  rw [show (1 - q)⁻¹ = 1 / (1 - q) from (one_div _).symm, lt_div_iff₀ h1q]
  rw [hgeom]
  linarith

/-- **The uniform ground-weight bound**: `λ(0) = 1/Z > 1 − e^{−a}` whenever `a ≤ x`, `0 < a`. -/
theorem gibbsEigen_zero_bound {D : ℕ} (hD : 1 ≤ D) {x a : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    1 - Real.exp (-a) < gibbsEigen D x ⟨0, by omega⟩ := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hq0 : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hq1 : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hZ : Zgeom D (Real.exp (-x)) < (1 - Real.exp (-x))⁻¹ :=
    Zgeom_lt_inv_one_sub hD hq0 hq1
  have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-x)) := Zgeom_pos hD hq0.le
  have h0 : gibbsEigen D x ⟨0, by omega⟩ = (Zgeom D (Real.exp (-x)))⁻¹ := by
    rw [gibbsEigen]
    norm_num
  rw [h0]
  have hexpa : Real.exp (-x) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  have h1q : (0 : ℝ) < 1 - Real.exp (-x) := by linarith
  have hkey : (1 - Real.exp (-a)) * Zgeom D (Real.exp (-x)) < 1 := by
    have h1x : Zgeom D (Real.exp (-x)) * (1 - Real.exp (-x)) < 1 := by
      calc Zgeom D (Real.exp (-x)) * (1 - Real.exp (-x))
          < (1 - Real.exp (-x))⁻¹ * (1 - Real.exp (-x)) :=
            mul_lt_mul_of_pos_right hZ h1q
        _ = 1 := inv_mul_cancel₀ h1q.ne'
    calc (1 - Real.exp (-a)) * Zgeom D (Real.exp (-x))
        ≤ (1 - Real.exp (-x)) * Zgeom D (Real.exp (-x)) := by
          apply mul_le_mul_of_nonneg_right _ hZpos.le
          linarith
      _ = Zgeom D (Real.exp (-x)) * (1 - Real.exp (-x)) := by ring
      _ < 1 := h1x
  rw [show (Zgeom D (Real.exp (-x)))⁻¹ = 1 / Zgeom D (Real.exp (-x)) from (one_div _).symm,
    lt_div_iff₀ hZpos]
  exact hkey

/-- **The uniform first-level weight bound**: `λ(1) > e^{−b}(1 − e^{−a})` on `a ≤ x ≤ b`. -/
theorem gibbsEigen_one_bound {D : ℕ} (hD : 2 ≤ D) {x a b : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp (-b) * (1 - Real.exp (-a)) < gibbsEigen D x ⟨1, by omega⟩ := by
  have h0 := gibbsEigen_zero_bound (le_trans (by omega) hD) ha hax
  have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-x)) := Zgeom_pos (by omega) (Real.exp_pos _).le
  have h1 : gibbsEigen D x ⟨1, by omega⟩
      = Real.exp (-x) * gibbsEigen D x ⟨0, by omega⟩ := by
    rw [gibbsEigen, gibbsEigen]
    rw [show (((⟨1, by omega⟩ : Fin D) : ℕ) : ℝ) = 1 from by norm_num,
      show (((⟨0, by omega⟩ : Fin D) : ℕ) : ℝ) = 0 from by norm_num]
    rw [mul_zero, neg_zero, Real.exp_zero, mul_one, mul_one_div]
  rw [h1]
  have hexpb : Real.exp (-b) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  calc Real.exp (-b) * (1 - Real.exp (-a))
      ≤ Real.exp (-x) * (1 - Real.exp (-a)) := by
        apply mul_le_mul_of_nonneg_right hexpb
        have : Real.exp (-a) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        linarith
    _ < Real.exp (-x) * gibbsEigen D x ⟨0, by omega⟩ :=
        mul_lt_mul_of_pos_left h0 hpos

/-- **The EXACT modular ratio**: `λ(1)/λ(0) = e^{−x}` — the partition function cancels
    identically (exact, never approximated: the fingerprint exponents are exact). -/
theorem gibbsEigen_ratio {D : ℕ} (hD : 2 ≤ D) (x : ℝ) :
    gibbsEigen D x ⟨1, by omega⟩ / gibbsEigen D x ⟨0, by omega⟩ = Real.exp (-x) := by
  have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-x)) := Zgeom_pos (by omega) (Real.exp_pos _).le
  rw [gibbsEigen, gibbsEigen,
    show (((⟨1, by omega⟩ : Fin D) : ℕ) : ℝ) = 1 from by norm_num,
    show (((⟨0, by omega⟩ : Fin D) : ℕ) : ℝ) = 0 from by norm_num]
  rw [mul_zero, neg_zero, Real.exp_zero, mul_one]
  field_simp

/-! ### The fingerprint predicates (additive, in the modular exponent κ) -/

/-- **κ is a TAIL MODULAR EXPONENT** of the eigenvalue family `Λ`: witnessed with UNIFORM weight
    `δ` in factors beyond every `N`, to accuracy `ε`. Both clauses are load-bearing (see the
    module docstring's counterexamples). -/
def IsTailModularExponent {D : ℕ → ℕ} (Λ : ∀ k, Fin (D k) → ℝ) (κ : ℝ) : Prop :=
  ∃ δ > 0, ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ∃ i j : Fin (D k),
    δ ≤ Λ k i ∧ δ ≤ Λ k j ∧ |Real.log (Λ k i) - Real.log (Λ k j) - κ| ≤ ε

/-- **THE ARAKI–WOODS III₁ FINGERPRINT**: the additive subgroup generated by the witnessed tail
    modular exponents is dense in ℝ. An ARITHMETIC property of the eigenvalue-list family — the
    operator interpretation (r∞ = [0,∞), the III₁ class) is cited at the T3 capstone, never
    proved. -/
def AWFingerprintIII1 {D : ℕ → ℕ} (Λ : ∀ k, Fin (D k) → ℝ) : Prop :=
  Dense ((AddSubgroup.closure {κ | IsTailModularExponent Λ κ} : AddSubgroup ℝ) : Set ℝ)

/-! ### The κ-bridge: the fingerprint exponents ARE the corner modular eigen-exponents -/

/-- The Gibbs eigenvalue list's modular exponent (the held `kappaOf`) is exactly
    `x·(j − i)`. -/
theorem kappaOf_gibbsEigen {D : ℕ} (hD : 1 ≤ D) (x : ℝ) (i j : Fin D) :
    QIQTH.TypeIITrace.kappaOf (gibbsEigen D x) i j
      = x * ((j : ℕ) : ℝ) - x * ((i : ℕ) : ℝ) := by
  have hZpos : (0 : ℝ) < Zgeom D (Real.exp (-x)) := Zgeom_pos hD (Real.exp_pos _).le
  rw [QIQTH.TypeIITrace.kappaOf, gibbsEigen, gibbsEigen,
    Real.log_div (Real.exp_ne_zero _) hZpos.ne', Real.log_div (Real.exp_ne_zero _) hZpos.ne',
    Real.log_exp, Real.log_exp]
  ring

/-- The exponential of the modular exponent is the eigenvalue ratio (any positive list). -/
theorem exp_kappaOf {ι : Type*} (p : ι → ℝ) (hp : ∀ i, 0 < p i) (i j : ι) :
    Real.exp (QIQTH.TypeIITrace.kappaOf p i j) = p i / p j := by
  rw [QIQTH.TypeIITrace.kappaOf, Real.exp_sub, Real.exp_log (hp i), Real.exp_log (hp j)]

end QIQTH.Tower
