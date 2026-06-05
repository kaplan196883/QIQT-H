/-
  Regression suite for the finite Goldstein–Struyve uniqueness predicates.

  Per the GPT-5.5-pro adversarial review: the axiom-budget / `#print axioms` checks
  cannot see *vacuity* or *too-permissive hypotheses*.  The defence is concrete
  models — positive witnesses (the hypotheses are jointly satisfiable, so the
  flagship theorem is NON-VACUOUS) and negative witnesses (each load-bearing
  hypothesis genuinely *rejects* a known countermodel).

  POSITIVE
    • the identity satisfies every hypothesis of `canonical_ic_measure_principle`
      (so the principle is non-vacuous; we even apply it).

  NEGATIVE (each shows a hypothesis is doing real work)
    • `ρ ↦ i·ρ`        violates `IsHermitianPreserving`  (the reality condition
                        that makes Step 1's coefficients real — without it Step 1
                        is inconsistent).
    • depolarizing `schurForm 0 1` (`A ↦ (tr A/d)·I`) violates `IsNonDegenerate`
      (the `(α,β)=(0,1)` branch that Step 4 must exclude).
-/

import QIQTH.GoldsteinStruyveFinDim
import QIQTH.FQEquivarianceUniqueness

namespace QIQTH
namespace GoldsteinStruyveModels

open Matrix GoldsteinStruyveFinDim

/- ── POSITIVE: the identity is a witness (non-vacuity) ─────────────── -/

/-- The identity functional is non-degenerate (witnessed by `E₀₀`). -/
theorem identity_isNonDegenerate {d : ℕ} (hd : 1 < d) :
    IsNonDegenerate (id : DensityFunctional d) := by
  haveI : NeZero d := ⟨by omega⟩
  have h01 : (0 : Fin d) ≠ 1 := by
    apply Fin.ne_of_val_ne; rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt hd]; omega
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  refine ⟨single 0 0 1, by simp [Matrix.trace_single_eq_same], ?_⟩
  intro hcon
  have h11 := congrFun (congrFun hcon 1) 1
  simp only [id_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.single_apply_of_ne, h01, false_and, not_false_eq_true] at h11
  exact (one_div_ne_zero hd0) h11.symm

/-- **NON-VACUITY:** the identity satisfies *all* hypotheses of the flagship
    `canonical_ic_measure_principle`, so the principle is not vacuously true. -/
theorem canonical_principle_nonvacuous {d : ℕ} (hd : 1 < d) :
    (id : DensityFunctional d) = FQEquivarianceUniqueness.canonicalDensity d :=
  FQEquivarianceUniqueness.canonical_ic_measure_principle hd id id
    (fun _ _ _ _ => rfl)                       -- IsLinear D
    (fun _ _ _ => rfl)                         -- IsUnitaryEquivariant D
    (fun _ h => h)                             -- IsHermitianPreserving D
    (fun _ _ _ _ => rfl)                       -- IsLinear Dd2
    (fun _ _ _ => rfl)                         -- IsUnitaryEquivariant Dd2
    (fun _ h => h)                             -- IsHermitianPreserving Dd2
    (fun _ => rfl)                             -- IsNormalized D
    (fun _ _ => rfl)                           -- IsTensorMultiplicative D Dd2
    (identity_isNonDegenerate hd)              -- IsNonDegenerate D

/- ── NEGATIVE: each hypothesis rejects a countermodel ─────────────── -/

/-- `ρ ↦ i·ρ` is NOT Hermiticity-preserving (it sends the Hermitian `E₀₀` to the
    anti-Hermitian `i·E₀₀`).  This is exactly the map that made Step 1 inconsistent
    before `IsHermitianPreserving` was added. -/
theorem imaginaryId_not_hermitianPreserving {d : ℕ} (hd : 1 < d) :
    ¬ IsHermitianPreserving (fun ρ => Complex.I • ρ : DensityFunctional d) := by
  haveI : NeZero d := ⟨by omega⟩
  intro h
  have hHerm : star (single 0 0 1 : Matrix (Fin d) (Fin d) ℂ) = single 0 0 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]
  have hcon := h (single 0 0 1 : Matrix (Fin d) (Fin d) ℂ) hHerm
  have h00 := congrFun (congrFun hcon 0) 0
  rw [Matrix.star_apply] at h00
  simp only [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one] at h00
  rw [show star Complex.I = -Complex.I from by simp] at h00
  rw [Complex.ext_iff] at h00
  norm_num at h00

/-- The depolarizing map `A ↦ (tr A / d)·I` (= `schurForm 0 1`) is NOT
    non-degenerate: it sends every trace-1 state to `(1/d)·I`.  This is the
    `(α,β)=(0,1)` branch that Step 4's non-degeneracy must (and does) exclude. -/
theorem depolarizing_not_nonDegenerate {d : ℕ} (hd : 1 < d) :
    ¬ IsNonDegenerate (@schurForm d 0 1) := by
  rintro ⟨P, hP, hne⟩
  apply hne
  simp [schurForm, hP]

end GoldsteinStruyveModels
end QIQTH
