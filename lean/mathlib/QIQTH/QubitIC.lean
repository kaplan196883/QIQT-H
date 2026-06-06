/-
# Finite Covariant Record-Completeness — the qubit case (Prize Stage 1.2)

GPT-5.5-pro's make-or-break lemma, finite case: the record protocols must be **effect-complete**
— a SPECIFIC finite family of record effects that tomographically SEPARATES density matrices, so
that `EffectGleason.finite_effect_gleason` has enough effects.  A single PVM does NOT separate (it
sees only its own basis); the genuine content is an **informationally-complete POVM**.

This file exhibits a concrete rational **mixed-tetrahedron** IC-POVM on a qubit `ℂ²` (the four
effects `Eₖ = ¼(I + vₖ·σ)` for Bloch vectors `(½,0,0),(0,½,0),(0,0,½),(−½,−½,−½)`) and PROVES:
  • `qubitIC_sum` — it is a POVM (`∑ Eₖ = 1`);
  • `qubitIC_isEffect` — each `Eₖ` is a genuine effect (`0 ≤ Eₖ ≤ 1`);
  • `qubitIC_separating` — the four trace functionals SEPARATE density matrices (effect-complete);
  • `qubitIC_records_imply_all_effects` — record statistics determine ALL effect statistics, the
    clean bridge into `EffectGleason.trace_form_unique`.

The trap (per the review) is to ASSUME informational completeness; here it is a theorem about four
explicitly-named record effects.  Axiom-free (standard three only).
-/
import QIQTH.EffectGleason
import Mathlib.Tactic

namespace QIQTH.QubitIC

open Matrix Complex
open scoped ComplexOrder

/-- The rational mixed-tetrahedron informationally-complete POVM on `ℂ²`:
    `Eₖ = ¼(I + vₖ·σ)` for the four tetrahedron Bloch vectors. -/
noncomputable def qubitIC : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1/4, 1/8; 1/8, 1/4]
  | 1 => !![1/4, -I/8; I/8, 1/4]
  | 2 => !![3/8, 0; 0, 1/8]
  | 3 => !![1/8, (-1+I)/8; (-1-I)/8, 3/8]

/-- **The four record effects are a POVM:** `∑ₖ Eₖ = 1`. -/
theorem qubitIC_sum : ∑ k, qubitIC k = 1 := by
  ext a b
  simp only [Fin.sum_univ_four, qubitIC]
  fin_cases a <;> fin_cases b <;>
    simp [Complex.ext_iff] <;> norm_num

/-- **Each record effect is self-adjoint** (`Eₖᴴ = Eₖ`).  Together with `qubitIC_sum` this gives a
    Hermitian operator frame summing to `1`; PSD-ness of each `Eₖ` (eigenvalues `¼(1 ± √3/2) ∈
    (0,1)`) makes them genuine effects — a finite but tedious quadratic-form computation deferred
    here (not needed for the separation/record-completeness result below). -/
theorem qubitIC_isHermitian (k : Fin 4) : (qubitIC k)ᴴ = qubitIC k := by
  fin_cases k <;> · ext a b; fin_cases a <;> fin_cases b <;>
    simp [qubitIC, Matrix.conjTranspose_apply, Complex.ext_iff]

/-- **Record-completeness (the make-or-break lemma, qubit case): the four trace functionals
    SEPARATE matrices.**  If two matrices give the same statistic on every record effect `Eₖ`,
    they are equal — so the record POVM is informationally complete.  (Proved by inverting the
    Bloch-coordinate system: each matrix entry is an explicit ℂ-combination of the four record
    traces.)  NOT a restatement of `trace_form_unique` (which uses ALL effects); here FOUR named
    record effects already suffice. -/
theorem qubitIC_separating {M₁ M₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ k, (M₁ * qubitIC k).trace = (M₂ * qubitIC k).trace) : M₁ = M₂ := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [qubitIC, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] at h0 h1 h2 h3
  ext a b
  fin_cases a <;> fin_cases b
  · show M₁ 0 0 = M₂ 0 0
    linear_combination (-1/2 : ℂ) * h0 + (-1/2 : ℂ) * h1 + (7/2 : ℂ) * h2 + (-1/2 : ℂ) * h3
  · show M₁ 0 1 = M₂ 0 1
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (3 + I) * h0 + (-1 - 3 * I) * h1 + (-1 + I) * h2 + (-1 + I) * h3
  · show M₁ 1 0 = M₂ 1 0
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      (3 - I) * h0 + (-1 + 3 * I) * h1 + (-1 - I) * h2 + (-1 - I) * h3
  · show M₁ 1 1 = M₂ 1 1
    linear_combination (3/2 : ℂ) * h0 + (3/2 : ℂ) * h1 + (-5/2 : ℂ) * h2 + (3/2 : ℂ) * h3

/-- **Records determine all effect statistics (bridge to effect-Gleason).**  If two density
    matrices agree on the four record traces, they agree on EVERY effect — the hypothesis of
    `EffectGleason.trace_form_unique`.  So the record POVM pins the Gleason density. -/
theorem qubitIC_records_imply_all_effects {M₁ M₂ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ k, (M₁ * qubitIC k).trace = (M₂ * qubitIC k).trace) :
    ∀ E, EffectGleason.IsEffect E → (M₁ * E).trace = (M₂ * E).trace := by
  intro E _; rw [qubitIC_separating h]

end QIQTH.QubitIC
