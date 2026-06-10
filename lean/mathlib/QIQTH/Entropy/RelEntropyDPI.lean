/-
  **Toward the data-processing inequality** (Carlen §6.4) from the joint convexity of relative
  entropy (`relEntropy_subadditive`).  This file builds the two structural properties of the
  Umegaki relative entropy that, together with joint convexity, give DPI for mixed-unitary
  (random-unitary) channels `Φ(ρ) = Σₖ pₖ Uₖ ρ Uₖ⋆`:

  * **unitary invariance** `D(U ρ U⋆ ‖ U σ U⋆) = D(ρ‖σ)` (here);
  * scaling `D(c·ρ ‖ c·σ) = c·D(ρ‖σ)` and finite subadditivity (later),

  whence `D(Φρ‖Φσ) ≤ Σₖ D(pₖUₖρUₖ⋆‖pₖUₖσUₖ⋆) = Σₖ pₖ D(ρ‖σ) = D(ρ‖σ)`.
-/
import QIQTH.Entropy.RelEntropyConvex

namespace QIQTH.Entropy

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm commutes with unitary conjugation: `log(u·M·u⋆) = u · log M · u⋆`.
    CFC naturality (`map_cfc`) under the inner ∗-automorphism `conjStarAlgAut u`. -/
lemma cfc_log_conj {M : Matrix n n ℂ} (hM : M.PosDef) (u : unitary (Matrix n n ℂ)) :
    cfc Real.log ((u : Matrix n n ℂ) * M * (star u : Matrix n n ℂ))
      = (u : Matrix n n ℂ) * cfc Real.log M * (star u : Matrix n n ℂ) := by
  have hconj : ∀ x : Matrix n n ℂ,
      (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) x
        = (u : Matrix n n ℂ) * x * (star u : Matrix n n ℂ) :=
    fun x => Unitary.conjStarAlgAut_apply u x
  have hcont : Continuous (⇑(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u)) := by
    have he : (⇑(Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u))
        = fun x => (u : Matrix n n ℂ) * x * (star u : Matrix n n ℂ) := funext hconj
    rw [he]; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hf : ContinuousOn Real.log (spectrum ℝ M) := QIQTH.QuantumEntropy.continuousOn_log_spectrum hM
  rw [← hconj M,
    ← StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u) Real.log M hf hcont,
    hconj (cfc Real.log M)]

/-- The matrix logarithm of a unitary conjugate: `log(u·M·u⋆) = u · log M · u⋆`. -/
lemma matLog_conj {M : Matrix n n ℂ} (hM : M.PosDef) (u : unitary (Matrix n n ℂ))
    (h : ((u : Matrix n n ℂ) * M * (star u : Matrix n n ℂ)).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h
      = (u : Matrix n n ℂ) * QIQTH.QuantumEntropy.matLog hM.1 * (star u : Matrix n n ℂ) := by
  unfold QIQTH.QuantumEntropy.matLog
  rw [← h.cfc_eq Real.log, cfc_log_conj hM u, hM.1.cfc_eq Real.log]

/-- **Unitary invariance of the quantum relative entropy**: `D(u·ρ·u⋆ ‖ u·σ·u⋆) = D(ρ‖σ)`. -/
lemma relEntropy_unitary_invariant {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (u : unitary (Matrix n n ℂ))
    (hρ' : ((u : Matrix n n ℂ) * ρ * (star u : Matrix n n ℂ)).IsHermitian)
    (hσ' : ((u : Matrix n n ℂ) * σ * (star u : Matrix n n ℂ)).IsHermitian) :
    QIQTH.QuantumEntropy.relEntropy hρ' hσ' = QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1 := by
  have hsu : (star (u : Matrix n n ℂ)) * (u : Matrix n n ℂ) = 1 :=
    Unitary.star_mul_self_of_mem u.2
  -- `Tr(u ρ u⋆ · u Y u⋆) = Tr(ρ Y)`
  have htr : ∀ Y : Matrix n n ℂ,
      ((u : Matrix n n ℂ) * ρ * (star u : Matrix n n ℂ)
        * ((u : Matrix n n ℂ) * Y * (star u : Matrix n n ℂ))).trace = (ρ * Y).trace := by
    intro Y
    rw [show (u : Matrix n n ℂ) * ρ * (star u : Matrix n n ℂ)
          * ((u : Matrix n n ℂ) * Y * (star u : Matrix n n ℂ))
        = (u : Matrix n n ℂ) * ρ * ((star u : Matrix n n ℂ) * (u : Matrix n n ℂ))
          * Y * (star u : Matrix n n ℂ) by simp only [Matrix.mul_assoc],
      hsu, Matrix.mul_one, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hsu, Matrix.one_mul]
  rw [QIQTH.QuantumEntropy.relEntropy, QIQTH.QuantumEntropy.relEntropy,
    matLog_conj hρ u hρ', matLog_conj hσ u hσ',
    show (u : Matrix n n ℂ) * QIQTH.QuantumEntropy.matLog hρ.1 * (star u : Matrix n n ℂ)
        - (u : Matrix n n ℂ) * QIQTH.QuantumEntropy.matLog hσ.1 * (star u : Matrix n n ℂ)
      = (u : Matrix n n ℂ)
          * (QIQTH.QuantumEntropy.matLog hρ.1 - QIQTH.QuantumEntropy.matLog hσ.1)
          * (star u : Matrix n n ℂ) by rw [Matrix.mul_sub, Matrix.sub_mul],
    htr]

/-- `log(c·ρ) = (log c)·1 + log ρ` for a positive scalar `c` and positive-definite `ρ`. -/
lemma matLog_smul {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) {c : ℝ} (hc : 0 < c)
    (h : ((c : ℝ) • ρ).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h
      = (Real.log c) • (1 : Matrix n n ℂ) + QIQTH.QuantumEntropy.matLog hρ.1 := by
  have hspec : ∀ x ∈ spectrum ℝ ρ, 0 < x := by
    intro x hx
    rw [hρ.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hρ.eigenvalues_pos i
  have hcont_img : ContinuousOn Real.log ((c • ·) '' spectrum ℝ ρ) := by
    apply Real.continuousOn_log.mono
    rintro _ ⟨x, hx, rfl⟩
    exact (mul_pos hc (hspec x hx)).ne'
  unfold QIQTH.QuantumEntropy.matLog
  rw [← h.cfc_eq Real.log, ← cfc_comp_smul c Real.log ρ hcont_img]
  rw [cfc_congr (g := fun x => Real.log c + Real.log x)
      (fun x hx => by simp only [smul_eq_mul]; exact Real.log_mul hc.ne' (hspec x hx).ne')]
  rw [cfc_const_add (Real.log c) Real.log ρ
      (QIQTH.QuantumEntropy.continuousOn_log_spectrum hρ) hρ.1.isSelfAdjoint]
  rw [Algebra.algebraMap_eq_smul_one, hρ.1.cfc_eq Real.log]

/-- **Scaling of the relative entropy**: `D(c·ρ ‖ c·σ) = c·D(ρ‖σ)` for `c > 0` (the `(log c)·1`
    terms cancel in `log(c·ρ) − log(c·σ)`). -/
lemma relEntropy_smul {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) {c : ℝ} (hc : 0 < c)
    (hρ' : ((c : ℝ) • ρ).IsHermitian) (hσ' : ((c : ℝ) • σ).IsHermitian) :
    QIQTH.QuantumEntropy.relEntropy hρ' hσ' = c * QIQTH.QuantumEntropy.relEntropy hρ.1 hσ.1 := by
  rw [QIQTH.QuantumEntropy.relEntropy, QIQTH.QuantumEntropy.relEntropy,
    matLog_smul hρ hc hρ', matLog_smul hσ hc hσ',
    show (Real.log c • (1 : Matrix n n ℂ) + QIQTH.QuantumEntropy.matLog hρ.1)
        - (Real.log c • (1 : Matrix n n ℂ) + QIQTH.QuantumEntropy.matLog hσ.1)
      = QIQTH.QuantumEntropy.matLog hρ.1 - QIQTH.QuantumEntropy.matLog hσ.1 by abel,
    Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

end QIQTH.Entropy
