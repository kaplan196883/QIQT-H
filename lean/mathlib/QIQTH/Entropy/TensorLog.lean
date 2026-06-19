import QIQTH.Entropy.PartialTraceDPI
import QIQTH.Entropy.RelEntropyConvex
import QIQTH.Entropy.CommuteRpow

/-!
# Toward subadditivity: the general tensor logarithm `log(A ⊗ B) = log A ⊗ I + I ⊗ log B`

With partial-trace data processing in hand (`partial_trace_dpi`), the next headline results are the
**subadditivity** `S(ρ) ≤ S(ρ₁) + S(ρ₂)` (Carlen §6.5) and **strong subadditivity**
`S(ρ₁₃)+S(ρ₂₃) ≥ S(ρ₁₂₃)+S(ρ₃)` (§6.6) of the von Neumann entropy. Both rest on the **tensor logarithm**
identity `log(ρ₁ ⊗ ρ₂) = log ρ₁ ⊗ I + I ⊗ log ρ₂`.

`matLog_kron_one` (in `PartialTraceDPI.lean`) already gives the right-factor half `log(A ⊗ 1) = (log A)⊗1`.
This file supplies the **left-factor half** `log(1 ⊗ B) = 1 ⊗ (log B)`, via the two-type left Kronecker
homomorphism `kronLeftHom` and CFC naturality — the exact mirror of `kronRightHom`/`matLog_kron_one`.
The remaining ingredient for the full identity (the commuting-product log rule
`log(PQ) = log P + log Q` for commuting positive `P, Q`, applied to `P = A⊗1`, `Q = 1⊗B`) is the cited
next brick. Axiom-free.
-/

namespace QIQTH.Entropy

open Matrix CStarMatrix Filter
open scoped Kronecker ComplexOrder Topology MatrixOrder NNReal Matrix.Norms.Frobenius

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- `B ↦ 1_n ⊗ₖ B` as a unital ⋆-algebra homomorphism `Matrix p p ℂ →⋆ₐ Matrix (n×p)(n×p) ℂ` (the
left-factor, two-type generalization of `TensorPower.kroneckerLeftHom`). -/
@[simps]
noncomputable def kronLeftHom (n p : Type*) [Fintype n] [DecidableEq n] [Fintype p]
    [DecidableEq p] : Matrix p p ℂ →⋆ₐ[ℂ] Matrix (n × p) (n × p) ℂ where
  toFun B := (1 : Matrix n n ℂ) ⊗ₖ B
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, Matrix.mul_one]
  map_zero' := kronecker_zero 1
  map_add' A B := kronecker_add 1 A B
  commutes' r := by simp only [Algebra.algebraMap_eq_smul_one, kronecker_smul, one_kronecker_one]
  map_star' A := by
    simp only [Matrix.star_eq_conjTranspose, conjTranspose_kronecker, Matrix.conjTranspose_one]

lemma continuous_kronLeftHom :
    Continuous (kronLeftHom n m : Matrix m m ℂ → Matrix (n × m) (n × m) ℂ) := by
  apply continuous_matrix
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [kronLeftHom_apply, Matrix.kroneckerMap_apply]
  exact continuous_const.mul (continuous_id.matrix_elem i₂ j₂)

/-- **The matrix logarithm of `1 ⊗ B` factors**: `log(1_n ⊗ B) = 1_n ⊗ (log B)`. CFC naturality
(`map_cfc`) under `kronLeftHom` — the left-factor mirror of `matLog_kron_one`. -/
lemma matLog_one_kron {B : Matrix m m ℂ} (hB : B.PosDef)
    (h : ((1 : Matrix n n ℂ) ⊗ₖ B).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h = (1 : Matrix n n ℂ) ⊗ₖ (QIQTH.QuantumEntropy.matLog hB.1) := by
  unfold QIQTH.QuantumEntropy.matLog
  have hf : ContinuousOn Real.log (spectrum ℝ B) :=
    QIQTH.QuantumEntropy.continuousOn_log_spectrum hB
  rw [← h.cfc_eq Real.log, show ((1 : Matrix n n ℂ) ⊗ₖ B) = kronLeftHom n m B from rfl,
    ← StarAlgHomClass.map_cfc (kronLeftHom n m) Real.log B hf continuous_kronLeftHom (ha := hB.1),
    kronLeftHom_apply]
  exact congrArg ((1 : Matrix n n ℂ) ⊗ₖ ·) (hB.1.cfc_eq Real.log)

/-- **The logarithm of a commuting product is the sum of logarithms**: `log(P·Q) = log P + log Q`
for commuting positive-definite `P, Q`. Proved by differentiating Mathlib-free identity
`(P·Q)^t = P^t·Q^t` (`commute_rpow_mul`, valid for `t ≥ 0`) at `t = 0`: both sides are differentiable
there (`hasDerivAt_rpow_zero`), `d/dt M^t|₀ = log M`, and the product rule gives `log P + log Q`; since
the two functions agree on `[0,∞)`, their right-derivatives at `0` coincide. -/
theorem matLog_mul_of_commute {P Q : Matrix n n ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hc : Commute P Q) (hPQ : (P * Q).IsHermitian) :
    QIQTH.QuantumEntropy.matLog hPQ
      = QIQTH.QuantumEntropy.matLog hP.1 + QIQTH.QuantumEntropy.matLog hQ.1 := by
  have hPQpd : (P * Q).PosDef := posDef_mul_of_commute hP hQ hc
  have h1 : HasDerivAt (fun t : ℝ => (P * Q) ^ t) (QIQTH.QuantumEntropy.matLog hPQpd.1) 0 :=
    hasDerivAt_rpow_zero hPQpd
  have h2 : HasDerivAt (fun t : ℝ => P ^ t * Q ^ t)
      (QIQTH.QuantumEntropy.matLog hP.1 + QIQTH.QuantumEntropy.matLog hQ.1) 0 := by
    have hm := (hasDerivAt_rpow_zero hP).mul (hasDerivAt_rpow_zero hQ)
    rw [CFC.rpow_zero P hP.posSemidef.nonneg, CFC.rpow_zero Q hQ.posSemidef.nonneg,
      Matrix.mul_one, Matrix.one_mul] at hm
    exact hm
  have heq : (fun t : ℝ => P ^ t * Q ^ t) =ᶠ[𝓝[≥] (0:ℝ)] (fun t : ℝ => (P * Q) ^ t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (commute_rpow_mul hP hQ hc ht).symm
  have hd1 : HasDerivWithinAt (fun t : ℝ => P ^ t * Q ^ t)
      (QIQTH.QuantumEntropy.matLog hPQpd.1) (Set.Ici 0) 0 :=
    h1.hasDerivWithinAt.congr_of_eventuallyEq heq (by
      simp [CFC.rpow_zero P hP.posSemidef.nonneg, CFC.rpow_zero Q hQ.posSemidef.nonneg,
        CFC.rpow_zero (P * Q) hPQpd.posSemidef.nonneg])
  have hu : UniqueDiffWithinAt ℝ (Set.Ici (0:ℝ)) 0 := uniqueDiffWithinAt_Ici 0
  exact (hd1.derivWithin hu).symm.trans (h2.hasDerivWithinAt.derivWithin hu)

/-- **The general tensor logarithm**: `log(A ⊗ B) = (log A) ⊗ I + I ⊗ (log B)` for positive-definite
`A, B`. Since `A ⊗ B = (A ⊗ 1)·(1 ⊗ B)` and the factors commute, `matLog_mul_of_commute` splits the log,
and `matLog_kron_one` / `matLog_one_kron` evaluate each piece. This is the identity behind the
subadditivity `S(ρ) ≤ S(ρ₁) + S(ρ₂)` (Carlen §6.5) and strong subadditivity (§6.6). -/
theorem matLog_kronecker {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (h : (A ⊗ₖ B).IsHermitian) :
    QIQTH.QuantumEntropy.matLog h
      = QIQTH.QuantumEntropy.matLog hA.1 ⊗ₖ (1 : Matrix m m ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ QIQTH.QuantumEntropy.matLog hB.1 := by
  have hcomm : Commute (A ⊗ₖ (1 : Matrix m m ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ B) := by
    show (A ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B)
        = ((1 : Matrix n n ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix m m ℂ))
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul, Matrix.mul_one]
  have hA1 : (A ⊗ₖ (1 : Matrix m m ℂ)).PosDef := hA.kronecker Matrix.PosDef.one
  have hB1 : ((1 : Matrix n n ℂ) ⊗ₖ B).PosDef := Matrix.PosDef.one.kronecker hB
  have hfac : (A ⊗ₖ B) = (A ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have h' : ((A ⊗ₖ (1 : Matrix m m ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ B)).IsHermitian := hfac ▸ h
  have hmul := matLog_mul_of_commute hA1 hB1 hcomm h'
  rw [matLog_kron_one hA, matLog_one_kron hB] at hmul
  rw [← hmul]
  congr 1

end QIQTH.Entropy
