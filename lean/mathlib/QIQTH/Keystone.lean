/-
  K0 (KEYSTONE_PLAN.md) — the finite trace-entropy lemmas for THE COUNT.

  The entropy substrate the count capstones stand on (unnormalized counting trace — the binding
  correction: τ(1) = N, never normalized):
  • `maxMixed` — the maximally mixed density `N⁻¹·1` with `maxMixed_isDensity`;
  • `maxMixed_eigenvalues` — every spectral eigenvalue is `N⁻¹` (scalar matrices via the
    eigenvector-basis relation);
  • **`vonNeumannEntropy_maxMixed`** — `S(maxMixed) = log N`: the maximal-entropy state's entropy IS the
    log of the (unnormalized-trace) dimension — the entropy half of the count;
  • **`vonNeumannEntropy_le_log_card`** — the Gibbs/Jensen guard `S(ρ) ≤ log N` for EVERY density
    (riding the held classical `shannon_le_log_card` on the eigenvalue vector): the count equality is
    claimed only where it holds — at maximal mixing. (The strict-concavity uniqueness refinement is the
    standard textbook addendum, not needed by K2.)
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.QuantumRelativeEntropy
import QIQTH.RecordContract

namespace QIQTH.Keystone

open QIQTH.QuantumEntropy
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximally mixed density `N⁻¹·1` (w.r.t. the UNNORMALIZED counting trace). -/
noncomputable def maxMixed (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix ι ι ℂ :=
  ((Fintype.card ι : ℂ))⁻¹ • 1

theorem maxMixed_isDensity [Nonempty ι] : IsDensity (maxMixed ι) where
  posSemidef := by
    rw [maxMixed, show ((Fintype.card ι : ℂ))⁻¹ = (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) from by
      push_cast
      rfl]
    have h1 : (Matrix.PosSemidef (1 : Matrix ι ι ℂ)) := Matrix.PosSemidef.one
    have hc : (0 : ℂ) ≤ (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.zero_le_real]
      positivity
    exact h1.smul hc
  trace_one := by
    rw [maxMixed, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    have hc : (Fintype.card ι : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- Every eigenvalue of the maximally mixed density is `N⁻¹` (a scalar matrix has constant
    spectrum — via the eigenvector-basis relation). -/
theorem maxMixed_eigenvalues [Nonempty ι] (j : ι) :
    (maxMixed_isDensity (ι := ι)).eigenvalues j = ((Fintype.card ι : ℝ))⁻¹ := by
  have hH := (maxMixed_isDensity (ι := ι)).posSemidef.1
  have h := hH.mulVec_eigenvectorBasis j
  have hlhs : (maxMixed ι).mulVec (hH.eigenvectorBasis j).ofLp
      = ((Fintype.card ι : ℂ))⁻¹ • (hH.eigenvectorBasis j).ofLp := by
    simp only [maxMixed, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hlhs] at h
  have hreal : hH.eigenvalues j • (hH.eigenvectorBasis j).ofLp
      = ((hH.eigenvalues j : ℝ) : ℂ) • (hH.eigenvectorBasis j).ofLp := by
    funext i
    simp [Complex.real_smul]
  rw [hreal] at h
  have hvne : hH.eigenvectorBasis j ≠ 0 := hH.eigenvectorBasis.orthonormal.ne_zero j
  have hv : (hH.eigenvectorBasis j).ofLp ≠ 0 := by
    intro h0
    apply hvne
    ext i
    exact congrFun h0 i
  have hsub : (((Fintype.card ι : ℂ))⁻¹ - ((hH.eigenvalues j : ℝ) : ℂ))
      • (hH.eigenvectorBasis j).ofLp = 0 := by
    rw [sub_smul, h]
    simp
  rcases smul_eq_zero.mp hsub with hc | hzero
  · have hceq : ((Fintype.card ι : ℂ))⁻¹ = ((hH.eigenvalues j : ℝ) : ℂ) :=
      sub_eq_zero.mp hc
    have hcast : ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) = ((hH.eigenvalues j : ℝ) : ℂ) := by
      rw [← hceq]
      push_cast
      rfl
    exact (Complex.ofReal_inj.mp hcast).symm
  · exact absurd hzero hv

/-- **K0 CAPSTONE (entropy value) — `S(maxMixed) = log N`:** the maximally mixed state's entropy is
    the log of the unnormalized-trace dimension — the entropy half of the count. -/
theorem vonNeumannEntropy_maxMixed [Nonempty ι] :
    vonNeumannEntropy (maxMixed_isDensity (ι := ι)) = Real.log (Fintype.card ι) := by
  rw [vonNeumannEntropy,
    Finset.sum_congr rfl fun j _ => by rw [maxMixed_eigenvalues],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  simp only [Real.negMulLog_def, Real.log_inv]
  field_simp

/-- **K0 CAPSTONE (the guard) — the Gibbs/Jensen bound `S(ρ) ≤ log N` for EVERY density** (riding the
    held classical bound on the eigenvalue vector): the count equality is claimed only at maximal
    mixing. -/
theorem vonNeumannEntropy_le_log_card {ρ : Matrix ι ι ℂ} (h : IsDensity ρ) :
    vonNeumannEntropy h ≤ Real.log (Fintype.card ι) := by
  have hb := QIQTH.RecordContract.shannon_le_log_card h.eigenvalues
    h.eigenvalues_nonneg h.sum_eigenvalues
  rwa [QIQTH.RecordContract.shannon_eq_sum_negMulLog] at hb

end QIQTH.Keystone
