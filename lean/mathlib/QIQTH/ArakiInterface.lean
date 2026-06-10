/-
  ArakiInterface — the finite-dimensional realization of the Araki relative-entropy interface.

  Formerly this module declared `NormalState`, `IsFaithful`, `mixture`, `AkRelEnt`, `Akre_nonneg`,
  `donald_araki`, `NormalUCPChannel`, `NormalUCPChannel.pull` and `dpi_ucp` as opaque AXIOMS over an
  abstract regional von Neumann algebra.  Nine of those eleven are now **DISCHARGED** by the
  finite-dimensional model (`NormalState := HermitianMat`, the carrier of `QuantumEntropy`'s
  `DonaldSystem`):

    * `AkRelEnt`     := the Umegaki relative entropy `DonaldSystem.D` (= `relEntropy`);
    * `Akre_nonneg`  := **Klein's inequality** `relEntropy_nonneg` (a theorem — conditioned on the
                        density-matrix hypotheses Klein genuinely requires);
    * `donald_araki` := **Donald's identity** `Donald.donald_identity` (a theorem);
    * `dpi_ucp`      := the **data-processing inequality** `DPI.DPI_inequality` (a theorem, for the
                        mixed-unitary channel class).

  HONEST SCOPE (per the original GPT-5.5-pro audit): in the genuine Araki / Tomita–Takesaki setting
  the cross-entropy object is unbounded and `AkRelEnt` can be `+∞`; this module is the *finite-dim
  model*, where those pathologies are absent — the unconditional abstract axioms become the honest
  conditional (density-matrix) theorems.  Two results remain axioms here, as the cited frontier:
  `IHol_le_Shannon` (Holevo's bound) and `AkRelEnt_eq_zero_iff` (the Klein *equality* case — only the
  trivial direction `ρ = σ ⟹ D = 0` is finite-dim immediate; the converse is a deeper milestone).
-/

import QIQTH.QuantumRelativeEntropy
import QIQTH.DPI
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

namespace QIQTH
namespace ArakiInterface

open QIQTH.QuantumEntropy QIQTH.Entropy CStarMatrix
open scoped ComplexOrder MatrixOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **Normal state** (finite-dim model): a Hermitian matrix — the carrier of the `DonaldSystem`.
    It is a genuine density matrix when additionally positive-definite with unit trace. -/
abbrev NormalState (n : Type) [Fintype n] [DecidableEq n] : Type := HermitianMat n

/-- **Faithful** = positive-definite (full support). -/
def IsFaithful (ρ : NormalState n) : Prop := ρ.1.PosDef

/-- **Araki relative entropy**, realized as the finite-dim Umegaki relative entropy `D`. -/
noncomputable def AkRelEnt (ρ σ : NormalState n) : ℝ := DonaldSystem.D ρ σ

/-- **Mixture** of finitely many normal states — the `DonaldSystem` weighted mixture. -/
noncomputable def mixture {ι : Type} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState n) :
    NormalState n :=
  DonaldSystem.mixture s p ρ

/-- `AkRelEnt` is the Umegaki relative entropy. -/
lemma AkRelEnt_eq_relEntropy (ρ σ : NormalState n) : AkRelEnt ρ σ = relEntropy ρ.2 σ.2 := by
  show (-((ρ.1 * matLog σ.2).trace.re) - -((ρ.1 * matLog ρ.2).trace.re))
      = (ρ.1 * (matLog ρ.2 - matLog σ.2)).trace.re
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]; ring

/-- Predicate: a finite ensemble has finite Araki relative entropy against the reference state.
    (Always finite in the finite-dim model.) -/
def FiniteEntropy (σ : NormalState n) (ρ : NormalState n) : Prop :=
  ∃ B : ℝ, AkRelEnt ρ σ ≤ B

/-- **Klein positivity (theorem).**  `0 ≤ AkRelEnt ω σ` for density matrices — the finite-dim
    content of the former `Akre_nonneg` axiom, now `relEntropy_nonneg` (Klein's inequality). -/
theorem Akre_nonneg (ρ σ : NormalState n) (hρ : ρ.1.PosDef) (hσ : σ.1.PosDef)
    (hρ1 : ρ.1.trace = 1) (hσ1 : σ.1.trace = 1) : 0 ≤ AkRelEnt ρ σ := by
  rw [AkRelEnt_eq_relEntropy]; exact relEntropy_nonneg hρ hσ hρ1 hσ1

/-- **Donald's identity (theorem).**  The former `donald_araki` axiom, now `Donald.donald_identity`
    over the finite-dim `DonaldSystem`. -/
theorem donald_araki {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (ρ : ι → NormalState n) (σ : NormalState n) :
    ∑ k ∈ s, p k * AkRelEnt (ρ k) σ
      = AkRelEnt (mixture s p ρ) σ + ∑ k ∈ s, p k * AkRelEnt (ρ k) (mixture s p ρ) :=
  Donald.donald_identity s p ρ σ

/-- **Normal UCP channel** (finite-dim model): a mixed-unitary channel. -/
abbrev NormalUCPChannel (n : Type) [Fintype n] [DecidableEq n] := DPI.MixedUnitaryChannel n

/-- A channel acts on states by Schrödinger pullback (Hermitian, since `Φ(ρ) = Σ pₖ Uₖ ρ Uₖ⋆`). -/
noncomputable def NormalUCPChannel.pull (Φ : NormalUCPChannel n) (ρ : NormalState n) :
    NormalState n :=
  ⟨DPI.MixedUnitaryChannel.pull Φ ρ.1, by
    rw [Matrix.isHermitian_iff_isSelfAdjoint]
    refine isSelfAdjoint_sum _ fun k _ => (IsSelfAdjoint.all (Φ.p k)).smul ?_
    rw [isSelfAdjoint_iff, star_mul, star_mul, star_star,
      ρ.2.isSelfAdjoint.star_eq, ← mul_assoc]⟩

/-- **Data-processing inequality (theorem).**  For density-matrix states, applying a mixed-unitary
    channel can only decrease the relative entropy — the former `dpi_ucp` axiom, now
    `DPI.DPI_inequality` (Lindblad–Uhlmann via Lieb's concavity). -/
theorem dpi_ucp (Φ : NormalUCPChannel n) (ρ σ : NormalState n)
    (hρ : ρ.1.PosDef) (hσ : σ.1.PosDef) :
    AkRelEnt (Φ.pull ρ) (Φ.pull σ) ≤ AkRelEnt ρ σ := by
  rw [AkRelEnt_eq_relEntropy, AkRelEnt_eq_relEntropy]
  exact DPI.DPI_inequality Φ hρ hσ (Φ.pull ρ).2 (Φ.pull σ).2

/-! ### Holevo information -/

/-- The trace of a product of positive-semidefinite matrices has nonnegative real part:
    `0 ≤ Re Tr(ρ·M)`.  Via `Tr(ρ·M) = Tr(√ρ·M·√ρ)` (cyclicity) and `√ρ·M·√ρ ⪰ 0`. -/
lemma trace_mul_re_nonneg {ρ M : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hM : M.PosSemidef) :
    0 ≤ (ρ * M).trace.re := by
  have hsq : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hsqH : (CFC.sqrt ρ).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)).isHermitian
  have hPSD : (CFC.sqrt ρ * M * CFC.sqrt ρ).PosSemidef := by
    have h := hM.mul_mul_conjTranspose_same (CFC.sqrt ρ)
    rwa [hsqH.eq] at h
  have hcyc : (ρ * M).trace = (CFC.sqrt ρ * M * CFC.sqrt ρ).trace := by
    conv_lhs => rw [← hsq, Matrix.mul_assoc]
    exact Matrix.trace_mul_comm (CFC.sqrt ρ) (CFC.sqrt ρ * M)
  rw [hcyc]
  exact (Complex.le_def.mp hPSD.trace_nonneg).1

/-- `matLog` as the (Mathlib) `cfc` of `Real.log`. -/
lemma matLog_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) : matLog hA = cfc Real.log A :=
  (hA.cfc_eq Real.log).symm

/-- **Operator monotonicity of the matrix logarithm**: `A ⪯ B ⟹ log A ⪯ log B` for positive-definite
    `A, B`.  Mathlib's `CFC.log_le_log` lives on a CStarAlgebra (`Matrix n n ℂ` in the Frobenius norm
    is not one), so we transport through the `CStarMatrix` bridge. -/
lemma matLog_le {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    matLog hA.1 ≤ matLog hB.1 := by
  have hsp : IsStrictlyPositive (ofMatrixStarAlgEquiv A) :=
    IsStrictlyPositive.iff_of_unital.mpr
      ⟨ofMatrix_nonneg_iff.mpr hA.posSemidef, (Matrix.PosDef.isUnit hA).map ofMatrixStarAlgEquiv⟩
  rw [matLog_eq_cfc, matLog_eq_cfc, ← ofMatrix_le_iff,
    ofMatrix_cfc Real.log A hA.1.isSelfAdjoint (continuousOn_log_spectrum hA),
    ofMatrix_cfc Real.log B hB.1.isSelfAdjoint (continuousOn_log_spectrum hB)]
  exact CFC.log_le_log (ofMatrix_le_iff.mpr hAB) hsp

/-- **Per-ensemble Holevo bound (per-term).**  If `c·ρ ⪯ τ` for density matrices `ρ, τ` and `c > 0`,
    then `D(ρ‖τ) ≤ −log c`.  (With `c = pᵢ` and `τ = ρ̄ = Σ pₖρₖ`, this is `D(ρᵢ‖ρ̄) ≤ −log pᵢ`.)
    Proof: operator monotonicity of `log` gives `log(c·ρ) ⪯ log τ`; pairing with `ρ ⪰ 0` and
    `log(c·ρ) = (log c)·1 + log ρ` (`matLog_smul`) yields `Re Tr(ρ log τ) ≥ log c + Re Tr(ρ log ρ)`. -/
lemma relEntropy_le_neg_log {ρ τ : Matrix n n ℂ} (hρ : ρ.PosDef) (hτ : τ.PosDef)
    (hρ1 : ρ.trace = 1) {c : ℝ} (hc : 0 < c) (hcρ : ((c : ℝ) • ρ).PosDef)
    (hle : ((c : ℝ) • ρ) ≤ τ) : relEntropy hρ.1 hτ.1 ≤ -Real.log c := by
  have hlog_le : matLog hcρ.1 ≤ matLog hτ.1 := matLog_le hcρ hτ hle
  have hmono : (ρ * matLog hcρ.1).trace.re ≤ (ρ * matLog hτ.1).trace.re := by
    have hN := trace_mul_re_nonneg hρ.posSemidef (Matrix.le_iff.mp hlog_le)
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hN
    linarith
  have hsmul : (ρ * matLog hcρ.1).trace.re = Real.log c + (ρ * matLog hρ.1).trace.re := by
    rw [QIQTH.Entropy.matLog_smul hρ hc hcρ.1, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    congr 1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, hρ1]
    simp
  rw [relEntropy, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith [hmono, hsmul]

/-- Holevo mutual information of a finite ensemble. -/
noncomputable def IHol {ι : Type} (s : Finset ι) (p : ι → ℝ) (ρ : ι → NormalState n) : ℝ :=
  ∑ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ)

/-- **Holevo non-negativity** — from Klein (density ensemble against the mixture). -/
theorem IHol_nonneg {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → NormalState n)
    (hdens : ∀ i ∈ s, (ρ i).1.PosDef ∧ (ρ i).1.trace = 1)
    (hbar : (mixture s p ρ).1.PosDef ∧ (mixture s p ρ).1.trace = 1) :
    0 ≤ IHol s p ρ := by
  refine Finset.sum_nonneg fun k hk => ?_
  exact mul_nonneg (hp_nn k hk)
    (Akre_nonneg _ _ (hdens k hk).1 hbar.1 (hdens k hk).2 hbar.2)

/-- Shannon entropy of the weight distribution (in nats). -/
noncomputable def ShannonWeights {ι : Type} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)

/-- **Holevo's bound (theorem).**  `χ = Σᵢ pᵢ D(ρᵢ‖ρ̄) ≤ H(p)` (Shannon entropy of the weights) for
    a density-matrix ensemble.  The former axiom, now discharged — and *without* the orthogonality
    hypothesis (the inequality is general).  Per term: `pᵢρᵢ ⪯ ρ̄`, so by operator monotonicity of
    `log` (`matLog_le`), `D(ρᵢ‖ρ̄) ≤ −log pᵢ` (`relEntropy_le_neg_log`); summing gives `χ ≤ H(p)`. -/
theorem IHol_le_Shannon {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → ℝ)
    (hp_pos : ∀ i ∈ s, 0 < p i) (hp_sum : ∑ i ∈ s, p i = 1)
    (ρ : ι → NormalState n)
    (hdens : ∀ i ∈ s, (ρ i).1.PosDef ∧ (ρ i).1.trace = 1) :
    IHol s p ρ ≤ ShannonWeights s p := by
  have hsmul_eq : ∀ (c : ℝ) (M : Matrix n n ℂ), (↑c : ℂ) • M = c • M :=
    fun c M => algebraMap_smul ℂ c M
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with rfl | h
    · simp at hp_sum
    · exact h
  have hbarmat : (mixture s p ρ).1 = ∑ k ∈ s, (↑(p k) : ℂ) • (ρ k).1 := rfl
  have hPSDk : ∀ k ∈ s, ((↑(p k) : ℂ) • (ρ k).1).PosDef := fun k hk => by
    rw [hsmul_eq]; exact ((hdens k hk).1).smul (hp_pos k hk)
  have hbarpos : (mixture s p ρ).1.PosDef := by
    rw [hbarmat]; exact Matrix.posDef_sum hne fun k hk => hPSDk k hk
  have hle : ∀ i ∈ s, ((p i : ℝ) • (ρ i).1) ≤ (mixture s p ρ).1 := by
    intro i hi
    rw [Matrix.le_iff, hbarmat, ← hsmul_eq (p i) (ρ i).1, ← Finset.add_sum_erase s _ hi,
      add_sub_cancel_left]
    exact Matrix.posSemidef_sum (s.erase i)
      fun k hk => (hPSDk k (Finset.mem_of_mem_erase hk)).posSemidef
  rw [IHol, ShannonWeights]
  have hbound : ∀ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ) ≤ -(p i * Real.log (p i)) := by
    intro i hi
    rw [AkRelEnt_eq_relEntropy]
    have hper := relEntropy_le_neg_log (hdens i hi).1 hbarpos (hdens i hi).2 (hp_pos i hi)
      ((hdens i hi).1.smul (hp_pos i hi)) (hle i hi)
    nlinarith [hper, hp_pos i hi]
  calc ∑ i ∈ s, p i * AkRelEnt (ρ i) (mixture s p ρ)
      ≤ ∑ i ∈ s, -(p i * Real.log (p i)) := Finset.sum_le_sum hbound
    _ = -∑ i ∈ s, p i * Real.log (p i) := by rw [Finset.sum_neg_distrib]

/-- The trivial direction of the Klein equality case: `ρ = σ ⟹ D(ρ‖σ) = 0`. -/
theorem AkRelEnt_self (ρ : NormalState n) : AkRelEnt ρ ρ = 0 := by
  rw [AkRelEnt_eq_relEntropy]; exact relEntropy_self ρ.2

/-- **Klein equality case (theorem).**  For density matrices, `AkRelEnt(ω ‖ σ) = 0 ↔ ω = σ`.  The
    former axiom, now discharged: the `←` direction is `AkRelEnt_self`, and the hard `→` direction
    is `relEntropy_eq_zero` (Klein's equality case, via the strict concavity of `log`). -/
theorem AkRelEnt_eq_zero_iff (ω σ : NormalState n)
    (hω : ω.1.PosDef) (hσ : σ.1.PosDef) (hω1 : ω.1.trace = 1) (hσ1 : σ.1.trace = 1) :
    AkRelEnt ω σ = 0 ↔ ω = σ := by
  constructor
  · intro h
    rw [AkRelEnt_eq_relEntropy] at h
    exact Subtype.ext (relEntropy_eq_zero hω hσ hω1 hσ1 h)
  · rintro rfl; exact AkRelEnt_self _

end ArakiInterface
end QIQTH
