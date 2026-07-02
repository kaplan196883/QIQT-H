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

/-! ## K2a — the standalone finite count

The screen's diamond algebra with the UNNORMALIZED counting trace; the weight is TRACE-DEFINED
(`wEntτ e = log D_e` where `D_e` is the trace of the link projection — per the binding correction, an
EXTERNAL weight matching `log D_e` is the old calibration and is stated only as the honest iff). -/

/-- Link dimensions (positive). -/
structure LinkDims (E : Type*) where
  /-- the dimension of each link fiber -/
  D : E → ℕ
  /-- positivity -/
  hD : ∀ e, 0 < D e

variable {E : Type*} [DecidableEq E]

/-- The screen microstates over a cut: one `Fin (D e)` record fiber per link. -/
abbrev Micro (L : LinkDims E) (C : Finset E) : Type _ := (e : C) → Fin (L.D e.val)

instance microNonempty (L : LinkDims E) (C : Finset E) : Nonempty (Micro L C) :=
  ⟨fun e => ⟨0, L.hD e.val⟩⟩

/-- The microstate count `N_C = Π_{e∈C} D_e`. -/
noncomputable def NC (L : LinkDims E) (C : Finset E) : ℕ := ∏ e ∈ C, L.D e

theorem card_micro (L : LinkDims E) (C : Finset E) :
    Fintype.card (Micro L C) = NC L C := by
  rw [NC, Fintype.card_pi, ← Finset.prod_coe_sort C (fun e => L.D e)]
  exact Finset.prod_congr rfl fun e _ => Fintype.card_fin _

theorem NC_pos (L : LinkDims E) (C : Finset E) : 0 < NC L C :=
  Finset.prod_pos fun e _ => L.hD e

/-- The diamond algebra of the cut: the full matrix algebra on the microstates. -/
abbrev DiamondAlg (L : LinkDims E) (C : Finset E) : Type _ :=
  Matrix (Micro L C) (Micro L C) ℂ

/-- **The UNNORMALIZED counting trace** (`τ(1) = N_C` — the binding correction; a normalized trace
    kills the count). -/
noncomputable def tauCount (L : LinkDims E) (C : Finset E) (x : DiamondAlg L C) : ℂ :=
  Matrix.trace x

/-- The record projection onto a set of microstates. -/
noncomputable def recordProj (L : LinkDims E) (C : Finset E) (R : Finset (Micro L C)) :
    DiamondAlg L C :=
  Matrix.diagonal fun m => if m ∈ R then 1 else 0

/-- `τ(P_R) = |R|` — the trace COUNTS the records. -/
theorem tau_recordProj (L : LinkDims E) (C : Finset E) (R : Finset (Micro L C)) :
    tauCount L C (recordProj L C R) = (R.card : ℂ) := by
  rw [tauCount, recordProj, Matrix.trace_diagonal]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `τ(1) = N_C` — the top projection counts everything. -/
theorem tau_top (L : LinkDims E) (C : Finset E) :
    tauCount L C (1 : DiamondAlg L C) = (NC L C : ℂ) := by
  rw [tauCount, Matrix.trace_one, card_micro]

/-- **The TRACE-DEFINED link weight** `wEntτ e := log D_e` (`D_e` is the τ-dimension of the link
    fiber — the weight comes FROM the trace, never from an external geometric assignment). -/
noncomputable def wEntTau (L : LinkDims E) (e : E) : ℝ := Real.log (L.D e)

/-- The trace-defined cut weight. -/
noncomputable def cutTau (L : LinkDims E) (C : Finset E) : ℝ := ∑ e ∈ C, wEntTau L e

/-- The trace-induced screen area (G enters ONLY as the normalization — never derived). -/
noncomputable def inducedScreenAreaTau (L : LinkDims E) (G : ℝ) (C : Finset E) : ℝ :=
  (4 * G) * cutTau L C

theorem log_NC_eq_cutTau (L : LinkDims E) (C : Finset E) :
    Real.log (NC L C) = cutTau L C := by
  rw [NC, cutTau]
  push_cast
  rw [Real.log_prod]
  · rfl
  · intro e _
    exact_mod_cast (L.hD e).ne'

/-- **K2a CAPSTONE — THE COUNT (standalone finite form):** the maximal entropy of the diamond algebra
    w.r.t. the unnormalized counting trace equals the trace-induced screen area over `4G` —
    `S(maxMixed) = log N_C = Σ_e log D_e = A_τ(C)/4G`, with `G` entering only through the
    normalization. Combined with K0's guard, the equality holds exactly at maximal mixing. -/
theorem K2a_count_capstone (L : LinkDims E) (C : Finset E) {G : ℝ} (hG : G ≠ 0) :
    vonNeumannEntropy (maxMixed_isDensity (ι := Micro L C))
      = inducedScreenAreaTau L G C / (4 * G) := by
  rw [vonNeumannEntropy_maxMixed, card_micro, log_NC_eq_cutTau, inducedScreenAreaTau]
  field_simp

/-- **The honest external-weight statement (the binding correction):** the trace-defined cut matches
    an EXTERNAL weight assignment iff the external weights sum to the log-dimensions — i.e., pointwise
    matching IS the old calibration hypothesis. It is stated, not deleted. -/
theorem count_matches_external_weights_iff (L : LinkDims E) (C : Finset E) (wExt : E → ℝ) :
    cutTau L C = ∑ e ∈ C, wExt e ↔ ∑ e ∈ C, Real.log (L.D e) = ∑ e ∈ C, wExt e :=
  Iff.rfl

end QIQTH.Keystone
