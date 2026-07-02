/-
  J1 (HYPOTHESIS_DELETION_PLAN.md) — the finite corner DISCHARGES the eigen-core matter inputs.

  The three carried matter hypotheses of the W3b trace laws — the KMS-eigen law, frequency conservation, and
  state positivity — are all THEOREMS of the concrete finite corner: `A = Matrix ι ι ℂ`, the state
  `ω = tr(ρ·)` with `ρ = diag p` (`p > 0`), and the matter eigenoperators = the matrix units `E_ij`, whose
  modular frequency is `κ_ij = log p_i − log p_j` (`sigmaDiag_single`: `σ_t(E_ij) = e^{itκ_ij}E_ij` under the
  finite modular flow `ρ^{it}·ρ^{−it}`). Consequences, with NO matter hypotheses:
  • `finiteCorner_kms_E`   — the KMS-eigen law `ω(E_ij·E_kl) = e^{κ_ij}·ω(E_kl·E_ij)`, unconditional;
  • `finiteCorner_freq_E`  — frequency conservation, AUTOMATIC from the matrix-unit index loop (a nonzero trace
    forces `j = k ∧ i = l`, whence total frequency `κ_ij + κ_ji = 0` — no nondegeneracy needed);
  • `finiteCorner_pos`     — positivity `ω(A*A) = ∑ p_m‖A_km‖² ≥ 0`;
  and therefore the CONCRETE eigen-term family `finiteCornerTerm` satisfies **traciality
  (`finiteCorner_tau_trace`) and positivity (`finiteCorner_tau_pos`) UNCONDITIONALLY** — the constructed
  dual-weight trace's laws hold in a genuine model with every matter input a theorem.
  HYPOTHESES DELETED (for this model): hkms, hfreq, hpos.

  ⚠ Honest scope: the finite (Type I) corner — the concrete witness, not the continuum matter algebra; diagonal
  `ρ` (general PosDef via eigenbasis transport = follow-on); the vN closure stays carried. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.EigenCore
import QIQTH.FiniteModularTheory

namespace QIQTH.TypeIITrace

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal density `ρ = diag p`. -/
noncomputable def rhoDiag (p : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun i => (p i : ℂ)

/-- The matter state `ω(A) = tr(ρA)`. -/
noncomputable def matState (p : ι → ℝ) (A : Matrix ι ι ℂ) : ℂ := (rhoDiag p * A).trace

/-- The matrix unit `E_ij`. -/
def unitE (i j : ι) : Matrix ι ι ℂ := Matrix.single i j 1

/-- The modular frequency of `E_ij`: `κ_ij = log p_i − log p_j`. -/
noncomputable def kappaOf (p : ι → ℝ) (i j : ι) : ℝ := Real.log (p i) - Real.log (p j)

/-- **The eigen law (convention verified by the consult)**: under the finite modular flow
    `σ_t = ρ^{it}·ρ^{−it}` (`QIQTH.sigmaDiag`), the matrix unit is a modular eigenoperator,
    `σ_t(E_ij) = e^{it·κ_ij}·E_ij`. -/
theorem sigmaDiag_single (p : ι → ℝ) (hp : ∀ i, 0 < p i) (t : ℝ) (i j : ι) :
    QIQTH.FiniteModularTheory.sigmaDiag p t (unitE i j)
      = Complex.exp (Complex.I * (t : ℂ) * (kappaOf p i j : ℂ)) • unitE i j := by
  ext a b
  rw [Matrix.smul_apply]
  have h1 : QIQTH.FiniteModularTheory.sigmaDiag p t (unitE i j) a b
      = (p a : ℂ) ^ (Complex.I * (t : ℂ)) * unitE i j a b
        * (p b : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ)) := by
    rw [QIQTH.FiniteModularTheory.sigmaDiag, QIQTH.FiniteModularTheory.diagPow,
      QIQTH.FiniteModularTheory.diagPow, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [h1, unitE, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, mul_one, smul_eq_mul, mul_one]
    have hpi : (p i : ℂ) ≠ 0 := by exact_mod_cast (hp i).ne'
    have hpj : (p j : ℂ) ≠ 0 := by exact_mod_cast (hp j).ne'
    rw [Complex.cpow_def_of_ne_zero hpi, Complex.cpow_def_of_ne_zero hpj, ← Complex.exp_add]
    congr 1
    rw [show Complex.log ((p i : ℝ) : ℂ) = ((Real.log (p i) : ℝ) : ℂ) from
        (Complex.ofReal_log (hp i).le).symm,
      show Complex.log ((p j : ℝ) : ℂ) = ((Real.log (p j) : ℝ) : ℂ) from
        (Complex.ofReal_log (hp j).le).symm,
      kappaOf]
    push_cast
    ring
  · rw [if_neg h, mul_zero, zero_mul, smul_eq_mul, mul_zero]

/-- The matrix-unit trace formula: `ω(E_ij·E_kl) = if j = k ∧ i = l then p_i else 0`. -/
theorem matState_E_mul_E (p : ι → ℝ) (i j k l : ι) :
    matState p (unitE i j * unitE k l) = if j = k ∧ i = l then (p i : ℂ) else 0 := by
  by_cases hjk : j = k
  · subst hjk
    rw [matState, unitE, unitE, Matrix.single_mul_single_same, one_mul,
      Matrix.trace_mul_comm, Matrix.trace_single_mul, rhoDiag, Matrix.diagonal_apply]
    by_cases hil : i = l
    · subst hil
      simp
    · simp [hil, Ne.symm hil]
  · rw [matState, unitE, unitE, Matrix.single_mul_single_of_ne (h := hjk), mul_zero, trace_zero]
    simp [hjk]

/-- **The KMS-eigen law, UNCONDITIONAL**: `ω(E_ij·E_kl) = e^{κ_ij}·ω(E_kl·E_ij)` — the carried `hkms` of the
    eigen-core traciality is a THEOREM of the finite corner (from `ρE_ij = e^{κ_ij}E_ijρ`). -/
theorem finiteCorner_kms_E (p : ι → ℝ) (hp : ∀ i, 0 < p i) (i j k l : ι) :
    matState p (unitE i j * unitE k l)
      = (Real.exp (kappaOf p i j) : ℂ) * matState p (unitE k l * unitE i j) := by
  rw [matState_E_mul_E, matState_E_mul_E]
  by_cases hjk : j = k
  · by_cases hil : i = l
    · subst hjk; subst hil
      rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, kappaOf, Real.exp_sub,
        Real.exp_log (hp i), Real.exp_log (hp j)]
      have hpjc : (p j : ℂ) ≠ 0 := by exact_mod_cast (hp j).ne'
      push_cast
      rw [div_mul_cancel₀ _ hpjc]
    · rw [if_neg (fun h => hil h.2), if_neg (fun h => hil (h.1.symm)), mul_zero]
  · rw [if_neg (fun h => hjk h.1), if_neg (fun h => hjk (h.2.symm)), mul_zero]

/-- **Frequency conservation, AUTOMATIC**: at nonzero total frequency both matter factors vanish — the carried
    `hfreq` of the eigen-core traciality is a THEOREM (the matrix-unit index loop forces `κ_ij + κ_ji = 0`). -/
theorem finiteCorner_freq_E (p : ι → ℝ) (i j k l : ι)
    (hfreq : kappaOf p i j + kappaOf p k l ≠ 0) :
    matState p (unitE i j * unitE k l) = 0 ∧ matState p (unitE k l * unitE i j) = 0 := by
  constructor
  · rw [matState_E_mul_E]
    by_cases h : j = k ∧ i = l
    · exfalso
      apply hfreq
      rw [h.1, h.2, kappaOf, kappaOf]
      ring
    · rw [if_neg h]
  · rw [matState_E_mul_E]
    by_cases h : l = i ∧ k = j
    · exfalso
      apply hfreq
      rw [← h.1, ← h.2, kappaOf, kappaOf]
      ring
    · rw [if_neg h]

/-- **Positivity, UNCONDITIONAL**: `ω(A*A) = ∑ p_m‖A_km‖²` is a nonnegative real — the carried `hpos` of the
    eigen-core positivity is a THEOREM of the finite corner. -/
theorem finiteCorner_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (A : Matrix ι ι ℂ) :
    0 ≤ (matState p (star A * A)).re ∧ (matState p (star A * A)).im = 0 := by
  have hterm : ∀ m, ((Matrix.diagonal fun i => (p i : ℂ)) * (star A * A)).diag m
      = ((p m * ∑ k, Complex.normSq (A k m) : ℝ) : ℂ) := by
    intro m
    rw [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.mul_apply]
    rw [show (∑ k, star A m k * A k m) = ∑ k, ((Complex.normSq (A k m) : ℝ) : ℂ) from
      Finset.sum_congr rfl fun k _ => by
        rw [Matrix.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]]
    push_cast
    rw [Finset.mul_sum]
  have hcalc : matState p (star A * A)
      = ∑ m, ((p m * ∑ k, Complex.normSq (A k m) : ℝ) : ℂ) := by
    rw [matState, rhoDiag, Matrix.trace]
    exact Finset.sum_congr rfl fun m _ => hterm m
  rw [hcalc]
  constructor
  · rw [Complex.re_sum]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [Complex.ofReal_re]
    exact mul_nonneg (hp m) (Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
  · rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun m _ => Complex.ofReal_im _

/-! ## The concrete eigen-term family: the trace laws with NO matter hypotheses -/

/-- The finite-corner eigen term `(κ_ij, E_ij, F)`. -/
noncomputable def finiteCornerTerm (p : ι → ℝ) (i j : ι) (F : ExpTest) :
    EigenTerm (Matrix ι ι ℂ) where
  κ := kappaOf p i j
  a := unitE i j
  F := F

/-- **J1 CAPSTONE (traciality) — the constructed trace is TRACIAL on the finite corner, UNCONDITIONALLY:**
    `τ₀(xy) = τ₀(yx)` for all finite-corner eigen terms, with the KMS-eigen law and frequency conservation
    supplied as THEOREMS (`finiteCorner_kms_E`, `finiteCorner_freq_E`) — no matter hypotheses. -/
theorem finiteCorner_tau_trace (p : ι → ℝ) (hp : ∀ i, 0 < p i) (i j k l : ι) (F G : ExpTest) :
    ((finiteCornerTerm p i j F).mul (finiteCornerTerm p k l G)).tau (matState p)
      = ((finiteCornerTerm p k l G).mul (finiteCornerTerm p i j F)).tau (matState p) :=
  eigen_tau_trace (matState p) _ _
    (fun _ => finiteCorner_kms_E p hp i j k l)
    (fun hne => finiteCorner_freq_E p i j k l hne)

/-- **J1 CAPSTONE (positivity) — the constructed trace is POSITIVE on the finite corner, UNCONDITIONALLY:**
    `τ₀(x*x) ≥ 0` with the matter positivity supplied as a THEOREM (`finiteCorner_pos`). -/
theorem finiteCorner_tau_pos (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (i j : ι) (F : ExpTest) :
    0 ≤ (((finiteCornerTerm p i j F).star.mul (finiteCornerTerm p i j F)).tau (matState p)).re
      ∧ (((finiteCornerTerm p i j F).star.mul (finiteCornerTerm p i j F)).tau (matState p)).im
        = 0 :=
  eigen_tau_star_mul_nonneg (matState p) _ (finiteCorner_pos p hp (unitE i j))

end QIQTH.TypeIITrace
