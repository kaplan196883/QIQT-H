/-
  Relative entropy positivity — Klein's inequality.

  Statement:  D(ρ ‖ σ) ≥ 0,  with equality iff ρ = σ.

  At the Araki / vN level this is Lindblad / Uhlmann, requiring
  operator-convexity of x ↦ −log x.  (Update 2026-06: the former
  `D_nonneg`/`D_eq_zero_iff` AXIOMS are DISCHARGED — this module carries
  no project axioms (std-3 only).  `D_weighted_nonneg` (`:41`) and the
  finite *classical* `KL_classical_nonneg` (`:88`) are full theorems via
  `Real.log` inequalities; quantum nonnegativity is supplied as an explicit
  hypothesis where used, and proved finite-dim in `Entropy/` as
  `QuantumEntropy.relEntropy_nonneg` (Klein).  The continuum / vN-algebra
  Uhlmann case is the cited frontier.)
-/

import QIQTH.Donald
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace RelEntPositivity

open Donald DonaldSystem

variable {State : Type} [DonaldSystem State]

/-! ### Klein's inequality `D(ρ‖σ) ≥ 0` — interface hypothesis, DISCHARGED in finite dimensions.

Formerly two axioms `D_nonneg`/`D_eq_zero_iff_eq` over the opaque `Donald.D`.  At the Araki/vN level
Klein's inequality is Lindblad–Uhlmann (operator convexity of `−log`); over the *uninterpreted* `D` it
cannot be proved, so we no longer assert it as an axiom.  Instead the nonnegativity is carried as an
explicit hypothesis `hD_nonneg` by the few theorems that need it (the "interface-as-hypothesis, not axiom"
pattern), and it is **discharged for the genuine finite-dimensional model**:
`QIQTH.QuantumEntropy.relEntropy_nonneg` proves `D(ρ‖σ) = tr(ρ(log ρ − log σ)) ≥ 0` for concrete
positive-definite density matrices, axiom-free, by the doubly-stochastic/Jensen route (using
`KL_classical_nonneg` below as the Gibbs step).  The equality case `D = 0 ↔ ρ = σ` (former
`D_eq_zero_iff_eq`, used nowhere) is dropped — it is the strict-Jensen refinement, a later milestone. -/

/-- A non-negativity corollary on a weighted sum of relative entropies, given relative-entropy
    nonnegativity `hD_nonneg` (Klein's inequality — discharged for density matrices by
    `QuantumEntropy.relEntropy_nonneg`). -/
theorem D_weighted_nonneg
    {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) (σ : State)
    (hD_nonneg : ∀ ρ' σ' : State, 0 ≤ D ρ' σ') :
    0 ≤ ∑ k ∈ s, p k * D (ρ k) σ := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hp_nn k hk) (hD_nonneg _ _)

/-- Donald's identity rewritten as `D(ρ̄ ‖ σ) ≤ Σ p_k D(ρ_k ‖ σ)` —
    convexity of relative entropy in its first argument (Lindblad,
    classical Gibbs), given Klein nonnegativity `hD_nonneg`. -/
theorem D_convex_in_first_arg
    {ι : Type} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) (σ : State)
    (hD_nonneg : ∀ ρ' σ' : State, 0 ≤ D ρ' σ') :
    D (mixture s p ρ) σ ≤ ∑ k ∈ s, p k * D (ρ k) σ := by
  have hDonald := donald_identity s p ρ σ
  have hHol_nn : 0 ≤ ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) :=
    D_weighted_nonneg s p hp_nn ρ (mixture s p ρ) hD_nonneg
  linarith

/-- **Classical KL non-negativity** — the finite-distribution version
    of Klein's inequality.  Provable from the elementary log inequality
    `log x ≤ x − 1` (i.e. `−log x ≥ 1 − x`).

    For finite probability distributions `p, q : ι → ℝ`:
        KL(p ‖ q)  :=  Σ_i p_i · log(p_i / q_i)  ≥  0.

    We axiomatize at this layer to keep the file small; the proof
    is `Real.log_le_sub_one_of_pos` applied to each term plus
    `Finset.sum_nonneg`. -/
noncomputable def KL {ι : Type*} (s : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * Real.log (p i / q i)

/-- **Klein-style inequality for *finite classical* KL — PROVED** (the
    *full-support* finite Gibbs' inequality: `q` strictly positive on all of `s`,
    the standard hypothesis; the more general support-degenerate form would
    instead require only `p_i > 0 → q_i > 0` with the `0·log(0/q)=0` convention).
    Discharges the former axiom by the elementary log bound
    `Real.log x ≤ x − 1`: termwise `p_i - q_i ≤ p_i·log(p_i/q_i)`, then sum and
    use `∑ p = ∑ q = 1`.  This is the finite-classical shadow of Klein /
    relative-entropy positivity (Open Problem 9 / the information bound behind
    Open Problem 6); the continuum vN-algebraic `D_nonneg` remains analytic
    (operator convexity of `−log`, not in Mathlib). -/
theorem KL_classical_nonneg
    {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hq_pos : ∀ i ∈ s, 0 < q i)
    (hp_sum : ∑ i ∈ s, p i = 1) (hq_sum : ∑ i ∈ s, q i = 1) :
    0 ≤ KL s p q := by
  unfold KL
  have hterm : ∀ i ∈ s, p i - q i ≤ p i * Real.log (p i / q i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp_nn i hi) with hpi | hpi
    · -- p i = 0: term is 0, and p i - q i = -q i ≤ 0
      rw [← hpi]; simp; linarith [hq_pos i hi]
    · -- 0 < p i
      have hqi := hq_pos i hi
      have hx : (0 : ℝ) < q i / p i := div_pos hqi hpi
      have hlog : Real.log (q i / p i) ≤ q i / p i - 1 := Real.log_le_sub_one_of_pos hx
      have hpq : Real.log (p i / q i) = - Real.log (q i / p i) := by
        rw [← Real.log_inv, inv_div]
      have hple : p i * Real.log (q i / p i) ≤ p i * (q i / p i - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
      have heq : p i * (q i / p i - 1) = q i - p i := by field_simp
      rw [hpq, mul_neg]
      linarith [hple, heq]
  calc (0 : ℝ) = ∑ i ∈ s, (p i - q i) := by
        rw [Finset.sum_sub_distrib, hp_sum, hq_sum]; ring
    _ ≤ ∑ i ∈ s, p i * Real.log (p i / q i) := Finset.sum_le_sum hterm

end RelEntPositivity
end QIQTH
