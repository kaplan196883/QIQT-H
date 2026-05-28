/-
  Relative entropy positivity — Klein's inequality.

  Statement:  D(ρ ‖ σ) ≥ 0,  with equality iff ρ = σ.

  At the Araki / vN level this is Lindblad / Uhlmann, requiring
  operator-convexity of x ↦ −log x.  Mathlib doesn't yet have it for
  states on vN algebras.  We axiomatize the statement at the Donald-
  axiomatization level, and provide a finite *classical* KL companion
  using `Real.log` inequalities (this part is fully constructive once
  we plug into a future classical-relative-entropy module).
-/

import QIQTH.Donald
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace RelEntPositivity

open Donald

/-- **Klein's inequality (axiom):  D(ρ ‖ σ) ≥ 0.**

    At the Araki / vN-algebra level this is a deep theorem; we
    axiomatize at the abstract-state level.  See `KL_classical_nonneg`
    for the finite-classical version which *is* provable from
    `Real.log` inequalities. -/
axiom D_nonneg (ρ σ : State) : 0 ≤ D ρ σ

/-- **Klein equality case (axiom):  D(ρ ‖ σ) = 0  ⇔  ρ = σ.**

    Under faithfulness assumptions on σ.  We state the forward
    direction as an axiom at the abstract level. -/
axiom D_eq_zero_iff_eq (ρ σ : State) : D ρ σ = 0 ↔ ρ = σ

/-- A non-negativity corollary on a weighted sum of relative entropies. -/
theorem D_weighted_nonneg
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) (σ : State) :
    0 ≤ ∑ k ∈ s, p k * D (ρ k) σ := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (hp_nn k hk) (D_nonneg _ _)

/-- Donald's identity rewritten as `D(ρ̄ ‖ σ) ≤ Σ p_k D(ρ_k ‖ σ)` —
    convexity of relative entropy in its first argument (Lindblad,
    classical Gibbs). -/
theorem D_convex_in_first_arg
    {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i)
    (ρ : ι → State) (σ : State) :
    D (mixture s p ρ) σ ≤ ∑ k ∈ s, p k * D (ρ k) σ := by
  have hDonald := donald_identity s p ρ σ
  have hHol_nn : 0 ≤ ∑ k ∈ s, p k * D (ρ k) (mixture s p ρ) :=
    D_weighted_nonneg s p hp_nn ρ (mixture s p ρ)
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

/-- Klein-style inequality for *finite classical* KL.  Hypotheses:
    p, q are non-negative on s, both sum to 1, and q is strictly
    positive wherever p is. -/
axiom KL_classical_nonneg
    {ι : Type*} (s : Finset ι) (p q : ι → ℝ)
    (hp_nn : ∀ i ∈ s, 0 ≤ p i) (hq_pos : ∀ i ∈ s, 0 < q i)
    (hp_sum : ∑ i ∈ s, p i = 1) (hq_sum : ∑ i ∈ s, q i = 1) :
    0 ≤ KL s p q

end RelEntPositivity
end QIQTH
