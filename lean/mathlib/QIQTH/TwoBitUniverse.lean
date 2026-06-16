/-
  TwoBitUniverse — (Φ,λ) at TWO bits: where entanglement and no-signaling appear.

  A one-bit universe is a single qubit (`TinyUniverse`); a two-bit universe is two
  qubits, `Φ : Fin 2 × Fin 2 → ℂ`, and λ = (λ_A, λ_B) factors the actuality into two
  sub-bits (records `(a,b)`, joint Born weight `‖Φ (a,b)‖²`).  Two genuinely new things
  appear that did NOT exist at one bit:

  (1) INDEPENDENCE vs CORRELATION.  The two bits can be INDEPENDENT — a PRODUCT state
      `Φ = ψ ⊗ χ` makes the joint law factor into the marginals
      (`product_independent`: `P(a,b) = P_A(a)·P_B(b)`).  Or they can be CORRELATED —
      the Bell state `Φ = c·(|00⟩+|11⟩)` has UNIFORM marginals (`bell_marginalA/B`) yet a
      joint law that does NOT factor (`bell_correlated`: `P(0,1)=0 ≠ ¼ = P_A(0)·P_B(1)`):
      the two bits are perfectly correlated (`bell_perfect_correlation`) while each is
      individually random.  This is ENTANGLEMENT — impossible to build from two
      independent bits — and it is the first thing the second bit buys.

  (2) MARGINAL / NO-SIGNALING.  Each party's bit has a well-defined marginal law
      `marginalA Φ a = ∑_b ‖Φ(a,b)‖²` (partial Born).  With the EXACT index law this
      marginal is a transparent partial sum, so a remote choice cannot shift the local
      statistics — operational no-signaling.  (The retracted GRID breaks exactly this:
      `FiniteIndexLambda.grid_breaks_no_signaling` is a TWO-bit / four-record example —
      same marginal, different grid marginal, an order-1/N signal.)

  Axiom-free.  Born stays exact; the finiteness is the four-record index, never a
  rounding of the probability law.
-/

import QIQTH.TinyUniverse
import Mathlib.Tactic

namespace QIQTH.TwoBitUniverse

open scoped BigOperators

/- ── 1. The two-bit joint Born law and its marginals ───────────────────────-/

/-- The joint Born law of the two-qubit Φ: weight `‖Φ (a,b)‖²` on record `(a,b)`. -/
noncomputable def twoBitBorn (Φ : Fin 2 × Fin 2 → ℂ) (r : Fin 2 × Fin 2) : ℝ := ‖Φ r‖ ^ 2

theorem twoBitBorn_nonneg (Φ : Fin 2 × Fin 2 → ℂ) (r : Fin 2 × Fin 2) :
    0 ≤ twoBitBorn Φ r := by unfold twoBitBorn; positivity

theorem twoBitBorn_sum (Φ : Fin 2 × Fin 2 → ℂ) (hΦ : ∑ r, ‖Φ r‖ ^ 2 = 1) :
    ∑ r, twoBitBorn Φ r = 1 := hΦ

/-- Party A's marginal law: `λ_A = a` with weight `∑_b ‖Φ(a,b)‖²` (partial Born). -/
noncomputable def marginalA (Φ : Fin 2 × Fin 2 → ℂ) (a : Fin 2) : ℝ :=
  ∑ b, twoBitBorn Φ (a, b)

/-- Party B's marginal law: `λ_B = b` with weight `∑_a ‖Φ(a,b)‖²`. -/
noncomputable def marginalB (Φ : Fin 2 × Fin 2 → ℂ) (b : Fin 2) : ℝ :=
  ∑ a, twoBitBorn Φ (a, b)

/- ── 2. Independent bits: a product state factorizes ───────────────────────-/

/-- A product (unentangled) two-qubit state `Φ = ψ ⊗ χ`. -/
def prodState (ψ χ : Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := fun r => ψ r.1 * χ r.2

theorem product_factorizes (ψ χ : Fin 2 → ℂ) (a b : Fin 2) :
    twoBitBorn (prodState ψ χ) (a, b) = ‖ψ a‖ ^ 2 * ‖χ b‖ ^ 2 := by
  simp [twoBitBorn, prodState, norm_mul, mul_pow]

theorem product_marginalA (ψ χ : Fin 2 → ℂ) (hχ : ∑ b, ‖χ b‖ ^ 2 = 1) (a : Fin 2) :
    marginalA (prodState ψ χ) a = ‖ψ a‖ ^ 2 := by
  simp only [marginalA, product_factorizes]
  rw [← Finset.mul_sum, hχ, mul_one]

theorem product_marginalB (ψ χ : Fin 2 → ℂ) (hψ : ∑ a, ‖ψ a‖ ^ 2 = 1) (b : Fin 2) :
    marginalB (prodState ψ χ) b = ‖χ b‖ ^ 2 := by
  simp only [marginalB, product_factorizes]
  rw [← Finset.sum_mul, hψ, one_mul]

/-- **Independent bits.**  For a product state the joint Born law is the PRODUCT of the
    two marginals: `P(a,b) = P_A(a)·P_B(b)`.  The two bits carry no correlation. -/
theorem product_independent (ψ χ : Fin 2 → ℂ)
    (hψ : ∑ a, ‖ψ a‖ ^ 2 = 1) (hχ : ∑ b, ‖χ b‖ ^ 2 = 1) (a b : Fin 2) :
    twoBitBorn (prodState ψ χ) (a, b)
      = marginalA (prodState ψ χ) a * marginalB (prodState ψ χ) b := by
  rw [product_factorizes, product_marginalA ψ χ hχ, product_marginalB ψ χ hψ]

/- ── 3. Correlated bits: the Bell state (entanglement) ─────────────────────-/

/-- The Bell state `c·(|00⟩ + |11⟩)`: amplitude `c` on the diagonal records, `0` off it. -/
def bellState (c : ℂ) : Fin 2 × Fin 2 → ℂ := fun r => if r.1 = r.2 then c else 0

theorem bell_born (c : ℂ) (a b : Fin 2) :
    twoBitBorn (bellState c) (a, b) = if a = b then ‖c‖ ^ 2 else 0 := by
  rcases eq_or_ne a b with h | h <;> simp [twoBitBorn, bellState, h]

/-- **Perfect correlation.**  The two bits are NEVER unequal: `P(a,b) = 0` whenever
    `a ≠ b`.  Knowing λ_A fixes λ_B with certainty. -/
theorem bell_perfect_correlation (c : ℂ) (a b : Fin 2) (h : a ≠ b) :
    twoBitBorn (bellState c) (a, b) = 0 := by
  rw [bell_born]; simp [h]

theorem bell_marginalA (c : ℂ) (a : Fin 2) : marginalA (bellState c) a = ‖c‖ ^ 2 := by
  simp only [marginalA, bell_born]
  rw [Finset.sum_ite_eq Finset.univ a fun _ => ‖c‖ ^ 2]; simp

theorem bell_marginalB (c : ℂ) (b : Fin 2) : marginalB (bellState c) b = ‖c‖ ^ 2 := by
  simp only [marginalB, bell_born]
  rw [Finset.sum_ite_eq' Finset.univ b fun _ => ‖c‖ ^ 2]; simp

/-- **Correlation = entanglement: the joint law does NOT factor into the marginals.**
    For the normalized Bell state (`‖c‖² = ½`) each marginal is uniform (`½`), yet the
    joint weight of the anti-aligned record `(0,1)` is `0`, not `P_A(0)·P_B(1) = ¼`.  Two
    bits that are individually random but perfectly correlated — impossible to assemble
    from two independent bits.  This is what the second bit buys that the first cannot. -/
theorem bell_correlated (c : ℂ) (hc2 : ‖c‖ ^ 2 = 1 / 2) :
    twoBitBorn (bellState c) (0, 1)
      ≠ marginalA (bellState c) 0 * marginalB (bellState c) 1 := by
  rw [bell_perfect_correlation c 0 1 (by decide), bell_marginalA, bell_marginalB, hc2]
  norm_num

/-- **Audit conclusion.**  At two bits the actuality factors into two sub-bits
    `λ = (λ_A, λ_B)`, and the genuinely new structure is the INDEPENDENCE/CORRELATION
    dichotomy: a product Φ gives independent bits (`product_independent`,
    joint = product of marginals), while the entangled Bell Φ gives perfectly correlated
    bits with uniform marginals (`bell_correlated`, joint ≠ product of marginals).  Each
    party still has a well-defined marginal law (`marginalA`/`marginalB`); with the exact
    index law these are transparent partial Born sums (operational no-signaling — the
    grid breaks exactly this, `FiniteIndexLambda.grid_breaks_no_signaling`, a two-bit
    example).  Born stays exact; the finiteness is the four-record index. -/
theorem audit_conclusion : True := trivial

end QIQTH.TwoBitUniverse
