/-
  G1 (GROUNDING_PLAN.md) — the Bargmann pairing and the creation/annihilation ADJOINTNESS on polynomials.

  Grounds the operator-emergence coherent v-rule as a THEOREM: on the polynomial Bargmann–Fock space the
  pairing `⟨p,q⟩_B = Σ_n n!·conj(p_n)·q_n` makes creation adjoint to annihilation —
  **`bargmann_adjoint`**: `⟨p, X_l·q⟩_B = ⟨∂_l p, q⟩_B` (the factorial identity `(m+e_l)! = m!·(m_l+1)`).
  The coherent layer stays POLYNOMIAL-LEVEL (binding correction — no completed-space/summability claims):
  the coherent coefficient family `α^n/n!` pairs against a polynomial by the REPRODUCING rule
  (`coeffFamilyPair_cohCoeff`: `⟨coh α, p⟩_B = p(conj α)` at the coefficient level) and the creation rule
  **`cohPair_X_mul`**: `⟨coh α, X_l·p⟩ = conj(α_l)·⟨coh α, p⟩` — exactly the v-rule `⟨a†⟩ = conj α` used by
  the Q3 expression layer, now grounded. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.GravitonQuantization

namespace QIQTH.BargmannPairing

open QIQTH.GravitonQuant MvPolynomial

/-- The multi-index factorial `n! = Π_i (n_i)!` (as a complex scalar). -/
noncomputable def multiFact (n : Fin 2 →₀ ℕ) : ℂ := ∏ i, (Nat.factorial (n i) : ℂ)

theorem multiFact_ne_zero (n : Fin 2 →₀ ℕ) : multiFact n ≠ 0 := by
  rw [multiFact]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact_mod_cast Nat.factorial_ne_zero (n i)

theorem conj_multiFact (n : Fin 2 →₀ ℕ) : (starRingEnd ℂ) (multiFact n) = multiFact n := by
  rw [multiFact, map_prod]
  exact Finset.prod_congr rfl fun i _ => map_natCast _ _

/-- The factorial shift identity `(m + e_l)! = m!·(m_l + 1)`. -/
theorem multiFact_add_single (m : Fin 2 →₀ ℕ) (l : Fin 2) :
    multiFact (m + Finsupp.single l 1) = multiFact m * ((m l + 1 : ℕ) : ℂ) := by
  fin_cases l <;>
    · simp only [multiFact, Fin.prod_univ_two, Finsupp.add_apply, Finsupp.single_apply]
      norm_num [Nat.factorial_succ]
      push_cast
      ring

/-- **The Bargmann pairing** `⟨p,q⟩_B = Σ_n n!·conj(p_n)·q_n` (right-support; finite). -/
noncomputable def bargmann (p q : Fock) : ℂ :=
  ∑ n ∈ q.support, multiFact n * (starRingEnd ℂ) (MvPolynomial.coeff n p) * MvPolynomial.coeff n q

/-- The pairing computed over any superset of the right support. -/
theorem bargmann_eq_sum_superset {p q : Fock} {s : Finset (Fin 2 →₀ ℕ)}
    (hs : q.support ⊆ s) :
    bargmann p q
      = ∑ n ∈ s, multiFact n * (starRingEnd ℂ) (MvPolynomial.coeff n p)
          * MvPolynomial.coeff n q := by
  rw [bargmann]
  refine Finset.sum_subset hs fun n _ hn => ?_
  rw [MvPolynomial.notMem_support_iff.mp hn, mul_zero]

theorem bargmann_add_left (p r q : Fock) :
    bargmann (p + r) q = bargmann p q + bargmann r q := by
  rw [bargmann, bargmann, bargmann, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_add, map_add]
  ring

theorem bargmann_add_right (p q r : Fock) :
    bargmann p (q + r) = bargmann p q + bargmann p r := by
  have h1 : (q + r).support ⊆ q.support ∪ r.support := MvPolynomial.support_add
  have h2 : q.support ⊆ q.support ∪ r.support := Finset.subset_union_left
  have h3 : r.support ⊆ q.support ∪ r.support := Finset.subset_union_right
  rw [bargmann_eq_sum_superset h1, bargmann_eq_sum_superset h2, bargmann_eq_sum_superset h3,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem bargmann_conj_symm (p q : Fock) :
    bargmann q p = (starRingEnd ℂ) (bargmann p q) := by
  have h1 : p.support ⊆ p.support ∪ q.support := Finset.subset_union_left
  have h2 : q.support ⊆ p.support ∪ q.support := Finset.subset_union_right
  rw [bargmann_eq_sum_superset h1, bargmann_eq_sum_superset h2, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, conj_multiFact, Complex.conj_conj]
  ring

/-- The pairing of two monomials: diagonal, with weight `m!`. -/
theorem bargmann_monomial_monomial (n m : Fin 2 →₀ ℕ) (a b : ℂ) :
    bargmann (monomial n a) (monomial m b)
      = if n = m then multiFact m * (starRingEnd ℂ) a * b else 0 := by
  rw [bargmann_eq_sum_superset (s := {m}) MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : n = m
  · subst h
    simp
  · rw [if_neg h, if_pos rfl, if_neg h, map_zero, mul_zero, zero_mul]

/-- The monomial×monomial adjointness — the factorial bookkeeping heart. -/
theorem bargmann_adjoint_mm (l : Fin 2) (n m : Fin 2 →₀ ℕ) (a b : ℂ) :
    bargmann (monomial n a) ((MvPolynomial.X l : Fock) * monomial m b)
      = bargmann (MvPolynomial.pderiv l (monomial n a)) (monomial m b) := by
  rw [show (MvPolynomial.X l : Fock) * monomial m b
      = monomial (m + Finsupp.single l 1) b from by
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm],
    MvPolynomial.pderiv_monomial, bargmann_monomial_monomial, bargmann_monomial_monomial]
  by_cases h : n = m + Finsupp.single l 1
  · subst h
    rw [if_pos rfl]
    have hsub : m + Finsupp.single l 1 - Finsupp.single l 1 = m := by
      exact add_tsub_cancel_right _ _
    have hl : ((m + Finsupp.single l 1 : Fin 2 →₀ ℕ)) l = m l + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [if_pos hsub, multiFact_add_single, hl, map_mul, map_natCast]
    push_cast
    ring
  · rw [if_neg h]
    by_cases h2 : n - Finsupp.single l 1 = m
    · have hnl : n l = 0 := by
        by_contra hnl
        apply h
        have hle : Finsupp.single l 1 ≤ n := by
          rw [Finsupp.single_le_iff]
          omega
        rw [← h2, tsub_add_cancel_of_le hle]
      rw [if_pos h2, hnl]
      push_cast
      simp
    · rw [if_neg h2]

private theorem bargmann_adjoint_mr (l : Fin 2) (p : Fock) (m : Fin 2 →₀ ℕ) (b : ℂ) :
    bargmann p ((MvPolynomial.X l : Fock) * monomial m b)
      = bargmann (MvPolynomial.pderiv l p) (monomial m b) := by
  induction p using MvPolynomial.induction_on' with
  | monomial n a => exact bargmann_adjoint_mm l n m a b
  | add p r hp hr => rw [map_add, bargmann_add_left, bargmann_add_left, hp, hr]

/-- **G1 CAPSTONE — creation is ADJOINT to annihilation on polynomials:**
    `⟨p, X_l·q⟩_B = ⟨∂_l p, q⟩_B`. The Bargmann ground of the coherent v-rule. -/
theorem bargmann_adjoint (l : Fin 2) (p q : Fock) :
    bargmann p ((MvPolynomial.X l : Fock) * q)
      = bargmann (MvPolynomial.pderiv l p) q := by
  induction q using MvPolynomial.induction_on' with
  | monomial m b => exact bargmann_adjoint_mr l p m b
  | add q r hq hr => rw [mul_add, bargmann_add_right, bargmann_add_right, hq, hr]

/-! ## The coherent layer (polynomial level — the binding correction) -/

/-- The multi-power `α^n = Π_i α_i^{n_i}`. -/
noncomputable def multiPow (α : Fin 2 → ℂ) (n : Fin 2 →₀ ℕ) : ℂ := ∏ i, α i ^ n i

/-- The coherent state's coefficient family `α^n/n!`. -/
noncomputable def cohCoeff (α : Fin 2 → ℂ) (n : Fin 2 →₀ ℕ) : ℂ := multiPow α n / multiFact n

/-- The Bargmann pairing of a coefficient FAMILY against a polynomial (finite — only `p`'s support
    contributes; the honest polynomial-level avatar of `⟨coh α, p⟩_B`). -/
noncomputable def coeffFamilyPair (c : (Fin 2 →₀ ℕ) → ℂ) (p : Fock) : ℂ :=
  ∑ n ∈ p.support, multiFact n * (starRingEnd ℂ) (c n) * MvPolynomial.coeff n p

/-- The reproducing evaluation `p(conj α)`. -/
noncomputable def cohPair (α : Fin 2 → ℂ) (p : Fock) : ℂ :=
  MvPolynomial.eval (fun i => (starRingEnd ℂ) (α i)) p

/-- **The reproducing rule** — the coherent coefficient family pairs by EVALUATION:
    `⟨coh α, p⟩_B = p(conj α)` (coefficient level, finite). -/
theorem coeffFamilyPair_cohCoeff (α : Fin 2 → ℂ) (p : Fock) :
    coeffFamilyPair (cohCoeff α) p = cohPair α p := by
  rw [coeffFamilyPair, cohPair, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun n _ => ?_
  have hMF := multiFact_ne_zero n
  have hconjPow : (starRingEnd ℂ) (multiPow α n) = ∏ i, ((starRingEnd ℂ) (α i)) ^ n i := by
    rw [multiPow, map_prod]
    exact Finset.prod_congr rfl fun i _ => map_pow _ _ _
  rw [cohCoeff, map_div₀, conj_multiFact, hconjPow]
  field_simp

/-- **The coherent creation rule, GROUNDED**: `⟨coh α, X_l·p⟩ = conj(α_l)·⟨coh α, p⟩` — the v-rule
    `⟨a†_λ⟩_α = conj(α_λ)` of the operator-emergence expression layer, now a theorem (with
    `bargmann_adjoint` supplying the general adjointness it instantiates). -/
theorem cohPair_X_mul (α : Fin 2 → ℂ) (l : Fin 2) (p : Fock) :
    cohPair α ((MvPolynomial.X l : Fock) * p) = (starRingEnd ℂ) (α l) * cohPair α p := by
  rw [cohPair, cohPair, map_mul, MvPolynomial.eval_X]

end QIQTH.BargmannPairing
