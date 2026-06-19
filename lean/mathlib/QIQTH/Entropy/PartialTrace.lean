import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.BigOperators

/-!
# Partial trace and its trace/positivity preservation (Carlen Thm 5.6)

Toward **fully general CPTP data processing** (beyond the mixed-unitary class already covered by
`QIQTH.Entropy.dpi_mixed_unitary`), the key channel is the **partial trace** `Tr₂ : Matrix (n×m) → Matrix n`,
`(Tr₂ ρ)_{ij} = Σ_a ρ_{(i,a)(j,a)}` (Carlen, *Trace Inequalities and Quantum Entropy*, Def. 5.5 / eq. 5.25).
Carlen's route to partial-trace DPI (§5.7) realizes the conditional expectation
`ρ ↦ (Tr₂ ρ) ⊗ (I_m/m)` as a **mixed-unitary channel** — averaging `(I_n ⊗ W_k) ρ (I_n ⊗ W_k)⋆` over the
discrete Weyl (clock–shift) unitaries, a unitary 1-design — so that `dpi_mixed_unitary` then yields
`D(Tr₂ρ ‖ Tr₂σ) ≤ D(ρ‖σ)`.

This file supplies the **foundational, reusable** first brick of that program: the partial trace itself and
its two defining structural properties (Carlen Thm 5.6) — it is **trace-preserving** and
**positivity-preserving** (hence Hermitian-preserving) — all axiom-free. The discrete-Weyl 1-design and the
DPI assembly are the subsequent increments.
-/

namespace QIQTH.Entropy

open Matrix
open scoped ComplexOrder

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Partial trace over the second tensor factor.** For `ρ : Matrix (n × m) (n × m) ℂ`, the partial
trace `Tr₂ ρ : Matrix n n ℂ` is `(Tr₂ ρ)_{ij} = Σ_a ρ_{(i,a)(j,a)}` (Carlen Def. 5.5). -/
noncomputable def partialTraceRight (ρ : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  fun i j => ∑ a, ρ (i, a) (j, a)

@[simp] lemma partialTraceRight_apply (ρ : Matrix (n × m) (n × m) ℂ) (i j : n) :
    partialTraceRight ρ i j = ∑ a, ρ (i, a) (j, a) := rfl

/-- **The partial trace is trace-preserving** (Carlen Thm 5.6): `Tr(Tr₂ ρ) = Tr ρ`. -/
theorem trace_partialTraceRight (ρ : Matrix (n × m) (n × m) ℂ) :
    (partialTraceRight ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fintype.sum_prod_type]
  rfl

/-- **The partial trace preserves the Hermitian property.** -/
theorem partialTraceRight_isHermitian {ρ : Matrix (n × m) (n × m) ℂ} (hρ : ρ.IsHermitian) :
    (partialTraceRight ρ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, partialTraceRight_apply, star_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact hρ.apply (i, a) (j, a)

/-- **The partial trace is positivity-preserving** (Carlen Thm 5.6): `ρ ≥ 0 ⟹ Tr₂ ρ ≥ 0`. For any
`v : n → ℂ`, `⟨v, (Tr₂ρ) v⟩ = Σ_a ⟨w_a, ρ w_a⟩` with `w_a` the vector supported on the `a`-slice of the
second factor (`w_a(k,b) = [b=a] v_k`), so the quadratic form is a sum of the nonnegative quadratic forms
of `ρ`. -/
theorem partialTraceRight_posSemidef {ρ : Matrix (n × m) (n × m) ℂ} (hρ : ρ.PosSemidef) :
    (partialTraceRight ρ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (partialTraceRight_isHermitian hρ.1)
    (fun v => ?_)
  -- the slice vectors `w_a (k,b) = [b = a] v_k`
  set w : m → (n × m) → ℂ := fun a p => if p.2 = a then v p.1 else 0 with hw
  -- the quadratic form of `ρ` on `w a` is the `a`-summand of the partial-trace quadratic form
  have term : ∀ a : m, star (w a) ⬝ᵥ (ρ *ᵥ (w a))
      = ∑ i, ∑ j, star (v i) * (ρ (i, a) (j, a) * v j) := by
    intro a
    simp only [dotProduct, mulVec, hw, Pi.star_apply, Fintype.sum_prod_type,
      apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero, ite_mul, zero_mul, Finset.mul_sum,
      Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- LHS in canonical `∑ i ∑ j ∑ a` order, by hand (avoids simp's variable reshuffle)
  have lhs_eq : star v ⬝ᵥ (partialTraceRight ρ *ᵥ v)
      = ∑ i, ∑ j, ∑ a, star (v i) * (ρ (i, a) (j, a) * v j) := by
    simp only [dotProduct, mulVec, partialTraceRight_apply, Pi.star_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
  have rhs_eq : (∑ a : m, star (w a) ⬝ᵥ (ρ *ᵥ (w a)))
      = ∑ a, ∑ i, ∑ j, star (v i) * (ρ (i, a) (j, a) * v j) :=
    Finset.sum_congr rfl (fun a _ => term a)
  have key : star v ⬝ᵥ (partialTraceRight ρ *ᵥ v) = ∑ a : m, star (w a) ⬝ᵥ (ρ *ᵥ (w a)) := by
    rw [lhs_eq, rhs_eq,
      show (∑ i, ∑ j, ∑ a, star (v i) * (ρ (i, a) (j, a) * v j))
          = ∑ i, ∑ a, ∑ j, star (v i) * (ρ (i, a) (j, a) * v j) from
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    exact Finset.sum_comm
  rw [key]
  exact Finset.sum_nonneg (fun a _ => hρ.dotProduct_mulVec_nonneg (w a))

end QIQTH.Entropy
