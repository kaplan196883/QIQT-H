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

/-- The **`a`-slice vector** `w_a (k,b) = [b = a] v_k` — `v` placed on the `a`-fibre of the second
factor, zero elsewhere. The partial-trace quadratic form decomposes as a sum of `ρ`'s quadratic forms
over these. -/
def sliceVec (v : n → ℂ) (a : m) : (n × m) → ℂ := fun p => if p.2 = a then v p.1 else 0

/-- A slice vector of a nonzero `v` is nonzero (its `a`-fibre carries `v`). -/
lemma sliceVec_ne_zero {v : n → ℂ} (hv : v ≠ 0) (a : m) : sliceVec v a ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  refine Function.ne_iff.mpr ⟨(k, a), ?_⟩
  simpa [sliceVec] using hk

/-- **The partial-trace quadratic-form decomposition.** `⟨v, (Tr₂ρ) v⟩ = Σ_a ⟨w_a, ρ w_a⟩` with `w_a`
the `a`-slice of `v`. This is the heart of both the positivity statements: the partial-trace quadratic
form is a sum of `ρ`'s quadratic forms over the fibres. -/
theorem partialTraceRight_quadForm (ρ : Matrix (n × m) (n × m) ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (partialTraceRight ρ *ᵥ v)
      = ∑ a : m, star (sliceVec v a) ⬝ᵥ (ρ *ᵥ (sliceVec v a)) := by
  have term : ∀ a : m, star (sliceVec v a) ⬝ᵥ (ρ *ᵥ (sliceVec v a))
      = ∑ i, ∑ j, star (v i) * (ρ (i, a) (j, a) * v j) := by
    intro a
    simp only [dotProduct, mulVec, sliceVec, Pi.star_apply, Fintype.sum_prod_type,
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
  rw [lhs_eq, Finset.sum_congr rfl (fun a _ => term a),
    show (∑ i, ∑ j, ∑ a, star (v i) * (ρ (i, a) (j, a) * v j))
        = ∑ i, ∑ a, ∑ j, star (v i) * (ρ (i, a) (j, a) * v j) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  exact Finset.sum_comm

/-- **The partial trace is positivity-preserving** (Carlen Thm 5.6): `ρ ≥ 0 ⟹ Tr₂ ρ ≥ 0`. The
quadratic form is a sum (over the fibres) of the nonnegative quadratic forms of `ρ`. -/
theorem partialTraceRight_posSemidef {ρ : Matrix (n × m) (n × m) ℂ} (hρ : ρ.PosSemidef) :
    (partialTraceRight ρ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (partialTraceRight_isHermitian hρ.1)
    (fun v => ?_)
  rw [partialTraceRight_quadForm]
  exact Finset.sum_nonneg (fun a _ => hρ.dotProduct_mulVec_nonneg (sliceVec v a))

/-- **The partial trace preserves strict positivity** (over a nonempty traced-out factor): `ρ > 0 ⟹
Tr₂ ρ > 0`. Needed because the Umegaki relative entropy `D(·‖·)` is defined for positive-definite
states — so partial-trace data processing `D(Tr₂ρ ‖ Tr₂σ) ≤ D(ρ‖σ)` requires `Tr₂` to land in
`PosDef`. For `v ≠ 0` every slice `w_a ≠ 0`, so every summand `⟨w_a, ρ w_a⟩ > 0`. -/
theorem partialTraceRight_posDef [Nonempty m] {ρ : Matrix (n × m) (n × m) ℂ} (hρ : ρ.PosDef) :
    (partialTraceRight ρ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (partialTraceRight_isHermitian hρ.1)
    (fun v hv => ?_)
  rw [partialTraceRight_quadForm]
  exact Finset.sum_pos (fun a _ => hρ.dotProduct_mulVec_pos (sliceVec_ne_zero hv a))
    Finset.univ_nonempty

end QIQTH.Entropy
