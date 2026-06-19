import QIQTH.Entropy.TensorLog
import QIQTH.Entropy.PartialTraceDPI

/-!
# Strong subadditivity of the von Neumann entropy (Carlen §6.6)

The deepest inequality of the family (Lieb–Ruskai 1973): for a three-factor state `ρ` on
`A ⊗ B ⊗ C`,
`S(ρ_AB) + S(ρ_BC) ≥ S(ρ_ABC) + S(ρ_B)`.

It follows from the **monotonicity** of relative entropy under partial trace (`partial_trace_dpi`,
the engine) together with the **relEntropy ↔ entropy decomposition** (`relEntropy_marginals_eq`)
applied to the two bipartitions `(AB)|C` and `B|C`, bridged by the **reindex naturality** of the
relative entropy (`relEntropy_reindex`).

The three subsystems are `A = Fin N` (so the second-factor `partial_trace_dpi` can trace it out
after a regrouping), `B = p`, `C = q`. The state lives on `(A × B) × C`; `rotAssoc` regroups it to
`(B × C) × A` so that tracing the last factor discards `A`. All entrywise marginal-matching
identities reduce to Fubini sum swaps. Axiom-free.
-/

namespace QIQTH.Entropy

open Matrix
open scoped Kronecker ComplexOrder

variable {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- Regroup the three tensor factors `(A × B) × C ≃ (B × C) × A`, moving the first subsystem `A`
to the last position so the second-factor `partial_trace_dpi` traces it out. -/
def rotAssoc (N : ℕ) : (Fin N × p) × q ≃ (p × q) × Fin N where
  toFun x := ((x.1.2, x.2), x.1.1)
  invFun y := ((y.2, y.1.1), y.1.2)
  left_inv := by rintro ⟨⟨i, b⟩, c⟩; rfl
  right_inv := by rintro ⟨⟨b, c⟩, i⟩; rfl

@[simp] lemma rotAssoc_symm_apply (N : ℕ) (b : p) (c : q) (i : Fin N) :
    (rotAssoc (p := p) (q := q) N).symm ((b, c), i) = ((i, b), c) := rfl

variable {N : ℕ}

/-- The `C`-marginal computed via the regrouped `BC`-marginal agrees with the direct `C`-marginal:
`Tr_B (Tr_A ρ) = Tr_{AB} ρ`. (Fubini.) -/
lemma ptL_ptR_rot (ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ) :
    partialTraceLeft (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))
      = partialTraceLeft ρ := by
  ext c c'
  simp only [partialTraceLeft_apply, partialTraceRight_apply, reindex_apply, submatrix_apply,
    rotAssoc_symm_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The `B`-marginal computed via the regrouped `BC`-marginal agrees with `Tr_C (Tr_A...)`:
`Tr_C (Tr_A ρ) = Tr_A (Tr_C ρ)`. (Fubini.) -/
lemma ptR_ptR_rot (ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ) :
    partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))
      = partialTraceLeft (partialTraceRight ρ) := by
  ext b b'
  simp only [partialTraceRight_apply, partialTraceLeft_apply, reindex_apply, submatrix_apply,
    rotAssoc_symm_apply]
  rw [Finset.sum_comm]

/-- The partial trace of the product state `ρ_AB ⊗ ρ_C` over `A` (after regrouping) factors as
`ρ_B ⊗ ρ_C` — the reduced state of the monotonicity step matches the `B|C` decomposition. -/
lemma ptR_rot_kron (ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ) :
    partialTraceRight (reindex (rotAssoc N) (rotAssoc N)
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ))
      = partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))
        ⊗ₖ partialTraceLeft (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)) := by
  rw [ptR_ptR_rot, ptL_ptR_rot]
  ext ⟨b, c⟩ ⟨b', c'⟩
  simp only [partialTraceRight_apply, reindex_apply, submatrix_apply, rotAssoc_symm_apply,
    kronecker_apply, partialTraceRight_apply, partialTraceLeft_apply, Finset.sum_mul]

/-- The von Neumann entropy depends only on the matrix, not the density proof. -/
lemma vonNeumannEntropy_congr {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hd : QIQTH.QuantumEntropy.IsDensity A) (hd' : QIQTH.QuantumEntropy.IsDensity B) (h : A = B) :
    QIQTH.QuantumEntropy.vonNeumannEntropy hd = QIQTH.QuantumEntropy.vonNeumannEntropy hd' := by
  subst h; rfl

/-- **Strong subadditivity of the von Neumann entropy** (Lieb–Ruskai 1973; Carlen §6.6):
for a state `ρ` on `A ⊗ B ⊗ C` (with `A = Fin N`, `B = p`, `C = q`),
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

Here `ρ_AB = Tr_C ρ = partialTraceRight ρ`, and the `BC` and `B` marginals are obtained after the
regrouping `rotAssoc` that moves `A` to the traced position. The proof: `partial_trace_dpi` traces
out `A` to get `D(ρ ‖ ρ_AB⊗ρ_C) ≥ D(ρ_BC ‖ ρ_B⊗ρ_C)`; `relEntropy_marginals_eq` expands both sides;
the `S(ρ_C)` terms cancel by `ptL_ptR_rot`; `linarith` finishes. Axiom-free. -/
theorem strong_subadditivity {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    [Nonempty p] [Nonempty q]
    {ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ} (hρ : ρ.PosDef) (hρ1 : ρ.trace = 1)
    (hdρ : QIQTH.QuantumEntropy.IsDensity ρ)
    (hdAB : QIQTH.QuantumEntropy.IsDensity (partialTraceRight ρ))
    (hdBC : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))
    (hdB : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))) :
    QIQTH.QuantumEntropy.vonNeumannEntropy hdρ
        + QIQTH.QuantumEntropy.vonNeumannEntropy hdB
      ≤ QIQTH.QuantumEntropy.vonNeumannEntropy hdAB
        + QIQTH.QuantumEntropy.vonNeumannEntropy hdBC := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  haveI : Nonempty (Fin N × p) := inferInstance
  -- the regrouped state and its positivity / normalization
  have hρ' : (reindex (rotAssoc N) (rotAssoc N) ρ).PosDef :=
    hρ.submatrix (rotAssoc N).symm.injective
  have hρ'tr : (reindex (rotAssoc N) (rotAssoc N) ρ).trace = 1 := by
    rw [trace_reindex]; exact hρ1
  have hσI : (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ).PosDef :=
    (partialTraceRight_posDef hρ).kronecker (partialTraceLeft_posDef hρ)
  have hρBC : (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)).PosDef :=
    partialTraceRight_posDef hρ'
  have hρBCtr : (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)).trace = 1 := by
    rw [trace_partialTraceRight]; exact hρ'tr
  -- the `C`-marginal densities (these cancel in the end)
  have hdC : QIQTH.QuantumEntropy.IsDensity (partialTraceLeft ρ) :=
    ⟨(partialTraceLeft_posDef hρ).posSemidef, by rw [trace_partialTraceLeft]; exact hρ1⟩
  have hdC' : QIQTH.QuantumEntropy.IsDensity
      (partialTraceLeft (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))) :=
    ⟨(partialTraceLeft_posDef hρBC).posSemidef, by rw [trace_partialTraceLeft]; exact hρBCtr⟩
  have hσ' : (reindex (rotAssoc N) (rotAssoc N)
      (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ)).PosDef :=
    hσI.submatrix (rotAssoc N).symm.injective
  have hκ : (partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))
      ⊗ₖ partialTraceLeft (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ))).PosDef :=
    (partialTraceRight_posDef hρBC).kronecker (partialTraceLeft_posDef hρBC)
  -- the two decompositions (Carlen §6.5 applied to the (AB)|C and B|C bipartitions)
  have hI := relEntropy_marginals_eq hρ hdρ hdAB hdC
  have hII := relEntropy_marginals_eq hρBC hdBC hdB hdC'
  -- monotonicity under tracing out A, bridged to the unrotated state
  have hdpi := partial_trace_dpi hω hρ' hσ'
  rw [relEntropy_reindex (rotAssoc N) hρ hσI hρ'.1 hσ'.1,
    relEntropy_congr (partialTraceRight_posDef hρ').1 hρBC.1
      (partialTraceRight_posDef hσ').1 hκ.1 rfl (ptR_rot_kron ρ)] at hdpi
  rw [hI, hII] at hdpi
  -- the C-marginal entropies coincide
  have hCeq : QIQTH.QuantumEntropy.vonNeumannEntropy hdC'
      = QIQTH.QuantumEntropy.vonNeumannEntropy hdC :=
    vonNeumannEntropy_congr hdC' hdC (ptL_ptR_rot ρ)
  linarith [hdpi, hCeq]

/-- The **quantum conditional mutual information** `I(A : C | B) := S(ρ_AB) + S(ρ_BC) − S(ρ_ABC) − S(ρ_B)`
of a three-party state. The quantity whose non-negativity is the operational content of strong
subadditivity and the cornerstone of the entanglement-entropy / Ryu–Takayanagi calculus. -/
noncomputable def condMutualInfo {N : ℕ}
    {ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ}
    (hdρ : QIQTH.QuantumEntropy.IsDensity ρ)
    (hdAB : QIQTH.QuantumEntropy.IsDensity (partialTraceRight ρ))
    (hdBC : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))
    (hdB : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))) : ℝ :=
  QIQTH.QuantumEntropy.vonNeumannEntropy hdAB + QIQTH.QuantumEntropy.vonNeumannEntropy hdBC
    - QIQTH.QuantumEntropy.vonNeumannEntropy hdρ - QIQTH.QuantumEntropy.vonNeumannEntropy hdB

/-- **Non-negativity of the quantum conditional mutual information** `I(A : C | B) ≥ 0` — the
operational form of strong subadditivity. Equivalently, conditioning never makes `A` and `C` more
correlated than strong subadditivity allows; `= 0` characterizes quantum Markov chains. Axiom-free. -/
theorem condMutualInfo_nonneg {N : ℕ} [NeZero N] {ω : ℂ} (hω : IsPrimitiveRoot ω N)
    [Nonempty p] [Nonempty q]
    {ρ : Matrix ((Fin N × p) × q) ((Fin N × p) × q) ℂ} (hρ : ρ.PosDef) (hρ1 : ρ.trace = 1)
    (hdρ : QIQTH.QuantumEntropy.IsDensity ρ)
    (hdAB : QIQTH.QuantumEntropy.IsDensity (partialTraceRight ρ))
    (hdBC : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))
    (hdB : QIQTH.QuantumEntropy.IsDensity
      (partialTraceRight (partialTraceRight (reindex (rotAssoc N) (rotAssoc N) ρ)))) :
    0 ≤ condMutualInfo hdρ hdAB hdBC hdB := by
  have h := strong_subadditivity hω hρ hρ1 hdρ hdAB hdBC hdB
  unfold condMutualInfo
  linarith

end QIQTH.Entropy


