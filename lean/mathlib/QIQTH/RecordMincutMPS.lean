/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# A CONCRETE tensor-network instance: the min-cut record bound on a 3-layer MPS

This discharges the `FactorsThroughCut` hypothesis of
`QIQTH.RecordMincut.mincut_bounds_distinguishable_records` for a **concrete, non-circular** finite
tensor-network model — so the "capacity is area" record bound applies to a real instance, not just
an assumption.

## The model (matrix-product-state / tensor-train, 3 layers, 2 internal bonds)

A boundary state's flattening across the bipartition `input | output` is the contraction of three
tensors along two internal bonds `e₀` (dimension `d₀`) and `e₁` (dimension `d₁`):

    F  =  R · T · L        (`mps3FlattenMat`),

with `L : Matrix Bond₀ I K`, `T : Matrix Bond₁ Bond₀ K`, `R : Matrix O Bond₁ K`.  The **model datum**
is the local contraction `R·T·L` — the flattening is NOT defined as `r ∘ l`; the two cut
factorizations are DERIVED (by `Matrix.toLin'_mul` + associativity), not assumed:

* through bond `e₀`: `F = (R·T) · L`  factors as  `toLin'(R·T) ∘ toLin' L`  through `Bond₀` (dim `d₀`);
* through bond `e₁`: `F = R · (T·L)`  factors as  `toLin' R ∘ toLin'(T·L)`   through `Bond₁` (dim `d₁`).

Hence the distinguishable-record count is bounded by **each** cut, and by the min-cut it is
`≤ min d₀ d₁` (`mps3_records_le_min`) — the canonical "entanglement across a cut ≤ bond dimension",
with the minimum a genuine minimum over two distinct cuts.

## Scope firewall (HONEST)

This is a finite, explicit, non-circular INSTANCE of the §2.2 record bound — the tensor-network
factorization is now a THEOREM (`mps3_hfac`), not a hypothesis.  It is still NOT a claim that the
physical world is holographic (min-cut = geometric AREA stays Tier-3/OPEN), NOT a continuum limit,
NOT emergent spacetime, NOT QG, NOT numerical-`G`.  It exhibits the record/area bound in a model.
-/
import QIQTH.RecordMincut
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace QIQTH.RecordMincutMPS

open QIQTH.RecordMincut

/-- Two internal bonds `e₀, e₁`. -/
abbrev Edge2 := Fin 2

/-- The bond dimension assignment: `e₀ ↦ d₀`, `e₁ ↦ d₁`. -/
def D2 (d0 d1 : ℕ) : Edge2 → ℕ := fun e => if e = 0 then d0 else d1

/-- The cut through bond `e₀`. -/
def cut0 : Finset Edge2 := {0}
/-- The cut through bond `e₁`. -/
def cut1 : Finset Edge2 := {1}
/-- The two admissible cuts of the bipartition. -/
def cuts2 : Finset (Finset Edge2) := {cut0, cut1}

@[simp] lemma D2_zero (d0 d1 : ℕ) : D2 d0 d1 0 = d0 := by simp [D2]
@[simp] lemma D2_one (d0 d1 : ℕ) : D2 d0 d1 1 = d1 := by simp [D2]

@[simp] lemma cap_cut0 (d0 d1 : ℕ) : cutBondCapacity (D2 d0 d1) cut0 = d0 := by
  simp [cutBondCapacity, cut0]
@[simp] lemma cap_cut1 (d0 d1 : ℕ) : cutBondCapacity (D2 d0 d1) cut1 = d1 := by
  simp [cutBondCapacity, cut1]

/-- The `e₀`-bond index space (dimension `d₀`). -/
abbrev Bond0 (d0 d1 : ℕ) := CutAssignments (D2 d0 d1) cut0
/-- The `e₁`-bond index space (dimension `d₁`). -/
abbrev Bond1 (d0 d1 : ℕ) := CutAssignments (D2 d0 d1) cut1

variable {K : Type*} [Field K] {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {d0 d1 : ℕ}

/-- The 3-layer contraction matrix `R·T·L` (the model datum). -/
noncomputable def mps3FlattenMat
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) : Matrix O I K :=
  R * T * L

/-- The boundary flattening as a linear map `(I → K) →ₗ (O → K)`. -/
noncomputable def mps3Flatten
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) : (I → K) →ₗ[K] (O → K) :=
  Matrix.toLin' (mps3FlattenMat L T R)

/-- **Factorization through the `e₀` cut** — derived, not assumed. -/
lemma mps3_factors_cut0
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) :
    FactorsThroughCut (D2 d0 d1) cut0 (mps3Flatten L T R) := by
  refine ⟨Matrix.toLin' L, Matrix.toLin' (R * T), ?_⟩
  simp only [mps3Flatten, mps3FlattenMat]
  rw [Matrix.toLin'_mul (R * T) L]

/-- **Factorization through the `e₁` cut** — derived, not assumed. -/
lemma mps3_factors_cut1
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) :
    FactorsThroughCut (D2 d0 d1) cut1 (mps3Flatten L T R) := by
  refine ⟨Matrix.toLin' (T * L), Matrix.toLin' R, ?_⟩
  simp only [mps3Flatten, mps3FlattenMat, Matrix.mul_assoc]
  rw [Matrix.toLin'_mul R (T * L)]

/-- **The discharged `hfac`**: the flattening factors through every admissible cut — a THEOREM. -/
lemma mps3_hfac
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) :
    ∀ C ∈ cuts2, FactorsThroughCut (D2 d0 d1) C (mps3Flatten L T R) := by
  intro C hC
  rcases (by simpa [cuts2] using hC : C = cut0 ∨ C = cut1) with rfl | rfl
  · exact mps3_factors_cut0 L T R
  · exact mps3_factors_cut1 L T R

/-- The cut of smaller bond dimension (the min-cut). -/
def chosenCut (d0 d1 : ℕ) : Finset Edge2 := if d0 ≤ d1 then cut0 else cut1

lemma chosenCut_isMinCut (d0 d1 : ℕ) : IsMinCut (D2 d0 d1) cuts2 (chosenCut d0 d1) := by
  by_cases h : d0 ≤ d1
  · refine ⟨by simp [chosenCut, h, cuts2], ?_⟩
    intro C hC
    rcases (by simpa [cuts2] using hC : C = cut0 ∨ C = cut1) with rfl | rfl
    · simp [chosenCut, h]
    · simpa [chosenCut, h] using h
  · have h10 : d1 ≤ d0 := le_of_lt (lt_of_not_ge h)
    refine ⟨by simp [chosenCut, h, cuts2], ?_⟩
    intro C hC
    rcases (by simpa [cuts2] using hC : C = cut0 ∨ C = cut1) with rfl | rfl
    · simpa [chosenCut, h] using h10
    · simp [chosenCut, h]

@[simp] lemma chosenCut_capacity (d0 d1 : ℕ) :
    cutBondCapacity (D2 d0 d1) (chosenCut d0 d1) = min d0 d1 := by
  by_cases h : d0 ≤ d1
  · simp [chosenCut, h, min_eq_left h]
  · have h10 : d1 ≤ d0 := le_of_lt (lt_of_not_ge h)
    simp [chosenCut, h, min_eq_right h10]

/-- **The concrete instance — distinguishable records of a 3-layer MPS ≤ the min bond dimension.**

No `FactorsThroughCut` hypothesis remains: it is discharged by `mps3_hfac`.  The bound `min d₀ d₁`
is a genuine minimum over the two distinct cuts. -/
theorem mps3_records_le_min
    (L : Matrix (Bond0 d0 d1) I K) (T : Matrix (Bond1 d0 d1) (Bond0 d0 d1) K)
    (R : Matrix O (Bond1 d0 d1) K) :
    distinguishableRecords (mps3Flatten L T R) ≤ min d0 d1 := by
  have h := mincut_bounds_distinguishable_records (D2 d0 d1) cuts2 (chosenCut d0 d1)
    (chosenCut_isMinCut d0 d1) (mps3Flatten L T R) (mps3_hfac L T R)
  simpa using h

end QIQTH.RecordMincutMPS
