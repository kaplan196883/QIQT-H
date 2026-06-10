/-
  Bridge: harvesting Mathlib's operator-convexity machinery for our matrix entropy stack.

  Mathlib proves Löwner–Heinz (`CFC.concaveOn_rpow`, `CFC.monotone_rpow`, `CFC.rpow_le_rpow`,
  `CFC.sqrt_le_sqrt`, `CFC.concaveOn_sqrt`, …) on a (non-unital) `CStarAlgebra`.  Our entropy stack
  lives on the Frobenius-normed `Matrix n n ℂ`, which is *not* wired as a `CStarAlgebra` (only
  `CStarRing` is scoped, under `Matrix.Norms.L2Operator`; the full instance has a norm diamond —
  empirically `CStarAlgebra (Matrix n n ℂ)` does not synthesize).  Mathlib's clean carrier for the
  C⋆-structure is the type synonym **`CStarMatrix n n ℂ`** (operator norm, full `CStarAlgebra`).

  This file builds the bridge across the bundled `*`-algebra equivalence
  `CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ`, in three layers:

  1. **Filling the `CStarMatrix` instance gap.**  Although `CStarMatrix n n ℂ` is a `CStarAlgebra`, its
     downstream continuous-functional-calculus instances do not fire out of the box: `FiniteDimensional`
     is missing, and the *real* CFC (`ContinuousFunctionalCalculus ℝ … IsSelfAdjoint`) and
     `NonnegSpectrumClass ℝ` fail to synthesize even though the *complex* CFC works.  We supply the three
     missing instances explicitly (the `FiniteDimensional` cascades to `CompleteSpace`; the real CFC and
     `NonnegSpectrumClass` are Mathlib's own instance bodies, forced through by name).  With these, the
     **entire Löwner–Heinz toolkit fires on `CStarMatrix n n ℂ`** (`sqrt_le_sqrt`, `rpow_le_rpow`,
     `concaveOn_rpow`, `concaveOn_sqrt`).

  2. **Order coincidence.**  A `StarRingEquiv` between `StarOrderedRing`s is automatically an
     `OrderIsoClass` (`StarRingEquivClass.instOrderIsoClass`).  `Matrix n n ℂ` (Loewner order, scoped
     `MatrixOrder`) and `CStarMatrix n n ℂ` (spectral order) are both `StarOrderedRing`s, so
     `ofMatrixStarAlgEquiv` is an order iso: `e A ≤ e B ↔ A ≤ B`.

  3. **CFC naturality.**  `e (cfc f A) = cfc f (e A)` (`StarAlgHomClass.map_cfc`, continuity from
     `ofMatrixL`).  Together with (2) this transports any operator-monotone / -concave fact proved on
     `CStarMatrix` back to `Matrix` — the engine for the geometric-mean / Lieb tower.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Layer 1 — the missing `CStarMatrix` CFC instances

These fill a genuine gap: `CStarMatrix n n ℂ` is declared a `CStarAlgebra` but its real-CFC instance
chain does not auto-synthesize.  All three are the canonical derivations (the `FiniteDimensional` is
transported along the linear equiv; the real CFC and `NonnegSpectrumClass` are Mathlib's own instance
bodies for a unital `CStarAlgebra`, referenced by name to bypass the failing search). -/

/-- `CStarMatrix n n ℂ` is finite-dimensional (transported along `ofMatrixₗ`).  Cascades to
    `CompleteSpace`, which the CFC instances need. -/
noncomputable instance instFiniteDimensionalCStarMatrix :
    FiniteDimensional ℂ (CStarMatrix n n ℂ) :=
  FiniteDimensional.of_injective (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
    (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.injective

/-- The **real** continuous functional calculus on `CStarMatrix n n ℂ` (restriction of the complex
    CFC to self-adjoint elements).  Mathlib's `IsSelfAdjoint.instContinuousFunctionalCalculus` body,
    forced through by name. -/
noncomputable instance instCFCRealCStarMatrix :
    ContinuousFunctionalCalculus ℝ (CStarMatrix n n ℂ) IsSelfAdjoint :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

/-- `NonnegSpectrumClass ℝ (CStarMatrix n n ℂ)` (Mathlib's `CStarAlgebra.instNonnegSpectrumClass`,
    by name). -/
noncomputable instance instNonnegSpectrumClassCStarMatrix :
    NonnegSpectrumClass ℝ (CStarMatrix n n ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

/-! ### Layer 2 — order coincidence -/

/-- **Order coincidence (Loewner order).**  The bundled `*`-algebra equivalence is an order
    isomorphism, so `e A ≤ e B ↔ A ≤ B`. -/
lemma ofMatrix_le_iff {A B : Matrix n n ℂ} :
    ofMatrixStarAlgEquiv A ≤ ofMatrixStarAlgEquiv B ↔ A ≤ B :=
  map_le_map_iff (ofMatrixStarAlgEquiv (A := ℂ) (n := n))

/-- **Order coincidence (positivity).**  Under the bundled `*`-algebra equivalence the abstract
    `CStarMatrix` order agrees with the Loewner `PosSemidef` order on `Matrix`. -/
lemma ofMatrix_nonneg_iff {A : Matrix n n ℂ} :
    0 ≤ ofMatrixStarAlgEquiv A ↔ A.PosSemidef := by
  rw [← map_zero (ofMatrixStarAlgEquiv (A := ℂ) (n := n)), ofMatrix_le_iff, nonneg_iff_posSemidef]

/-! ### Layer 3 — CFC naturality (the transport engine) -/

/-- **CFC naturality across the bridge.**  `e (cfc f A) = cfc f (e A)` for self-adjoint `A` and `f`
    continuous on the spectrum — `StarAlgHomClass.map_cfc`, with continuity of `e` from `ofMatrixL`.
    This transports operator-monotone / -concave facts from `CStarMatrix` (where the full Löwner–Heinz
    toolkit fires) back to `Matrix`. -/
lemma ofMatrix_cfc (f : ℝ → ℝ) (A : Matrix n n ℂ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    ofMatrixStarAlgEquiv (cfc f A) = cfc f (ofMatrixStarAlgEquiv A) :=
  StarAlgHomClass.map_cfc ofMatrixStarAlgEquiv f A hf
    (ofMatrixL (A := ℂ) (m := n) (n := n)).continuous hA

end QIQTH.Entropy
