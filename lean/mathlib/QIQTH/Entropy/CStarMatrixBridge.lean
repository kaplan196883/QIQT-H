/-
  Bridge: harvesting Mathlib's operator-convexity machinery for our matrix entropy stack.

  Mathlib proves Löwner–Heinz (`CFC.concaveOn_rpow`, `CFC.monotone_rpow`, `CFC.rpow_le_rpow`,
  `CFC.concaveOn_sqrt`, …) on a `NonUnitalCStarAlgebra`.  Our entropy stack lives on the
  Frobenius-normed `Matrix n n ℂ`, which is *not* wired as a `CStarAlgebra` (only `CStarRing` is
  scoped, under `Matrix.Norms.L2Operator`; the full instance has a norm diamond / `CompleteSpace`
  gap — empirically `CStarAlgebra (Matrix n n ℂ)` does not synthesize).  Mathlib's clean carrier for
  the C⋆-structure is the type synonym **`CStarMatrix n n ℂ`** (operator norm, full `CStarAlgebra`).

  This file builds the bridge across the bundled `*`-algebra equivalence
  `CStarMatrix.ofMatrixStarAlgEquiv : Matrix n n ℂ ≃⋆ₐ[ℂ] CStarMatrix n n ℂ`.

  **Order coincidence (this increment).**  A `StarRingEquiv` between `StarOrderedRing`s is
  automatically an `OrderIsoClass` (`StarRingEquivClass.instOrderIsoClass`).  `Matrix n n ℂ` (Loewner
  order, scoped `MatrixOrder`) and `CStarMatrix n n ℂ` (spectral order) are both `StarOrderedRing`s,
  so `ofMatrixStarAlgEquiv` is an order iso and the two orders coincide — for free, no continuous
  functional calculus required.

  **Status of the rpow transport.**  The original aim was to transport Mathlib's `CFC.concaveOn_rpow`
  (operator concavity of `Aᵖ`) back to `Matrix`.  That is currently *blocked*: although
  `CStarMatrix n n ℂ` is declared a `CStarAlgebra`, its downstream CFC instance stack does NOT fire
  out of the box — `FiniteDimensional ℂ (CStarMatrix n n ℂ)` is missing (manufacturable, and it
  cascades to `CompleteSpace`), but the `ℝ`/`ℂ`/`ℝ≥0` continuous functional calculi, `NonnegSpectrumClass`,
  and hence the `HPow _ ℝ` (`rpow`) notation still fail to synthesize on the concrete synonym.  Closing
  that is a Mathlib-infrastructure project (arguably an upstream contribution) of uncertain depth.
  *Crucially it is not on the critical path:* Carlen's Ando route to the operator geometric mean (→
  Lieb's concavity) uses the **Schur-complement variational characterization** (already in hand:
  `fromBlocks_star_inv_posSemidef`, `star_inv_le_of_fromBlocks_posSemidef`) together with the
  **matrix square root** (`CFC.sqrt`, which *does* work natively on `Matrix`), so the rpow transport is
  not needed for the DPI/Lieb tower.  The order coincidence below is retained as an independently useful
  tool for moving order facts across the synonym.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

namespace QIQTH.Entropy

open Matrix CStarMatrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

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

end QIQTH.Entropy
