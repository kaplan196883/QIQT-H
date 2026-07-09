/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# A minimal finite-dim quantum-information layer — reduced density matrix + Schmidt rank

M3b (`BellCutRank.lean`) computed the Schmidt rank of a Bell-pair state at the **bipartite-flattening
(coefficient-matrix)** level.  This file supplies the genuine **reduced-density-matrix** formulation
for a pure bipartite finite-dimensional state, and proves the standard bridge that its rank equals the
flattening rank — so M3b's Schmidt rank IS the rank of the reduced density matrix, not merely of the
coefficient matrix.

For a pure bipartite state with coefficient matrix `M : Matrix m n ℂ` (`M i j = ⟨ij|ψ⟩`), the **left
reduced density matrix** is `ρ_A = M Mᴴ` — no general partial-trace machinery is needed for a pure
state: tracing `|ψ⟩⟨ψ|` over the `B` factor gives exactly `M Mᴴ` (`partialTraceRight_pureDensity`).
It is a genuine density matrix: **positive semidefinite** with **trace = ‖ψ‖²** (Frobenius norm
squared), and its **rank is the Schmidt rank**, equal to `rank M` (`Matrix.rank_self_mul_conjTranspose`).

## What is proved (axiom-free)

* `reducedDensityLeft M := M * Mᴴ`; `schmidtRank M := rank ρ_A`.
* `reducedDensityLeft_posSemidef` — `ρ_A` is PSD (a genuine density operator).
* `trace_reducedDensityLeft_eq_frobeniusNormSq` — `tr ρ_A = ‖ψ‖²` (unit-normalized ⟹ trace 1).
* `schmidtRank_eq_flattening_rank` — `schmidtRank M = rank M` (the reduced-density ↔ flattening bridge).
* `partialTraceRight_pureDensity` — for the pure density `|ψ⟩⟨ψ|`, the finite-index partial trace over
  `B` equals `ρ_A = M Mᴴ` (so `reducedDensityLeft` really is the reduced density, not an ansatz).
* `bell_schmidtRank_eq_pow_crossingCard` — M3b, upgraded: the Bell-pair product's reduced-density
  Schmidt rank across the cut is `q^crossingCard G A`.

## Scope firewall (HONEST)

This is the pure-bipartite reduced density matrix (`ρ_A = M Mᴴ`) — the standard, correct finite-dim
object; its rank IS the Schmidt rank.  It does NOT build a general MIXED-state partial-trace API
(`ρ_A = Tr_B ρ` for arbitrary `ρ`, with linearity/CP/tensor bookkeeping) — that remains a larger
Mathlib gap, cited not faked; the pure-state finite-index partial trace suffices here.  Grounds the
metric-from-state area in genuine reduced-density Schmidt rank; NOT continuum geometry, NOT GR, NOT QG.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import QIQTH.BellCutRank

namespace QIQTH.ReducedDensity

open Matrix
open scoped BigOperators ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The left reduced density matrix** of a pure bipartite state with coefficient matrix `M`:
`ρ_A = M Mᴴ`. -/
noncomputable def reducedDensityLeft (M : Matrix m n ℂ) : Matrix m m ℂ := M * Mᴴ

/-- **The Schmidt rank** of a pure bipartite state = rank of its reduced density matrix. -/
noncomputable def schmidtRank (M : Matrix m n ℂ) : ℕ := Matrix.rank (reducedDensityLeft M)

/-- The reduced density matrix is **positive semidefinite** — a genuine density operator. -/
theorem reducedDensityLeft_posSemidef (M : Matrix m n ℂ) :
    (reducedDensityLeft M).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose M

/-- `ρ_A` entrywise: `(M Mᴴ) i i' = ∑_j M i j · conj(M i' j)`. -/
theorem reducedDensityLeft_apply (M : Matrix m n ℂ) (i i' : m) :
    reducedDensityLeft M i i' = ∑ j, M i j * (starRingEnd ℂ) (M i' j) := by
  simp [reducedDensityLeft, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The **squared Frobenius norm** `‖ψ‖² = ∑_{i,j} |M i j|²` of the state. -/
def frobeniusNormSq (M : Matrix m n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

/-- **`tr ρ_A = ‖ψ‖²`** — the reduced density's trace is the state's squared norm (so a unit state
gives a trace-one density matrix). -/
theorem trace_reducedDensityLeft_eq_frobeniusNormSq (M : Matrix m n ℂ) :
    Matrix.trace (reducedDensityLeft M) = (frobeniusNormSq M : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, reducedDensityLeft_apply, frobeniusNormSq]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.mul_conj]

/-- If the state is unit-normalized (`‖ψ‖² = 1`), the reduced density has **trace 1**. -/
theorem trace_reducedDensityLeft_eq_one {M : Matrix m n ℂ} (hM : frobeniusNormSq M = 1) :
    Matrix.trace (reducedDensityLeft M) = 1 := by
  rw [trace_reducedDensityLeft_eq_frobeniusNormSq, hM, Complex.ofReal_one]

/-- **The reduced-density ↔ flattening bridge.**  The Schmidt rank (rank of `ρ_A = M Mᴴ`) equals the
rank of the coefficient matrix `M`.  This is `Matrix.rank_self_mul_conjTranspose` — so M3b's
flattening rank IS the reduced-density Schmidt rank. -/
theorem schmidtRank_eq_flattening_rank (M : Matrix m n ℂ) :
    schmidtRank M = Matrix.rank M := by
  simp only [schmidtRank, reducedDensityLeft]
  exact Matrix.rank_self_mul_conjTranspose M

/-! ### Pure-state finite-index partial trace (justifies `ρ_A = M Mᴴ` as the reduced density) -/

/-- The **pure density matrix** `|ψ⟩⟨ψ|` on `m × n`, from the coefficient matrix `M`. -/
noncomputable def pureDensity (M : Matrix m n ℂ) : Matrix (m × n) (m × n) ℂ :=
  fun p q => M p.1 p.2 * (starRingEnd ℂ) (M q.1 q.2)

/-- The **finite-index partial trace over the `B` (n) factor**: `(Tr_B ρ) i i' = ∑_j ρ (i,j) (i',j)`. -/
noncomputable def partialTraceRight (ρ : Matrix (m × n) (m × n) ℂ) : Matrix m m ℂ :=
  fun i i' => ∑ j, ρ (i, j) (i', j)

/-- **`Tr_B |ψ⟩⟨ψ| = ρ_A`** — the finite-index partial trace of the pure density over `B` is exactly
the left reduced density `M Mᴴ`.  So `reducedDensityLeft` genuinely IS the reduced density matrix, not
an ansatz. -/
theorem partialTraceRight_pureDensity (M : Matrix m n ℂ) :
    partialTraceRight (pureDensity M) = reducedDensityLeft M := by
  ext i i'
  simp [partialTraceRight, pureDensity, reducedDensityLeft_apply]

/-- The Schmidt rank equals the rank of the partial trace of the pure density. -/
theorem schmidtRank_eq_rank_partialTrace (M : Matrix m n ℂ) :
    schmidtRank M = Matrix.rank (partialTraceRight (pureDensity M)) := by
  rw [partialTraceRight_pureDensity, schmidtRank]

/-- **M3b upgraded — the Bell-pair product's REDUCED-DENSITY Schmidt rank across the cut is
`q^crossingCard G A`.**  The Bell flattening is the identity coefficient matrix (`BellCutRank`), so its
reduced density `M Mᴴ` has rank `q^(#crossing edges)` = `q^crossingCard G A`.  The metric-from-state
area is the genuine reduced-density Schmidt rank of an explicit Bell state. -/
theorem bell_schmidtRank_eq_pow_crossingCard (q : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Finset V) (hcard : Fintype.card ι = QIQTH.MetricFromState.crossingCard G A) :
    schmidtRank (QIQTH.BellCutRank.bellFlattening ℂ q ι)
      = q ^ QIQTH.MetricFromState.crossingCard G A := by
  rw [schmidtRank_eq_flattening_rank,
    QIQTH.BellCutRank.rank_bellFlattening_eq_pow_crossingCard ℂ q ι A hcard]

end QIQTH.ReducedDensity
