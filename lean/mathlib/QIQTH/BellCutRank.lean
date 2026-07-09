/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# M3b — the QUANTUM realization: Bell-pair Schmidt rank = `q^(area)`

The combinatorial metric-from-state layer (`MetricFromState.lean`, M1–M5) uses the edge-crossing count
`crossingCard G A` as the "area" of a cut.  This file grounds that area in **genuine entanglement**: an
explicit product of Bell pairs — one `q`-dimensional maximally-entangled pair per crossing edge — has
**Schmidt rank `q^(#crossing edges)` across the cut**, computed as the rank of its bipartite
coefficient (flattening) matrix.

The unnormalized Bell-product state across a cut with crossing-edge type `ι` and local alphabet
`Fin q` is `∑_{x : ι → Fin q} |x⟩_A ⊗ |x⟩_{Aᶜ}` — its A-side/Aᶜ-side coefficient matrix is the
**identity** on assignments `ι → Fin q`, whose rank is `card (ι → Fin q) = q^(card ι)`.  Non-crossing
Bell pairs are product factors across the cut and do not change the Schmidt rank, so `ι` = the crossing
edges suffices.

## What is proved (axiom-free)

* `bellFlattening K q ι = (1 : Matrix (ι → Fin q) (ι → Fin q) K)` — the bipartite coefficient matrix.
* `rank_bellFlattening : Matrix.rank (bellFlattening K q ι) = q ^ Fintype.card ι` — the **matrix
  Schmidt rank** of the Bell-pair product across the cut.
* `rank_bellFlattening_eq_pow_crossingCard` — the graph bridge: with a crossing-edge type of
  cardinality `crossingCard G A`, the Schmidt rank is exactly `q ^ crossingCard G A` = `cutRank` of the
  explicit profile — the entanglement realizes the combinatorial area.

## Scope firewall (HONEST)

This is the Schmidt rank at the **bipartite-flattening (coefficient-matrix)** level — the standard,
correct finite-dim computation.  It is NOT stated via reduced density matrices / partial trace: Mathlib
v4.30.0 has NO finite-dim quantum-information layer (no `partialTrace`, no `SchmidtRank`, no
`rank(reducedDensity) = rank(flattening)` theorem) — that packaging is a separate multi-file
infrastructure gap, cited not faked.  This grounds the area of `MetricFromState` in genuine
entanglement (Schmidt rank), NOT continuum geometry, NOT GR, NOT QG.  `q, ι` are explicit data.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators
import QIQTH.MetricFromState

namespace QIQTH.BellCutRank

open Matrix

variable (K : Type*) [Field K] (q : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- **The bipartite coefficient (flattening) matrix** of the unnormalized Bell-pair product across a
cut with crossing-edge type `ι` and local alphabet `Fin q`.  Rows are A-side assignments `ι → Fin q`,
columns are Aᶜ-side assignments; the maximally-entangled Bell state `∑_x |x⟩⊗|x⟩` has the **identity**
coefficient matrix. -/
noncomputable def bellFlattening : Matrix (ι → Fin q) (ι → Fin q) K :=
  (1 : Matrix (ι → Fin q) (ι → Fin q) K)

/-- **The matrix Schmidt rank of the Bell-pair product across the cut** is `q^(#crossing edges)`.
The flattening is the identity on assignments `ι → Fin q`, whose rank is
`card (ι → Fin q) = q ^ card ι` (`Matrix.rank_one` + `Fintype.card_fun`). -/
theorem rank_bellFlattening [Nontrivial K] :
    Matrix.rank (bellFlattening K q ι) = q ^ Fintype.card ι := by
  rw [bellFlattening, Matrix.rank_one, Fintype.card_fun, Fintype.card_fin]

/-- **The graph bridge (M3b) — genuine entanglement realizes the combinatorial area.**  Given a
crossing-edge type whose cardinality is `crossingCard G A`, the Schmidt rank of the Bell-pair product
across the cut `A | Aᶜ` is exactly `q ^ crossingCard G A` — i.e. `cutRank (explicitProfile G) A`.  So
the "area" of the metric-from-state construction is the honest entanglement (Schmidt rank) of an
explicit Bell state, not merely a combinatorial count. -/
theorem rank_bellFlattening_eq_pow_crossingCard [Nontrivial K]
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Finset V) (hcard : Fintype.card ι = QIQTH.MetricFromState.crossingCard G A) :
    Matrix.rank (bellFlattening K q ι) = q ^ QIQTH.MetricFromState.crossingCard G A := by
  rw [rank_bellFlattening, hcard]

end QIQTH.BellCutRank
