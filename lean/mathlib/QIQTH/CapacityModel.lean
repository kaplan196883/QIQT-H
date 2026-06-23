/-
# QIQT-H capacity model: DERIVING the finite-capacity bound

`QIQTH/CoreNoCollapse.lean` proved the conditional single-outcome theorem, but it
*assumed* the saturation premise `cost r > Q_max/2` (the one physical input). GPT-5.5-pro
flagged that as the genuine open content. This file removes that assumption for a
concrete capacity model: records occupy mutually-orthogonal subspaces of a
finite-dimensional "record register", so their dimensions ADD and are capped by the
register dimension `D = finrank`. The capacity bound is then a THEOREM (orthonormality
+ a dimension count), not a hypothesis.

★ Paper correspondence: the register dimension `D` is the finite-dimensional PROXY for
the regional holographic capacity `Q_R = A(∂R)/4ℓ_P²` (FQ postulate); it is MODULAR-LOCAL
(one region's register), not a spacetime-global budget.  This file mechanizes only the
finite number-bound; the continuum cost claim `χ_R > Q_R` (H2) and the postulate
`Q_R = A/4ℓ_P²` are NOT proved here (GAP 1 / GAP 4 of 48_GAP_PRIZE_List.md).

This is the rigorous backbone of the Strasberg–Schindler–Wang–Winter "branch selection
problem" (arXiv:2601.19703): a family of N almost-orthogonal record vectors cannot
exceed the register dimension D — the number of identifiable records is capacity-bounded.

Model:
  • a finite record register `H` (finite-dim ℂ-Hilbert space), `D := finrank ℂ H`;
  • each record `j` is realized by an orthonormal *frame* of `recDim j` pointer
    vectors, all frames mutually orthogonal (one global orthonormal family `v`
    labelled by `label : κ → ι`);
  • `recDim label j` = number of frame vectors of record `j`.

DERIVED (no capacity assumed):
  • `orthonormal_card_le_finrank` : # pointer states ≤ D  (the raw capacity fact).
  • `capacity_total` : `∑ⱼ recDim j ≤ D`  (dimensions add, capped by D).
  • `macroscopic_subsingleton` : at most ONE *macroscopic* record (one using > D/2 of the
    register) — the saturation premise of `CoreNoCollapse` is now a theorem.
  • `capacity_exactly_one` : with a selector (≥1 macroscopic record present), EXACTLY one.

Honest residual: "macroscopic = occupies > half the register" (`finrank < 2·recDim j`)
is the remaining physical modelling choice — but it is now a transparent dimensional
condition, and everything else is derived. Axiom-free (standard three only). -/
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic

namespace QIQTH.CapacityModel

open scoped BigOperators
open Module Finset

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- **The raw capacity fact** (Strasberg et al.): a family of orthonormal record /
    pointer states has at most `finrank 𝕜 H` members — the register dimension bounds
    the number of distinguishable records. -/
theorem orthonormal_card_le_finrank {ι : Type*} [Fintype ι] {v : ι → H}
    (hv : Orthonormal 𝕜 v) : Fintype.card ι ≤ finrank 𝕜 H :=
  hv.linearIndependent.fintype_card_le_finrank

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The dimension (frame size) consumed by record `j`: the number of orthonormal
    pointer vectors labelled `j`. -/
def recDim (label : κ → ι) (j : ι) : ℕ :=
  (Finset.univ.filter (fun k => label k = j)).card

/-- **Capacity is additive and bounded:** `∑ⱼ recDim j ≤ D`.  This is the per-region
    aggregate capacity bound `∑ cost ≤ Qmax` of `CoreNoCollapse.RecordContext` (one
    region's register, NOT a spacetime budget) — here DERIVED from orthonormality, not
    assumed.  The register dimension `D` is the finite proxy for `Q_R = A(∂R)/4ℓ_P²`. -/
theorem capacity_total {v : κ → H} (hv : Orthonormal 𝕜 v) (label : κ → ι) :
    ∑ j : ι, recDim label j ≤ finrank 𝕜 H := by
  have h : ∑ j : ι, recDim label j = Fintype.card κ := by
    simp only [recDim]
    rw [← Finset.card_univ (α := κ),
      Finset.card_eq_sum_card_fiberwise (f := label) (fun k _ => Finset.mem_univ _)]
  rw [h]; exact orthonormal_card_le_finrank hv

/-- A record is **macroscopic** (relative to a register dimension `D`) if it occupies
    more than half the register (`D < 2·recDim j`).  Transparent dimensional form of
    the saturation premise `cost > Q_max/2`.  `D : ℕ` is explicit (it is the only place
    the register `H` enters, via `D = finrank 𝕜 H`). -/
def Macroscopic (D : ℕ) (label : κ → ι) (j : ι) : Prop :=
  D < 2 * recDim label j

instance (D : ℕ) (label : κ → ι) (j : ι) : Decidable (Macroscopic D label j) :=
  Nat.decLt _ _

/-- **Macroscopic exclusion (DERIVED):** at most ONE macroscopic record can be present.
    Two would consume `> D/2 + D/2 = D` of the register, exceeding the derived capacity
    bound `∑ ≤ D`.  This is `CoreNoCollapse.coactual_subsingleton` with the saturation
    premise now a theorem. -/
theorem macroscopic_subsingleton {v : κ → H} (hv : Orthonormal 𝕜 v) (label : κ → ι) :
    (Finset.univ.filter (Macroscopic (finrank 𝕜 H) label)).card ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨j₁, j₂, hj₁, hj₂, hne⟩ := Finset.one_lt_card_iff.mp h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Macroscopic] at hj₁ hj₂
  have hsum : recDim label j₁ + recDim label j₂ ≤ ∑ j : ι, recDim label j := by
    calc recDim label j₁ + recDim label j₂
        = ∑ j ∈ ({j₁, j₂} : Finset ι), recDim label j := (Finset.sum_pair hne).symm
      _ ≤ ∑ j : ι, recDim label j :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hcap := capacity_total hv label
  omega

/-- **Capacity + selector ⇒ EXACTLY ONE macroscopic record.**  The fully-derived
    counterpart of `CoreNoCollapse.exactly_one_actual`: single-outcome experience,
    with the capacity bound and the saturation premise both proved (not assumed), and
    only "at least one macroscopic record is present" (the actuality selector `λ`)
    supplied as the irreducibly-selective input. -/
theorem capacity_exactly_one {v : κ → H} (hv : Orthonormal 𝕜 v) (label : κ → ι)
    (hsel : (Finset.univ.filter (Macroscopic (finrank 𝕜 H) label)).Nonempty) :
    (Finset.univ.filter (Macroscopic (finrank 𝕜 H) label)).card = 1 := by
  have hle := macroscopic_subsingleton (𝕜 := 𝕜) hv label
  have hge := hsel.card_pos
  omega

end QIQTH.CapacityModel
