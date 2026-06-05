/-
# Grounding the subadditive core: pairwise overflow FROM orthogonality

`CoreNoCollapse.JointRecordContext` replaced the unjustified additive capacity bound
with a MONOTONE joint cost + a `pair_exceeds` premise (two distinct records jointly
exceed `Q_max`).  GPT-5.5-pro's caveat: in a pure dimension model two subspaces each of
dim `> D/2` need NOT overflow — they can SHARE their overlap.  So `pair_exceeds` is a
genuine extra input that must be sourced from DISTINGUISHABILITY, i.e. ORTHOGONALITY of
distinct objective records.

This file closes that loop.  The honest physical model:

  • a finite-dimensional register `H`;
  • each record `r` occupies a subspace `sub r ⊆ H`;
  • distinct records occupy PAIRWISE-ORTHOGONAL subspaces (`ortho` — the content of
    distinguishability: different objective outcomes are perfectly distinguishable);
  • the joint cost of an active set is the dimension of the SPAN of its subspaces
    (`finrank (⨆ active sub)`) — manifestly SUBADDITIVE, no additivity assumed;
  • a record is macroscopic if it occupies `> Q_max/2` of the register.

From these, `pair_exceeds` is a THEOREM: two distinct macroscopic records are orthogonal,
so their span dimension is the SUM of their dimensions (`finrank_sup_add_finrank_inf_eq`
with `⊓ = ⊥` from `IsOrtho.disjoint`), which exceeds `Q_max`.  Monotonicity is
`Submodule.finrank_mono ∘ Finset.sup_mono`.  Feeding `OrthogonalRecordModel.toJoint` into
`qiqth_single_outcome_joint` gives single-outcome with the pairwise-overflow premise
DERIVED from orthogonality — not assumed.  Axiom-free (standard three only). -/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import QIQTH.CoreNoCollapse
import Mathlib.Tactic

namespace QIQTH.OrthogonalCapacity

open scoped BigOperators
open Module Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- **Physical (orthogonal) record model.**  Records occupy subspaces of a finite register
    `H`; distinct records are PAIRWISE ORTHOGONAL (distinguishability); each macroscopic
    record occupies more than half the capacity `Q_max`.  No additivity is assumed — the
    joint cost will be the (subadditive) span dimension. -/
structure OrthogonalRecordModel (𝕜 : Type*) [RCLike 𝕜] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H] where
  Rec : Type
  [recFintype : Fintype Rec]
  [recDecEq : DecidableEq Rec]
  /-- the subspace of the register occupied by record `r` -/
  sub : Rec → Submodule 𝕜 H
  /-- distinct records occupy orthogonal subspaces (perfect distinguishability) -/
  ortho : ∀ r s, r ≠ s → Submodule.IsOrtho (sub r) (sub s)
  /-- the finite capacity bound -/
  Qmax : ℝ
  /-- each (macroscopic) record occupies more than half the register -/
  macroscopic : ∀ r, Qmax / 2 < (finrank 𝕜 (sub r) : ℝ)

attribute [instance] OrthogonalRecordModel.recFintype OrthogonalRecordModel.recDecEq

variable (O : OrthogonalRecordModel 𝕜 H)

/-- **Joint cost = dimension of the span of the active records' subspaces** — manifestly
    subadditive (`dim(U+V) ≤ dim U + dim V`), no additivity assumed. -/
noncomputable def jointCost (A : Finset O.Rec) : ℝ :=
  (finrank 𝕜 ↥(Finset.sup A O.sub) : ℝ)

/-- **Monotonicity** of the span-dimension joint cost (bigger active set, bigger span). -/
theorem jointCost_mono {A B : Finset O.Rec} (h : A ⊆ B) :
    jointCost O A ≤ jointCost O B := by
  have hsub : Finset.sup A O.sub ≤ Finset.sup B O.sub := Finset.sup_mono h
  unfold jointCost
  exact_mod_cast Submodule.finrank_mono hsub

/-- **Span dimension of a pair of ORTHOGONAL records adds** (`⊓ = ⊥`, so
    `finrank(U ⊔ V) = finrank U + finrank V`). -/
theorem jointCost_pair {r s : O.Rec} (h : r ≠ s) :
    jointCost O {r, s} = (finrank 𝕜 (O.sub r) : ℝ) + (finrank 𝕜 (O.sub s) : ℝ) := by
  have hsup : Finset.sup ({r, s} : Finset O.Rec) O.sub = O.sub r ⊔ O.sub s := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  have hdisj : Disjoint (O.sub r) (O.sub s) := (O.ortho r s h).disjoint
  have key := Submodule.finrank_sup_add_finrank_inf_eq (O.sub r) (O.sub s)
  rw [hdisj.eq_bot, finrank_bot, add_zero] at key
  unfold jointCost
  rw [hsup, key]
  push_cast
  ring

/-- **`pair_exceeds` DERIVED from orthogonality.**  Two distinct macroscopic records are
    orthogonal, so their span dimension is the SUM of their dimensions, each `> Q_max/2`,
    hence `> Q_max`.  This is the physical content GPT-5.5-pro asked for: pairwise overflow
    is a consequence of distinguishability (orthogonality), not a bare assumption. -/
theorem pair_exceeds {r s : O.Rec} (h : r ≠ s) : O.Qmax < jointCost O {r, s} := by
  rw [jointCost_pair O h]
  linarith [O.macroscopic r, O.macroscopic s]

/-- **The grounded bridge.**  An orthogonal record model yields a
    `CoreNoCollapse.JointRecordContext` whose monotone joint cost is the span dimension and
    whose pairwise-overflow premise is the THEOREM `pair_exceeds` — sourced from
    orthogonality, not assumed. -/
noncomputable def toJoint : CoreNoCollapse.JointRecordContext where
  Rec := O.Rec
  recFintype := O.recFintype
  recDecEq := O.recDecEq
  jointCost := jointCost O
  mono := fun h => jointCost_mono O h
  Qmax := O.Qmax
  pair_exceeds := fun _ _ h => pair_exceeds O h

/-- **Single-outcome from orthogonal distinguishability + finite capacity (fully grounded).**
    In any run of an orthogonal record model, the actuality selector picks EXACTLY ONE actual
    record — with the pairwise-overflow premise DERIVED from orthogonality, the joint cost a
    genuine (subadditive) span dimension, and NO collapse postulate. -/
theorem orthogonal_single_outcome
    (sel : CoreNoCollapse.JointSelection (toJoint O)) :
    ∃! r : O.Rec, r ∈ sel.config.active :=
  CoreNoCollapse.qiqth_single_outcome_joint sel

/- ── A concrete 2-record witness (non-vacuity of the orthogonal hypotheses) ──-/

/-- A concrete **2-record** orthogonal model on `ℂ²`: the two coordinate lines, each
    1-dimensional (macroscopic for `Q_max = 1`, since `1/2 < 1`) and mutually orthogonal.
    Witnesses that the orthogonality + macroscopicity hypotheses are jointly satisfiable
    for TWO distinct records — so `pair_exceeds` is genuinely non-vacuous (not vacuously
    true for lack of a distinct pair). -/
noncomputable def witness : OrthogonalRecordModel ℂ (EuclideanSpace ℂ (Fin 2)) where
  Rec := Fin 2
  sub := fun i => Submodule.span ℂ {(EuclideanSpace.basisFun (Fin 2) ℂ) i}
  ortho := fun i j hij => by
    rw [isOrtho_span]
    intro u hu v hv
    rw [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    rw [orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal i j, if_neg hij]
  Qmax := 1
  macroscopic := fun i => by
    rw [finrank_span_singleton ((EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal.ne_zero i)]
    norm_num

/-- **Non-vacuity of `pair_exceeds`.**  In the witness the two DISTINCT orthogonal
    macroscopic records jointly span dimension `2 > Q_max = 1`, so the pairwise-overflow
    premise genuinely fires — the orthogonal hypotheses are satisfiable for two records,
    and exclusion is not vacuous.  (Any selector over such a model then yields exactly one
    actual record by `orthogonal_single_outcome`.) -/
example : (1 : ℝ) < jointCost witness ({0, 1} : Finset (Fin 2)) :=
  pair_exceeds witness (show (0 : Fin 2) ≠ 1 by decide)

end QIQTH.OrthogonalCapacity
