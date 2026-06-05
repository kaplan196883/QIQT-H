/-
# From "one actual RECORD" to "one actual VALUE" (prize bridge C1)

GPT-5.5-pro's review (2026-06): the no-collapse core proves `∃! r, r ∈ active` — exactly
one actual RECORD — but real measurements have many coactual records/fragments carrying the
SAME pointer value (SBS redundancy).  The honest, referee-recognizable statement is value-
level: at most one POINTER VALUE is coactual, while many same-value records may coexist.

This file closes that gap.  A `ValueContext` equips a capacity structure
(`CoreNoCollapse.JointRecordContext`) with a pointer value `valueOf : Rec → α` and the
value-level distinguishability premise: two records of DIFFERENT value jointly exceed
capacity (`pair_exceeds_value`).  Then in ANY coactual configuration all active records
share one value (`active_value_eq`, from monotonicity + the overflow premise), and with the
selector exactly one value is actual (`existsUnique_actualValue`).  Iterated over `n` trials
this gives a unique actual pointer-value HISTORY (`existsUnique_actualHistory`) — the object
the Born product law will later be pushed onto (prize join, next step).

Axiom-free (standard three only). -/
import QIQTH.CoreNoCollapse
import Mathlib.Tactic

namespace QIQTH.PointerValue

open CoreNoCollapse

/-- A capacity-limited measurement context whose records carry **pointer values** in `α`.
    The physical premise is value-level distinguishability: two records of DIFFERENT value
    jointly exceed the capacity `Q_max` (different macroscopic outcomes cannot be co-stored).
    Many records may carry the SAME value — redundancy is allowed. -/
structure ValueContext (α : Type*) where
  J : JointRecordContext
  valueOf : J.Rec → α
  /-- two records of different value jointly overflow capacity -/
  pair_exceeds_value : ∀ r s, valueOf r ≠ valueOf s → J.Qmax < J.jointCost {r, s}

/-- A **run** of a value context: a coactual configuration (capacity-bounded active set)
    made nonempty by the actuality selector `λ`. -/
structure ValueSelection (α : Type*) where
  ctx : ValueContext α
  config : JointCoactual ctx.J
  selected : config.active.Nonempty

namespace ValueSelection

variable {α : Type*} (V : ValueSelection α)

/-- **All coactual records share one pointer value.**  Two active records of different value
    would, by `pair_exceeds_value` + monotonicity, force `jointCost active > Q_max`,
    contradicting the capacity bound.  (Many same-value records may still be active.) -/
theorem active_value_eq {r s : V.ctx.J.Rec}
    (hr : r ∈ V.config.active) (hs : s ∈ V.config.active) :
    V.ctx.valueOf r = V.ctx.valueOf s := by
  by_contra hne
  have hsub : ({r, s} : Finset V.ctx.J.Rec) ⊆ V.config.active := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hmono := V.ctx.J.mono hsub
  linarith [V.ctx.pair_exceeds_value r s hne, V.config.capacity]

/-- **Exactly one actual pointer value (value-level single-outcome).**  Capacity forbids two
    distinct coactual values; the selector supplies at least one.  This upgrades
    `CoreNoCollapse.exactly_one_actual` from "one RECORD" to "one VALUE": the experienced
    pointer value is unique even though many same-value records may be coactual. -/
theorem existsUnique_actualValue :
    ∃! a : α, ∃ r ∈ V.config.active, V.ctx.valueOf r = a := by
  obtain ⟨r₀, hr₀⟩ := V.selected
  refine ⟨V.ctx.valueOf r₀, ⟨r₀, hr₀, rfl⟩, ?_⟩
  rintro a ⟨r, hr, rfl⟩
  exact active_value_eq V hr hr₀

/-- The unique actual pointer value of a run. -/
noncomputable def actualValue : α := V.existsUnique_actualValue.exists.choose

theorem actualValue_spec : ∃ r ∈ V.config.active, V.ctx.valueOf r = V.actualValue :=
  V.existsUnique_actualValue.exists.choose_spec

/-- Characterization: the actual value is the value of any active record. -/
theorem actualValue_eq_of_mem {r : V.ctx.J.Rec} (hr : r ∈ V.config.active) :
    V.ctx.valueOf r = V.actualValue := by
  obtain ⟨s, hs, hsv⟩ := V.actualValue_spec
  rw [← hsv]; exact active_value_eq V hr hs

end ValueSelection

/-- The **actual pointer-value history** of an `n`-trial run (one value per trial). -/
noncomputable def actualHistory {α : Type*} {n : ℕ} (V : Fin n → ValueSelection α) :
    Fin n → α := fun t => (V t).actualValue

/-- **Unique actual value history.**  An `n`-trial sequence of value-context runs has exactly
    one actual pointer-value history — the value-level single-outcome theorem, iterated.
    This is the object onto which the Born product law / typicality will be pushed (the
    prize join). -/
theorem existsUnique_actualHistory {α : Type*} {n : ℕ} (V : Fin n → ValueSelection α) :
    ∃! h : Fin n → α, ∀ t, ∃ r ∈ (V t).config.active, (V t).ctx.valueOf r = h t := by
  refine ⟨actualHistory V, fun t => (V t).actualValue_spec, ?_⟩
  intro h hh
  funext t
  exact ((V t).existsUnique_actualValue.unique (hh t) (V t).actualValue_spec)

/- ── Non-vacuity: every capacity context is a value context (records as values) ──-/

/-- Every `JointRecordContext` is a `ValueContext` with `valueOf = id` (each record is its
    own value); the value-overflow premise is just `pair_exceeds`.  Shows `ValueContext` is
    inhabited and `existsUnique_actualValue` is not vacuous.  (Genuine redundancy — many
    records, one value — is realized in the prize-join step, not here.) -/
def ValueContext.ofJoint (J : JointRecordContext) : ValueContext J.Rec where
  J := J
  valueOf := id
  pair_exceeds_value := fun r s h => J.pair_exceeds r s h

/-- Every joint selection induces a value selection. -/
def ofJointSelection {J : JointRecordContext} (S : JointSelection J) :
    ValueSelection J.Rec where
  ctx := ValueContext.ofJoint J
  config := S.config
  selected := S.selected

/-- Concrete non-vacuous instance: the `CoreNoCollapse` witness run has a unique actual
    value (`value-level single outcome fires on a concrete model). -/
noncomputable example : (CoreNoCollapse.witnessContext.toJoint).Rec :=
  (ofJointSelection CoreNoCollapse.witnessJointSelection).actualValue

end QIQTH.PointerValue
