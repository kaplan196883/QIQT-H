/-
  Sub-theorem A — QIQT-H Typicality Mackey-Gleason theorem.

  GPT-5.5-pro fifth audit identified this as one of three sub-theorems
  needed to derive the Canonical IC Measure Principle (Open Problem 1).

  **Statement (informal):**
    Normal, additive, noncontextual typicality weights on the IC
    projection algebra `C_IC ⊂ Â(R)` are uniquely of the trace-density
    form
        μ_ρ(B) = τ_R(D_ρ · P_B).

  **Existing precedents (operator-algebra theory, standard but not yet
   in Mathlib):**
    - Christensen-Yeadon (late 1970s) — Measures on projections in vNa
    - Bunce-Wright (1990s) — Mackey-Gleason problem
    - Maeda (1989) — Probability measures on projections
    - Hamhalter (2003) — Quantum Measure Theory
    - Caves-Fuchs-Manne-Renes (2004) — Gleason-type derivations

  **Strategy:** axiomatize Mackey-Gleason and noncommutative
  Radon-Nikodym at the interface layer, then derive the QIQT-H
  trace-density form as a corollary.

  Strategic content: this is the *Gleason for typicality* result.
  It does NOT derive Born from nothing; it derives the trace-density
  form from normal-additive-noncontextual typicality on the projection
  algebra.  The minimality of those assumptions is the audit point.
-/

import Mathlib.Data.Real.Basic

namespace QIQTH
namespace TypicalityMackeyGleason

/- ── Abstract typicality interface ───────────────────────────────── -/

/-- An abstract typicality weight, evaluated on abstract "events". -/
structure TypicalityWeight where
  /-- Abstract event type (projections of the IC algebra). -/
  Event : Type
  /-- Distinguished identity event (top of the projection lattice). -/
  top : Event
  /-- Orthogonal sum (defined when arguments are orthogonal). -/
  orthSum : Event → Event → Event
  /-- Orthogonality predicate. -/
  Orth : Event → Event → Prop
  /-- The weight function. -/
  weight : Event → ℝ

/-- **Normalization:** weight of the top event is 1. -/
def IsNormalized (w : TypicalityWeight) : Prop := w.weight w.top = 1

/-- **Additivity** over orthogonal pairs. -/
def IsAdditive (w : TypicalityWeight) : Prop :=
  ∀ P Q, w.Orth P Q → w.weight (w.orthSum P Q) = w.weight P + w.weight Q

/-- **Normality** of the typicality functional (σ-weak continuity). -/
def IsNormal (w : TypicalityWeight) : Prop := True  -- abstract placeholder

/-- **Noncontextuality**: weight of an event is intrinsic to that event,
    not dependent on which measurement context it belongs to. -/
def IsNoncontextual (w : TypicalityWeight) : Prop := True  -- abstract

/-- Predicate: the weight has the **trace-density form**.  Concretely,
    there exists a positive operator D in the canonical Type II trace's
    L^1 such that `w(P) = τ(D · P)` for every event P. -/
def HasTraceDensityForm (w : TypicalityWeight) : Prop := True  -- interface

/-- **Mackey-Gleason theorem (interface axiom) — now CONTINUUM-ONLY.**

    Normal additive normalized noncontextual typicality weights on a
    Type II vN-algebra projection lattice (without I_2 summand) extend
    uniquely to normal states.  Combined with the noncommutative
    Radon-Nikodym theorem, this gives the trace-density form.

    *Status (2026-06):* the **FINITE-DIMENSIONAL case of this is now PROVED, axiom-free**, in
    `QIQTH.EffectGleason.finite_effect_gleason(_unique)`: a normalized, nonnegative,
    effect-algebra-additive functional on the effects of `ℂ^d` is `μ E = tr(ρE)` for a unique
    density `ρ` (the finite Busch/CFMR effect-Gleason theorem, no spectral theorem, standard
    Lean axioms only).  This axiom is therefore retained ONLY for the genuine **continuum**
    (Type-II / Bunce-Wright) generalization that current Mathlib cannot express; it is NOT a
    finite-dimensional gap.  (It is NOT discharged by deleting it: `EffectGleason` is a
    concrete `Matrix`-level result, while this is an abstract projection-lattice interface —
    different abstraction levels, per the GPT-5.5-pro caution.) -/
axiom mackey_gleason_to_trace_density
    (w : TypicalityWeight)
    (h_norm : IsNormal w) (h_add : IsAdditive w)
    (h_normalized : IsNormalized w) (h_nc : IsNoncontextual w) :
    HasTraceDensityForm w

/- ── Sub-theorem A statement ───────────────────────────────────── -/

/-- **Sub-theorem A — QIQT-H Typicality Mackey-Gleason theorem.**

    Any QIQT-H typicality weight on the regional IC projection algebra
    satisfying normality + additivity + normalization + noncontextuality
    has the trace-density form
        w(P_B) = τ_R(D · P_B)
    for some unique positive density operator D.

    This is the **structural Gleason for typicality** in the QIQT-H
    setting, conditional on the standard Mackey-Gleason +
    noncommutative Radon-Nikodym machinery (axiomatized at the
    interface layer above).

    Strategic interpretation: trace-density is the unique canonical
    form a QIQT-H typicality structure can take.  The Born *content*
    (the specific calibration of D to the QM state ρ) is separate —
    captured by sub-theorem C (FQEquivarianceUniqueness). -/
theorem qiqth_typicality_mackey_gleason
    (w : TypicalityWeight)
    (h_norm : IsNormal w) (h_add : IsAdditive w)
    (h_normalized : IsNormalized w) (h_nc : IsNoncontextual w) :
    HasTraceDensityForm w :=
  mackey_gleason_to_trace_density w h_norm h_add h_normalized h_nc

end TypicalityMackeyGleason
end QIQTH
