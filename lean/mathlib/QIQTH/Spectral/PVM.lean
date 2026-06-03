/-
  Phase 1 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md):
  the KEYSTONE — projection-valued measures (PVM), the scalar spectral
  measures, the simple-function spectral integral, and the *named* analytic
  targets (bounded-Borel functional calculus + the spectral theorem).

  Status: this module builds the PVM scaffold and proves the structural
  content axiom-free (each `E s` is a projection ⇒ `⟪x, E s x⟫ = ‖E s x‖²`,
  complementation `E sᶜ = 1 - E s`, the scalar measure `μ_x(s) = ‖E s x‖²`
  with `μ_x(univ) = ‖x‖²`).  The deep analytic core — σ-additivity of the
  scalar measures as genuine `Measure`s, the bounded-Borel integral, and the
  spectral theorem (existence/uniqueness of `E` for a bounded self-adjoint
  `T`) — is the Phase-1 deliverable still to be built, recorded here as the
  precise target.  This is general operator-algebra material intended for
  upstreaming to Mathlib; it adds NO project axioms.

  Scaffold note: for now the PVM axioms are stated on *all* subsets of the
  index `Ω`; the faithful version restricts to a `MeasurableSpace Ω` (a
  Phase-1 refinement).  This does not affect any structural lemma below.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace QIQTH
namespace Spectral

open scoped BigOperators

variable {Ω : Type*} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A **projection-valued measure** on index space `Ω` acting on the Hilbert
    space `H`: a map `E` from subsets to bounded operators, each value an
    orthogonal projection (`IsSelfAdjoint` + `IsIdempotentElem`), with
    `E ∅ = 0`, `E univ = 1`, multiplicativity `E (s ∩ t) = E s * E t`, and
    finite additivity on disjoint sets.  (σ-additivity in the strong topology
    — equivalently, each scalar measure `μ_x` below is countably additive — is
    the analytic refinement, a Phase-1 target.) -/
structure PVM (Ω H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the projection associated to a set -/
  E : Set Ω → (H →L[ℂ] H)
  /-- each `E s` is self-adjoint -/
  isSA : ∀ s, IsSelfAdjoint (E s)
  /-- each `E s` is idempotent (hence, with `isSA`, an orthogonal projection) -/
  isIdem : ∀ s, IsIdempotentElem (E s)
  /-- `E ∅ = 0` -/
  E_empty : E ∅ = 0
  /-- `E univ = 1` (resolution of identity) -/
  E_univ : E Set.univ = 1
  /-- multiplicativity: `E (s ∩ t) = E s ∘ E t` -/
  E_inter : ∀ s t, E (s ∩ t) = E s * E t
  /-- finite additivity on disjoint sets -/
  E_add : ∀ s t, Disjoint s t → E (s ∪ t) = E s + E t

namespace PVM

variable (P : PVM Ω H)

/-- The defining idempotence, as an operator equation. -/
theorem mul_self (s : Set Ω) : P.E s * P.E s = P.E s := P.isIdem s

/-- The defining self-adjointness, as `(E s)† = E s`. -/
theorem adjoint_eq (s : Set Ω) : ContinuousLinearMap.adjoint (P.E s) = P.E s := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact P.isSA s

/-- Applying `E s` twice equals applying it once. -/
theorem E_apply_idem (s : Set Ω) (x : H) : P.E s (P.E s x) = P.E s x := by
  rw [← ContinuousLinearMap.mul_apply, P.mul_self]

/-- **Key projection identity:** `⟪x, E s x⟫ = ‖E s x‖²`.  (A projection's
    diagonal form equals the squared norm of the projected vector — the basis of
    the scalar spectral measure being a positive measure.) -/
theorem inner_E_self (s : Set Ω) (x : H) :
    inner ℂ x (P.E s x) = (‖P.E s x‖ : ℂ) ^ 2 := by
  have key : inner ℂ x (ContinuousLinearMap.adjoint (P.E s) (P.E s x))
      = inner ℂ (P.E s x) (P.E s x) :=
    ContinuousLinearMap.adjoint_inner_right (P.E s) x (P.E s x)
  rw [P.adjoint_eq, P.E_apply_idem] at key
  rw [key]; exact inner_self_eq_norm_sq_to_K _

/-- **Complementation:** `E sᶜ = 1 - E s`. -/
theorem E_compl (s : Set Ω) : P.E sᶜ = 1 - P.E s := by
  have h := P.E_add s sᶜ disjoint_compl_right
  rw [Set.union_compl_self, P.E_univ] at h
  rw [h]; abel

/-- The **scalar spectral measure** of a vector `x`: `μ_x(s) = ‖E s x‖²`.
    (When the PVM is σ-additive in the strong topology this is a genuine finite
    positive `Measure` of total mass `‖x‖²`; constructing it as such is a
    Phase-1 target.) -/
noncomputable def mu (x : H) (s : Set Ω) : ℝ := ‖P.E s x‖ ^ 2

theorem mu_nonneg (x : H) (s : Set Ω) : 0 ≤ P.mu x s := sq_nonneg _

theorem mu_empty (x : H) : P.mu x ∅ = 0 := by simp [mu, P.E_empty]

/-- Total mass of the scalar spectral measure is `‖x‖²`. -/
theorem mu_univ (x : H) : P.mu x Set.univ = ‖x‖ ^ 2 := by
  simp [mu, P.E_univ, ContinuousLinearMap.one_apply]

/-- The scalar measure recovers the inner product. -/
theorem mu_eq_inner (x : H) (s : Set Ω) :
    (P.mu x s : ℂ) = inner ℂ x (P.E s x) := by
  show ((‖P.E s x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x (P.E s x)
  rw [P.inner_E_self]; push_cast; ring

/-- **Spectral integral of a SIMPLE function** `∑ᵢ cᵢ 𝟙_{sᵢ}`: the operator
    `∑ᵢ cᵢ · E(sᵢ)`.  This is the fully-constructive core of the Borel
    functional calculus; its extension to bounded Borel `f` by norm-limit, and
    the spectral theorem, are the Phase-1 analytic targets below. -/
noncomputable def integralSimple {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (sets : ι → Set Ω) : H →L[ℂ] H :=
  ∑ i ∈ t, c i • P.E (sets i)

/-- The simple integral is additive over the index family. -/
theorem integralSimple_union {ι : Type*} [DecidableEq ι] (t₁ t₂ : Finset ι)
    (h : Disjoint t₁ t₂) (c : ι → ℂ) (sets : ι → Set Ω) :
    P.integralSimple (t₁ ∪ t₂) c sets
      = P.integralSimple t₁ c sets + P.integralSimple t₂ c sets := by
  simp only [integralSimple, Finset.sum_union h]

end PVM

/- ── Phase-1 analytic TARGETS (named, not yet proved) ───────────────────────

    These are the deep analytic deliverables that complete Phase 1.  They are
    recorded precisely (not as opaque axioms — the module stays axiom-free) so
    the keystone goal is unambiguous:

    (T1) σ-ADDITIVITY / scalar measures.  For each `x : H`, the set function
         `P.mu x` extends to a genuine finite positive `MeasureTheory.Measure`
         on `Ω` (total mass `‖x‖²`), equivalently `E` is σ-additive in the
         strong operator topology.  [Needs: Carathéodory/Hahn extension from the
         finitely-additive `mu`, plus SOT-σ-additivity of `E`.]

    (T2) BOUNDED-BOREL FUNCTIONAL CALCULUS.  Extend `integralSimple` to a
         `*`-homomorphism `f ↦ ∫ f dE : (bounded Borel functions) → (H →L[ℂ] H)`
         with `‖∫ f dE‖ ≤ ‖f‖∞`, `∫ f̄ dE = (∫ f dE)†`, `∫(fg)dE = (∫f dE)(∫g dE)`,
         and `⟪x, (∫ f dE) y⟫ = ∫ f d⟪x, E(·) y⟫`.  [Needs: T1 + a norm-limit /
         Bochner argument.]

    (T3) SPECTRAL THEOREM.  Every bounded self-adjoint `T : H →L[ℂ] H` admits a
         unique PVM `P : PVM ℝ H` supported on `spectrum ℂ T` with
         `T = ∫ id dP` (i.e. `⟪x, T x⟫ = ∫ λ dμ_x`).  [The keystone; classically
         via the continuous functional calculus + Riesz–Markov.  Mathlib already
         has the continuous FC (`CStarAlgebra/ContinuousFunctionalCalculus/`), so
         the realistic route is CFC + Riesz–Markov to manufacture `E`, then T1/T2.]

    Downstream (Phase 2): the unbounded analogue gives `Δ^{it}` and the modular
    flow — see the roadmap. -/

end Spectral
end QIQTH
