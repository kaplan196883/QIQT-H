/-
  Phase 3′ of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md), Track B:
  free-field / standard-subspace modular theory via the BOUNDED-OPERATOR approach of

    M. A. Rieffel & A. Van Daele, "A bounded operator approach to Tomita–Takesaki
    theory", Pacific J. Math. 69 (1977), no. 1, 187–221.   [refs/books_papers/]

  RvD build the modular conjugation `J` and modular operator from TWO closed real
  subspaces 𝒦, ℒ of a Hilbert space satisfying the *nondegeneracy* conditions
  `𝒦 ∩ ℒ = {0}` and `𝒦 + ℒ` dense — using only BOUNDED operators, with no unbounded
  domains.  For the Tomita–Takesaki application one takes ℒ = i𝒦.

  This maps EXACTLY onto Mathlib's `StandardSubspace` (Y. Tanimoto, 2026):
    • 𝒦  = `S.toClosedSubmodule`,  ℒ = i𝒦 = `S.toClosedSubmodule.mulI`;
    • RvD's `𝒦 ∩ ℒ = {0}`         = `S.IsSeparating`  (`K ⊓ iK = ⊥`);
    • RvD's `𝒦 + ℒ` dense          = `S.IsCyclic`      (`K ⊔ iK = ⊤`).

  RvD Definition 2.1: `P, Q` = orthogonal projections onto 𝒦, ℒ; `R = P + Q`;
  `J·T = P − Q` is the polar decomposition (`J` self-adjoint orthogonal, `J² = 1`;
  `T = R^{1/2}(2−R)^{1/2} ≥ 0`).  This file sets up `P, Q, R` on `StandardSubspace`
  and proves RvD Prop 2.2(1)'s key quadratic-form identity
  `⟪R ξ, ξ⟫ = ‖P ξ‖² + ‖Q ξ‖²`, the engine for injectivity of `R` (whence the
  modular operator is well-defined).

  Axiom-free: depends only on Lean's standard `propext, Classical.choice, Quot.sound`.
  (`StandardSubspace` opens the scoped real inner product `⟪·,·⟫_ℝ := Re⟪·,·⟫`.)
-/
import Mathlib.Analysis.InnerProductSpace.StandardSubspace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

namespace QIQTH.StandardSubspaceModular

open ClosedSubmodule StandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **RvD `P`** — the real-orthogonal projection onto the standard subspace `𝒦`. -/
noncomputable def projK (S : StandardSubspace H) : H →L[ℝ] H :=
  (S.toClosedSubmodule.toSubmodule).starProjection

/-- **RvD `Q`** — the real-orthogonal projection onto `i𝒦 = mulI 𝒦`. -/
noncomputable def projIK (S : StandardSubspace H) : H →L[ℝ] H :=
  (S.toClosedSubmodule.mulI.toSubmodule).starProjection

/-- **RvD `R = P + Q`** (Definition 2.1). -/
noncomputable def rvdR (S : StandardSubspace H) : H →L[ℝ] H := projK S + projIK S

/-- `P` is idempotent (a projection). -/
theorem projK_idem (S : StandardSubspace H) : IsIdempotentElem (projK S) :=
  Submodule.isIdempotentElem_starProjection _

/-- `Q` is idempotent (a projection). -/
theorem projIK_idem (S : StandardSubspace H) : IsIdempotentElem (projIK S) :=
  Submodule.isIdempotentElem_starProjection _

@[simp]
theorem rvdR_apply (S : StandardSubspace H) (ξ : H) :
    rvdR S ξ = projK S ξ + projIK S ξ := rfl

/-- **RvD Prop 2.2(1), key identity:** `⟪R ξ, ξ⟫ = ‖P ξ‖² + ‖Q ξ‖²`.
    (Each projection is self-adjoint idempotent, so `⟪P ξ, ξ⟫ = ‖P ξ‖²`.)
    This is the quadratic form whose vanishing forces `P ξ = Q ξ = 0`, the crux
    of `R`'s injectivity and hence of the well-definedness of the modular operator. -/
theorem rvdR_inner_self (S : StandardSubspace H) (ξ : H) :
    (inner ℝ (rvdR S ξ) ξ) = ‖projK S ξ‖ ^ 2 + ‖projIK S ξ‖ ^ 2 := by
  rw [rvdR_apply, inner_add_left]
  congr 1
  · simpa [projK] using
      Submodule.re_inner_starProjection_eq_normSq (S.toClosedSubmodule.toSubmodule) ξ
  · simpa [projIK] using
      Submodule.re_inner_starProjection_eq_normSq (S.toClosedSubmodule.mulI.toSubmodule) ξ

/-- `0 ≤ ⟪R ξ, ξ⟫` — `R` is a positive operator (RvD: `0 ≤ R ≤ 2`). -/
theorem rvdR_inner_self_nonneg (S : StandardSubspace H) (ξ : H) :
    0 ≤ (inner ℝ (rvdR S ξ) ξ) := by
  rw [rvdR_inner_self]; positivity

end QIQTH.StandardSubspaceModular
