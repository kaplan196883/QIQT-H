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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
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

/-- `0 ≤ ⟪R ξ, ξ⟫` — the lower half of RvD's `0 ≤ R ≤ 2`. -/
theorem rvdR_inner_self_nonneg (S : StandardSubspace H) (ξ : H) :
    0 ≤ (inner ℝ (rvdR S ξ) ξ) := by
  rw [rvdR_inner_self]; positivity

/-- `P` is a contraction: `‖P ξ‖ ≤ ‖ξ‖`. -/
theorem norm_projK_apply_le (S : StandardSubspace H) (ξ : H) : ‖projK S ξ‖ ≤ ‖ξ‖ :=
  Submodule.norm_starProjection_apply_le _ ξ

/-- `Q` is a contraction: `‖Q ξ‖ ≤ ‖ξ‖`. -/
theorem norm_projIK_apply_le (S : StandardSubspace H) (ξ : H) : ‖projIK S ξ‖ ≤ ‖ξ‖ :=
  Submodule.norm_starProjection_apply_le _ ξ

/-- `⟪R ξ, ξ⟫ ≤ 2‖ξ‖²` — the upper half of RvD's `0 ≤ R ≤ 2` (each projection is a
    contraction, so `‖P ξ‖² + ‖Q ξ‖² ≤ 2‖ξ‖²`). -/
theorem rvdR_inner_self_le (S : StandardSubspace H) (ξ : H) :
    (inner ℝ (rvdR S ξ) ξ) ≤ 2 * ‖ξ‖ ^ 2 := by
  rw [rvdR_inner_self]
  have hP : ‖projK S ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) (norm_projK_apply_le S ξ)
  have hQ : ‖projIK S ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg _) (norm_projIK_apply_le S ξ)
  linarith

/-- **`R` is symmetric** (self-adjoint in the inner-product sense): `⟪R x, y⟫ = ⟪x, R y⟫`.
    Each projection `P, Q` is self-adjoint (`inner_starProjection_left_eq_right`).  (The stronger
    *operator-level* statement `IsSelfAdjoint (rvdR S)` — `star R = R` — is `rvdR_isSelfAdjoint`
    below, available now that `open ClosedSubmodule` supplies `InnerProductSpace ℝ H` and hence the
    adjoint/`Star` on `H →L[ℝ] H`.) -/
theorem rvdR_inner_symm (S : StandardSubspace H) (x y : H) :
    (inner ℝ (rvdR S x) y) = inner ℝ x (rvdR S y) := by
  simp only [rvdR_apply, projK, projIK, inner_add_left, inner_add_right]
  rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.inner_starProjection_left_eq_right]

/-- **RvD Prop 2.2(1): `R` is injective.**  If `R ξ = 0` then `⟪R ξ, ξ⟫ = 0`, so by
    `rvdR_inner_self` both `‖P ξ‖ = ‖Q ξ‖ = 0`; hence `ξ ⊥ 𝒦` and `ξ ⊥ i𝒦`, i.e.
    `ξ ∈ 𝒦ᗮ ⊓ (i𝒦)ᗮ = (𝒦 ⊔ i𝒦)ᗮ = ⊤ᗮ = ⊥` using `S.IsCyclic` (`𝒦 + i𝒦` dense).
    Injectivity of `R` is what makes the modular operator well-defined. -/
theorem rvdR_eq_zero (S : StandardSubspace H) {ξ : H} (h : rvdR S ξ = 0) : ξ = 0 := by
  have hquad : ‖projK S ξ‖ ^ 2 + ‖projIK S ξ‖ ^ 2 = 0 := by
    have hi := rvdR_inner_self S ξ
    rw [h, inner_zero_left] at hi
    linarith
  have hP2 : ‖projK S ξ‖ ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg ‖projIK S ξ‖]) (sq_nonneg _)
  have hQ2 : ‖projIK S ξ‖ ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg ‖projK S ξ‖]) (sq_nonneg _)
  have hPK0 : projK S ξ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hP2)
  have hQK0 : projIK S ξ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp hQ2)
  have hmemK : ξ ∈ (S.toClosedSubmodule)ᗮ := by
    rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff,
        ← Submodule.orthogonalProjection_eq_zero_iff]
    have hh : (S.toClosedSubmodule.toSubmodule).starProjection ξ = 0 := hPK0
    rw [Submodule.starProjection_apply] at hh
    exact_mod_cast hh
  have hmemIK : ξ ∈ (S.toClosedSubmodule.mulI)ᗮ := by
    rw [← ClosedSubmodule.mem_orthogonal_toSubmodule_iff,
        ← Submodule.orthogonalProjection_eq_zero_iff]
    have hh : (S.toClosedSubmodule.mulI.toSubmodule).starProjection ξ = 0 := hQK0
    rw [Submodule.starProjection_apply] at hh
    exact_mod_cast hh
  have hbot : ξ ∈ (⊥ : ClosedSubmodule ℝ H) := by
    rw [← ClosedSubmodule.top_orthogonal_eq_bot, ← S.IsCyclic,
        ← ClosedSubmodule.inf_orthogonal]
    exact ⟨hmemK, hmemIK⟩
  exact ClosedSubmodule.mem_bot.mp hbot

/-- **`R = P + Q` is injective** (RvD Prop 2.2(1)). -/
theorem rvdR_injective (S : StandardSubspace H) : Function.Injective (rvdR S) := by
  intro a b hab
  have hz : rvdR S (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (rvdR_eq_zero S hz)

/-! ### Operator-level adjoint structure (unblocking the polar decomposition)

`open ClosedSubmodule` (above) supplies the scoped real inner product `InnerProductSpace ℝ H`
(`⟪x,y⟫_ℝ = re⟪x,y⟫`); with `CompleteSpace H` this gives `H →L[ℝ] H` its adjoint / `Star` and
`IsSelfAdjoint`/`IsPositive` API.  So the operators `P, Q, R, P−Q` are genuine self-adjoint bounded
operators (not merely symmetric quadratic forms), and `R` is **positive** — the prerequisite for the
square root `R^{1/2}` in the polar decomposition `T = R^{1/2}(2−R)^{1/2}` (RvD Prop 2.2(2)). -/

/-- `P` is self-adjoint as a bounded operator (`star (projK S) = projK S`). -/
theorem projK_isSelfAdjoint (S : StandardSubspace H) : IsSelfAdjoint (projK S) :=
  isSelfAdjoint_starProjection _

/-- `Q` is self-adjoint as a bounded operator. -/
theorem projIK_isSelfAdjoint (S : StandardSubspace H) : IsSelfAdjoint (projIK S) :=
  isSelfAdjoint_starProjection _

/-- `R = P + Q` is self-adjoint. -/
theorem rvdR_isSelfAdjoint (S : StandardSubspace H) : IsSelfAdjoint (rvdR S) :=
  (projK_isSelfAdjoint S).add (projIK_isSelfAdjoint S)

/-- **`R = P + Q` is a positive operator** (`0 ≤ R` in the Loewner order, RvD `0 ≤ R ≤ 2`).
    Self-adjoint (`rvdR_isSelfAdjoint`) with `⟪R ξ, ξ⟫ ≥ 0` (`rvdR_inner_self_nonneg`).  This is what
    licenses the continuous-functional-calculus square root `R^{1/2}`, the first analytic step of the
    Rieffel–Van Daele polar decomposition `JT = P − Q`, `T = R^{1/2}(2−R)^{1/2}`. -/
theorem rvdR_isPositive (S : StandardSubspace H) : (rvdR S).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · exact rvdR_inner_symm S x y
  · simpa [ContinuousLinearMap.reApplyInnerSelf] using rvdR_inner_self_nonneg S x

/-- **RvD `P − Q`** — the self-adjoint operator whose polar decomposition `JT = P − Q`
    (RvD Definition 2.1) yields the modular conjugation `J` and the positive `T`. -/
noncomputable def rvdPmQ (S : StandardSubspace H) : H →L[ℝ] H := projK S - projIK S

/-- `P − Q` is self-adjoint (its polar decomposition `J·T` then has `J` self-adjoint, `T ≥ 0`). -/
theorem rvdPmQ_isSelfAdjoint (S : StandardSubspace H) : IsSelfAdjoint (rvdPmQ S) :=
  (projK_isSelfAdjoint S).sub (projIK_isSelfAdjoint S)

/-- **RvD upper bound `R ≤ 2`** (operator form): `2·1 − R` is positive.  With `rvdR_isPositive`
    (`0 ≤ R`) this is the complete RvD bound `0 ≤ R ≤ 2` at the operator level — `2 − R` is then also
    positive, so BOTH `R^{1/2}` and `(2 − R)^{1/2}` exist by the continuous functional calculus, the
    two factors of the polar decomposition `T = R^{1/2}(2 − R)^{1/2}` (RvD Prop 2.2(2)). -/
theorem rvdR_le_two (S : StandardSubspace H) :
    ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR S).IsPositive := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := rvdR_inner_symm S x y
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_sub_left,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    linarith [h]
  · have hle := rvdR_inner_self_le S x
    have hxx : (inner ℝ x x : ℝ) = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
    have key : (0 : ℝ) ≤ 2 * ‖x‖ ^ 2 - inner ℝ (rvdR S x) x := by linarith
    simpa [ContinuousLinearMap.reApplyInnerSelf, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_sub_left,
      real_inner_smul_left, hxx] using key

/-- **RvD Prop 2.2(2), the `T²` identity:** `(P − Q)² = P + Q − (P·Q + Q·P)`, which
    is exactly `R(2 − R)`.  Pure idempotent algebra (`P² = P`, `Q² = Q`); since
    `J T = P − Q` with `J² = 1`, this is `T² = R(2 − R)`, so `T = R^{1/2}(2 − R)^{1/2}`. -/
theorem rvdPmQ_sq (S : StandardSubspace H) :
    rvdPmQ S * rvdPmQ S
      = projK S + projIK S - (projK S * projIK S + projIK S * projK S) := by
  have hP : projK S * projK S = projK S := projK_idem S
  have hQ : projIK S * projIK S = projIK S := projIK_idem S
  simp only [rvdPmQ]
  rw [mul_sub, sub_mul, sub_mul, hP, hQ]
  abel

end QIQTH.StandardSubspaceModular
