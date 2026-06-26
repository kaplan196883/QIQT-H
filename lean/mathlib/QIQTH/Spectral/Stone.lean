import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Stone's theorem — the infinitesimal generator (Phase 3.1)

For a one-parameter family of bounded operators `U : ℝ → (H →L[ℂ] H)` (in the intended use, a strongly-continuous
one-parameter *unitary* group `U_t`), the **infinitesimal generator** is the unbounded operator
`A x = −i · (d/dt U_t x)|₀`, defined on the **smooth domain** `D(A) = {x : t ↦ U_t x is differentiable at 0}`.

This is **Phase 3.1 of `STONE_THEOREM_PLAN.md`** (= the pivotal P4-wall Phase 4.2): the generator as a genuine
`LinearPMap` (unbounded linear map). The construction needs no hypotheses on `U` — the smooth domain is a
submodule and `A` is ℂ-linear on it for *any* operator family (each `U_t` is a CLM, so `t ↦ U_t(x+y)` and
`t ↦ U_t(c•x)` split, and `deriv` is additive/homogeneous on the differentiable domain).

**Honest scope:** this delivers the generator as an unbounded operator. Its **self-adjointness** (Phase 3.2,
essential self-adjointness via the group / Nelson analytic vectors) and the **Cayley transform + unbounded
spectral theorem** (Phase 3.3) are the genuine Mathlib-grade frontiers — no Stone's theorem and no unbounded
self-adjoint spectral theory exist in Mathlib. Applying this to `clockTransl` (`λ_t`) to get the clock energy
`X = A_edge` (P4-wall Phase 4.3) is gated on 3.2/3.3.
-/

namespace QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **The smooth domain** of a one-parameter operator family `U`: the vectors `x` for which `t ↦ U_t x` is
    differentiable at `0`. A `ℂ`-submodule (each `U_t` is `ℂ`-linear, so the domain is closed under `+`, `•`). -/
def stoneDomain (U : ℝ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {x | DifferentiableAt ℝ (fun t => U t x) 0}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact differentiableAt_const 0
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have h : (fun t => U t (x + y)) = (fun t => U t x + U t y) := funext fun t => map_add (U t) x y
    rw [h]; exact hx.add hy
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    have h : (fun t => U t (c • x)) = (fun t => c • U t x) := funext fun t => map_smul (U t) c x
    rw [h]; exact hx.const_smul c

/-- **The infinitesimal generator** `A x = −i · (d/dt U_t x)|₀` of the family `U`, as an unbounded operator
    (`LinearPMap`) on the smooth domain `stoneDomain U`. For a strongly-continuous unitary group this is the
    self-adjoint generator of Stone's theorem (self-adjointness = the cited frontier). -/
noncomputable def stoneGen (U : ℝ → (H →L[ℂ] H)) : H →ₗ.[ℂ] H where
  domain := stoneDomain U
  toFun :=
    { toFun := fun x => -Complex.I • deriv (fun t => U t (x : H)) 0
      map_add' := fun x y => by
        have hx : DifferentiableAt ℝ (fun t => U t (x : H)) 0 := x.2
        have hy : DifferentiableAt ℝ (fun t => U t (y : H)) 0 := y.2
        have h : (fun t => U t ((x : H) + (y : H)))
            = (fun t => U t (x : H)) + (fun t => U t (y : H)) := by
          funext t; simp only [Pi.add_apply]; exact map_add (U t) _ _
        simp only [Submodule.coe_add]
        rw [h, deriv_add hx hy, smul_add]
      map_smul' := fun c x => by
        have hx : DifferentiableAt ℝ (fun t => U t (x : H)) 0 := x.2
        have h : (fun t => U t (c • (x : H))) = c • (fun t => U t (x : H)) := by
          funext t; simp only [Pi.smul_apply]; exact map_smul (U t) c _
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [h, deriv_const_smul c hx, smul_comm] }

/-- The generator acts as `A x = −i · (d/dt U_t x)|₀` on the smooth domain. -/
theorem stoneGen_apply (U : ℝ → (H →L[ℂ] H)) (x : stoneDomain U) :
    stoneGen U x = -Complex.I • deriv (fun t => U t (x : H)) 0 := rfl

/-- **The generator–derivative relation:** for `x` in the smooth domain, `t ↦ U_t x` has derivative
    `i · A x` at `0` (equivalently `A x = −i · (d/dt U_t x)|₀`). This is the `HasDerivAt` form the downstream
    Stone arguments (symmetry, `U`-invariance, essential self-adjointness) consume. -/
theorem hasDerivAt_stoneGen (U : ℝ → (H →L[ℂ] H)) (x : stoneDomain U) :
    HasDerivAt (fun t => U t (x : H)) (Complex.I • stoneGen U x) 0 := by
  rw [stoneGen_apply, smul_smul, show Complex.I * -Complex.I = 1 by
    rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]
  exact x.2.hasDerivAt

end QIQTH.Spectral
