import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LinearPMap

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

/-- **The shifted orbit `t ↦ U_t (U_s x)` has derivative `i • U_s (A x)` at `0`** (group law +
    `U_s` a smooth CLM). The key derivative computation behind both flow-invariance of the smooth domain
    and the commutation `[A, U_s] = 0`. -/
theorem hasDerivAt_stoneGen_flow (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (s : ℝ) (x : stoneDomain U) :
    HasDerivAt (fun t => U t (U s (x : H))) (Complex.I • U s (stoneGen U x)) 0 := by
  set d := Complex.I • stoneGen U x with hd
  have hx' : HasDerivAt (fun t => U t (x : H)) d 0 := hasDerivAt_stoneGen U x
  -- the orbit `τ ↦ U_τ x` is differentiable at `s`: `U_τ x = U_s (U_{τ−s} x)`
  have hsub : HasDerivAt (fun τ => U (τ - s) (x : H)) d s := by
    simpa using HasDerivAt.scomp_of_eq (hg := hx') (hh := (hasDerivAt_id s).sub_const s)
      (hy := (sub_self s).symm)
  have hgs : HasDerivAt (fun τ => U τ (x : H)) ((U s) d) s := by
    have h2 : (fun τ => U τ (x : H)) = fun τ => ((U s).restrictScalars ℝ) (U (τ - s) (x : H)) := by
      funext τ; rw [ContinuousLinearMap.coe_restrictScalars', ← ContinuousLinearMap.comp_apply,
        ← hgrp s (τ - s), add_sub_cancel]
    rw [h2]
    simpa using HasFDerivAt.comp_hasDerivAt
      (hl := ContinuousLinearMap.hasFDerivAt ((U s).restrictScalars ℝ)) (hf := hsub)
  -- `t ↦ U_t (U_s x) = U_{t+s} x`, differentiable at `0`
  have hfin : HasDerivAt (fun t => U t (U s (x : H))) ((U s) d) 0 := by
    have h3 : (fun t => U t (U s (x : H))) = fun t => U (t + s) (x : H) := by
      funext t; rw [← ContinuousLinearMap.comp_apply, ← hgrp t s]
    rw [h3]
    simpa using HasDerivAt.scomp_of_eq (hg := hgs) (hh := (hasDerivAt_id 0).add_const s)
      (hy := (zero_add s).symm)
  rw [hd, map_smul] at hfin
  exact hfin

/-- **`U_s` maps `stoneDomain U` into itself** — the orbit `τ ↦ U_τ (U_s x)` is differentiable at `0`
    (`hasDerivAt_stoneGen_flow`). The `U`-invariance of the smooth domain, a prerequisite for essential
    self-adjointness (Phase 3.2). -/
theorem stoneDomain_apply_mem (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (s : ℝ) (x : H) (hx : x ∈ stoneDomain U) : U s x ∈ stoneDomain U :=
  (hasDerivAt_stoneGen_flow U hgrp s ⟨x, hx⟩).differentiableAt

/-- The backward flow `t ↦ U_{−t} x` has derivative `−i · A x` at `0` (chain rule on `hasDerivAt_stoneGen`). -/
theorem hasDerivAt_stoneGen_neg (U : ℝ → (H →L[ℂ] H)) (x : stoneDomain U) :
    HasDerivAt (fun t => U (-t) (x : H)) (-(Complex.I • stoneGen U x)) 0 := by
  simpa using HasDerivAt.scomp_of_eq (hg := hasDerivAt_stoneGen U x)
    (hh := (hasDerivAt_id (0 : ℝ)).neg) (hy := neg_zero.symm)

/-- **Identification of the generator by any witnessed derivative.** If the orbit `t ↦ U_t x` is differentiable
    at `0` with derivative `i • v`, then `stoneGen U x = v`. The generator is *pinned* by the derivative — this is
    the bridge from the abstract `stoneGen` to a concrete operator: to show `stoneGen` of a given group equals a
    known operator `B`, it suffices to exhibit `HasDerivAt (t ↦ U_t x) (i • B x) 0`. (Uniqueness half of Stone's
    correspondence; no density needed.) -/
theorem stoneGen_eq_of_hasDerivAt (U : ℝ → (H →L[ℂ] H)) (x v : H) (hx : x ∈ stoneDomain U)
    (h : HasDerivAt (fun t => U t x) (Complex.I • v) 0) :
    stoneGen U ⟨x, hx⟩ = v := by
  have huniq := (hasDerivAt_stoneGen U ⟨x, hx⟩).unique h
  exact smul_right_injective H Complex.I_ne_zero huniq

/-- **The generator commutes with the flow:** `A (U_s x) = U_s (A x)` on the smooth domain, i.e.
    `[A, U_s] = 0`. Proof: the shifted orbit `t ↦ U_t (U_s x)` has derivative `i • U_s (A x)`
    (`hasDerivAt_stoneGen_flow`), so by generator-identification `stoneGen U (U_s x) = U_s (A x)`. This
    `U`-invariance of `A` is what makes the generator (hence the clock energy `X = A_edge`, Phase 4.3)
    compatible with the modular flow it is read off from. -/
theorem stoneGen_comm_flow (U : ℝ → (H →L[ℂ] H)) (hgrp : ∀ s t, U (s + t) = U s ∘L U t)
    (s : ℝ) (x : stoneDomain U) :
    stoneGen U ⟨U s (x : H), stoneDomain_apply_mem U hgrp s x x.2⟩ = U s (stoneGen U x) :=
  stoneGen_eq_of_hasDerivAt U (U s (x : H)) (U s (stoneGen U x)) _
    (hasDerivAt_stoneGen_flow U hgrp s x)

section Symmetry
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The generator is symmetric:** `⟪A x, y⟫ = ⟪x, A y⟫` on the smooth domain, for a one-parameter *unitary*
    group (`U` a group with `U_t` inner-product-preserving). Symmetry of `A = −i (d/dt U_t)` is the first half of
    self-adjointness (Stone Phase 3.2). Proof: the unitary relation `⟪U_t x, y⟫ = ⟪x, U_{−t} y⟫` differentiated at
    `0` two ways gives `⟪i·Ax, y⟫ = ⟪x, −i·Ay⟫`, i.e. `−i⟪Ax,y⟫ = −i⟪x,Ay⟫`; cancel `−i`. -/
theorem stoneGen_symmetric (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x y : stoneDomain U) :
    (inner ℂ (stoneGen U x) (y : H) : ℂ) = inner ℂ (x : H) (stoneGen U y) := by
  have hrel : (fun t => (inner ℂ (U t (x : H)) (y : H) : ℂ))
      = fun t => (inner ℂ (x : H) (U (-t) (y : H)) : ℂ) := by
    funext t
    rw [← hUinner t (x : H) (U (-t) (y : H)), ← ContinuousLinearMap.comp_apply, ← hgrp t (-t),
      add_neg_cancel, hU0, ContinuousLinearMap.one_apply]
  have h1 := HasDerivAt.inner ℂ (hasDerivAt_stoneGen U x) (hasDerivAt_const (0 : ℝ) (y : H))
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) (x : H)) (hasDerivAt_stoneGen_neg U y)
  rw [hrel] at h1
  have hkey := h1.unique h2
  simp only [inner_zero_right, inner_zero_left, add_zero, zero_add] at hkey
  rw [inner_smul_left, inner_neg_right, inner_smul_right, Complex.conj_I] at hkey
  have : (-Complex.I) * (inner ℂ (stoneGen U x) (y : H) : ℂ)
      = (-Complex.I) * (inner ℂ (x : H) (stoneGen U y) : ℂ) := by linear_combination hkey
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) this

/-- **The generator is a formal adjoint of itself** (a *symmetric* unbounded operator in Mathlib's
    `LinearPMap` framework): `(stoneGen U).IsFormalAdjoint (stoneGen U)` for a one-parameter unitary group.
    Equivalently `stoneGen U ⊆ (stoneGen U)†` once the domain is dense — the `A ⊆ A*` relation that
    self-adjointness `Ā = Ā*` is built on (Phase 3.2). -/
theorem stoneGen_isFormalAdjoint_self (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) :
    (stoneGen U).IsFormalAdjoint (stoneGen U) :=
  fun x y => stoneGen_symmetric U hgrp hU0 hUinner x y

/-- Auxiliary: for the symmetric generator, the cross term `re⟪A x, i • x⟫ = 0`. (`⟪A x, x⟫` is real by
    symmetry; multiplying by `i` rotates it to the imaginary axis.) The cancellation behind the Cayley
    estimate. -/
theorem stoneGen_re_inner_smul_I (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : stoneDomain U) :
    RCLike.re (Complex.I * (inner ℂ (stoneGen U x) (x : H) : ℂ)) = 0 := by
  have hsym : (inner ℂ (stoneGen U x) (x : H) : ℂ) = inner ℂ (x : H) (stoneGen U x) :=
    stoneGen_symmetric U hgrp hU0 hUinner x x
  have h : (starRingEnd ℂ) (inner ℂ (stoneGen U x) (x : H)) = inner ℂ (stoneGen U x) (x : H) :=
    (inner_conj_symm (x : H) (stoneGen U x)).trans hsym.symm
  have hreal : RCLike.im (inner ℂ (stoneGen U x) (x : H) : ℂ) = 0 := RCLike.conj_eq_iff_im.mp h
  rw [show (Complex.I : ℂ) = RCLike.I from rfl, RCLike.I_mul_re, hreal, neg_zero]

/-- **The Cayley estimate** `‖(A + i) x‖² = ‖A x‖² + ‖x‖²` for the symmetric generator. The cross term
    vanishes (`stoneGen_re_inner_smul_I`). This bounds `A + i` below (`‖(A+i)x‖ ≥ ‖x‖`), so it is *injective*
    — the entry point to the Cayley transform `(A−i)(A+i)⁻¹` and the deficiency-index criterion for essential
    self-adjointness (Phase 3.2/3.3). -/
theorem stoneGen_norm_add_smul_I_sq (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : stoneDomain U) :
    ‖stoneGen U x + Complex.I • (x : H)‖ ^ 2 = ‖stoneGen U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right,
    stoneGen_re_inner_smul_I U hgrp hU0 hUinner x, norm_smul, Complex.norm_I, one_mul]
  ring

/-- **The Cayley estimate** `‖(A − i) x‖² = ‖A x‖² + ‖x‖²` — the `A − i` companion bounding `A − i` below,
    hence injective. Together with `stoneGen_norm_add_smul_I_sq` this is the deficiency-index pair for the
    Cayley transform / essential self-adjointness (Phase 3.2/3.3). -/
theorem stoneGen_norm_sub_smul_I_sq (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : stoneDomain U) :
    ‖stoneGen U x - Complex.I • (x : H)‖ ^ 2 = ‖stoneGen U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right,
    stoneGen_re_inner_smul_I U hgrp hU0 hUinner x, norm_smul, Complex.norm_I, one_mul]
  ring

/-- **The Cayley transform is isometric on the range:** `‖(A − i) x‖ = ‖(A + i) x‖`. Both sides equal
    `√(‖A x‖² + ‖x‖²)` (the two Cayley estimates), so the map `V : (A + i) x ↦ (A − i) x` is norm-preserving —
    the defining property of the Cayley transform `V = (A−i)(A+i)⁻¹` (an isometry `Range(A+i) → Range(A−i)`;
    it is *unitary*, hence `A` essentially self-adjoint, exactly when both ranges are dense — Phase 3.3). -/
theorem stoneGen_norm_cayley_eq (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : stoneDomain U) :
    ‖stoneGen U x - Complex.I • (x : H)‖ = ‖stoneGen U x + Complex.I • (x : H)‖ := by
  have hsq : ‖stoneGen U x - Complex.I • (x : H)‖ ^ 2
      = ‖stoneGen U x + Complex.I • (x : H)‖ ^ 2 := by
    rw [stoneGen_norm_sub_smul_I_sq U hgrp hU0 hUinner x,
      stoneGen_norm_add_smul_I_sq U hgrp hU0 hUinner x]
  have := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- **`A + i` is bounded below:** `‖x‖ ≤ ‖(A + i) x‖` (from the Cayley estimate, `‖Ax‖² ≥ 0`). Hence `A + i` is
    *injective* on the smooth domain — half of the deficiency-index data for essential self-adjointness. -/
theorem stoneGen_norm_le_norm_add_smul_I (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : stoneDomain U) :
    ‖(x : H)‖ ≤ ‖stoneGen U x + Complex.I • (x : H)‖ := by
  have hsq : ‖(x : H)‖ ^ 2 ≤ ‖stoneGen U x + Complex.I • (x : H)‖ ^ 2 := by
    rw [stoneGen_norm_add_smul_I_sq U hgrp hU0 hUinner x]
    nlinarith [sq_nonneg ‖stoneGen U x‖]
  have h2 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- `(stoneGen U).domain`-stated form of the Cayley estimate — identical content to
    `stoneGen_norm_add_smul_I_sq` but with `x` typed via the `LinearPMap.domain` projection. This is the form
    needed to *instantiate* the estimate at a concrete heavy type (e.g. `Lp`) under
    `attribute [local irreducible] stoneGen`, where `stoneDomain U` and `(stoneGen U).domain` are no longer
    defeq-interchangeable. -/
theorem stoneGen_norm_add_smul_I_sq_dom (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : (stoneGen U).domain) :
    ‖stoneGen U x + Complex.I • (x : H)‖ ^ 2 = ‖stoneGen U x‖ ^ 2 + ‖(x : H)‖ ^ 2 :=
  stoneGen_norm_add_smul_I_sq U hgrp hU0 hUinner x

/-- `(stoneGen U).domain`-stated form of the bounded-below bound `‖x‖ ≤ ‖(A + i) x‖` (see
    `stoneGen_norm_add_smul_I_sq_dom` for why the projection-typed form). -/
theorem stoneGen_norm_le_norm_add_smul_I_dom (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b) (x : (stoneGen U).domain) :
    ‖(x : H)‖ ≤ ‖stoneGen U x + Complex.I • (x : H)‖ :=
  stoneGen_norm_le_norm_add_smul_I U hgrp hU0 hUinner x

/-- **`A ⊆ A†` for the Stone generator** — the explicit symmetric-operator containment, conditional on
    `hdense`, the density of the smooth domain (Gårding density, the genuine open analytic frontier of
    Phase 3.2). Given that density, the generator is contained in its `LinearPMap` adjoint:
    `stoneGen U ≤ (stoneGen U)†`. This is the precise statement on which self-adjointness `Ā = Ā†`
    rests — essential self-adjointness then upgrades `⊆` to `=` on the closure. The density hypothesis
    is left explicit and undischarged: proving `Dense (stoneGen U).domain` for the concrete C₀ groups
    (the Gårding/mollified-vector argument) is the Mathlib-grade wall, honestly carried here. -/
theorem stoneGen_le_adjoint [CompleteSpace H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hdense : Dense ((stoneGen U).domain : Set H)) :
    stoneGen U ≤ (stoneGen U).adjoint :=
  (stoneGen_isFormalAdjoint_self U hgrp hU0 hUinner).le_adjoint (hT := hdense)

end Symmetry

end QIQTH.Spectral
