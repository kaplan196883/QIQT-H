/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall — the fiberwise (bulk) modular flow `Δ̂^{it}` on `L²(ℝ; H)` (toward Increment 1c)

The dressed JLMS modular Hamiltonian `K̃ = K_bulk + A_edge·(1/4ℓ_P²)` is the Stone generator of the product of
two **commuting** one-parameter unitary groups on the crossed-product space `L²(ℝ; H)`: the **clock** group
`λ_t = clockTransl t` (base-shift `s ↦ s + t`, generator `X = A_edge`, `CrossedProductGenerator.lean`) and the
**fiberwise bulk modular** group `Δ̂^{it}` (postcompose each fiber with the one-particle modular flow
`Δ^{it} = modUnitary S t`, generator `K_bulk`).  The abstract "sum of commuting self-adjoint generators is
self-adjoint" is `QIQTH/Spectral/StoneProduct.lean` (`stoneGen_prod_isSelfAdjoint`); this module supplies the
**fiberwise group `Δ̂^{it} := (modUnitary S t).compLpL 2 volume`** and the structural hypotheses it needs.

Delivered here (axiom-free): the group law `Δ̂^{i(s+t)} = Δ̂^{is} ∘ Δ̂^{it}`, `Δ̂^{i·0} = 1`, the contraction
`‖Δ̂^{it} ξ‖ ≤ ‖ξ‖` (from `‖Δ^{it}‖ ≤ 1`), and — the key compatibility — **`Δ̂^{it}` commutes with the clock
group `λ_s`** (fiberwise postcomposition commutes with the measure-preserving base-shift).  So the two summands
of `K̃` strongly commute, the hypothesis `stoneGen_prod_isSelfAdjoint` consumes.

HONEST scope: the two remaining C₀-group hypotheses of `Δ̂^{it}` — inner-product preservation (unitarity on
`L²(ℝ;H)`, via the fiber integral) and strong continuity (via dominated convergence on `Lp`) — are the labelled
analytic steps to *assemble* the full dressed-generator self-adjointness (`stoneGen (Δ̂^{i·} ∘ λ_·)` self-adjoint)
from `stoneGen_prod_isSelfAdjoint`.  Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).  No `sorry`.
-/
import QIQTH.StandardSubspaceModularFlow
import QIQTH.CrossedProductTranslation
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The fiberwise (bulk) modular flow `Δ̂^{it}`** on `L²(ℝ; H)`: postcompose each fiber with the one-particle
modular flow `Δ^{it} = modUnitary S t` (Mathlib's `compLpL`).  The generator is the bulk modular Hamiltonian
`K_bulk`; together with the clock energy `X = A_edge` it forms the dressed `K̃`. -/
noncomputable def fiberModFlow (S : StandardSubspace H) (t : ℝ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (modUnitary S t).compLpL 2 volume

/-- The fiber: `(Δ̂^{it} ξ)(s) = Δ^{it}(ξ s)` a.e. -/
theorem fiberModFlow_coeFn (S : StandardSubspace H) (t : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    fiberModFlow S t ξ =ᵐ[volume] fun s => modUnitary S t (ξ s) :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- **`Δ̂^{i·0} = 1`.** -/
theorem fiberModFlow_zero (S : StandardSubspace H) :
    (fiberModFlow S 0 : Lp H 2 (volume : Measure ℝ) →L[ℂ] _) = 1 := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.one_apply, Lp.ext_iff]
  filter_upwards [fiberModFlow_coeFn S 0 ξ] with u e1
  rw [e1, modUnitary_zero, ContinuousLinearMap.one_apply]

/-- **The one-parameter group law** `Δ̂^{i(s+t)} = Δ̂^{is} ∘ Δ̂^{it}` (from the one-particle group law
`modUnitary_add` + functoriality of fiberwise postcomposition). -/
theorem fiberModFlow_add (S : StandardSubspace H) (s t : ℝ) :
    (fiberModFlow S (s + t) : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = fiberModFlow S s ∘L fiberModFlow S t := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, Lp.ext_iff]
  filter_upwards [fiberModFlow_coeFn S (s + t) ξ,
    fiberModFlow_coeFn S s (fiberModFlow S t ξ), fiberModFlow_coeFn S t ξ] with u e1 e2 e3
  rw [e1, e2, e3, modUnitary_add]
  rfl

/-- **The fiberwise modular flow is a contraction** `‖Δ̂^{it} ξ‖ ≤ ‖ξ‖` (since `‖Δ^{it}‖ ≤ 1`). -/
theorem fiberModFlow_norm_le (S : StandardSubspace H) (t : ℝ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    ‖fiberModFlow S t ξ‖ ≤ ‖ξ‖ := by
  have hop : ‖modUnitary S t‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact le_of_eq (modUnitary_norm S t x)
  have h1 : ‖fiberModFlow S t‖ ≤ 1 :=
    le_trans (ContinuousLinearMap.norm_compLpL_le _) hop
  calc ‖fiberModFlow S t ξ‖ ≤ ‖fiberModFlow S t‖ * ‖ξ‖ := (fiberModFlow S t).le_opNorm ξ
    _ ≤ 1 * ‖ξ‖ := by gcongr
    _ = ‖ξ‖ := one_mul _

/-- The one-particle modular flow preserves the inner product (unitary): `⟪Δ^{it} x, Δ^{it} y⟫ = ⟪x, y⟫`
(from `Δ^{it}⋆ = Δ^{-it}` and the group law). -/
theorem modUnitary_inner (S : StandardSubspace H) (t : ℝ) (x y : H) :
    (inner ℂ (modUnitary S t x) (modUnitary S t y) : ℂ) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right, modUnitary_adjoint,
    ← ContinuousLinearMap.mul_apply, ← modUnitary_add, neg_add_cancel, modUnitary_zero,
    ContinuousLinearMap.one_apply]

/-- **The fiberwise modular flow preserves the `L²(ℝ; H)` inner product** (unitarity): `⟪Δ̂^{it} a, Δ̂^{it} b⟫ =
⟪a, b⟫`, from the fiber integral `⟪f, g⟫ = ∫ ⟪f s, g s⟫ ds` and the one-particle unitarity `modUnitary_inner`.
The `hAinner` C₀-unitary-group hypothesis of `Δ̂^{it}` for `stoneGen_prod_isSelfAdjoint`. -/
theorem fiberModFlow_inner (S : StandardSubspace H) (t : ℝ) (a b : Lp H 2 (volume : Measure ℝ)) :
    (inner ℂ (fiberModFlow S t a) (fiberModFlow S t b) : ℂ) = inner ℂ a b := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fiberModFlow_coeFn S t a, fiberModFlow_coeFn S t b] with s e1 e2
  rw [e1, e2, modUnitary_inner]

/-- **★ The fiberwise modular flow commutes with the clock group:** `Δ̂^{it} ∘ λ_s = λ_s ∘ Δ̂^{it}`.  Postcomposing
each fiber with `Δ^{it}` and shifting the base argument by `s` act on different "slots" (the `H`-fiber value vs
the `ℝ`-base point), so they commute.  This is the **strong-commutativity** hypothesis the dressed-generator
self-adjointness (`stoneGen_prod_isSelfAdjoint`, Increment 1c) consumes: `K_bulk` and `A_edge` strongly commute. -/
theorem fiberModFlow_comm_clockTransl (S : StandardSubspace H) (t s : ℝ) :
    (fiberModFlow S t ∘L clockTransl s : Lp H 2 (volume : Measure ℝ) →L[ℂ] _)
      = clockTransl s ∘L fiberModFlow S t := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, Lp.ext_iff]
  -- RHS reindex: `(λ_s (Δ̂ ξ))(u) = (Δ̂ ξ)(u + s) =ᵐ Δ^{it}(ξ(u + s))`
  have hmap : Measure.map (· + s) (volume : Measure ℝ) = volume :=
    (measurePreserving_addRight_volume s).map_eq
  have hco : fiberModFlow S t ξ =ᵐ[Measure.map (· + s) volume] fun v => modUnitary S t (ξ v) := by
    simp only [hmap]; exact fiberModFlow_coeFn S t ξ
  have h3' : (fun u => (fiberModFlow S t ξ) (u + s)) =ᵐ[volume]
      fun u => modUnitary S t (ξ (u + s)) :=
    ae_eq_comp (measurePreserving_addRight_volume s).measurable.aemeasurable hco
  filter_upwards [fiberModFlow_coeFn S t (clockTransl s ξ), clockTransl_coeFn s ξ,
    clockTransl_coeFn s (fiberModFlow S t ξ), h3'] with u e1 e2 e3 e4
  -- LHS: (Δ̂ (λ_s ξ))(u) = Δ^{it}((λ_s ξ)(u)) = Δ^{it}(ξ(u+s));  RHS: (λ_s (Δ̂ ξ))(u) = Δ^{it}(ξ(u+s))
  rw [e1, e2, e3, e4]

end QIQTH.StandardSubspaceModular
