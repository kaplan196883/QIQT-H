/-
  THE REPRESENTATION R6 (THE_REPRESENTATION_PLAN.md) — THE BOUNDED PRE-OPERATOR.

  Left multiplication by a corner element `a` at stage `C₀`, acting on the whole tower
  pre-space: each component `x` at stage `C` goes to `of (C₀ ⊔ C) (ι a · ι x)` — the raw
  linear map `leftMulRaw`, its collapse compatibility `collapse_leftMul` (collapsing the
  image at `C₀ ⊔ K` is left multiplication by the embedded `a` after collapsing at `C₀ ⊔ K`),
  and the NORM BOUND `leftMulRaw_norm_le`:

      ‖π₀(a) x‖ ≤ √(frobNormSq a) · ‖x‖,

  by stage collapse + R5's GNS boundedness inequality. `LinearMap.mkContinuous` then packages
  the CONTINUOUS pre-operator `towerLeftMul : TowerPre →L[ℂ] TowerPre`, ready for R7's
  extension to the completion.

  HONEST SCOPE: the constant is the FROBENIUS (Hilbert–Schmidt) norm — π is proved BOUNDED,
  never claimed contractive; no C*-norm bound `‖π(a)‖ ≤ ‖a‖` is stated.

  LEAN ARCHITECTURE (the R3 lesson, binding): all working lemmas live at the RAW
  `⨁ C : Finset M, DiamondAlg L C` type (`leftMulRaw`, `collapse_leftMul`, and the re-inner
  inequality `leftMulRaw_re_inner_le`); the `TowerPre`-typed items (`towerLeftMulₗ`,
  `leftMulRaw_norm_le`, `towerLeftMul`) are final wrappers accepted by application-position
  definitional equality — never `rw` across the synonym.
-/
import Mathlib
import QIQTH.TowerGNS.StageBound

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The raw pre-operator -/

/-- **The raw left-multiplication pre-operator**: the component at stage `C` is embedded into
    `C₀ ⊔ C` and multiplied on the left by the embedded `a` — the GNS action of the corner
    element `a`, at the raw direct sum. -/
noncomputable def leftMulRaw (C₀ : Finset M) (a : DiamondAlg L C₀) :
    (⨁ C : Finset M, DiamondAlg L C) →ₗ[ℂ] (⨁ C : Finset M, DiamondAlg L C) :=
  DirectSum.toModule ℂ (Finset M) (⨁ C : Finset M, DiamondAlg L C) fun C =>
    (DirectSum.lof ℂ (Finset M) (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)) ∘ₗ
      (LinearMap.mulLeft ℂ (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a)) ∘ₗ
        (cornerEmbedₗ L C (C₀ ⊔ C) Finset.subset_union_right)

@[simp] theorem leftMulRaw_of (C₀ : Finset M) (a : DiamondAlg L C₀) (C : Finset M)
    (x : DiamondAlg L C) :
    leftMulRaw L C₀ a (DirectSum.of _ C x)
      = DirectSum.of (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)
          (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a
            * cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right x) := by
  rw [← DirectSum.lof_eq_of ℂ, leftMulRaw]
  erw [DirectSum.toModule_lof]
  rfl

/-! ### Collapse compatibility -/

/-- **The collapse of the image**: collapsing `leftMulRaw a x` at the stage `C₀ ⊔ K` is left
    multiplication by the embedded `a` after collapsing `x` there — the pre-operator is the
    honest left multiplication in every sufficiently large corner. -/
theorem collapse_leftMul (C₀ : Finset M) (a : DiamondAlg L C₀) (K : Finset M)
    (x : ⨁ C : Finset M, DiamondAlg L C) (hx : ∀ C, x C ≠ 0 → C ⊆ K) :
    collapseRaw L (C₀ ⊔ K) (leftMulRaw L C₀ a x)
      = cornerEmbed L C₀ (C₀ ⊔ K) Finset.subset_union_left a
          * collapseRaw L (C₀ ⊔ K) x := by
  classical
  have hxsum : x = ∑ C ∈ DFinsupp.support x, DirectSum.of _ C (x C) :=
    (DirectSum.sum_support_of x).symm
  rw [hxsum]
  rw [map_sum (leftMulRaw L C₀ a) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
  rw [map_sum (collapseRaw L (C₀ ⊔ K))
    (fun C => leftMulRaw L C₀ a (DirectSum.of _ C (x C))) (DFinsupp.support x)]
  rw [map_sum (collapseRaw L (C₀ ⊔ K)) (fun C => DirectSum.of _ C (x C))
    (DFinsupp.support x)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCK : C ⊆ K := hx C (DFinsupp.mem_support_iff.mp hC)
  have hsub : C₀ ⊔ C ⊆ C₀ ⊔ K := Finset.union_subset_union_right hCK
  have hCsub : C ⊆ C₀ ⊔ K := hCK.trans Finset.subset_union_right
  rw [leftMulRaw_of, collapseRaw_of_le L hsub, collapseRaw_of_le L hCsub,
    cornerEmbed_mul, cornerEmbed_trans L C₀ (C₀ ⊔ C) (C₀ ⊔ K),
    cornerEmbed_trans L C (C₀ ⊔ C) (C₀ ⊔ K)]

/-! ### The re-inner inequality (R5 fed through the collapse — all raw) -/

/-- **R6 KEY (raw)**: the tower form of the pre-operator image is dominated by the Frobenius
    constant times the form of the argument — stage collapse at `C₀ ⊔ K` plus R5's GNS
    boundedness inequality. -/
theorem leftMulRaw_re_inner_le (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    RCLike.re (rawInner L ω β (leftMulRaw L C₀ a x) (leftMulRaw L C₀ a x))
      ≤ frobNormSq L C₀ a * RCLike.re (rawInner L ω β x x) := by
  classical
  set K : Finset M := (DFinsupp.support x).sup id with hK
  have hx : ∀ C, x C ≠ 0 → C ⊆ K := fun C hC =>
    Finset.le_sup (f := id) (DFinsupp.mem_support_iff.mpr hC)
  have hxK : ∀ C, x C ≠ 0 → C ⊆ C₀ ⊔ K := fun C hC =>
    (hx C hC).trans Finset.subset_union_right
  -- the image is supported under `C₀ ⊔ K`
  have hTx : leftMulRaw L C₀ a x
      = ∑ C ∈ DFinsupp.support x,
          DirectSum.of (fun C : Finset M => DiamondAlg L C) (C₀ ⊔ C)
            (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left a
              * cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right (x C)) := by
    conv_lhs => rw [← DirectSum.sum_support_of x]
    rw [map_sum (leftMulRaw L C₀ a) (fun C => DirectSum.of _ C (x C)) (DFinsupp.support x)]
    exact Finset.sum_congr rfl fun C _ => leftMulRaw_of L C₀ a C (x C)
  have hx' : ∀ C', (leftMulRaw L C₀ a x) C' ≠ 0 → C' ⊆ C₀ ⊔ K := by
    intro C' hC'
    by_contra hnot
    apply hC'
    rw [hTx]
    erw [DFinsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun C hC => ?_
    refine DirectSum.of_eq_of_ne _ _ _ fun he => hnot ?_
    rw [he]
    exact Finset.union_subset_union_right (hx C (DFinsupp.mem_support_iff.mp hC))
  rw [rawInner_eq_collapse L ω β (C₀ ⊔ K) _ _ hx' hx',
    rawInner_eq_collapse L ω β (C₀ ⊔ K) x x hxK hxK,
    collapse_leftMul L C₀ a K x hx]
  exact gnsInner_leftMul_le L ω β C₀ (C₀ ⊔ K) Finset.subset_union_left a
    (collapseRaw L (C₀ ⊔ K) x)

/-! ### The synonym wrappers (application-position defeq only — the R3 lesson) -/

/-- The pre-operator at the synonym, as a plain linear map (fields delegate to the raw map by
    definitional equality). -/
noncomputable def towerLeftMulₗ (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerPre L ω β →ₗ[ℂ] TowerPre L ω β where
  toFun x := leftMulRaw L C₀ a x
  map_add' x y := (leftMulRaw L C₀ a).map_add x y
  map_smul' r x := (leftMulRaw L C₀ a).map_smul r x

@[simp] theorem towerLeftMulₗ_apply (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : TowerPre L ω β) :
    towerLeftMulₗ L ω β C₀ a x = leftMulRaw L C₀ a x := rfl

/-- **R6 — the norm bound**: the pre-operator is bounded on the tower seminorm with the
    Frobenius constant of R5 — `‖π₀(a) x‖ ≤ √(frobNormSq a) · ‖x‖`. (Frobenius bound, NOT
    the C*-norm — π is bounded, never claimed contractive.) -/
theorem leftMulRaw_norm_le (C₀ : Finset M) (a : DiamondAlg L C₀) (x : TowerPre L ω β) :
    ‖towerLeftMulₗ L ω β C₀ a x‖ ≤ Real.sqrt (frobNormSq L C₀ a) * ‖x‖ := by
  have key := leftMulRaw_re_inner_le L ω β C₀ a x
  have hsq : ‖towerLeftMulₗ L ω β C₀ a x‖ ^ 2 ≤ frobNormSq L C₀ a * ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (towerLeftMulₗ L ω β C₀ a x),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) x]
    exact key
  calc ‖towerLeftMulₗ L ω β C₀ a x‖
      = Real.sqrt (‖towerLeftMulₗ L ω β C₀ a x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (frobNormSq L C₀ a * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (frobNormSq L C₀ a) * Real.sqrt (‖x‖ ^ 2) :=
        Real.sqrt_mul (frobNormSq_nonneg L C₀ a) _
    _ = Real.sqrt (frobNormSq L C₀ a) * ‖x‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

/-- **R6 CAPSTONE — the bounded pre-operator**: left multiplication by the corner element `a`
    as a CONTINUOUS linear map on the tower pre-space, with the Frobenius constant
    `√(frobNormSq a)` (bounded, never claimed contractive). R7 extends it to the
    completion. -/
noncomputable def towerLeftMul (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerPre L ω β →L[ℂ] TowerPre L ω β :=
  LinearMap.mkContinuous (towerLeftMulₗ L ω β C₀ a) (Real.sqrt (frobNormSq L C₀ a))
    fun x => leftMulRaw_norm_le L ω β C₀ a x

@[simp] theorem towerLeftMul_apply (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x : TowerPre L ω β) :
    towerLeftMul L ω β C₀ a x = leftMulRaw L C₀ a x := rfl

end QIQTH.TowerGNS
