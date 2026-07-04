/-
  THE REPRESENTATION R7 (THE_REPRESENTATION_PLAN.md) — towerRep, the compatible ⋆-representation.

  The bounded pre-operator `towerLeftMul` (R6) is lifted to the completion by
  `ContinuousLinearMap.completion` (the GNS-file recipe, binding verdict), and the lifts are
  bundled into the unital ⋆-algebra homomorphism

      towerRep C₀ : DiamondAlg C₀ →⋆ₐ[ℂ] (TowerGNS →L[ℂ] TowerGNS).

  THE ALGEBRA LAWS LIVE IN THE COMPLETION, NOT THE PRE-SPACE: at the pre-level,
  `leftMulRaw C₀ 1 (of C x) = of (C₀ ⊔ C) (ι x) ≠ of C x` and
  `leftMulRaw (a*b)` lands at stage `C₀ ⊔ C` while `leftMulRaw a ∘ leftMulRaw b` lands at
  `C₀ ⊔ (C₀ ⊔ C)` — the identities are FALSE as pre-space equations and become true only after
  the germ identity (R4) glues the stages in the completion. Additivity and ℂ-homogeneity in
  the algebra element DO hold at the pre-level (same stage) and are proved raw.

  The ⋆-law is the adjoint relation ⟪π(aᴴ)x, y⟫ = ⟪x, π(a)y⟫, proved raw at a common deep
  stage (R1 functoriality + the ⋆/mul embedding laws + `mul_assoc` under the state), then
  transported by `ContinuousLinearMap.eq_adjoint_iff` + double completion induction.

  CAPSTONE — COMPATIBILITY: `towerRep C' (ι a) = towerRep C a`: the representation of a corner
  element does not depend on the stage through which it is presented — the tower of finite
  corners acts coherently on ONE Hilbert space.

  LEAN ARCHITECTURE (the R3 lesson, binding): the DirectSum inductions run at the RAW `⨁` type
  (`towerCoe` wraps the synonym coercion so raw vectors can be stated in the completion);
  completion-level proofs use the GNS-file incantations verbatim
  (`UniformSpace.Completion.induction_on` with `isClosed_eq <;> fun_prop`); the synonym is
  crossed only in application position, never by `rw`.
-/
import Mathlib
import QIQTH.TowerGNS.Germ
import QIQTH.TowerGNS.LeftMul

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### Pre-level algebra laws in the ALGEBRA slot (same stage — these DO hold raw).

    NOTE: `map_one` and `map_mul` are deliberately ABSENT here: they are false at the
    pre-space level (the stages differ) and hold only in the completion via `towerGerm`. -/

/-- Additivity of the pre-operator in the algebra element (componentwise — SAME stage). -/
theorem leftMulRaw_add_left (C₀ : Finset M) (a b : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    leftMulRaw L C₀ (a + b) x = leftMulRaw L C₀ a x + leftMulRaw L C₀ b x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | of C v =>
    rw [leftMulRaw_of, leftMulRaw_of, leftMulRaw_of, cornerEmbed_add, add_mul, map_add]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, h₁, h₂, add_add_add_comm]

/-- ℂ-homogeneity of the pre-operator in the algebra element (componentwise — SAME stage). -/
theorem leftMulRaw_smul_left (C₀ : Finset M) (r : ℂ) (a : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    leftMulRaw L C₀ (r • a) x = r • leftMulRaw L C₀ a x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | of C v =>
    rw [leftMulRaw_of, leftMulRaw_of, cornerEmbed_smul, smul_mul_assoc,
      ← DirectSum.lof_eq_of ℂ, ← DirectSum.lof_eq_of ℂ, map_smul]
  | add x₁ x₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]

/-- The pre-operator of the zero algebra element is zero. -/
theorem leftMulRaw_zero_left (C₀ : Finset M) (x : ⨁ C : Finset M, DiamondAlg L C) :
    leftMulRaw L C₀ (0 : DiamondAlg L C₀) x = 0 := by
  have h := leftMulRaw_smul_left L C₀ (0 : ℂ) 0 x
  rw [zero_smul, zero_smul] at h
  exact h

/-! ### The raw adjoint relation (the ⋆-law before completion) -/

/-- **The raw adjoint relation**: `⟪π₀(aᴴ) x, y⟫ = ⟪x, π₀(a) y⟫` at the raw direct sum —
    both sides collapse to a common deep stage (R2 stability), where the embeddings push
    through ⋆ and mul (R1 + T7) and the identity is `mul_assoc` under the Gibbs state. -/
theorem rawInner_leftMulRaw_conjTranspose (C₀ : Finset M) (a : DiamondAlg L C₀)
    (x y : ⨁ C : Finset M, DiamondAlg L C) :
    rawInner L ω β (leftMulRaw L C₀ aᴴ x) y = rawInner L ω β x (leftMulRaw L C₀ a y) := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (leftMulRaw L C₀ aᴴ), map_zero (rawInner L ω β),
      AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  | of C v =>
    induction y using DirectSum.induction_on with
    | zero =>
      rw [map_zero (leftMulRaw L C₀ a),
        map_zero (rawInner L ω β (leftMulRaw L C₀ aᴴ (DirectSum.of _ C v))),
        map_zero (rawInner L ω β (DirectSum.of _ C v))]
    | of C' w =>
      rw [leftMulRaw_of, leftMulRaw_of, rawInner_of_of, rawInner_of_of]
      have hC₀K : C₀ ⊆ C₀ ⊔ (C ⊔ C') := Finset.subset_union_left
      have hCK : C ⊆ C₀ ⊔ (C ⊔ C') :=
        Finset.subset_union_left.trans Finset.subset_union_right
      have hC'K : C' ⊆ C₀ ⊔ (C ⊔ C') :=
        Finset.subset_union_right.trans Finset.subset_union_right
      rw [pairInner_embed L ω β (C₀ ⊔ C) C' (C₀ ⊔ (C ⊔ C'))
          (Finset.union_subset hC₀K hCK) hC'K,
        pairInner_embed L ω β C (C₀ ⊔ C') (C₀ ⊔ (C ⊔ C'))
          hCK (Finset.union_subset hC₀K hC'K)]
      simp only [cornerEmbed_mul, cornerEmbed_trans]
      rw [cornerEmbed_star, gnsInner_def, gnsInner_def, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add (leftMulRaw L C₀ a),
        map_add (rawInner L ω β (leftMulRaw L C₀ aᴴ (DirectSum.of _ C v))),
        map_add (rawInner L ω β (DirectSum.of _ C v)), h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (leftMulRaw L C₀ aᴴ), map_add (rawInner L ω β), AddMonoidHom.add_apply,
      map_add (rawInner L ω β), AddMonoidHom.add_apply, h₁, h₂]

/-! ### The synonym-coercion wrapper (raw vectors stated in the completion) -/

/-- The canonical coercion of a pre-space vector into the tower Hilbert space, wrapped as a
    definition so that RAW `⨁`-typed vectors can be fed in application position (the R3
    lesson: type ascription does not retype for instances — wrap). -/
noncomputable def towerCoe (x : TowerPre L ω β) : TowerGNS L ω β := x

theorem towerCoe_def (x : TowerPre L ω β) : towerCoe L ω β x = (x : TowerGNS L ω β) := rfl

/-- The wrapped coercion is additive (stated for RAW vectors — raw `+` inside). -/
theorem towerCoe_add_raw (u v : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (u + v) = towerCoe L ω β u + towerCoe L ω β v :=
  UniformSpace.Completion.coe_add (α := TowerPre L ω β) u v

/-- The wrapped coercion is ℂ-homogeneous (stated for RAW vectors — raw `•` inside). -/
theorem towerCoe_smul_raw (r : ℂ) (u : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (r • u) = r • towerCoe L ω β u :=
  UniformSpace.Completion.coe_smul (X := TowerPre L ω β) r u

/-! ### The germ-reconciled completion identities (raw induction + towerGerm) -/

/-- **Unitality in the completion**: `↑(π₀(1) x) = ↑x` — at the pre-level the image lands at
    the DEEPER stage `C₀ ⊔ C`; the germ identity glues it back. -/
theorem towerCoe_leftMulRaw_one (C₀ : Finset M) (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (leftMulRaw L C₀ (1 : DiamondAlg L C₀) x) = towerCoe L ω β x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero]
  | of C v =>
    rw [leftMulRaw_of, cornerEmbed_one, one_mul]
    exact towerGerm L ω β Finset.subset_union_right v
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, towerCoe_add_raw, towerCoe_add_raw, h₁, h₂]

/-- **Multiplicativity in the completion**: `↑(π₀(ab) x) = ↑(π₀(a) (π₀(b) x))` — the two sides
    land at stages `C₀ ⊔ C` and `C₀ ⊔ (C₀ ⊔ C)`; R1 functoriality reconciles the matrices at
    the deep stage and the germ identity glues. -/
theorem towerCoe_leftMulRaw_mul (C₀ : Finset M) (a b : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (leftMulRaw L C₀ (a * b) x)
      = towerCoe L ω β (leftMulRaw L C₀ a (leftMulRaw L C₀ b x)) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of C v =>
    rw [leftMulRaw_of, leftMulRaw_of, leftMulRaw_of]
    have hDE : C₀ ⊔ C ⊆ C₀ ⊔ (C₀ ⊔ C) := Finset.subset_union_right
    have hmat : cornerEmbed L C₀ (C₀ ⊔ (C₀ ⊔ C)) Finset.subset_union_left a
          * cornerEmbed L (C₀ ⊔ C) (C₀ ⊔ (C₀ ⊔ C)) Finset.subset_union_right
              (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left b
                * cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right v)
        = cornerEmbed L (C₀ ⊔ C) (C₀ ⊔ (C₀ ⊔ C)) hDE
            (cornerEmbed L C₀ (C₀ ⊔ C) Finset.subset_union_left (a * b)
              * cornerEmbed L C (C₀ ⊔ C) Finset.subset_union_right v) := by
      simp only [cornerEmbed_mul, cornerEmbed_trans, mul_assoc]
    rw [hmat]
    exact (towerGerm L ω β hDE _).symm
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, towerCoe_add_raw, towerCoe_add_raw, h₁, h₂]

/-- Additivity, coerced (pre-level law + coe additivity). -/
theorem towerCoe_leftMulRaw_add (C₀ : Finset M) (a b : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (leftMulRaw L C₀ (a + b) x)
      = towerCoe L ω β (leftMulRaw L C₀ a x) + towerCoe L ω β (leftMulRaw L C₀ b x) := by
  rw [leftMulRaw_add_left, towerCoe_add_raw]

/-- ℂ-homogeneity, coerced (pre-level law + coe homogeneity). -/
theorem towerCoe_leftMulRaw_smul (C₀ : Finset M) (r : ℂ) (a : DiamondAlg L C₀)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    towerCoe L ω β (leftMulRaw L C₀ (r • a) x)
      = r • towerCoe L ω β (leftMulRaw L C₀ a x) := by
  rw [leftMulRaw_smul_left, towerCoe_smul_raw]

/-- **Stage compatibility in the completion**: acting by the embedded element `ι a` at stage
    `C'` equals acting by `a` at stage `C` — the matrices agree at the common deep stage
    `C' ⊔ C''` and the germ identity glues. -/
theorem towerCoe_leftMulRaw_cornerEmbed (C C' : Finset M) (h : C ⊆ C') (a : DiamondAlg L C)
    (x : ⨁ C'' : Finset M, DiamondAlg L C'') :
    towerCoe L ω β (leftMulRaw L C' (cornerEmbed L C C' h a) x)
      = towerCoe L ω β (leftMulRaw L C a x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of C'' v =>
    rw [leftMulRaw_of, leftMulRaw_of]
    have h'' : C ⊔ C'' ⊆ C' ⊔ C'' := Finset.union_subset_union h subset_rfl
    have hmat : cornerEmbed L C' (C' ⊔ C'') Finset.subset_union_left
            (cornerEmbed L C C' h a)
          * cornerEmbed L C'' (C' ⊔ C'') Finset.subset_union_right v
        = cornerEmbed L (C ⊔ C'') (C' ⊔ C'') h''
            (cornerEmbed L C (C ⊔ C'') Finset.subset_union_left a
              * cornerEmbed L C'' (C ⊔ C'') Finset.subset_union_right v) := by
      simp only [cornerEmbed_mul, cornerEmbed_trans]
    rw [hmat]
    exact towerGerm L ω β h'' _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, map_add, towerCoe_add_raw, towerCoe_add_raw, h₁, h₂]

/-! ### The lifted operator (the GNS-file recipe) -/

/-- **The represented operator**: the bounded pre-operator of R6, lifted to the completion by
    `ContinuousLinearMap.completion` — exactly the GNS-file recipe for `gnsNonUnitalStarAlgHom`. -/
noncomputable def towerRepCLM (C₀ : Finset M) (a : DiamondAlg L C₀) :
    TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  (towerLeftMul L ω β C₀ a).completion

@[simp] theorem towerRepCLM_coe (C₀ : Finset M) (a : DiamondAlg L C₀) (x : TowerPre L ω β) :
    towerRepCLM L ω β C₀ a (x : TowerGNS L ω β)
      = ((towerLeftMul L ω β C₀ a x : TowerPre L ω β) : TowerGNS L ω β) :=
  (towerLeftMul L ω β C₀ a).completion_apply_coe x

/-! ### The completion-level ⋆-algebra laws -/

/-- `π(1) = 1` — TRUE ONLY IN THE COMPLETION (the germ identity glues the deeper stage). -/
theorem towerRepCLM_one (C₀ : Finset M) : towerRepCLM L ω β C₀ 1 = 1 := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.one_apply, towerRepCLM_coe]
    exact towerCoe_leftMulRaw_one L ω β C₀ x

/-- `π(ab) = π(a) π(b)` — TRUE ONLY IN THE COMPLETION (stage reconciliation + germ). -/
theorem towerRepCLM_mul (C₀ : Finset M) (a b : DiamondAlg L C₀) :
    towerRepCLM L ω β C₀ (a * b)
      = towerRepCLM L ω β C₀ a * towerRepCLM L ω β C₀ b := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.mul_apply, towerRepCLM_coe, towerRepCLM_coe, towerRepCLM_coe]
    exact towerCoe_leftMulRaw_mul L ω β C₀ a b x

/-- `π(a + b) = π(a) + π(b)`. -/
theorem towerRepCLM_add (C₀ : Finset M) (a b : DiamondAlg L C₀) :
    towerRepCLM L ω β C₀ (a + b)
      = towerRepCLM L ω β C₀ a + towerRepCLM L ω β C₀ b := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.add_apply, towerRepCLM_coe, towerRepCLM_coe, towerRepCLM_coe]
    exact towerCoe_leftMulRaw_add L ω β C₀ a b x

/-- `π(r • a) = r • π(a)`. -/
theorem towerRepCLM_smul (C₀ : Finset M) (r : ℂ) (a : DiamondAlg L C₀) :
    towerRepCLM L ω β C₀ (r • a) = r • towerRepCLM L ω β C₀ a := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [ContinuousLinearMap.smul_apply, towerRepCLM_coe, towerRepCLM_coe]
    exact towerCoe_leftMulRaw_smul L ω β C₀ r a x

/-- `π(0) = 0`. -/
theorem towerRepCLM_zero (C₀ : Finset M) :
    towerRepCLM L ω β C₀ (0 : DiamondAlg L C₀) = 0 := by
  simpa using towerRepCLM_smul L ω β C₀ 0 0

/-- **The ⋆-law**: `π(aᴴ)` is the Hilbert-space adjoint of `π(a)` — the raw adjoint relation
    transported by `eq_adjoint_iff` + double completion induction (GNS-file incantation). -/
theorem towerRepCLM_star (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerRepCLM L ω β C₀ (star a)
      = ContinuousLinearMap.adjoint (towerRepCLM L ω β C₀ a) := by
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun ξ η => ?_
  induction ξ, η using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [towerRepCLM_coe, towerRepCLM_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, towerInner_def, towerInner_def]
    exact rawInner_leftMulRaw_conjTranspose L ω β C₀ a x y

/-! ### R7 — the bundled ⋆-representation -/

/-- **R7 — THE COMPATIBLE ⋆-REPRESENTATION**: the corner algebra acts on the tower Hilbert
    space by left multiplication after embedding, as a unital ⋆-algebra homomorphism into the
    bounded operators. (Bounded with the R6 Frobenius constant — never claimed contractive.) -/
noncomputable def towerRep (C₀ : Finset M) :
    DiamondAlg L C₀ →⋆ₐ[ℂ] (TowerGNS L ω β →L[ℂ] TowerGNS L ω β) where
  toFun a := towerRepCLM L ω β C₀ a
  map_one' := towerRepCLM_one L ω β C₀
  map_mul' := towerRepCLM_mul L ω β C₀
  map_zero' := towerRepCLM_zero L ω β C₀
  map_add' := towerRepCLM_add L ω β C₀
  commutes' r := by
    show towerRepCLM L ω β C₀ (algebraMap ℂ (DiamondAlg L C₀) r)
      = algebraMap ℂ (TowerGNS L ω β →L[ℂ] TowerGNS L ω β) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      towerRepCLM_smul, towerRepCLM_one]
  map_star' a := by
    show towerRepCLM L ω β C₀ (star a) = star (towerRepCLM L ω β C₀ a)
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact towerRepCLM_star L ω β C₀ a

@[simp] theorem towerRep_apply (C₀ : Finset M) (a : DiamondAlg L C₀) :
    towerRep L ω β C₀ a = towerRepCLM L ω β C₀ a := rfl

/-! ### R7 CAPSTONE — compatibility with the tower -/

/-- The operator form of the capstone: representing through a deeper stage does not change
    the operator. -/
theorem towerRepCLM_cornerEmbed (C C' : Finset M) (h : C ⊆ C') (a : DiamondAlg L C) :
    towerRepCLM L ω β C' (cornerEmbed L C C' h a) = towerRepCLM L ω β C a := by
  ext c
  induction c using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [towerRepCLM_coe, towerRepCLM_coe]
    exact towerCoe_leftMulRaw_cornerEmbed L ω β C C' h a x

/-- **R7 CAPSTONE — THE REPRESENTATIONS ARE COMPATIBLE WITH THE TOWER**:
    `towerRep C' (ι a) = towerRep C a` — the corner element acts the same through ANY stage
    that contains it: the finite refinement tower acts coherently on the single tower Hilbert
    space. -/
theorem towerRep_cornerEmbed (C C' : Finset M) (h : C ⊆ C') (a : DiamondAlg L C) :
    towerRep L ω β C' (cornerEmbed L C C' h a) = towerRep L ω β C a :=
  towerRepCLM_cornerEmbed L ω β C C' h a

end QIQTH.TowerGNS
