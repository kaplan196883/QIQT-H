/-
  THE MODULAR CONJUGATION J7 (THE_MODULAR_CONJUGATION_PLAN.md) — J CONJUGATES LEFT
  MULTIPLICATION INTO RIGHT MULTIPLICATION: `J π_C(a) J = R_{jStage a}`.

  Deliverables:
  • `jconj T := ξ ↦ towerJ (T (towerJ ξ))` — the double-conjugation of a bounded operator,
    hand-bundled as a genuinely ℂ-LINEAR CLM (the two anti-linear `towerJ`'s cancel:
    additivity is clear; `J(T(J(c•ξ))) = J(T(conj c • Jξ)) = J(conj c • T(Jξ))
    = conj(conj c) • J(T(Jξ)) = c • J(T(Jξ))` via `towerJ_smul` twice + `T`'s linearity;
    continuity is a composition bound `‖T‖`). `jconj_apply` — the rfl-spec.
  • `jconj_involutive` — `jconj (jconj T) = T` (`ext` + `towerJ_involutive` twice).
  • `jconj_norm_apply` — `‖jconj T ξ‖ = ‖T (towerJ ξ)‖` (the isometry of `towerJ`).
  • `jconj_sotApprox` — the SOT transport J8 consumes: `SOTApprox A T →
    SOTApprox (jconj '' A) (jconj T)` (evaluate the approximant tuple at `towerJ (ξ i)`;
    `towerJ` is an isometry, so the estimate transports verbatim).
  • ★ `jconj_towerRep` — THE CORE IDENTITY `jconj (towerRep C a) = towerRightMulCLM C (jStage a)`:
    `J π_C(a) J = R_{jStage a}`. Route: a RAW identity
    `jRaw (leftMulRaw C a (jRaw x)) = rightMulRaw C (jStage a) x` (DirectSum induction: on a
    pure component `jStage_{C⊔C'}(ι a · ι(jStage b)) = ι b · ι(jStage a)` by `jStage_anti_mul`
    + `cornerEmbed_jStage` + `jStage_involutive`), then `Completion.induction_on` + the coe
    incantations. The stage joins align: `leftMulRaw` lands at `C ⊔ C'` and `rightMulRaw` at
    `C ⊔ C'` — no `sup_comm` cast needed (mirrors `towerRightMulCLM_adjoint`).

  HONEST SCOPE: the intertwining identity ONLY. NO commutant statement is made — that
  `J·towerLimitVN·J ⊆ towerLimitVN′` follows is J8. No `J M J = M′` equality anywhere, no
  unbounded operator, no type classification. Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ModularConj
import QIQTH.TowerGNS.Representation
import QIQTH.TowerGNS.RightMul
import QIQTH.VonNeumann.Bicommutant

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.VonNeumann
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The double-conjugation operator `jconj` (hand-bundled ℂ-linear CLM) -/

/-- The double conjugation `ξ ↦ J (T (J ξ))` as a plain ℂ-LINEAR map — the two anti-linear
    `towerJ`'s compose the twist `starRingEnd ∘ starRingEnd = id` back to ℂ-homogeneity. -/
noncomputable def jconjₗ (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    TowerGNS L ω β →ₗ[ℂ] TowerGNS L ω β where
  toFun ξ := towerJ L ω β (T (towerJ L ω β ξ))
  map_add' x y := by
    show towerJ L ω β (T (towerJ L ω β (x + y)))
        = towerJ L ω β (T (towerJ L ω β x)) + towerJ L ω β (T (towerJ L ω β y))
    rw [map_add, map_add, map_add]
  map_smul' c x := by
    show towerJ L ω β (T (towerJ L ω β (c • x)))
        = (RingHom.id ℂ) c • towerJ L ω β (T (towerJ L ω β x))
    rw [towerJ_smul, map_smul, towerJ_smul, Complex.conj_conj, RingHom.id_apply]

/-- The norm bound for the double conjugation: `‖J (T (J ξ))‖ = ‖T (J ξ)‖ ≤ ‖T‖·‖ξ‖`
    (`towerJ` is an isometry on both ends). -/
theorem jconjₗ_norm_le (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) (ξ : TowerGNS L ω β) :
    ‖jconjₗ L ω β T ξ‖ ≤ ‖T‖ * ‖ξ‖ := by
  show ‖towerJ L ω β (T (towerJ L ω β ξ))‖ ≤ ‖T‖ * ‖ξ‖
  rw [towerJ_norm]
  calc ‖T (towerJ L ω β ξ)‖
      ≤ ‖T‖ * ‖towerJ L ω β ξ‖ := T.le_opNorm _
    _ = ‖T‖ * ‖ξ‖ := by rw [towerJ_norm]

/-- **THE DOUBLE-CONJUGATION OPERATOR** `jconj T := ξ ↦ J (T (J ξ))` — a bounded ℂ-LINEAR
    operator on the tower Hilbert space (the anti-linear `towerJ`'s cancel). The vehicle for
    `J π_C(a) J = R_{jStage a}`. -/
noncomputable def jconj (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    TowerGNS L ω β →L[ℂ] TowerGNS L ω β :=
  LinearMap.mkContinuous (jconjₗ L ω β T) ‖T‖ (jconjₗ_norm_le L ω β T)

@[simp] theorem jconj_apply (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) (ξ : TowerGNS L ω β) :
    jconj L ω β T ξ = towerJ L ω β (T (towerJ L ω β ξ)) := rfl

/-! ### Involutivity and the isometry form -/

/-- **`jconj² = id`**: `jconj (jconj T) = T` — the four `towerJ`'s cancel in two involutive
    pairs. -/
theorem jconj_involutive (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    jconj L ω β (jconj L ω β T) = T := by
  ext ξ
  simp only [jconj_apply]
  rw [towerJ_involutive, towerJ_involutive]

/-- **The isometry form**: `‖jconj T ξ‖ = ‖T (J ξ)‖` — `jconj` differs from `T` only by the
    isometric `towerJ` on either side. -/
theorem jconj_norm_apply (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) (ξ : TowerGNS L ω β) :
    ‖jconj L ω β T ξ‖ = ‖T (towerJ L ω β ξ)‖ := by
  rw [jconj_apply, towerJ_norm]

/-! ### The SOT transport (the form J8's `SOTApprox.mem_centralizer` consumes) -/

/-- **The SOT transport**: strong-operator approximability is carried through the double
    conjugation — `SOTApprox A T → SOTApprox (jconj '' A) (jconj T)`. Evaluate the approximant
    tuple of `T` at `towerJ (ξ i)`; the anti-isometry `towerJ` moves the norm estimate across
    unchanged. This is the operator-side vehicle for `J M J ⊆ M′` (J8). -/
theorem jconj_sotApprox {A : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β)}
    {T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β} (hT : SOTApprox A T) :
    SOTApprox (jconj L ω β '' A) (jconj L ω β T) := by
  intro n ξ ε hε
  obtain ⟨a, ha, hclose⟩ := hT n (fun i => towerJ L ω β (ξ i)) ε hε
  refine ⟨jconj L ω β a, ⟨a, ha, rfl⟩, fun i => ?_⟩
  rw [jconj_apply, jconj_apply, ← map_sub, towerJ_norm]
  exact hclose i

/-! ### ★ THE CORE IDENTITY — `J π_C(a) J = R_{jStage a}` -/

/-- **The raw intertwining identity** (all at `⨁` — the R3 lesson): conjugating left
    multiplication by `a` between two `jRaw`'s is right multiplication by `jStage a`.
    On a pure component `↑(of C' b)`:
    `jStage_{C⊔C'}(ι a · ι(jStage b)) = jStage(ι(jStage b))·jStage(ι a)
      = ι(jStage(jStage b))·ι(jStage a) = ι b · ι(jStage a)`
    (`jStage_anti_mul` + `cornerEmbed_jStage` + `jStage_involutive`) — exactly the entry the
    `rightMulRaw` action produces. -/
theorem jRaw_leftMulRaw_jRaw (C : Finset M) (a : DiamondAlg L C)
    (x : ⨁ C : Finset M, DiamondAlg L C) :
    jRaw L ω β (leftMulRaw L C a (jRaw L ω β x))
      = rightMulRaw L C (jStage L ω β C a) x := by
  induction x using DirectSum.induction_on with
  | zero =>
    rw [map_zero (jRaw L ω β), map_zero (leftMulRaw L C a), map_zero (jRaw L ω β),
      map_zero (rightMulRaw L C (jStage L ω β C a))]
  | of C' b =>
    rw [jRaw_of, leftMulRaw_of, jRaw_of, rightMulRaw_of, jStage_anti_mul,
      ← cornerEmbed_jStage, ← cornerEmbed_jStage, jStage_involutive]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (jRaw L ω β), map_add (leftMulRaw L C a), map_add (jRaw L ω β), h₁, h₂,
      map_add (rightMulRaw L C (jStage L ω β C a))]

/-- **★ J7 CAPSTONE — J CONJUGATES LEFT INTO RIGHT MULTIPLICATION**:
    `jconj (towerRep C a) = towerRightMulCLM C (jStage a)` — the modular conjugation intertwines
    the represented left multiplication `π_C(a)` with the commutant-side right multiplication by
    `jStage C a = √ρ·aᴴ·√ρ⁻¹`, i.e. `J π_C(a) J = R_{jStage a}` on the tower Hilbert space.
    `Completion.induction_on` reduces to the raw intertwining identity `jRaw_leftMulRaw_jRaw`.

    HONEST: this is the intertwining identity only — that `J·towerLimitVN·J ⊆ towerLimitVN′`
    follows is J8; no commutant equality is claimed here. -/
theorem jconj_towerRep (C : Finset M) (a : DiamondAlg L C) :
    jconj L ω β (towerRep L ω β C a)
      = towerRightMulCLM L ω β C (jStage L ω β C a) := by
  ext ξ
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [jconj_apply, towerRep_apply, towerJ_coe, towerRepCLM_coe, towerJ_coe,
      towerRightMulCLM_coe]
    have h : jPre L ω β (towerLeftMul L ω β C a (jPre L ω β x))
        = towerRightMul L ω β C (jStage L ω β C a) x :=
      jRaw_leftMulRaw_jRaw L ω β C a x
    rw [h]

end QIQTH.TowerGNS
