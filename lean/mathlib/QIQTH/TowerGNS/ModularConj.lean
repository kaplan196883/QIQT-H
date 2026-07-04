/-
  THE MODULAR CONJUGATION J4 (THE_MODULAR_CONJUGATION_PLAN.md) — THE ANTI-UNITARY PACK:
  `towerJ` is an involutive anti-unitary on the tower GNS space, fixing the cyclic vector.

  Deliverables:
  • `towerJ_of` — the dense-core action: `J ↑(of C a) = ↑(of C (jStage C a))`;
  • `towerJ_of_single` ★ — THE VERIFIED SCALAR on the GNS space:
    `J ↑(of C (E_{nm} c)) = √(w_m/w_n) • ↑(of C (E_{mn} (conj c)))` — indices FLIPPED,
    scalar CONJUGATED, weight ratio square-rooted (the eigenbasis action of J);
  • `towerJ_inner` ★ — THE ANTI-UNITARY SIGNATURE on the completion:
    `⟪Jξ, Jη⟫ = ⟪η, ξ⟫` (double completion induction + the raw anti-isometry
    `rawInner_jRaw`);
  • `towerJ_norm` — J is norm-preserving (the anti-isometry at ξ = η);
  • `towerJ_involutive` — `J(Jξ) = ξ` pointwise (completion induction + the raw
    involutivity from `jStage_involutive`; stated POINTWISE — the composite carries the
    ring-hom `starRingEnd ∘ starRingEnd`, so no bundled `J² = 1` is attempted);
  • `towerJ_cyclicVec` — `JΩ = Ω` (Ω is the unit of the trivial corner; `jStage 1 = 1`);
  • `towerJ_smul` — THE TWIST GUARD: `J(c • ξ) = conj c • Jξ` — the i-sensitivity is
    carried in the TYPE (`→SL[starRingEnd ℂ]`), displayed here explicitly;
  • `towerJ_surjective`, `towerJ_injective` — from involutivity.

  HONEST SCOPE: the anti-unitary pack ONLY. NO polar decomposition is claimed yet
  (S̄ = J∘Δ^{1/2} on the core is J5), no commutation with the modular group (J6), no
  Tomita II inclusion (J7–J8), no unbounded operator, no J M J = M′ equality anywhere.
  Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ConjPre
import QIQTH.TowerGNS.Germ
import QIQTH.TowerGNS.ModularEigenvectors

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The raw involutivity (everything at `⨁` — the R3 lesson) -/

/-- The raw conjugation is involutive (componentwise `jStage_involutive`). -/
theorem jRaw_involutive (x : ⨁ C : Finset M, DiamondAlg L C) :
    jRaw L ω β (jRaw L ω β x) = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero (jRaw L ω β), map_zero (jRaw L ω β)]
  | of C a => rw [jRaw_of, jRaw_of, jStage_involutive]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add (jRaw L ω β), map_add (jRaw L ω β), h₁, h₂]

/-! ### The dense-core action -/

/-- **The dense-core action of the conjugation**: `J ↑(of C a) = ↑(of C (jStage C a))` —
    the global conjugation acts componentwise through the coercion. -/
theorem towerJ_of (C : Finset M) (a : DiamondAlg L C) :
    towerJ L ω β ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      = ((towerOf L ω β C (jStage L ω β C a) : TowerPre L ω β) : TowerGNS L ω β) := by
  rw [towerJ_coe]
  have h : jPre L ω β (towerOf L ω β C a) = towerOf L ω β C (jStage L ω β C a) := by
    show jRaw L ω β (DirectSum.of (fun C : Finset M => DiamondAlg L C) C a)
        = DirectSum.of (fun C : Finset M => DiamondAlg L C) C (jStage L ω β C a)
    rw [jRaw_of]
  rw [h]

/-! ### ★ The eigenbasis action on the GNS space -/

/-- **★ THE J SCALAR ON THE GNS SPACE**: on the coerced matrix-unit basis the global
    conjugation acts as `J ↑(of C (E_{nm} c)) = √(w_m/w_n) • ↑(of C (E_{mn} (conj c)))` —
    indices FLIPPED, scalar CONJUGATED, weight ratio square-rooted (the COLUMN weight
    `w_m` on top; the isometry check is `(w_m/w_n)·w_n = w_m`). -/
theorem towerJ_of_single (C : Finset M) (n m : Micro L C) (c : ℂ) :
    towerJ L ω β
        ((towerOf L ω β C (Matrix.single n m c) : TowerPre L ω β) : TowerGNS L ω β)
      = ((Real.sqrt (gibbsWeight L C ω β m / gibbsWeight L C ω β n) : ℝ) : ℂ)
        • ((towerOf L ω β C (Matrix.single m n (starRingEnd ℂ c)) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  rw [towerJ_of, jStage_single]
  exact towerOf_smul_coe L ω β C _ _

/-! ### ★ The anti-unitary signature on the completion -/

/-- **★ THE ANTI-UNITARY SIGNATURE**: `⟪Jξ, Jη⟫ = ⟪η, ξ⟫` on the FULL completion — the
    conjugation flips the inner-product slots (double completion induction + the raw
    anti-isometry `rawInner_jRaw`). -/
theorem towerJ_inner (ξ η : TowerGNS L ω β) :
    ⟪towerJ L ω β ξ, towerJ L ω β η⟫_ℂ = ⟪η, ξ⟫_ℂ := by
  induction ξ, η using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [towerJ_coe, towerJ_coe, UniformSpace.Completion.inner_coe,
      UniformSpace.Completion.inner_coe, towerInner_def, towerInner_def]
    exact rawInner_jRaw L ω β x y

/-- **The conjugation is norm-preserving**: `‖Jξ‖ = ‖ξ‖` (the anti-isometry at `ξ = η` —
    the flipped slots agree there — + `√(‖·‖²)`). -/
theorem towerJ_norm (ξ : TowerGNS L ω β) :
    ‖towerJ L ω β ξ‖ = ‖ξ‖ := by
  have hinner : ⟪towerJ L ω β ξ, towerJ L ω β ξ⟫_ℂ = ⟪ξ, ξ⟫_ℂ :=
    towerJ_inner L ω β ξ ξ
  have h2 : ‖towerJ L ω β ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (towerJ L ω β ξ),
      ← inner_self_eq_norm_sq (𝕜 := ℂ) ξ, hinner]
  calc ‖towerJ L ω β ξ‖
      = Real.sqrt (‖towerJ L ω β ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖ξ‖ ^ 2) := by rw [h2]
    _ = ‖ξ‖ := Real.sqrt_sq (norm_nonneg _)

/-! ### The involution, the fixed point, and the twist guard -/

/-- **`J² = 1` pointwise**: `J(Jξ) = ξ` on the full completion (completion induction +
    the raw involutivity). Stated POINTWISE — the composite `J ∘ J` carries the ring-hom
    `starRingEnd ℂ ∘ starRingEnd ℂ = id`, so no bundled composition is attempted. -/
theorem towerJ_involutive (ξ : TowerGNS L ω β) :
    towerJ L ω β (towerJ L ω β ξ) = ξ := by
  induction ξ using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    rw [towerJ_coe, towerJ_coe]
    have h : jPre L ω β (jPre L ω β x) = x := jRaw_involutive L ω β x
    rw [h]

/-- **`JΩ = Ω`** — the conjugation fixes the cyclic vector (Ω is the unit of the trivial
    corner and `jStage 1 = 1`). -/
theorem towerJ_cyclicVec :
    towerJ L ω β (towerCyclicVec L ω β) = towerCyclicVec L ω β := by
  rw [towerCyclicVec, towerJ_of, jStage_one]

/-- **THE TWIST GUARD**: `J(c • ξ) = conj c • Jξ` — the conjugation is ANTI-linear on the
    completion; the i-sensitivity is carried in the TYPE (`→SL[starRingEnd ℂ]`), displayed
    here explicitly as the guard against a silently ℂ-linear J. -/
theorem towerJ_smul (c : ℂ) (ξ : TowerGNS L ω β) :
    towerJ L ω β (c • ξ) = starRingEnd ℂ c • towerJ L ω β ξ :=
  (towerJ L ω β).map_smulₛₗ c ξ

/-! ### Surjectivity and injectivity — J is a bijection -/

/-- The conjugation is surjective: every `ξ` is `J(Jξ)`. -/
theorem towerJ_surjective : Function.Surjective (towerJ L ω β) :=
  fun ξ => ⟨towerJ L ω β ξ, towerJ_involutive L ω β ξ⟩

/-- The conjugation is injective: apply `J` to both sides and collapse `J² = 1`. -/
theorem towerJ_injective : Function.Injective (towerJ L ω β) := by
  intro ξ η h
  have h' := congrArg (towerJ L ω β) h
  rwa [towerJ_involutive, towerJ_involutive] at h'

end QIQTH.TowerGNS
