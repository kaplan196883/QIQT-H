/-
  THE REPRESENTATION R1 (THE_REPRESENTATION_PLAN.md) — tower transitivity: the one missing
  T7 lemma.

  THE TOWER T7 built `cornerEmbed` as a state-compatible modular-equivariant unital ⋆-hom for a
  SINGLE inclusion C ⊆ C′. The GNS-of-the-tower construction composes inclusions, so it needs
  FUNCTORIALITY: `cornerEmbed_trans` — embedding C → C′ → C″ equals embedding C → C″ directly.
  The engine is `sameOffSub_split`: agreement off C at the top level factors as agreement off C′
  PLUS agreement off C of the restrictions. Also: the linear bundling `cornerEmbedₗ` (from the
  held add/smul laws) and `cornerEmbed_sub`, both consumed by the direct-sum pre-space (R3).

  Pure finite combinatorics; no state, no analysis, no representation here.
-/
import Mathlib
import QIQTH.Tower.CornerEmbed

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (C C' C'' : Finset M)

/-- Restriction is functorial: restricting C″ → C′ → C equals restricting C″ → C directly. -/
theorem restrictMicro_trans (h₁ : C ⊆ C') (h₂ : C' ⊆ C'') (n : Micro L C'') :
    restrictMicro L C' C h₁ (restrictMicro L C'' C' h₂ n)
      = restrictMicro L C'' C (h₁.trans h₂) n := by
  funext j
  rfl

/-- **The splitting of off-corner agreement**: two big-corner occupations agree off `C` iff they
    agree off `C′` AND their restrictions to `C′` agree off `C` (for `C ⊆ C′ ⊆ C″`). -/
theorem sameOffSub_split (h₁ : C ⊆ C') (h₂ : C' ⊆ C'') {m n : Micro L C''} :
    sameOffSub L C C'' m n
      ↔ sameOffSub L C' C'' m n
        ∧ sameOffSub L C C' (restrictMicro L C'' C' h₂ m) (restrictMicro L C'' C' h₂ n) := by
  constructor
  · intro h
    refine ⟨fun j hj => h j fun hjC => hj (h₁ hjC), fun j hj => ?_⟩
    show m ⟨j.val, h₂ j.2⟩ = n ⟨j.val, h₂ j.2⟩
    exact h ⟨j.val, h₂ j.2⟩ hj
  · rintro ⟨houter, hinner⟩ j hj
    by_cases hjC' : j.val ∈ C'
    · have := hinner ⟨j.val, hjC'⟩ hj
      show m j = n j
      have hm : m ⟨j.val, h₂ hjC'⟩ = n ⟨j.val, h₂ hjC'⟩ := this
      have hcast : (⟨j.val, h₂ hjC'⟩ : { x // x ∈ C'' }) = j := Subtype.ext rfl
      rwa [hcast] at hm
    · exact houter j hjC'

/-- **R1 CAPSTONE — the corner embeddings compose**: the tower is a functor on the directed
    order of finite corners. -/
theorem cornerEmbed_trans (h₁ : C ⊆ C') (h₂ : C' ⊆ C'') (A : DiamondAlg L C) :
    cornerEmbed L C' C'' h₂ (cornerEmbed L C C' h₁ A)
      = cornerEmbed L C C'' (h₁.trans h₂) A := by
  ext m n
  simp only [cornerEmbed_apply]
  by_cases houter : sameOffSub L C' C'' m n
  · rw [if_pos houter]
    by_cases hinner : sameOffSub L C C'
        (restrictMicro L C'' C' h₂ m) (restrictMicro L C'' C' h₂ n)
    · rw [if_pos hinner,
        if_pos ((sameOffSub_split L C C' C'' h₁ h₂).mpr ⟨houter, hinner⟩),
        restrictMicro_trans, restrictMicro_trans]
    · rw [if_neg hinner, if_neg fun h =>
        hinner ((sameOffSub_split L C C' C'' h₁ h₂).mp h).2]
  · rw [if_neg houter, if_neg fun h =>
      houter ((sameOffSub_split L C C' C'' h₁ h₂).mp h).1]

/-- The corner embedding as a ℂ-linear map (bundling the held add/smul laws). -/
noncomputable def cornerEmbedₗ (hCC : C ⊆ C') : DiamondAlg L C →ₗ[ℂ] DiamondAlg L C' where
  toFun := cornerEmbed L C C' hCC
  map_add' := cornerEmbed_add L C C' hCC
  map_smul' := cornerEmbed_smul L C C' hCC

theorem cornerEmbedₗ_apply (hCC : C ⊆ C') (A : DiamondAlg L C) :
    cornerEmbedₗ L C C' hCC A = cornerEmbed L C C' hCC A := rfl

/-- The embedding respects subtraction. -/
theorem cornerEmbed_sub (hCC : C ⊆ C') (A B : DiamondAlg L C) :
    cornerEmbed L C C' hCC (A - B)
      = cornerEmbed L C C' hCC A - cornerEmbed L C C' hCC B :=
  map_sub (cornerEmbedₗ L C C' hCC) A B

/-- The embedding respects zero. -/
theorem cornerEmbed_zero (hCC : C ⊆ C') :
    cornerEmbed L C C' hCC (0 : DiamondAlg L C) = 0 :=
  map_zero (cornerEmbedₗ L C C' hCC)

end QIQTH.TowerGNS
