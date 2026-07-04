/-
  THE REPRESENTATION R4 (THE_REPRESENTATION_PLAN.md) — THE GERM IDENTITY and the cyclic vector.

  `towerGerm`: in the completion, the image of a corner element equals the image of ANY of its
  embeddings — `↑(of C' (ι a)) = ↑(of C a)`. The difference is a null vector of the semidefinite
  pre-space (all four cross-pairings equal `gnsInner C' (ι a) (ι a)` when evaluated at the
  common stage C', by R2's stage stability + T7's state compatibility), and the METRIC
  completion identifies null-distance points — the direct-limit gluing happens HERE, with no
  quotient ever taken. This is the compatibility engine: R7's π-compatibility and map_one are
  germ + density.

  Plus `towerCyclicVec` (Ω := ↑(of ∅ 1)) with ⟪Ω,Ω⟫ = 1 (the Gibbs weights sum to one — DY2)
  and ‖Ω‖ = 1, and the completion-level pairing computation `inner_coe_of_of`.
-/
import Mathlib
import QIQTH.TowerGNS.PreSpace

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- Embedding along the trivial inclusion is the identity (Subtype eta + proof irrelevance). -/
theorem cornerEmbed_refl (C : Finset M) (h : C ⊆ C) (a : DiamondAlg L C) :
    cornerEmbed L C C h a = a := by
  ext m n
  have hsame : sameOffSub L C C m n := fun j hj => absurd j.2 hj
  rw [cornerEmbed_apply, if_pos hsame]
  rfl

/-- The completion-level pairing of two pure components. -/
theorem inner_coe_of_of (C C' : Finset M) (a : DiamondAlg L C) (b : DiamondAlg L C') :
    ⟪((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β),
        ((towerOf L ω β C' b : TowerPre L ω β) : TowerGNS L ω β)⟫_ℂ
      = pairInner L ω β C C' a b := by
  rw [UniformSpace.Completion.inner_coe]
  exact towerInner_of_of L ω β C C' a b

/-- **R4 CAPSTONE — THE GERM IDENTITY**: in the completion, embedding a corner element deeper
    into the tower does not move it — `↑(of C' (ι a)) = ↑(of C a)`. The difference is a null
    vector of the semidefinite pre-space; the metric completion identifies it with zero. THE
    direct-limit gluing, with no quotient ever taken. -/
theorem towerGerm {C C' : Finset M} (h : C ⊆ C') (a : DiamondAlg L C) :
    ((towerOf L ω β C' (cornerEmbed L C C' h a) : TowerPre L ω β) : TowerGNS L ω β)
      = ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β) := by
  set u : TowerPre L ω β := towerOf L ω β C' (cornerEmbed L C C' h a) with hu
  set v : TowerPre L ω β := towerOf L ω β C a with hv
  set w : DiamondAlg L C' := cornerEmbed L C C' h a with hw
  have huu : ⟪u, u⟫_ℂ = gnsInner L ω β C' w w := by
    rw [hu, towerInner_of_of,
      pairInner_embed L ω β C' C' C' subset_rfl subset_rfl, cornerEmbed_refl]
  have huv : ⟪u, v⟫_ℂ = gnsInner L ω β C' w w := by
    rw [hu, hv, towerInner_of_of,
      pairInner_embed L ω β C' C C' subset_rfl h, cornerEmbed_refl]
  have hvu : ⟪v, u⟫_ℂ = gnsInner L ω β C' w w := by
    rw [hu, hv, towerInner_of_of,
      pairInner_embed L ω β C C' C' h subset_rfl, cornerEmbed_refl]
  have hvv : ⟪v, v⟫_ℂ = gnsInner L ω β C' w w := by
    rw [hv, towerInner_of_of, pairInner_embed L ω β C C C' h h]
  have hzero : ⟪u - v, u - v⟫_ℂ = 0 := by
    rw [inner_sub_sub_self, huu, huv, hvu, hvv]
    ring
  have hnormsq : ‖u - v‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hzero]
    simp
  have hnorm : ‖u - v‖ = 0 :=
    (pow_eq_zero_iff (two_ne_zero)).mp hnormsq
  have hdist : dist ((u : TowerGNS L ω β)) ((v : TowerGNS L ω β)) = 0 := by
    rw [UniformSpace.Completion.dist_eq, dist_eq_norm, hnorm]
  exact eq_of_dist_eq_zero hdist

/-- **The cyclic vector** Ω — the unit of the trivial corner, in the completion. -/
noncomputable def towerCyclicVec : TowerGNS L ω β :=
  ((towerOf L ω β ∅ 1 : TowerPre L ω β) : TowerGNS L ω β)

/-- `⟪Ω, Ω⟫ = 1` — the Gibbs weights sum to one (DY2's normalization). -/
theorem inner_cyclicVec_self :
    ⟪towerCyclicVec L ω β, towerCyclicVec L ω β⟫_ℂ = 1 := by
  rw [towerCyclicVec, inner_coe_of_of,
    pairInner_embed L ω β ∅ ∅ ∅ subset_rfl subset_rfl, cornerEmbed_refl,
    gnsInner, Matrix.conjTranspose_one, one_mul, stateOf, Matrix.mul_one, gibbsDensity,
    Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum]
  rw [show ∑ n : Micro L ∅, gibbsWeight L ∅ ω β n = 1 from sum_gibbsWeight_one L ∅ ω β]
  exact Complex.ofReal_one

/-- `‖Ω‖ = 1`. -/
theorem norm_cyclicVec : ‖towerCyclicVec L ω β‖ = 1 := by
  have h2 : ‖towerCyclicVec L ω β‖ ^ 2 = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (towerCyclicVec L ω β)
    rw [inner_cyclicVec_self] at this
    rw [← this]
    simp
  nlinarith [norm_nonneg (towerCyclicVec L ω β)]

end QIQTH.TowerGNS
