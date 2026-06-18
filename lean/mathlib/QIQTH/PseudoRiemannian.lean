import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Pseudo-Riemannian (Lorentzian) metrics on a manifold

Mathlib's metric infrastructure (`Mathlib/Geometry/Manifold/Riemannian/`) is **positive-definite
only**. The Jacobson equation-of-state derivation, and any GR formalization, needs **indefinite
signature** (Lorentzian). This file begins the pseudo-Riemannian metric layer (P3 of the
abstract-manifold GR plan), which underlies the Levi-Civita connection → Ricci → Einstein tower.

**This increment:** the pointwise structure — a field of nondegenerate symmetric bilinear forms on
the tangent bundle — and the **index-lowering (musical `♭`) map**, with injectivity from
nondegeneracy (the first half of the musical isomorphism). Smoothness of the field, and surjectivity
of `♭` (the full iso, which needs finite-dimensionality), are the next increments.
-/

open Bundle
open scoped Manifold

namespace QIQTH.ManifoldGR

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A **pseudo-Riemannian metric** on the tangent bundle of `M`: a field of symmetric, nondegenerate
continuous bilinear forms `g x : T_xM × T_xM → 𝕜`. Lorentzian signature is the indefinite case
Mathlib's `RiemannianMetric` cannot express. (Smoothness of `g` is added in a later increment.) -/
structure PseudoRiemannianMetric (I : ModelWithCorners 𝕜 E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  /-- The metric tensor at each point, as a continuous bilinear form on the tangent space. -/
  g : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜
  /-- The metric is symmetric. -/
  symm' : ∀ (x : M) (v w : TangentSpace I x), g x v w = g x w v
  /-- The metric is nondegenerate: a vector orthogonal to everything is zero. -/
  nondeg' : ∀ (x : M) (v : TangentSpace I x), (∀ w, g x v w = 0) → v = 0

namespace PseudoRiemannianMetric

variable (gm : PseudoRiemannianMetric I M)

/-- The **index-lowering (musical `♭`) map** `v ↦ g(v, ·)`, sending a tangent vector to the cotangent
covector it determines. It is literally the metric read as a map into the dual. -/
def lower (x : M) : TangentSpace I x →L[𝕜] (TangentSpace I x →L[𝕜] 𝕜) := gm.g x

@[simp] theorem lower_apply (x : M) (v w : TangentSpace I x) : gm.lower x v w = gm.g x v w := rfl

/-- Symmetry, stated on `lower`. -/
theorem lower_symm (x : M) (v w : TangentSpace I x) : gm.lower x v w = gm.lower x w v :=
  gm.symm' x v w

/-- **The lowering map is injective** — the first half of the musical isomorphism. Two tangent
vectors with the same lowered covector are equal, directly from nondegeneracy. -/
theorem lower_injective (x : M) : Function.Injective (gm.lower x) := by
  intro v w hvw
  have hz : ∀ u, gm.g x (v - w) u = 0 := by
    intro u
    have : gm.g x v u = gm.g x w u := congrFun (congrArg DFunLike.coe hvw) u
    simp only [map_sub, ContinuousLinearMap.sub_apply, this, sub_self]
  have := gm.nondeg' x (v - w) hz
  rwa [sub_eq_zero] at this

end PseudoRiemannianMetric

end QIQTH.ManifoldGR
