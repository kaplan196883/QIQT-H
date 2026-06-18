import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The Lie-bracket-as-commutator on functions (manifold infrastructure)

To make the abstract-manifold curvature a genuine tensor (`C∞`-linearity in the section slot, the
first Bianchi identity, Ricci) one needs the fact that the Lie bracket of vector fields acts on a
scalar function as the **commutator of directional derivatives**:

  `df([X,Y]) = X(Yf) − Y(Xf)`.

Mathlib provides this only at the **normed-space** level
(`VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt`); there is no manifold (`mfderiv` /
`mlieBracket`) version. This file builds the manifold version bottom-up so the manifold curvature
stack stays genuinely **axiom-free** (no cited analytic hypothesis).

**This increment: the directional-derivative operator `dirDeriv` and the base case** — when the
manifold *is* its model space `E` (`I = 𝓘(𝕜,E)`), `mfderiv` reduces to `fderiv` and `mlieBracket` to
`lieBracket`, so the manifold commutator is exactly Mathlib's normed-space lemma. The
general-manifold case (chart/pullback transport) builds on this.
-/

open Bundle VectorField
open scoped Manifold ContDiff Topology

namespace QIQTH.ManifoldGR

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **directional derivative** `(Xf)(z) = df_z(X z)` of a scalar function `f` along a vector field
`X`, as a clean scalar function `M → 𝕜` (the codomain is pinned to `𝕜`, collapsing the dependent
tangent-space typing of `mfderiv`). -/
noncomputable def dirDeriv {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (X : Π z : M, TangentSpace I z) (f : M → 𝕜) (z : M) : 𝕜 :=
  mfderiv I 𝓘(𝕜) f z (X z)

section dirDerivAPI
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The directional derivative is **additive in the vector field** — pure fibrewise linearity of the
differential, no differentiability of the field needed. -/
@[simp] theorem dirDeriv_add_vectorField (X X' : Π z : M, TangentSpace I z) (f : M → 𝕜) :
    dirDeriv I (X + X') f = dirDeriv I X f + dirDeriv I X' f := by
  funext z; exact map_add (mfderiv I 𝓘(𝕜) f z) (X z) (X' z)

/-- The directional derivative is **homogeneous in the vector field** over scalars. -/
@[simp] theorem dirDeriv_smul_vectorField (c : 𝕜) (X : Π z : M, TangentSpace I z) (f : M → 𝕜) :
    dirDeriv I (c • X) f = c • dirDeriv I X f := by
  funext z; exact map_smul (mfderiv I 𝓘(𝕜) f z) c (X z)

/-- The directional derivative along the zero field vanishes. -/
@[simp] theorem dirDeriv_zero_vectorField (f : M → 𝕜) :
    dirDeriv I (0 : Π z : M, TangentSpace I z) f = 0 := by
  funext z; exact map_zero (mfderiv I 𝓘(𝕜) f z)

/-- The directional derivative is **additive in the function** (for differentiable functions). -/
theorem dirDeriv_add_fun (X : Π z : M, TangentSpace I z) (f g : M → 𝕜)
    (hf : ∀ z, MDifferentiableAt I 𝓘(𝕜) f z) (hg : ∀ z, MDifferentiableAt I 𝓘(𝕜) g z) :
    dirDeriv I X (f + g) = dirDeriv I X f + dirDeriv I X g := by
  funext z
  exact DFunLike.congr_fun (mfderiv_add (hf z) (hg z)) (X z)

end dirDerivAPI

/-- **Base case (model space):** the Lie bracket acts on a scalar as the commutator of directional
derivatives, `df([X,Y]) = X(Yf) − Y(Xf)`, when the manifold is its own model space `E`. Reduces
`mfderiv → fderiv`, `mlieBracket → lieBracket` and applies Mathlib's normed-space
`fderiv_apply_lieBracket_of_isSymmSndFDerivAt`. The symmetric-second-derivative hypothesis `hsymm`
holds for any `C²` `f` over `ℝ`/`ℂ` (`ContDiffAt.isSymmSndFDerivAt`). -/
theorem mfderiv_apply_mlieBracket_model
    {f : E → 𝕜} {X Y : E → E} {x : E}
    (hf : ContDiffAt 𝕜 2 f x) (hsymm : IsSymmSndFDerivAt 𝕜 f x)
    (hX : DifferentiableAt 𝕜 X x) (hY : DifferentiableAt 𝕜 Y x) :
    mfderiv 𝓘(𝕜, E) 𝓘(𝕜) f x (mlieBracket 𝓘(𝕜, E) X Y x)
      = dirDeriv 𝓘(𝕜, E) X (dirDeriv 𝓘(𝕜, E) Y f) x
        - dirDeriv 𝓘(𝕜, E) Y (dirDeriv 𝓘(𝕜, E) X f) x := by
  have hb : mlieBracket 𝓘(𝕜, E) X Y x = lieBracket 𝕜 X Y x := by
    rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  have hdY : dirDeriv 𝓘(𝕜, E) Y f = fun z => fderiv 𝕜 f z (Y z) := by
    funext z; exact DFunLike.congr_fun (mfderiv_eq_fderiv (f := f) (x := z)) (Y z)
  have hdX : dirDeriv 𝓘(𝕜, E) X f = fun z => fderiv 𝕜 f z (X z) := by
    funext z; exact DFunLike.congr_fun (mfderiv_eq_fderiv (f := f) (x := z)) (X z)
  -- rewrite every `mfderiv …` applied at an argument into a normed-space `fderiv …`, so the goal
  -- becomes E-native (avoids the `TangentSpace` synonym in the application nodes).
  have hL : mfderiv 𝓘(𝕜, E) 𝓘(𝕜) f x (mlieBracket 𝓘(𝕜, E) X Y x)
      = fderiv 𝕜 f x (lieBracket 𝕜 X Y x) := by
    rw [hb]; exact DFunLike.congr_fun (mfderiv_eq_fderiv (f := f) (x := x)) _
  have hR1 : dirDeriv 𝓘(𝕜, E) X (dirDeriv 𝓘(𝕜, E) Y f) x
      = fderiv 𝕜 (fun z => fderiv 𝕜 f z (Y z)) x (X x) := by
    rw [show dirDeriv 𝓘(𝕜, E) X (dirDeriv 𝓘(𝕜, E) Y f) x
          = fderiv 𝕜 (dirDeriv 𝓘(𝕜, E) Y f) x (X x) from
        DFunLike.congr_fun (mfderiv_eq_fderiv (f := dirDeriv 𝓘(𝕜, E) Y f) (x := x)) _, hdY]
  have hR2 : dirDeriv 𝓘(𝕜, E) Y (dirDeriv 𝓘(𝕜, E) X f) x
      = fderiv 𝕜 (fun z => fderiv 𝕜 f z (X z)) x (Y x) := by
    rw [show dirDeriv 𝓘(𝕜, E) Y (dirDeriv 𝓘(𝕜, E) X f) x
          = fderiv 𝕜 (dirDeriv 𝓘(𝕜, E) X f) x (Y x) from
        DFunLike.congr_fun (mfderiv_eq_fderiv (f := dirDeriv 𝓘(𝕜, E) X f) (x := x)) _, hdX]
  rw [hL, hR1, hR2]
  exact fderiv_apply_lieBracket_of_isSymmSndFDerivAt hf hsymm hY hX

/-! ## Toward the general-manifold commutator (chart transport)

The general manifold case is standard differential geometry (Lee, *Smooth Manifolds* §8) but Mathlib
lacks it, so we build it through the chart. First foundational block: the **directional-derivative
chart-covariance** — `(Yf)(x)` computed on `M` equals the normed-space directional derivative of the
chart representative `f ∘ e⁻¹` along the pushed-forward field, via the chain rule for `f = (f∘e⁻¹)∘e`.
-/
section GeneralManifold
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- **Directional-derivative chart-covariance.** The directional derivative `(Yf)(x)` on `M` equals
the normed-space directional derivative of the chart representative `f ∘ e⁻¹` at `e x`, evaluated on
the pushed-forward vector `(de)_x (Y x)`. Pure chain rule for `f = (f ∘ e⁻¹) ∘ e` near `x`. -/
theorem dirDeriv_eq_chart (f : M → 𝕜) (Y : Π z : M, TangentSpace I z) (x : M)
    (hf : MDifferentiableAt I 𝓘(𝕜) f x) :
    dirDeriv I Y f x
      = fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x)
          (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x (Y x)) := by
  have hee : MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  haveI : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  have hes : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜) (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    have h := (hf.mdifferentiableWithinAt (s := Set.univ)).differentiableWithinAt_comp_extChartAt_symm
    simpa [I.range_eq_univ, differentiableWithinAt_univ] using h
  have heq : (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x) =ᶠ[𝓝 x] f := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with z hz
    simp only [Function.comp_apply, (extChartAt I x).left_inv hz]
  show mfderiv I 𝓘(𝕜) f x (Y x) = _
  rw [← heq.mfderiv_eq, mfderiv_comp x hes hee]
  exact DFunLike.congr_fun
    (mfderiv_eq_fderiv (f := f ∘ ⇑(extChartAt I x).symm) (x := extChartAt I x x))
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) x (Y x))

end GeneralManifold

end QIQTH.ManifoldGR
