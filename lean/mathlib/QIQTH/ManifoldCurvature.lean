import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Curvature of a covariant derivative on an abstract manifold

This is the **first increment of the abstract-manifold GR stack** (gap 3 of the Jacobson
equation-of-state derivation: lift the component-level `QIQTH/Curvature.lean` results off the single
coordinate patch `Fin n → ℝ` onto genuine manifolds). Mathlib (2025) supplies covariant derivatives
(`IsCovariantDerivativeOn` / `CovariantDerivative`, Massot–Rothgang–Macbeth) and the manifold Lie
bracket `VectorField.mlieBracket`, but has **no Riemann curvature tensor**. We define it here for an
arbitrary connection on an arbitrary vector bundle `V → M`:

  `R(X,Y)σ = ∇_X ∇_Y σ − ∇_Y ∇_X σ − ∇_{[X,Y]} σ`

(the standard curvature endomorphism), and prove its first structural property — antisymmetry in the
two vector-field slots `R(X,Y) = −R(Y,X)`, which needs only the fibrewise linearity of `∇` and the
antisymmetry of the Lie bracket (no differentiability hypotheses).

The build order from here: fibrewise additivity/`C∞`-linearity (tensoriality) of `R`, the algebraic
Bianchi identity, then the Levi-Civita connection of a (pseudo-Riemannian / Lorentzian) metric —
which Mathlib also lacks — and finally Ricci/scalar/Einstein and the abstract field equation.
Everything axiom-free.
-/

open Bundle VectorField
open scoped Manifold ContDiff Topology

namespace QIQTH.ManifoldGR

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- **The Riemann curvature endomorphism of a covariant derivative**
`R(X,Y)σ = ∇_X ∇_Y σ − ∇_Y ∇_X σ − ∇_{[X,Y]} σ`, evaluated at a point `x`.

Recall the Mathlib convention `cov σ x (W x) = (∇_W σ) x`, so `∇_Y σ` is the section
`x' ↦ cov σ x' (Y x')`, and `∇_X(∇_Y σ) x = cov (∇_Y σ) x (X x)`. -/
noncomputable def curvature
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) : V x :=
  cov (fun x' => cov σ x' (Y x')) x (X x)
    - cov (fun x' => cov σ x' (X x')) x (Y x)
    - cov σ x (mlieBracket I X Y x)

/-- **Antisymmetry of the curvature in its two vector-field slots:** `R(X,Y)σ = −R(Y,X)σ`.
Purely algebraic — uses only that each `cov σ x` is a (continuous) linear map and that the Lie
bracket is antisymmetric `[Y,X] = −[X,Y]`. No differentiability of `σ`, `X`, `Y` is needed. -/
theorem curvature_antisymm
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    curvature cov X Y σ x = - curvature cov Y X σ x := by
  have h : mlieBracket I Y X x = - mlieBracket I X Y x := by
    rw [mlieBracket_swap (I := I) (V := Y) (W := X)]; rfl
  simp only [curvature, h, map_neg]
  abel

/-- The curvature vanishes when the two vector-field slots coincide, `R(X,X)σ = 0` — proved
directly (the two second-derivative terms are identical and `[X,X] = 0`), so it holds over any
`𝕜`-module fibre, not only where `2` is invertible. -/
theorem curvature_self
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    curvature cov X X σ x = 0 := by
  simp only [curvature, sub_self, mlieBracket_self, Pi.zero_apply, map_zero]

end QIQTH.ManifoldGR
