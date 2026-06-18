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

/-- **Tensoriality of the curvature in its first vector-field slot:** `R(fX,Y)σ = f·R(X,Y)σ` for a
scalar function `f`. This is the property that makes `curvature` a genuine tensor (pointwise in `X`):
the Leibniz term produced by `∇_{fX} = f∇_X` (the `(df·Y)∇_Xσ` piece) cancels *exactly* against the
`−(df·Y)X` term in the product rule `[fX,Y] = f[X,Y] − (Yf)X` for the Lie bracket — both are the same
directional derivative `d% f x (Y x)`. -/
theorem curvature_smul_left [CompleteSpace E] [IsManifold I 2 M]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M)
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hcovσX : MDiffAt (T% fun x' => cov σ x' (X x')) x) :
    curvature cov (f • X) Y σ x = f x • curvature cov X Y σ x := by
  have hsec : (fun x' => cov σ x' ((f • X) x')) = f • (fun x' => cov σ x' (X x')) := by
    funext x'; exact (cov σ x').map_smul (f x') (X x')
  have hT1 : (cov (fun x' => cov σ x' (Y x')) x) ((f • X) x)
      = f x • (cov (fun x' => cov σ x' (Y x')) x) (X x) := by
    rw [show (f • X) x = f x • X x from rfl]; exact map_smul _ _ _
  simp only [curvature, hsec, hT1,
    hcov.leibniz hcovσX hf, mlieBracket_smul_left hf hX,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  module

/-- **Tensoriality in the second vector-field slot:** `R(X,fY)σ = f·R(X,Y)σ` — a clean corollary of
slot-one tensoriality and antisymmetry. -/
theorem curvature_smul_right [CompleteSpace E] [IsManifold I 2 M]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M)
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hcovσY : MDiffAt (T% fun x' => cov σ x' (Y x')) x) :
    curvature cov X (f • Y) σ x = f x • curvature cov X Y σ x := by
  rw [curvature_antisymm cov X (f • Y) σ x,
    curvature_smul_left cov hcov f Y X σ x hf hY hcovσY,
    curvature_antisymm cov X Y σ x, smul_neg]

/-- **Additivity of the curvature in its first vector-field slot:** `R(X+X',Y)σ = R(X,Y)σ + R(X',Y)σ`.
Uses only fibrewise additivity of `∇` and of the Lie bracket — no Leibniz cancellation. -/
theorem curvature_add_left [CompleteSpace E] [IsManifold I 2 M]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M)
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hcovσX : MDiffAt (T% fun x' => cov σ x' (X x')) x)
    (hcovσX' : MDiffAt (T% fun x' => cov σ x' (X' x')) x) :
    curvature cov (X + X') Y σ x = curvature cov X Y σ x + curvature cov X' Y σ x := by
  have hsec : (fun x' => cov σ x' ((X + X') x'))
      = (fun x' => cov σ x' (X x')) + (fun x' => cov σ x' (X' x')) := by
    funext x'; simp only [Pi.add_apply, map_add]
  simp only [curvature]
  rw [hsec, hcov.add hcovσX hcovσX']
  simp only [Pi.add_apply, map_add, mlieBracket_add_left hX hX', ContinuousLinearMap.add_apply]
  abel

/-- **Additivity in the second vector-field slot:** `R(X,Y+Y')σ = R(X,Y)σ + R(X,Y')σ`, from
slot-one additivity and antisymmetry. -/
theorem curvature_add_right [CompleteSpace E] [IsManifold I 2 M]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M)
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hcovσY : MDiffAt (T% fun x' => cov σ x' (Y x')) x)
    (hcovσY' : MDiffAt (T% fun x' => cov σ x' (Y' x')) x) :
    curvature cov X (Y + Y') σ x = curvature cov X Y σ x + curvature cov X Y' σ x := by
  rw [curvature_antisymm cov X (Y + Y') σ x,
    curvature_add_left cov hcov Y Y' X σ x hY hY' hcovσY hcovσY',
    curvature_antisymm cov X Y σ x, curvature_antisymm cov X Y' σ x, neg_add]

end QIQTH.ManifoldGR
