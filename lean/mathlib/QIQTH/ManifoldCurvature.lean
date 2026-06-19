import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import QIQTH.ManifoldCommutator

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

/-- **Additivity of the curvature in the section slot:** `R(X,Y)(σ+σ')= R(X,Y)σ + R(X,Y)σ'`.
With `σ,σ'` differentiable everywhere the inner `∇(σ+σ') = ∇σ + ∇σ'` is a plain `funext`+`cov.add`
(no germ-localisation needed); the Lie-bracket term is untouched. -/
theorem curvature_add_section
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (X Y : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) (x : M)
    (hσ : ∀ z, MDiffAt (T% σ) z) (hσ' : ∀ z, MDiffAt (T% σ') z)
    (hcovσY : MDiffAt (T% fun x' => cov σ x' (Y x')) x)
    (hcovσ'Y : MDiffAt (T% fun x' => cov σ' x' (Y x')) x)
    (hcovσX : MDiffAt (T% fun x' => cov σ x' (X x')) x)
    (hcovσ'X : MDiffAt (T% fun x' => cov σ' x' (X x')) x) :
    curvature cov X Y (σ + σ') x = curvature cov X Y σ x + curvature cov X Y σ' x := by
  have hsecY : (fun x' => cov (σ + σ') x' (Y x'))
      = (fun x' => cov σ x' (Y x')) + (fun x' => cov σ' x' (Y x')) := by
    funext x'; simp only [Pi.add_apply, hcov.add (hσ x') (hσ' x'), ContinuousLinearMap.add_apply]
  have hsecX : (fun x' => cov (σ + σ') x' (X x'))
      = (fun x' => cov σ x' (X x')) + (fun x' => cov σ' x' (X x')) := by
    funext x'; simp only [Pi.add_apply, hcov.add (hσ x') (hσ' x'), ContinuousLinearMap.add_apply]
  simp only [curvature]
  rw [hsecY, hsecX, hcov.add hcovσY hcovσ'Y, hcov.add hcovσX hcovσ'X, hcov.add (hσ x) (hσ' x)]
  simp only [ContinuousLinearMap.add_apply]
  abel

/-- **Section-slot tensoriality (`C∞`-linearity) of the curvature:** `R(X,Y)(fσ) = f · R(X,Y)σ`.
This is the deepest tensoriality — it makes `R` a genuine pointwise tensor in the section slot, not
merely a differential operator. Leibniz-expanding the two second-derivative terms leaves a scalar
`(X(Yf) − Y(Xf))·σ`, and the Lie-bracket term contributes `−([X,Y]f)·σ`; these cancel **exactly** by
the general-manifold commutator `mfderiv_apply_mlieBracket` (`[X,Y]f = X(Yf) − Y(Xf)`). The curvature
"is a tensor" *because* the bracket measures the non-commutation of the directional derivatives — this
theorem is the concrete payoff of that commutator. The hypotheses `hg, hsymm, hXt, hYt` are the
chart-representative regularity feeding the commutator (over `ℝ`/`ℂ`, automatic for `C²` data). -/
theorem curvature_smul_section [CompleteSpace E] [I.Boundaryless] [IsManifold I 2 M]
    [VectorBundle 𝕜 F V]
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (hcov : IsCovariantDerivativeOn F cov Set.univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M)
    (hf : ∀ z, MDiffAt f z)
    (hYf : MDiffAt (dirDeriv I Y f) x) (hXf : MDiffAt (dirDeriv I X f) x)
    (hσ : ∀ z, MDiffAt (T% σ) z)
    (hcovσX : MDiffAt (T% fun x' => cov σ x' (X x')) x)
    (hcovσY : MDiffAt (T% fun x' => cov σ x' (Y x')) x)
    (hg : ContDiffAt 𝕜 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hsymm : IsSymmSndFDerivAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hXt : DifferentiableAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (Set.range I)) (extChartAt I x x))
    (hYt : DifferentiableAt 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (Set.range I)) (extChartAt I x x)) :
    curvature cov X Y (f • σ) x = f x • curvature cov X Y σ x := by
  -- inner sections, Leibniz-expanded: ∇_Y(fσ) = f·∇_Yσ + (Yf)·σ, and likewise for X
  have hIY : (fun x' => cov (f • σ) x' (Y x'))
      = f • (fun x' => cov σ x' (Y x')) + (dirDeriv I Y f) • σ := by
    funext x'
    simp only [hcov.leibniz (hσ x') (hf x') (Set.mem_univ x'), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply]
    rfl
  have hIX : (fun x' => cov (f • σ) x' (X x'))
      = f • (fun x' => cov σ x' (X x')) + (dirDeriv I X f) • σ := by
    funext x'
    simp only [hcov.leibniz (hσ x') (hf x') (Set.mem_univ x'), ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
      Pi.add_apply]
    rfl
  -- the commutator: the leftover scalar coefficient of σ vanishes
  have hcomm := mfderiv_apply_mlieBracket f X Y x hf hYf hXf hg hsymm hXt hYt
  -- defeq bridges d% (= mvfderiv, fromTangentSpace = id) to mfderiv/dirDeriv
  have hd1 : (d% f x) (X x) = dirDeriv I X f x := rfl
  have hd2 : (d% f x) (Y x) = dirDeriv I Y f x := rfl
  have hd3 : (d% (dirDeriv I Y f) x) (X x) = dirDeriv I X (dirDeriv I Y f) x := rfl
  have hd4 : (d% (dirDeriv I X f) x) (Y x) = dirDeriv I Y (dirDeriv I X f) x := rfl
  have hd5 : (d% f x) (mlieBracket I X Y x) = mfderiv I 𝓘(𝕜) f x (mlieBracket I X Y x) := rfl
  simp only [curvature, hIY, hIX, hcov.add ((hf x).smul_section hcovσY) (hYf.smul_section (hσ x)),
    hcov.add ((hf x).smul_section hcovσX) (hXf.smul_section (hσ x)),
    hcov.leibniz hcovσY (hf x) (Set.mem_univ x), hcov.leibniz (hσ x) hYf (Set.mem_univ x),
    hcov.leibniz hcovσX (hf x) (Set.mem_univ x), hcov.leibniz (hσ x) hXf (Set.mem_univ x),
    hcov.leibniz (hσ x) (hf x) (Set.mem_univ x), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    Pi.add_apply, hd1, hd2, hd3, hd4, hd5, hcomm]
  module

end QIQTH.ManifoldGR
