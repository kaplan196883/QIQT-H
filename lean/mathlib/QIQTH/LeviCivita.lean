import QIQTH.PseudoRiemannian
import QIQTH.ManifoldCommutator
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.LinearAlgebra.Trace

/-!
# Toward the Levi-Civita connection: the Koszul formula

The Levi-Civita connection of a pseudo-Riemannian metric is characterised by the **Koszul formula**

  `2 g(∇_X Y, Z) = X·g(Y,Z) + Y·g(X,Z) − Z·g(X,Y) + g([X,Y],Z) − g([Y,Z],X) + g([Z,X],Y)`.

This file defines the right-hand side (`koszul`) as a scalar field and proves the two algebraic
identities that *are* the defining properties of the Levi-Civita connection:

* `koszul_metric_compat` — `koszul X Y Z + koszul X Z Y = 2·X·g(Y,Z)` (metric compatibility),
* `koszul_torsion_free` — `koszul X Y Z − koszul Y X Z = 2·g([X,Y],Z)` (torsion-freeness).

Both follow from **metric symmetry + Lie-bracket antisymmetry alone** — no differentiability needed:
the directional-derivative terms either cancel pairwise or merge via metric symmetry, and the bracket
terms cancel via `mlieBracket_swap`. This is the algebraic heart of "the Levi-Civita connection
exists and is unique"; the remaining analytic step (dualising `koszul` to `∇_X Y` via the musical `♯`
— `lowerEquiv` — and verifying the connection axioms `IsCovariantDerivativeOn`) is the next layer.
-/

open scoped Manifold
open VectorField

namespace QIQTH.ManifoldGR

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The Koszul scalar** `2 g(∇_X Y, Z)` — the right-hand side of the Koszul formula, as a scalar
field on `M`. (The directional derivatives `X·g(Y,Z)` are taken with `dirDeriv`; the bracket terms use
the manifold Lie bracket.) Dualising this in `Z` via the metric gives `∇_X Y`. -/
noncomputable def koszul (gm : PseudoRiemannianMetric I M)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : 𝕜 :=
  dirDeriv I X (fun x' => gm.g x' (Y x') (Z x')) x
  + dirDeriv I Y (fun x' => gm.g x' (X x') (Z x')) x
  - dirDeriv I Z (fun x' => gm.g x' (X x') (Y x')) x
  + gm.g x (mlieBracket I X Y x) (Z x)
  - gm.g x (mlieBracket I Y Z x) (X x)
  + gm.g x (mlieBracket I Z X x) (Y x)

variable (gm : PseudoRiemannianMetric I M) (X Y Z : Π x : M, TangentSpace I x) (x : M)

/-- The metric-paired function is symmetric *as a function*, so its directional derivatives along any
field agree (`X·g(Y,Z) = X·g(Z,Y)`). -/
theorem dirDeriv_g_symm (W : Π x : M, TangentSpace I x) :
    dirDeriv I W (fun x' => gm.g x' (Y x') (Z x')) x
      = dirDeriv I W (fun x' => gm.g x' (Z x') (Y x')) x := by
  congr 1
  funext x'
  exact gm.symm' x' (Y x') (Z x')

/-- Lie-bracket antisymmetry, read through the metric: `g([Y,X], Z) = −g([X,Y], Z)`. -/
theorem g_mlieBracket_swap :
    gm.g x (mlieBracket I Y X x) (Z x) = - gm.g x (mlieBracket I X Y x) (Z x) := by
  rw [mlieBracket_swap_apply, map_neg, ContinuousLinearMap.neg_apply]

/-- **Metric compatibility of the Levi-Civita connection**, encoded in the Koszul formula:
`koszul X Y Z + koszul X Z Y = 2·(X·g(Y,Z))`. Equivalent to `∇g = 0`. Pure algebra from metric
symmetry + bracket antisymmetry — no differentiability hypotheses. -/
theorem koszul_metric_compat :
    koszul gm X Y Z x + koszul gm X Z Y x
      = 2 * dirDeriv I X (fun x' => gm.g x' (Y x') (Z x')) x := by
  have hf : (fun x' => gm.g x' (Z x') (Y x')) = (fun x' => gm.g x' (Y x') (Z x')) :=
    funext fun x' => gm.symm' x' (Z x') (Y x')
  simp only [koszul, hf]
  have b1 : gm.g x (mlieBracket I Y X x) (Z x) = - gm.g x (mlieBracket I X Y x) (Z x) :=
    g_mlieBracket_swap gm X Y Z x
  have b2 : gm.g x (mlieBracket I Z Y x) (X x) = - gm.g x (mlieBracket I Y Z x) (X x) :=
    g_mlieBracket_swap gm Y Z X x
  have b3 : gm.g x (mlieBracket I X Z x) (Y x) = - gm.g x (mlieBracket I Z X x) (Y x) :=
    g_mlieBracket_swap gm Z X Y x
  linear_combination b1 - b2 + b3

/-- **Torsion-freeness of the Levi-Civita connection**, encoded in the Koszul formula:
`koszul X Y Z − koszul Y X Z = 2·g([X,Y], Z)`. Equivalent to `∇_X Y − ∇_Y X = [X,Y]`. Pure algebra
from metric symmetry + bracket antisymmetry. -/
theorem koszul_torsion_free :
    koszul gm X Y Z x - koszul gm Y X Z x = 2 * gm.g x (mlieBracket I X Y x) (Z x) := by
  have hf : (fun x' => gm.g x' (Y x') (X x')) = (fun x' => gm.g x' (X x') (Y x')) :=
    funext fun x' => gm.symm' x' (Y x') (X x')
  simp only [koszul, hf]
  have b1 : gm.g x (mlieBracket I Y X x) (Z x) = - gm.g x (mlieBracket I X Y x) (Z x) :=
    g_mlieBracket_swap gm X Y Z x
  have b2 : gm.g x (mlieBracket I X Z x) (Y x) = - gm.g x (mlieBracket I Z X x) (Y x) :=
    g_mlieBracket_swap gm Z X Y x
  have b3 : gm.g x (mlieBracket I Z Y x) (X x) = - gm.g x (mlieBracket I Y Z x) (X x) :=
    g_mlieBracket_swap gm Y Z X x
  linear_combination -b1 + b2 - b3

/-- **Product (Leibniz) rule for the directional derivative** of a product of scalar functions:
`W·(f·h) = f·(W·h) + (W·f)·h`. From the manifold product rule `HasMFDerivAt.mul` (whose derivative
is `f x • dh + h x • df` with ordinary smul into `𝕜`, avoiding the opposite-action form). -/
theorem dirDeriv_mul (W : Π z : M, TangentSpace I z) (f h : M → 𝕜) (x : M)
    (hf : MDifferentiableAt I 𝓘(𝕜) f x) (hh : MDifferentiableAt I 𝓘(𝕜) h x) :
    dirDeriv I W (f * h) x = f x * dirDeriv I W h x + dirDeriv I W f x * h x := by
  have key : dirDeriv I W (f * h) x = f x • dirDeriv I W h x + h x • dirDeriv I W f x := by
    show mfderiv I 𝓘(𝕜) (f * h) x (W x) = _
    rw [(hf.hasMFDerivAt.mul hh.hasMFDerivAt).mfderiv]
    rfl
  rw [key]; simp only [smul_eq_mul]; ring

/-- The directional derivative is homogeneous in the field under a scalar function:
`(f•Z)·h = f·(Z·h)`. -/
theorem dirDeriv_smul_field (Z : Π z : M, TangentSpace I z) (f : M → 𝕜) (h : M → 𝕜) (x : M) :
    dirDeriv I (f • Z) h x = f x • dirDeriv I Z h x := by
  show mfderiv I 𝓘(𝕜) h x ((f • Z) x) = f x • mfderiv I 𝓘(𝕜) h x (Z x)
  exact map_smul (mfderiv I 𝓘(𝕜) h x) (f x) (Z x)

/-- **Pointwise** additivity of the directional derivative in the function slot: `W·(f+g) = W·f + W·g`
at a single point `x`, needing only differentiability *at* `x` (unlike `dirDeriv_add_fun`, the
function-level version, which needs differentiability everywhere). This is the form the tensoriality
criterion (`TensorialAt`) consumes. -/
theorem dirDeriv_add_fun_at (W : Π z : M, TangentSpace I z) (f g : M → 𝕜) (x : M)
    (hf : MDifferentiableAt I 𝓘(𝕜) f x) (hg : MDifferentiableAt I 𝓘(𝕜) g x) :
    dirDeriv I W (f + g) x = dirDeriv I W f x + dirDeriv I W g x := by
  show mfderiv I 𝓘(𝕜) (f + g) x (W x) = _
  rw [mfderiv_add hf hg]
  rfl

/-- **Additivity of `koszul` in the `Z` slot** — half of the `C∞`-linearity that lets the Koszul
formula descend to a covector `Z ↦ koszul X Y Z` (hence define `∇_X Y` via the musical `♯`). The
directional-derivative terms split via `dirDeriv` additivity (in the function and in the field) and
the bracket terms via `mlieBracket` additivity; the metric is bilinear. (The `h…` are the
differentiabilities those splits consume.) -/
theorem koszul_add_right_Z [CompleteSpace E] [IsManifold I 2 M]
    (gm : PseudoRiemannianMetric I M) (X Y Z Z' : Π x : M, TangentSpace I x) (x : M)
    (hgYZ : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (Y x') (Z x')) x)
    (hgYZ' : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (Y x') (Z' x')) x)
    (hgXZ : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (X x') (Z x')) x)
    (hgXZ' : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (X x') (Z' x')) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    koszul gm X Y (Z + Z') x = koszul gm X Y Z x + koszul gm X Y Z' x := by
  have e1 : (fun x' => gm.g x' (Y x') ((Z + Z') x'))
      = (fun x' => gm.g x' (Y x') (Z x')) + (fun x' => gm.g x' (Y x') (Z' x')) := by
    funext x'; simp [Pi.add_apply, map_add]
  have e2 : (fun x' => gm.g x' (X x') ((Z + Z') x'))
      = (fun x' => gm.g x' (X x') (Z x')) + (fun x' => gm.g x' (X x') (Z' x')) := by
    funext x'; simp [Pi.add_apply, map_add]
  simp only [koszul, e1, e2]
  rw [dirDeriv_add_fun_at X _ _ x hgYZ hgYZ', dirDeriv_add_fun_at Y _ _ x hgXZ hgXZ']
  simp only [dirDeriv_add_vectorField, mlieBracket_add_right hZ hZ', mlieBracket_add_left hZ hZ',
    Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
  ring

/-- **Homogeneity of `koszul` in the `Z` slot** under a scalar function: `koszul X Y (f•Z) =
f·koszul X Y Z`. Together with `koszul_add_right_Z` this is the full `C∞`-linearity making the Koszul
form a covector in `Z` — hence `∇_X Y := ♯(½·koszul)`. The Leibniz cross-terms `(X·f)·g(Y,Z)` and
`(Y·f)·g(X,Z)` (from the product rule) are cancelled **exactly** by `−(X·f)·g(Z,Y)` and `−(Y·f)·g(Z,X)`
(from the bracket Leibniz) **via metric symmetry** — the cancellation that makes the Levi-Civita
connection well-defined. -/
theorem koszul_smul_right_Z [CompleteSpace E] [IsManifold I 2 M]
    (gm : PseudoRiemannianMetric I M) (X Y Z : Π x : M, TangentSpace I x) (f : M → 𝕜) (x : M)
    (hf : MDifferentiableAt I 𝓘(𝕜) f x)
    (hgYZ : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (Y x') (Z x')) x)
    (hgXZ : MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (X x') (Z x')) x)
    (hZ : MDiffAt (T% Z) x) :
    koszul gm X Y (f • Z) x = f x * koszul gm X Y Z x := by
  have eYZ : (fun x' => gm.g x' (Y x') ((f • Z) x')) = f * fun x' => gm.g x' (Y x') (Z x') := by
    funext x'; simp [Pi.smul_apply, Pi.mul_apply, map_smul, smul_eq_mul]
  have eXZ : (fun x' => gm.g x' (X x') ((f • Z) x')) = f * fun x' => gm.g x' (X x') (Z x') := by
    funext x'; simp [Pi.smul_apply, Pi.mul_apply, map_smul, smul_eq_mul]
  have hbR : gm.g x (mlieBracket I Y (f • Z) x) (X x)
      = dirDeriv I Y f x * gm.g x (Z x) (X x) + f x * gm.g x (mlieBracket I Y Z x) (X x) := by
    rw [mlieBracket_smul_right hf hZ]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rfl
  have hbL : gm.g x (mlieBracket I (f • Z) X x) (Y x)
      = - (dirDeriv I X f x) * gm.g x (Z x) (Y x) + f x * gm.g x (mlieBracket I Z X x) (Y x) := by
    rw [mlieBracket_smul_left hf hZ]
    simp only [map_add, map_neg, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul]
    rfl
  have h4 : gm.g x (mlieBracket I X Y x) ((f • Z) x) = f x * gm.g x (mlieBracket I X Y x) (Z x) := by
    show gm.g x (mlieBracket I X Y x) (f x • Z x) = f x * gm.g x (mlieBracket I X Y x) (Z x)
    rw [map_smul, smul_eq_mul]
  have sYZ : gm.g x (Y x) (Z x) = gm.g x (Z x) (Y x) := gm.symm' x (Y x) (Z x)
  have sXZ : gm.g x (X x) (Z x) = gm.g x (Z x) (X x) := gm.symm' x (X x) (Z x)
  simp only [koszul, eYZ, eXZ, dirDeriv_mul X f _ x hf hgYZ,
    dirDeriv_mul Y f _ x hf hgXZ, dirDeriv_smul_field, h4, smul_eq_mul, hbR, hbL]
  linear_combination (dirDeriv I X f x) * sYZ + (dirDeriv I Y f x) * sXZ

open Bundle in
/-- **The Koszul form is tensorial in `Z`.** Packaging the additivity (`koszul_add_right_Z`) and
homogeneity (`koszul_smul_right_Z`) as Mathlib's `TensorialAt` criterion: `σ ↦ koszul X Y σ x` is a
tensorial operation at `x`. By `TensorialAt.mkHom` this defines a *covector* `T_xM →L 𝕜` — the Koszul
1-form — whose metric-dual (`♯`) is the Levi-Civita `∇_X Y`. `hsmooth` is metric smoothness (a smooth
metric pairs smooth fields to a smooth function); over `ℝ`/`ℂ` with a smooth metric it is automatic. -/
theorem koszul_tensorialAt [CompleteSpace E] [IsManifold I 2 M]
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x) :
    TensorialAt I E (fun σ => koszul gm X Y σ x) x where
  smul {f σ} hf hσ :=
    koszul_smul_right_Z gm X Y σ f x hf (hsmooth Y σ hY hσ) (hsmooth X σ hX hσ) hσ
  add {σ σ'} hσ hσ' :=
    koszul_add_right_Z gm X Y σ σ' x (hsmooth Y σ hY hσ) (hsmooth Y σ' hY hσ')
      (hsmooth X σ hX hσ) (hsmooth X σ' hX hσ') hσ hσ'

section LeviCivitaConnection

open Bundle

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- **The Koszul 1-form** `Z ↦ ½ g(∇_X Y, Z)` as a genuine covector `T_xM →L[𝕜] 𝕜`, obtained from the
tensorial Koszul scalar via Mathlib's `TensorialAt.mkHom`. (Carries the smoothness/regularity data
`hX, hY, hsmooth` the tensoriality needs.) -/
noncomputable def koszulForm
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x) :
    TangentSpace I x →L[𝕜] 𝕜 :=
  TensorialAt.mkHom (fun σ => koszul gm X Y σ x) x (koszul_tensorialAt gm X Y x hX hY hsmooth)

/-- The Koszul 1-form, evaluated on a differentiable field's value, returns the Koszul scalar. -/
theorem koszulForm_apply
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x)
    (Z : Π z : M, TangentSpace I z) (hZ : MDiffAt (T% Z) x) :
    koszulForm gm X Y x hX hY hsmooth (Z x) = koszul gm X Y Z x :=
  TensorialAt.mkHom_apply (koszul_tensorialAt gm X Y x hX hY hsmooth) hZ

/-- **The Levi-Civita connection vector** `∇_X Y` at `x`: the metric-dual (musical `♯`) of half the
Koszul 1-form. This is *the* vector characterised by the Koszul formula. -/
noncomputable def leviCivita
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x) :
    TangentSpace I x :=
  gm.raise x ((1 / 2 : 𝕜) • koszulForm gm X Y x hX hY hsmooth)

/-- **The Levi-Civita connection satisfies the Koszul formula:** `g(∇_X Y, Z) = ½·koszul X Y Z`.
This is the realisation of the defining equation — `∇_X Y` is exactly the vector whose metric pairing
reproduces the Koszul scalar. Combined with `koszul_metric_compat`/`koszul_torsion_free`, it certifies
`∇` as metric-compatible and torsion-free. -/
theorem leviCivita_koszul
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x)
    (Z : Π z : M, TangentSpace I z) (hZ : MDiffAt (T% Z) x) :
    gm.g x (leviCivita gm X Y x hX hY hsmooth) (Z x) = (1 / 2 : 𝕜) * koszul gm X Y Z x := by
  rw [leviCivita, ← PseudoRiemannianMetric.lower_apply, gm.lower_raise]
  rw [ContinuousLinearMap.smul_apply, koszulForm_apply gm X Y x hX hY hsmooth Z hZ, smul_eq_mul]

/-- **Uniqueness of the Levi-Civita vector (the musical solve).** Any tangent vector `V` whose lowered
covector is half the Koszul 1-form *is* `leviCivita` — the metric-dual `♯` is single-valued by
nondegeneracy (`lower_injective`). This realises "solve `g(∇_X Y, ·) = ½·koszul` for `∇_X Y`": the
Koszul 1-form determines `∇_X Y` uniquely, the abstract counterpart of the component fundamental
theorem `QIQTH.Curvature.christoffel_unique`. -/
theorem leviCivita_unique
    (gm : PseudoRiemannianMetric I M) (X Y : Π x : M, TangentSpace I x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hsmooth : ∀ A B : Π z : M, TangentSpace I z, MDiffAt (T% A) x → MDiffAt (T% B) x →
      MDifferentiableAt I 𝓘(𝕜) (fun x' => gm.g x' (A x') (B x')) x)
    (V : TangentSpace I x)
    (hV : gm.lower x V = (1 / 2 : 𝕜) • koszulForm gm X Y x hX hY hsmooth) :
    V = leviCivita gm X Y x hX hY hsmooth := by
  apply gm.lower_injective x
  rw [hV]
  simp only [leviCivita, PseudoRiemannianMetric.lower_raise]

end LeviCivitaConnection

section Einstein

open Bundle

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- **Scalar curvature** as the metric trace of a Ricci bilinear form `Ric`:
`R = g^{YZ} Ric(Y,Z) = tr(♯ ∘ Ric)`. (`♯ ∘ Ric : T_xM →L T_xM` is the Ricci operator; its trace is the
metric contraction.) -/
noncomputable def scalarCurvature (gm : PseudoRiemannianMetric I M) (x : M)
    (ricciForm : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) : 𝕜 :=
  LinearMap.trace 𝕜 (TangentSpace I x) ((gm.raise x).comp ricciForm).toLinearMap

/-- **The Einstein tensor** as a bilinear form on `T_xM`: `G = Ric − ½·R·g`, the combination whose
covariant divergence vanishes (contracted Bianchi) and which equals the stress-energy tensor in
Jacobson's equation of state. -/
noncomputable def einsteinForm (gm : PseudoRiemannianMetric I M) (x : M)
    (ricciForm : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜 :=
  ricciForm - ((1 / 2 : 𝕜) * scalarCurvature gm x ricciForm) • gm.g x

/-- The Einstein tensor unfolds to `Ric − ½·R·g` (definitional restatement, for downstream rewriting). -/
theorem einsteinForm_eq (gm : PseudoRiemannianMetric I M) (x : M)
    (ricciForm : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜) :
    einsteinForm gm x ricciForm
      = ricciForm - ((1 / 2 : 𝕜) * scalarCurvature gm x ricciForm) • gm.g x := rfl

/-- **The Einstein tensor is symmetric** — `G(v,w) = G(w,v)` — whenever the Ricci form is symmetric
(it is, for the Levi-Civita connection). The metric term is symmetric by `gm.symm'`. -/
theorem einsteinForm_symm (gm : PseudoRiemannianMetric I M) (x : M)
    (ricciForm : TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜)
    (hric : ∀ v w : TangentSpace I x, ricciForm v w = ricciForm w v)
    (v w : TangentSpace I x) :
    einsteinForm gm x ricciForm v w = einsteinForm gm x ricciForm w v := by
  simp only [einsteinForm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hric v w, gm.symm' x v w]

end Einstein

end QIQTH.ManifoldGR
