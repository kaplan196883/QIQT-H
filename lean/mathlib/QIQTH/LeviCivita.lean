import QIQTH.PseudoRiemannian
import QIQTH.ManifoldCommutator

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

end QIQTH.ManifoldGR
