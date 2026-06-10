/-
  Limit-stability of the Loewner order on `Matrix n n ℂ` — the analytical core of the continuity
  step in Ando's route to Lieb's concavity.

  A joint-concavity (superadditivity) inequality proved on a dense set of weights extends to all
  weights by continuity, *because the Loewner order is closed under limits*.  Mathlib proves the
  positive cone of a C⋆-algebra is closed (`OrderClosedTopology` for any `CStarAlgebra`); via the
  `CStarMatrix` bridge (`ofMatrix_le_iff` + the homeomorphism `ofMatrixL`) this transfers to our
  Frobenius-normed `Matrix n n ℂ`:

  * `matrix_le_of_tendsto` — `fᵢ ≤ gᵢ`, `fᵢ → a`, `gᵢ → b` ⟹ `a ≤ b`;
  * `matrix_superadditive_of_tendsto` — pointwise limits preserve the two-point superadditivity
    inequality, the exact shape of joint concavity used throughout the geometric-mean tower.
-/
import QIQTH.Entropy.CStarMatrixBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace QIQTH.Entropy

open Matrix CStarMatrix Filter Topology
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Loewner order is closed under limits.**  If `fᵢ ≤ gᵢ` for all `i`, `fᵢ → a` and `gᵢ → b`,
    then `a ≤ b`.  Transferred from the `OrderClosedTopology` of the C⋆-algebra `CStarMatrix n n ℂ`
    across the bridge (`ofMatrixStarAlgEquiv` is an order iso and a homeomorphism). -/
theorem matrix_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {f g : ι → Matrix n n ℂ} {a b : Matrix n n ℂ}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (h : ∀ i, f i ≤ g i) : a ≤ b := by
  have hcont : Continuous (ofMatrixStarAlgEquiv : Matrix n n ℂ → CStarMatrix n n ℂ) :=
    (ofMatrixL (A := ℂ) (m := n) (n := n)).continuous
  rw [← ofMatrix_le_iff]
  exact le_of_tendsto_of_tendsto' ((hcont.tendsto a).comp hf) ((hcont.tendsto b).comp hg)
    (fun i => ofMatrix_le_iff.mpr (h i))

/-- **Joint concavity (superadditivity) is preserved under pointwise limits**, in the shape produced
    by the geometric-mean tower: if `aᵢ + bᵢ ≤ cᵢ` for all `i`, `aᵢ → a`, `bᵢ → b`, `cᵢ → c`, then
    `a + b ≤ c`.  This is the limit step — superadditivity at a dense set of weights (e.g. the dyadics
    `t = 1/2ᵏ` from `nestGmean_superadditive`) extends to all weights. -/
theorem add_le_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {a' b' c' : ι → Matrix n n ℂ} {a b c : Matrix n n ℂ}
    (ha : Tendsto a' l (𝓝 a)) (hb : Tendsto b' l (𝓝 b)) (hc : Tendsto c' l (𝓝 c))
    (h : ∀ i, a' i + b' i ≤ c' i) : a + b ≤ c :=
  matrix_le_of_tendsto (ha.add hb) hc h

end QIQTH.Entropy
