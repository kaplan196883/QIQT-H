/-
  ParametrixResidualO1Total — M5 off-diagonal step: the TOTAL `O(1/t)` coefficient of the
  folded-parametrix residual, ASSEMBLED from the three isolated pieces (I)/(IV)/(II).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The off-diagonal heat-operator residual of the Minakshisundaram–DeWitt parametrix is decomposed
  UNCONDITIONALLY by `parametrixResidual_offdiag_absorbed` into five pieces:
      (I)   `(∂_t G − Δ_g G)(v)·P(v)`                      — flat-Gaussian curvature residue,
      (∂_t) `G·Σ_k w_k·(k t^{k−1})`                        — the `∂_t P` polynomial (order `t⁰…`),
      (II)  `(1/t)·G·(r∂_r P)(v)`                          — the RADIAL-TRANSPORT operator,
      (III) `−G·Σ_k (Δ_g w_k)·t^k`                         — `Δ_g` of the coefficients (order `t⁰…`),
      (IV)  `−Σᵢⱼ (gⁱʲ−δ)((∂ᵢG)(∂ⱼP)+(∂ⱼG)(∂ᵢP))(v)`       — metric-deviation cross-gradient residue.
  The three SINGULAR (`O(1/t)`, `O(1/t²)`) pieces have been isolated in normal form by the three
  landed bricks (c1/c2/c4):
      • (II)  `radialTransportTerm_leading_split` :  `= (1/t)·G·(r∂_r w₀) + G·Σ_{k<N}(r∂_r w_{k+1})t^k`,
      • (IV)  `deviationCrossTerm_leading_parametrix` : `= (1/t)·G·(−½ Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼP+vʲ∂ᵢP))`,
      • (I)   `flatCurvatureResidue_leading_parametrix` :
              `= ((1/t)·G·[½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ] + (1/t²)·G·[−¼Σ(gⁱʲ−δ)vⁱvʲ])·P`.

  This file ASSEMBLES those isolations into one place:

    • `parametrixResidual_offdiag_O1_total` — the FULL general-`N` assembled residual, with all three
      singular pieces substituted into their normal forms (a rewrite of `…_absorbed` by c1/c2/c4).

    • `totalRadialO1_coeff` — THE assembled `O(1/t)` coefficient (leading van-Vleck order):
        `[½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ]·w₀  +  (r∂_r w₀)  +  ½ Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)`
      — the sum of the leading (`t⁰`-order) contributions of (I), (II) and (−IV).  Its three summands
      are exactly the DeWitt transport-equation terms at `k=0`.

    • `parametrixResidual_N0_O1_isolated` — at `N=0` (the leading van-Vleck order, where the polynomial
      `P` collapses to `w₀` and `totalRadialO1_coeff` is EXACTLY the coefficient of `(1/t)·G`):
        `(∂_t − Δ_g)H_0(t,v) = (1/t)·G·totalRadialO1_coeff + (1/t²)·G·[−¼Σ(gⁱʲ−δ)vⁱvʲ]·w₀ − G·Δ_g w₀` .
      This EXHIBITS the assembled `O(1/t)` coefficient in isolation.

    • `totalRadialO1_coeff_center_vanishes` — at the RNC CENTRE (`v=0`, with `gⁱⁱ(0)=1`) the assembled
      `O(1/t)` coefficient VANISHES (`= 0`) — the DIAGONAL face of the cancellation, recovered here as
      a consequence of the assembly (validating that the three off-diagonal pieces sum correctly).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  This is the ASSEMBLED-TOTAL `O(1/t)` coefficient + the DIAGONAL (`v=0`)
  cancellation, NOT the full OFF-DIAGONAL (`v≠0`) cancellation to `0`.  The remaining identity is

      [CHECKPOINT — the general-`v` DeWitt transport equation]
        totalRadialO1_coeff g gi Θ u v = 0   for all `v` near the RNC centre,  i.e.
        `[½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ]·w₀(v) + (r∂_r w₀)(v) + ½Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)(v) = 0` .

  This is precisely the `k=0` DeWitt/van-Vleck transport equation `(r∂_r)w₀ = ½Θ^{−1/2}Δ_g(Θ^{1/2})`
  in the off-diagonal (radial-Raychaudhuri) form.  It is NOT available as a general-`v` identity in the
  current library:  the radial term `(r∂_r)w₀` is connected to `(r∂_r) log det g̃` and thence to Ricci
  ONLY in the `expMap`/`expPullbackMetric` representation (`radialDeriv_foldedCoeff_leading`,
  `vanVleck_radialDeriv_ricci_form`), whereas the `A` and deviation terms are carried SYMBOLICALLY in
  the `(gⁱʲ, Γ)` representation.  The two representations coincide only through the point-`0` RNC
  2-jets (`rnc_gInv_hessian`, `pd_christoffel_*`), which identify BOTH sides with the same Ricci
  contraction — a Taylor/RNC-substitution step, not a general-`v` algebraic identity.  So the `=0` is
  DEFERRED to the RNC-substitution brick; the DIAGONAL (`v=0`) face IS discharged here.

  This is NOT `a₁ = R/6` (M6 parametrix convergence remains).  No axioms, no `sorry`, no vacuous hyps.
  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1.
-/
import Mathlib
import QIQTH.HeatResidualBound
import QIQTH.ParametrixRadialTransportSplit
import QIQTH.ParametrixDeviationCrossTerm
import QIQTH.ParametrixFlatCurvatureResidue
import QIQTH.VanVleckCancellation
import QIQTH.RNCInverseMetricJet

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance
open QIQTH.ParametrixRadialTransportSplit
open QIQTH.VanVleckCancellation

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### The assembled general-`N` residual: (I)/(IV)/(II) in singular normal form. -/

/-- **THE ASSEMBLED OFF-DIAGONAL RESIDUAL (general `N`).**  Substituting the three landed isolations
    (c1 `radialTransportTerm_leading_split`, c2 `deviationCrossTerm_leading_parametrix`,
    c4 `flatCurvatureResidue_leading_parametrix`) into the unconditional decomposition
    `parametrixResidual_offdiag_absorbed`, the residual `(∂_t − Δ_g)H_N(t,v)` is written with ALL THREE
    singular pieces in their `(1/t)·G` / `(1/t²)·G` normal form:
      • (I)  `= ((1/t)·G·[½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ] + (1/t²)·G·[−¼Σ(gⁱʲ−δ)vⁱvʲ])·P`,
      • (II) `= (1/t)·G·(r∂_r w₀) + G·Σ_{k<N}(r∂_r w_{k+1})t^k`,
      • (IV) `= (1/t)·G·(−½ Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼP+vʲ∂ᵢP))` (subtracted).
    The two regular pieces (∂_t P and `Δ_g` of the coefficients) are carried verbatim.  This is the
    single collection point for the residual's `O(1/t)` content.  Only coefficient smoothness `hw` is
    used; the metric is arbitrary.  NOT the cancellation to `0` (see CHECKPOINT in header). -/
theorem parametrixResidual_offdiag_O1_total (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN N g gi Θ u t v
      = ((1 / t) * gaussDdim t v
            * ((1 / 2) * (∑ i, (gi v i i - 1))
                - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
          + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + ((1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
            + gaussDdim t v
                * ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k)
        - gaussDdim t v
            * (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (1 / t) * gaussDdim t v
            * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
                * (v i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
                    + v j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  rw [parametrixResidual_offdiag_absorbed N g gi Θ u t ht v hw,
      flatCurvatureResidue_leading_parametrix N g gi Θ u t ht v,
      radialTransportTerm_leading_split N Θ u t ht v hw,
      deviationCrossTerm_leading_parametrix N gi Θ u t ht v]

/-! ### The assembled `O(1/t)` coefficient (leading van-Vleck order). -/

/-- **THE ASSEMBLED `O(1/t)` COEFFICIENT of the folded-parametrix residual** — the sum of the
    leading (`t⁰`-order) contributions of pieces (I), (II) and (−IV):
      `[½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ]·w₀  +  (r∂_r w₀)  +  ½ Σᵢⱼ(gⁱʲ−δ)(vⁱ∂ⱼw₀+vʲ∂ᵢw₀)` .
    These three summands are precisely the terms of the `k=0` DeWitt/van-Vleck transport equation.
    (`w₀ = foldedCoeff Θ u 0 = Θ^{−1/2}·u₀`.)  Vanishing of this coefficient near the RNC centre is the
    off-diagonal M5 cancellation — the CHECKPOINTED identity (see header). -/
noncomputable def totalRadialO1_coeff (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n) : ℝ :=
  ((1 / 2) * (∑ i, (gi v i i - 1))
      - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
      * foldedCoeff Θ u 0 v
    + radialDeriv (foldedCoeff Θ u 0) v
    + (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd (foldedCoeff Θ u 0) j v + v j * pd (foldedCoeff Θ u 0) i v))

/-- **`N=0` RESIDUAL WITH THE ASSEMBLED `O(1/t)` COEFFICIENT EXHIBITED.**  At the leading van-Vleck
    order `N=0` the parametrix polynomial `P` collapses to the single coefficient `w₀`, so the mixing
    of `t`-orders disappears and `totalRadialO1_coeff` is EXACTLY the coefficient of `(1/t)·G`:
      `(∂_t − Δ_g)H_0(t,v)`
        `= (1/t)·G·totalRadialO1_coeff`
          `+ (1/t²)·G·[−¼Σᵢⱼ(gⁱʲ−δ)vⁱvʲ]·w₀`      -- the (I) `1/t²` residue (separate order)
          `− G·(Δ_g w₀)` .                          -- the regular `Δ_g` driver
    Only coefficient smoothness `hw` is used; the metric is arbitrary.  NOT the cancellation to `0`. -/
theorem parametrixResidual_N0_O1_isolated (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN 0 g gi Θ u t v
      = (1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
        + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
            * foldedCoeff Θ u 0 v
        - gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
  -- the `N=0` parametrix polynomial `Σ_{k≤0} w_k y t^k` is the constant-in-`t` field `w₀`.
  have hPfun : (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k)
      = foldedCoeff Θ u 0 := by
    funext y; rw [zero_add, Finset.sum_range_one, pow_zero, mul_one]
  rw [parametrixResidual_offdiag_O1_total 0 g gi Θ u t ht v hw, hPfun, zero_add,
      Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_zero]
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  unfold totalRadialO1_coeff
  ring

/-! ### The diagonal (`v = 0`) face of the assembled cancellation. -/

/-- **THE ASSEMBLED `O(1/t)` COEFFICIENT AT THE RNC CENTRE.**  At `v = 0` the Euler radial field
    vanishes (`radialDeriv_zero`) and every `vⁱ`-weighted term drops, leaving only the metric-trace
    term:  `totalRadialO1_coeff g gi Θ u 0 = ½·(Σᵢ(gⁱⁱ(0)−1))·w₀(0)`. -/
theorem totalRadialO1_coeff_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) :
    totalRadialO1_coeff g gi Θ u (0 : Point n)
      = (1 / 2) * (∑ i, (gi (0 : Point n) i i - 1)) * foldedCoeff Θ u 0 (0 : Point n) := by
  unfold totalRadialO1_coeff
  rw [radialDeriv_zero]
  have hΓ : (∑ i, ∑ j, ∑ k, gi (0 : Point n) i j
        * christoffel g gi k i j (0 : Point n) * (0 : Point n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    simp
  have hD : (∑ i, ∑ j, (gi (0 : Point n) i j - (if i = j then (1 : ℝ) else 0))
        * ((0 : Point n) i * pd (foldedCoeff Θ u 0) j (0 : Point n)
            + (0 : Point n) j * pd (foldedCoeff Θ u 0) i (0 : Point n))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp
  rw [hΓ, hD]
  ring

/-- **DIAGONAL CANCELLATION (the `v=0` face).**  At the RNC centre, with the single normal-coordinate
    datum `gⁱⁱ(0) = 1`, the assembled `O(1/t)` coefficient VANISHES:
      `totalRadialO1_coeff g gi Θ u 0 = 0` .
    This is the diagonal face of the van-Vleck leading cancellation, recovered here AS A CONSEQUENCE
    of the (I)/(II)/(IV) assembly — a consistency check that the three off-diagonal pieces sum
    correctly.  The OFF-diagonal (`v≠0`) vanishing is the CHECKPOINTED identity (see header). -/
theorem totalRadialO1_coeff_center_vanishes (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (hg0 : ∀ i, gi (0 : Point n) i i = 1) :
    totalRadialO1_coeff g gi Θ u (0 : Point n) = 0 := by
  rw [totalRadialO1_coeff_at_center]
  have : (∑ i, (gi (0 : Point n) i i - 1)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hg0 i]; ring
  rw [this]; ring

end QIQTH.HeatResidualBound
