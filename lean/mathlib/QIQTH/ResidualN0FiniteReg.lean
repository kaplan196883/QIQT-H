/-
  ResidualN0FiniteReg — brick R3b of the RECENTER campaign: the FINITE-REGULARITY
  (`ContDiffAt ℝ 2`) refactor of the `N = 0` parametrix-residual ALGEBRAIC ISOLATION.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The `N = 0` parametrix-residual Gaussian bound `residualN0_gaussian_bound`
  (`QIQTH.ParametrixResidualN0Bound`) assembles THREE pieces:

    (1) the leading `1/t` term  — `residualLeading_gaussian_bound`,
    (2) the `1/t²` residue      — `residualQuadratic_gaussian_bound`,
    (3) the `Δ_g w₀` driver     — via `|Δ_g w₀| ≤ L` + `gaussDdim ≤ gaussDdimWide`,

  glued by the ALGEBRAIC ISOLATION identity `parametrixResidual_N0_O1_isolated`, which rewrites the
  raw residual `parametrixResidualN 0` into those three terms.  All of these are stated at
  `ContDiff ℝ ⊤`.  Where is `⊤` genuinely needed?

    • term (2) `residualQuadratic_gaussian_bound` — ALREADY carries NO smoothness hypothesis
      (pure metric-deviation / polynomial-absorption algebra).  Nothing to weaken.
    • term (3) driver + `gaussDdim_le_gaussDdimWide` — carry NO smoothness (only the `|Δ_g w₀| ≤ L`
      boundedness).  Nothing to weaken.
    • the ISOLATION identity `parametrixResidual_N0_O1_isolated` — its ONLY smoothness use is on the
      coefficient `w₀ = foldedCoeff Θ u 0`, entering through `Δ_g w₀` (a SECOND-order operator) and a
      first-order cross-gradient.  So it needs `C²` of `w₀`, NOT `⊤`.  ★ THIS is what this file
      discharges: the isolation identity at `ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v`.
    • term (1) `residualLeading_gaussian_bound` → `totalRadialO1_coeff_isLittleO` — the `o(‖v‖²)`
      2-jet of a coefficient that CONTAINS the Christoffel symbols `Γ = ∂g`.  Its vanishing-Hessian
      proof needs the SECOND derivative of `Γ`, i.e. `g ∈ C³`.  This is a GENUINE `C³` wall, strictly
      above the `C²` that the q-centered `expPullbackMetric` supplies.  NOT discharged here (see the
      report / next R-brick).

  Landed here (all at `ContDiffAt ℝ 2`, all `[AF]` std-3, no `sorry`, no vacuous hypotheses):

    • `laplaceBeltrami_mul_mixed_C2` — the un-symmetrised `C²` Laplace–Beltrami product rule
      `Δ_g(fh) = (Δ_g f)h + f(Δ_g h) + Σᵢⱼ gⁱʲ(∂ᵢf ∂ⱼh + ∂ⱼf ∂ᵢh)`, the finite-regularity analogue of
      `HeatParametrixOrder.laplaceBeltrami_mul` (which keeps the un-symmetrised cross form, so NO
      inverse-metric symmetry hypothesis is required).  Reuses R1's `pd_pd_mul_C2` (which matches
      `pd_pd_mul_mixed` verbatim) and R1's `PdiffAt_of_contDiffAt`.
    • `parametrixResidual_offdiag_decomp_N0_C2`, `parametrixResidual_offdiag_absorbed_N0_C2`,
      `parametrixResidual_offdiag_O1_total_N0_C2` — the `N = 0` specialisations of the off-diagonal
      residual decomposition chain at `C²` (the `t`-derivative and the flat-Gaussian / cross-gradient
      transform lemmas already carry NO `w`-smoothness; only the `Δ_g(G·w₀)` split needed `C²`).
    • `parametrixResidual_N0_O1_isolated_C2` — ★ the isolation identity at `C²`:
        `parametrixResidualN 0 g gi Θ u t v
           = (1/t)·G·totalRadialO1_coeff + (1/t²)·G·[−¼Σ(gⁱʲ−δ)vⁱvʲ]·w₀ − G·Δ_g w₀` ,
      with the sole hypothesis `ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v` (down from `∀ k, ContDiff ℝ ⊤`).

  This strictly reduces the `⊤`-surface of the `N = 0` residual bound: after this file, the ONLY
  remaining `⊤`-dependency of `residualN0_gaussian_bound` is term (1)'s `C³` little-o wall.  NOT
  `a₁ = R/6`, NOT the general-`N` bound, NOT wired into `iterConv_bound`.
-/
import Mathlib
import QIQTH.ParametrixResidualN0Bound
import QIQTH.LaplaceBeltramiFiniteReg
import QIQTH.RNCExpansionFiniteReg
import QIQTH.ParametrixRadialTransportSplit
import QIQTH.ParametrixDeviationCrossTerm
import QIQTH.ParametrixFlatCurvatureResidue

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### The un-symmetrised Laplace–Beltrami product rule at `C²`. -/

/-- **The un-symmetrised `C²` Laplace–Beltrami product rule.**  The finite-regularity
    (`ContDiffAt ℝ 2`) analogue of `HeatParametrixOrder.laplaceBeltrami_mul`:
      `Δ_g(fh)(x) = (Δ_g f)(x)·h(x) + f(x)·(Δ_g h)(x) + Σᵢⱼ gⁱʲ(∂ᵢf ∂ⱼh + ∂ⱼf ∂ᵢh)(x)` .
    The cross term is kept UN-symmetrised (as in the `HeatParametrixOrder` version), so — unlike the
    symmetric `laplaceBeltrami_mul_C2` — NO inverse-metric symmetry hypothesis is needed.  Proof is a
    verbatim port of the `⊤` version with `pd_pd_mul_mixed → pd_pd_mul_C2` (R1, identical conclusion)
    and `PdiffAt_of_contDiff → PdiffAt_of_contDiffAt` (R1).  The metric / Christoffel data enter only
    as VALUES at `x`, so no metric-regularity hypothesis is required. -/
theorem laplaceBeltrami_mul_mixed_C2 (g gi : Point n → Fin n → Fin n → ℝ) (f h : Point n → ℝ)
    (x : Point n) (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    laplaceBeltrami g gi (fun y => f y * h y) x
      = laplaceBeltrami g gi f x * h x + f x * laplaceBeltrami g gi h x
        + ∑ i, ∑ j, gi x i j * (pd f i x * pd h j x + pd f j x * pd h i x) := by
  simp only [laplaceBeltrami]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by norm_num)
  have hh1 : ContDiffAt ℝ 1 h x := hh.of_le (by norm_num)
  have hsec : pd (fun y => pd (fun z => f z * h z) j y) i x
      = pd (fun y => pd f j y) i x * h x + pd f j x * pd h i x
        + pd f i x * pd h j x + f x * pd (fun y => pd h j y) i x :=
    pd_pd_mul_C2 f h i j x hf hh
  have hΓ : (∑ k, christoffel g gi k i j x * pd (fun z => f z * h z) k x)
      = (∑ k, christoffel g gi k i j x * pd f k x) * h x
        + f x * ∑ k, christoffel g gi k i j x * pd h k x := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul f h k x (PdiffAt_of_contDiffAt f k x hf1) (PdiffAt_of_contDiffAt h k x hh1)]; ring
  rw [hsec, hΓ]; ring

/-! ### The `N = 0` off-diagonal residual decomposition at `C²`. -/

/-- **`N = 0` off-diagonal residual decomposition at `C²`** — the finite-regularity analogue of
    `parametrixResidual_offdiag_decomp` at `N = 0`.  The only `⊤`-dependency of the general-`N`
    version was the `Δ_g(G·P)` split (`laplaceBeltrami_mul`) and the polynomial linearity
    (`laplaceBeltrami_sum_pow`); both are replaced by their `C²` / `N = 0` counterparts.  The
    `t`-derivative part carries no `w`-smoothness. -/
theorem parametrixResidual_offdiag_decomp_N0_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v) :
    parametrixResidualN 0 g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        - gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  -- (A) the `t`-derivative of `H_0(·,v)` via the product rule `(∂_t G)·P + G·(∂_t P)`
  have hgaussHD : HasDerivAt (fun s => gaussDdim s v)
      (deriv (fun s => gaussDdim s v) t) t := by
    have hFP := HasDerivAt.fun_finsetProd
      (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        heatKernel1D_hasDerivAt_t t (v i) ht)
    exact hFP.differentiableAt.hasDerivAt
  have hpoly : HasDerivAt
      (fun s => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * s ^ k)
      (∑ k ∈ Finset.range (0 + 1),
        foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t := by
    have key : HasDerivAt
        (∑ k ∈ Finset.range (0 + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        (∑ k ∈ Finset.range (0 + 1),
          foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1))) t :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k t).const_mul (foldedCoeff Θ u k v))
    have hfun : (∑ k ∈ Finset.range (0 + 1), fun s : ℝ => foldedCoeff Θ u k v * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key
    exact key
  have hderiv_fun : (fun s => heatParametrix 0 Θ u s v)
      = (fun s => gaussDdim s v
          * ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * s ^ k) :=
    funext (fun s => heatParametrix_folded 0 Θ u s v)
  have hderivval : deriv (fun s => heatParametrix 0 Θ u s v) t
      = deriv (fun s => gaussDdim s v) t
          * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * ∑ k ∈ Finset.range (0 + 1),
              foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)) := by
    rw [hderiv_fun]; exact (hgaussHD.mul hpoly).deriv
  -- (B) the `Δ_g` of `H_0(t,·)` via the un-symmetrised `C²` product rule (cross-gradient KEPT)
  have hHeq : heatParametrix 0 Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded 0 Θ u t y)
  have hCDg : ContDiffAt ℝ 2 (fun y => gaussDdim t y) v :=
    (gaussDdim_contDiff t).contDiffAt.of_le le_top
  have hCDP : ContDiffAt ℝ 2
      (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v := by
    have hcollapse : (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k)
        = foldedCoeff Θ u 0 := by
      funext y; rw [zero_add, Finset.sum_range_one, pow_zero, mul_one]
    rw [hcollapse]; exact hw0
  have hΔsum : laplaceBeltrami g gi
        (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v
      = ∑ k ∈ Finset.range (0 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k := by
    have hcollapse : (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k)
        = foldedCoeff Θ u 0 := by
      funext y; rw [zero_add, Finset.sum_range_one, pow_zero, mul_one]
    rw [hcollapse, zero_add, Finset.sum_range_one, pow_zero, mul_one]
  have hΔval : laplaceBeltrami g gi (heatParametrix 0 Θ u t) v
      = laplaceBeltrami g gi (gaussDdim t) v
          * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
          * (∑ k ∈ Finset.range (0 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        + ∑ i, ∑ j, gi v i j
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v) := by
    rw [hHeq,
        laplaceBeltrami_mul_mixed_C2 g gi (fun y => gaussDdim t y)
          (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v hCDg hCDP,
        hΔsum]
  unfold parametrixResidualN
  rw [hderivval, hΔval]
  ring

/-- **`N = 0` off-diagonal absorption identity at `C²`** — the finite-regularity analogue of
    `parametrixResidual_offdiag_absorbed` at `N = 0`.  Verbatim port: the flat cross-gradient is
    absorbed into the radial transport by `flatCrossTerm_eq` (no smoothness), and the decomposition
    is supplied by `parametrixResidual_offdiag_decomp_N0_C2`. -/
theorem parametrixResidual_offdiag_absorbed_N0_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v) :
    parametrixResidualN 0 g gi Θ u t v
      = (deriv (fun s => gaussDdim s v) t - laplaceBeltrami g gi (gaussDdim t) v)
          * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + (1 / t) * gaussDdim t v
            * radialDeriv (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v
        - gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  have hsplit : (∑ i, ∑ j, gi v i j
        * (pd (fun y => gaussDdim t y) i v
              * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
          + pd (fun y => gaussDdim t y) j v
              * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (pd (fun y => gaussDdim t y) i v
                * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
            + pd (fun y => gaussDdim t y) j v
                * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v))
        + (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0)
            * (pd (fun y => gaussDdim t y) i v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
              + pd (fun y => gaussDdim t y) j v
                  * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [parametrixResidual_offdiag_decomp_N0_C2 g gi Θ u t ht v hw0, hsplit,
      flatCrossTerm_eq t ht
        (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v]
  ring

/-- **`N = 0` assembled `O(1/t)` residual at `C²`** — the finite-regularity analogue of
    `parametrixResidual_offdiag_O1_total` at `N = 0`.  The three transform lemmas
    (`flatCurvatureResidue_leading_parametrix`, radial-transport collapse at `N = 0`,
    `deviationCrossTerm_leading_parametrix`) carry no `w`-smoothness; only the absorption identity
    needs `C²`. -/
theorem parametrixResidual_offdiag_O1_total_N0_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v) :
    parametrixResidualN 0 g gi Θ u t v
      = ((1 / t) * gaussDdim t v
            * ((1 / 2) * (∑ i, (gi v i i - 1))
                - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
          + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
          * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * t ^ k)
        + gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
        + ((1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
            + gaussDdim t v
                * ∑ k ∈ Finset.range 0, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k)
        - gaussDdim t v
            * (∑ k ∈ Finset.range (0 + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
        - (1 / t) * gaussDdim t v
            * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
                * (v i * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) j v
                    + v j * pd (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) i v)) := by
  -- the `N = 0` radial-transport collapse: `range 0 = ∅` and `P` collapses to `w₀`.
  have hRT : (1 / t) * gaussDdim t v
        * radialDeriv (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k) v
      = (1 / t) * gaussDdim t v * radialDeriv (foldedCoeff Θ u 0) v
        + gaussDdim t v
            * ∑ k ∈ Finset.range 0, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k := by
    have hcollapse : (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k)
        = foldedCoeff Θ u 0 := by
      funext y; rw [zero_add, Finset.sum_range_one, pow_zero, mul_one]
    rw [hcollapse, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
  rw [parametrixResidual_offdiag_absorbed_N0_C2 g gi Θ u t ht v hw0,
      flatCurvatureResidue_leading_parametrix 0 g gi Θ u t ht v, hRT,
      deviationCrossTerm_leading_parametrix 0 gi Θ u t ht v]

/-! ### ★ The `N = 0` isolation identity at `C²`. -/

/-- **★ THE `N = 0` PARAMETRIX-RESIDUAL ISOLATION IDENTITY AT `C²` (R3b).**  The finite-regularity
    analogue of `parametrixResidual_N0_O1_isolated`: at the leading van-Vleck order the raw heat
    residual splits into the three assembled terms
      `parametrixResidualN 0 g gi Θ u t v`
        `= (1/t)·G·totalRadialO1_coeff`
          `+ (1/t²)·G·[−¼Σᵢⱼ(gⁱʲ−δ)vⁱvʲ]·w₀`
          `− G·(Δ_g w₀)` ,
    with the SOLE smoothness hypothesis `ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v` — down from the
    `⊤`-version's `∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)`.  This is the finite-regularity form the
    q-centered pullback metric (only `ContDiffOn ℝ 2`) can eventually feed.  The metric `g, gi` and
    the Christoffel symbols enter only as VALUES, so no metric-regularity / symmetry hypothesis is
    needed (the un-symmetrised `laplaceBeltrami_mul_mixed_C2` avoids it).  NOT `a₁ = R/6`. -/
theorem parametrixResidual_N0_O1_isolated_C2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw0 : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v) :
    parametrixResidualN 0 g gi Θ u t v
      = (1 / t) * gaussDdim t v * totalRadialO1_coeff g gi Θ u v
        + (1 / t ^ 2) * gaussDdim t v
            * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
            * foldedCoeff Θ u 0 v
        - gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
  have hPfun : (fun y => ∑ k ∈ Finset.range (0 + 1), foldedCoeff Θ u k y * t ^ k)
      = foldedCoeff Θ u 0 := by
    funext y; rw [zero_add, Finset.sum_range_one, pow_zero, mul_one]
  rw [parametrixResidual_offdiag_O1_total_N0_C2 g gi Θ u t ht v hw0, hPfun, zero_add,
      Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_zero]
  simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, mul_zero, add_zero]
  unfold totalRadialO1_coeff
  ring

end QIQTH.HeatResidualBound
