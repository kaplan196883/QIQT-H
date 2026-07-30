/-
# RECENTER brick R4b-follow — the q-centered van-Vleck / DeWitt Hessian jet `hw0hessRicci`.

This file discharges (modulo the single van-Vleck germ identification `hfold`) the last hard carried
hypothesis `hw0hessRicci` of the q-centered near-diagonal residual bound `near_uncutResidual_expPullback`
(R4a, `QIQTH.RecenterConnectC3`).

## The coefficient bookkeeping (the factor-2, resolved)

`hw0hessRicci` demands, for `w₀ = foldedCoeff Θ u 0` at `0` (with `g̃`, `gĩ`, `Ric = ricci g̃ gĩ`):

  `∂_a∂_b w₀(0) + ∂_b∂_a w₀(0)
     = −( ⅓ Ric_{ab}(0) − ½ (Σᵢ ∂_bΓ^a_{ii}(0) + Σᵢ ∂_aΓ^b_{ii}(0)) )·w₀(0)`.

Two curvature facts collapse the right side:

* **Contracted-Christoffel trace** (`sum_pd_christoffel_ii_trace_c2`, the crux new lemma):
  `Σᵢ ∂_bΓ^a_{ii}(0) = ⅔ Ric_{ab}(0)`.  This is the trace over the LOWER pair, orthogonal to the
  `christoffel_contracted` identity; it is derived from the normal-coordinate gauge via
  `pd_christoffel_solve` (`∂Γ = ⅓(R+R)`) contracted with the Riemann **pair symmetry**
  `Σᵢ R^a_{ibi}(0) = Ric_{ab}(0)` — so it DOES reduce to `Ric` (the `coeffA_center_hessian` remark to the
  contrary is superseded by the gauge-based `pd_christoffel_solve`).  With it, the bracket
  `⅓Ric − ½(⅔Ric + ⅔Ric) = −⅓Ric_{ab}`, so the whole right side becomes `+⅓ Ric_{ab}(0)·w₀(0)`.

* **Van-Vleck Hessian** (`vanvleck_hessian_c2`): the CORRECT DeWitt power is `s = −¼`, i.e.
  `w₀ = (det g̃)^{−¼}` (the Van Vleck–Morette determinant `Δ^½ = 1 + 1/12 R_{ab}x^ax^b`), NOT `(det g̃)^{+¼}`.
  A critical-point rpow chain rule (`rpow_pd_pd_c2`) gives `Hess((det g̃)^{−¼})(0) = −¼·Hess(det g̃)(0)`,
  and `Hess(det g̃)(0) = −⅔ Ric` (from `sqrt_pd_pd_c2` + `sqrtdet_pd_pd_c2`), so
  `Hess((det g̃)^{−¼})_{ab}(0) = ⅙ Ric_{ab}(0)` and the symmetric double-Hessian is `⅓ Ric_{ab}(0)`.

`⅓Ric = ⅓Ric` — the two sides match with `s = −¼` (the `+¼` sign gives `−⅓Ric = +⅓Ric`, the reported
factor-2/sign tension).

## What is discharged, what is carried

`hw0hessRicci_expPullback` proves the exact `hw0hessRicci` shape for `g̃ = expPullbackMetric g₀ gi₀ hC p`
from the landed `QIQTH.PullbackMetric` RNC lemmas (frame + smoothness/symmetry/inverse) and ONE genuine,
load-bearing hypothesis:

  `hfold : foldedCoeff Θ u 0 =ᶠ[𝓝 0] (fun v => (det g̃ v)^{−¼})`,

i.e. the parametrix's leading coefficient IS the Van Vleck–Morette determinant (`Θ = √det g̃`, `u₀ = 1`).
This is the physical van-Vleck normalization, not a landed transport identity — honest and load-bearing
(remove it and the jet is false for arbitrary `Θ, u`).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RecenterConnectC3
import QIQTH.RNCExpansion
import QIQTH.PullbackMetric
import QIQTH.Curvature

open Finset Matrix
open QIQTH.Curvature QIQTH.RNCExpansion QIQTH.PullbackMetric

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The `C²` origin-Riemann Hessian formula and its pair symmetry -/

/-- `C²` variant of `rnc_riemann_hessian`: at a normal-coordinate origin (`g̃(0)=δ`, `∂g̃(0)=0`) the
    Riemann tensor is the antisymmetrized metric Hessian. -/
theorem rnc_riemann_hessian_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν 0
      = (1 / 2) * (pd (fun y => pd (fun w => g w ρ ν) σ y) μ 0
                 - pd (fun y => pd (fun w => g w ν σ) ρ y) μ 0
                 - pd (fun y => pd (fun w => g w ρ μ) σ y) ν 0
                 + pd (fun y => pd (fun w => g w μ σ) ρ y) ν 0) := by
  rw [riemann_at_origin g gi hdg0 ρ σ μ ν,
      pd_christoffel_origin_c2 g gi hg2 hgi1 hgi0 hdg0 ρ ν σ μ,
      pd_christoffel_origin_c2 g gi hg2 hgi1 hgi0 hdg0 ρ μ σ ν,
      pd_comm_of_contDiffAt2 (fun w => g w ρ σ) μ ν (hg2 ρ σ)]
  ring

/-- **Riemann pair symmetry at the origin** (`C²`): `R_{ρσμν}(0) = R_{μνρσ}(0)`.  Pure Schwarz +
    metric symmetry on the `rnc_riemann_hessian_c2` bracket — gauge-free. -/
theorem riemann_pair_symm_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν 0 = riemann g gi μ ν ρ σ 0 := by
  rw [rnc_riemann_hessian_c2 g gi hg2 hgi1 hgi0 hdg0 ρ σ μ ν,
      rnc_riemann_hessian_c2 g gi hg2 hgi1 hgi0 hdg0 μ ν ρ σ]
  -- match the four bracket terms via Schwarz + metric symmetry
  have h1 : pd (fun y => pd (fun w => g w ρ ν) σ y) μ 0
      = pd (fun y => pd (fun w => g w ρ ν) μ y) σ 0 :=
    pd_comm_of_contDiffAt2 (fun w => g w ρ ν) μ σ (hg2 ρ ν)
  have h4 : pd (fun y => pd (fun w => g w μ σ) ρ y) ν 0
      = pd (fun y => pd (fun w => g w μ σ) ν y) ρ 0 :=
    pd_comm_of_contDiffAt2 (fun w => g w μ σ) ν ρ (hg2 μ σ)
  have h2 : pd (fun y => pd (fun w => g w ν σ) ρ y) μ 0
      = pd (fun y => pd (fun w => g w σ ν) μ y) ρ 0 := by
    rw [show (fun w => g w ν σ) = (fun w => g w σ ν) from funext (fun w => hsymm w ν σ)]
    exact pd_comm_of_contDiffAt2 (fun w => g w σ ν) μ ρ (hg2 σ ν)
  have h3 : pd (fun y => pd (fun w => g w ρ μ) σ y) ν 0
      = pd (fun y => pd (fun w => g w μ ρ) ν y) σ 0 := by
    rw [show (fun w => g w ρ μ) = (fun w => g w μ ρ) from funext (fun w => hsymm w ρ μ)]
    exact pd_comm_of_contDiffAt2 (fun w => g w μ ρ) ν σ (hg2 μ ρ)
  linarith [h1, h2, h3, h4]

/-- **The `R^a_{ibi}` contraction is Ricci** (`C²`): `Σᵢ R_{aibi}(0) = Ric_{ab}(0)`.  A pure Riemann
    symmetry (pair symmetry + last-pair antisymmetry) — gauge-free. -/
theorem sum_riemann_aibi_eq_ricci_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (a b : Fin n) :
    (∑ i, riemann g gi a i b i 0) = ricci g gi a b 0 := by
  have per_i : ∀ i : Fin n, riemann g gi a i b i 0 = riemann g gi i a i b 0 := by
    intro i
    have p1 : riemann g gi a i b i 0 = riemann g gi b i a i 0 :=
      riemann_pair_symm_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm a i b i
    have p2 : riemann g gi b i a i 0 = - riemann g gi b i i a 0 :=
      riemann_antisymm g gi b i a i 0
    have p3 : riemann g gi b i i a 0 = riemann g gi i a b i 0 :=
      riemann_pair_symm_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm b i i a
    have p4 : riemann g gi i a b i 0 = - riemann g gi i a i b 0 :=
      riemann_antisymm g gi i a b i 0
    linarith [p1, p2, p3, p4]
  rw [Finset.sum_congr rfl (fun i _ => per_i i)]
  simp only [ricci]

/-- **Ricci symmetry at the origin** (`C²`): `Ric_{ab}(0) = Ric_{ba}(0)`, from pair symmetry. -/
theorem ricci_symm_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (a b : Fin n) :
    ricci g gi a b 0 = ricci g gi b a 0 := by
  simp only [ricci]
  apply Finset.sum_congr rfl
  intro μ _
  exact riemann_pair_symm_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm μ a μ b

/-- **★ THE CONTRACTED-CHRISTOFFEL `Γ^a_{ii}` SECOND-JET IDENTITY** (`C²`, the crux new lemma):
    `Σᵢ ∂_b Γ^a_{ii}(0) = ⅔ Ric_{ab}(0)`.  This is the trace over the LOWER index pair (orthogonal to
    the `Γ^b_{ab}=∂_a log√g` contraction `christoffel_contracted`).  Derived from the normal-coordinate
    gauge via `pd_christoffel_solve` (`∂_bΓ^a_{ii} = ⅓(R^a_{ibi}+R^a_{ibi})`) contracted with the pair
    symmetry `Σᵢ R^a_{ibi} = Ric_{ab}`.  Load-bearing: the gauge (`hgauge`) fixes `∂Γ`; removing it the
    identity fails. -/
theorem sum_pd_christoffel_ii_trace_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (a b : Fin n) :
    (∑ i, pd (fun y => christoffel g gi a i i y) b 0) = (2 / 3) * ricci g gi a b 0 := by
  have hsum : (∑ i, pd (fun y => christoffel g gi a i i y) b 0)
      = (2 / 3) * ∑ i, riemann g gi a i b i 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pd_christoffel_solve g gi hdg0 hsymm hgauge a b i i]
    ring
  rw [hsum, sum_riemann_aibi_eq_ricci_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm a b]

/-! ### The critical-point rpow chain rule and the `(det g̃)^{−¼}` van-Vleck Hessian -/

/-- First-order chain rule for `y ↦ (F y)^s` where `F > 0`: `∂_i (F^s) = s·F^{s−1}·∂_i F`. -/
theorem pd_comp_rpow (F : Point n → ℝ) (s : ℝ) (i : Fin n) (x : Point n)
    (hF : PdiffAt F i x) (hpos : 0 < F x) :
    pd (fun y => (F y) ^ s) i x = s * (F x) ^ (s - 1) * pd F i x := by
  simp only [pd]
  have hval : F (Function.update x i (x i)) = F x := by rw [Function.update_eq_self]
  have hrpow : HasDerivAt (fun z : ℝ => z ^ s) (s * (F x) ^ (s - 1))
      (F (Function.update x i (x i))) := by
    rw [hval]; exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
  have hcomp := hrpow.comp (x i) hF.hasDerivAt
  exact hcomp.deriv

/-- **Second derivative of `y ↦ (F y)^s` at a critical point** where `F = 1` and `∂F = 0`:
    `∂_c∂_d (F^s)(0) = s·∂_c∂_d F(0)`.  (The cross term `s(s−1)F^{s−2}(∂F)²` drops because `∂F(0)=0`;
    the surviving prefactor is `s·F^{s−1}(0) = s`.)  The rpow analogue of `sqrt_pd_pd_c2`. -/
theorem rpow_pd_pd_c2 (F : Point n → ℝ) (s : ℝ) (c d : Fin n)
    (hF : ContDiffAt ℝ 2 F 0) (hval : F 0 = 1) (hcrit : ∀ e, pd F e 0 = 0) :
    pd (fun y => pd (fun w => (F w) ^ s) d y) c 0 = s * pd (fun y => pd F d y) c 0 := by
  have hpos0 : 0 < F 0 := by rw [hval]; norm_num
  have hconst : ContinuousAt (fun _ : Point n => (0 : ℝ)) 0 := continuousAt_const
  have hnhds : ∀ᶠ y in nhds (0 : Point n), 0 < F y :=
    hconst.eventually_lt hF.continuousAt hpos0
  have hdiff_ev : ∀ᶠ y in nhds (0 : Point n), DifferentiableAt ℝ F y := by
    filter_upwards [hF.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have hchain : (fun y => pd (fun w => (F w) ^ s) d y)
      =ᶠ[nhds (0 : Point n)] (fun y => s * (F y) ^ (s - 1) * pd F d y) := by
    filter_upwards [hnhds, hdiff_ev] with y hy hdy
    exact pd_comp_rpow F s d y (RNCExpansion.pdiffAt_of_differentiableAt F d y hdy) hy
  rw [pd_congr c 0 hchain]
  have hB : PdiffAt (fun y => pd F d y) c 0 := RNCExpansion.PdiffAt_pd_zero_of_contDiffAt2 F d c hF
  have hFd0 : DifferentiableAt ℝ F 0 := hF.differentiableAt (by norm_num)
  have hApow : DifferentiableAt ℝ (fun y => (F y) ^ (s - 1)) 0 :=
    hFd0.rpow_const (Or.inl (ne_of_gt hpos0))
  have hA : PdiffAt (fun y => s * (F y) ^ (s - 1)) c 0 :=
    RNCExpansion.pdiffAt_of_differentiableAt _ c 0 ((differentiableAt_const s).mul hApow)
  rw [pd_mul (fun y => s * (F y) ^ (s - 1)) (fun y => pd F d y) c 0 hA hB,
      hcrit d, mul_zero, zero_add, hval, Real.one_rpow, mul_one]

/-- **The van-Vleck determinant Hessian** (`C²`, gauge-conditional): with the CORRECT DeWitt power
    `s = −¼`, `∂_c∂_d (det g̃)^{−¼}(0) = ⅙ Ric_{cd}(0)`.  Assembles the critical rpow rule
    (`Hess((det)^{−¼}) = −¼·Hess(det)`), `Hess(det) = 2·Hess(√det)` (`sqrt_pd_pd_c2`), and
    `Hess(√det) = −⅓Ric` (`sqrtdet_pd_pd_c2` with the gauge-derived `htr`). -/
theorem vanvleck_hessian_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (c d : Fin n) :
    pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) d y) c 0
      = (1 / 6) * ricci g gi c d 0 := by
  have htr : ∀ c' d', (∑ a, pd (fun y => pd (fun w => g w a a) d' y) c' 0)
      = -(2 / 3) * ricci g gi c' d' 0 :=
    fun c' d' => rnc_htr_of_gauge_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm hgauge c' d'
  have hFdet : ContDiffAt ℝ 2 (fun y => Matrix.det (g y)) 0 := det_contDiffAt2 g hg2
  have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
  have hdet0 : (fun y => Matrix.det (g y)) 0 = 1 := by
    show Matrix.det (g 0) = 1; rw [hg0mat, Matrix.det_one]
  have hdetcrit : ∀ e, pd (fun y => Matrix.det (g y)) e 0 = 0 :=
    fun e => det_pd_first_c2 g hg2 hdg0 e
  -- Hess(det) = -(2/3)Ric  (via  Hess(√det) = ½ Hess(det)  and  Hess(√det) = -⅓Ric)
  have hHessDet : pd (fun y => pd (fun w => Matrix.det (g w)) d y) c 0
      = -(2 / 3) * ricci g gi c d 0 := by
    have h1 := sqrt_pd_pd_c2 (fun y => Matrix.det (g y)) c d hFdet hdet0 hdetcrit
    have h2 := sqrtdet_pd_pd_c2 g (fun a b => ricci g gi a b 0) hg2 hg0 hdg0 htr c d
    dsimp only [] at h1
    linarith [h1, h2]
  rw [rpow_pd_pd_c2 (fun y => Matrix.det (g y)) (-1 / 4) c d hFdet hdet0 hdetcrit, hHessDet]
  ring

/-! ### The q-centered van-Vleck / DeWitt Hessian jet — abstract, then at `g̃` -/

/-- **The `hw0hessRicci` jet, abstractly** (`C²`, gauge-conditional): given the van-Vleck germ
    identification `hfold : w₀ =ᶠ (det g)^{−¼}` near `0`, the symmetric double-Hessian of `w₀` equals the
    DeWitt curvature source.  The contracted-Christoffel traces reduce to `⅔Ric`
    (`sum_pd_christoffel_ii_trace_c2`), collapsing the bracket to `−⅓Ric`; the `(det)^{−¼}` Hessian
    supplies the matching `+⅓Ric·w₀(0)`. -/
theorem hw0hessRicci_of_vanvleck_c2 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg2 : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgi1 : ∀ a b, ContDiffAt ℝ 1 (fun y => gi y a b) 0)
    (hgi0 : ∀ i j, gi 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (g v)) ^ (-1 / 4 : ℝ))
    (a b : Fin n) :
    pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
      + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
      = - ((1 / 3) * ricci g gi a b 0
           - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                      + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
        * foldedCoeff Θ u 0 0 := by
  -- (1) the contracted-Christoffel traces reduce to `⅔Ric`
  have hTa : (∑ i, pd (fun y => christoffel g gi a i i y) b 0) = (2 / 3) * ricci g gi a b 0 :=
    sum_pd_christoffel_ii_trace_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm hgauge a b
  have hTb : (∑ i, pd (fun y => christoffel g gi b i i y) a 0) = (2 / 3) * ricci g gi b a 0 :=
    sum_pd_christoffel_ii_trace_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm hgauge b a
  have hRsymm : ricci g gi b a 0 = ricci g gi a b 0 :=
    ricci_symm_c2 g gi hg2 hgi1 hgi0 hdg0 hsymm b a
  -- (2) `w₀(0) = 1`
  have hw00 : foldedCoeff Θ u 0 (0 : Point n) = 1 := by
    rw [hfold.self_of_nhds]
    have : Matrix.det (g (0 : Point n)) = 1 := by
      rw [show g (0 : Point n) = (1 : Matrix (Fin n) (Fin n) ℝ) from by funext i j; exact hg0 i j,
        Matrix.det_one]
    rw [this, Real.one_rpow]
  -- (3) germ-upgrade `hfold` from function level to `pd`-of-`pd` level
  have hev2 : (fun y => pd (foldedCoeff Θ u 0) b y)
      =ᶠ[nhds (0 : Point n)] (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) b y) := by
    filter_upwards [eventually_eventually_nhds.mpr hfold] with y hy
    exact pd_congr b y hy
  have hev2' : (fun y => pd (foldedCoeff Θ u 0) a y)
      =ᶠ[nhds (0 : Point n)] (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) a y) := by
    filter_upwards [eventually_eventually_nhds.mpr hfold] with y hy
    exact pd_congr a y hy
  have hLa : pd (fun y => pd (foldedCoeff Θ u 0) b y) a 0
      = pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) b y) a 0 :=
    pd_congr a 0 hev2
  have hLb : pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
      = pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) a y) b 0 :=
    pd_congr b 0 hev2'
  -- (4) the two van-Vleck Hessians
  have hVa : pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) b y) a 0
      = (1 / 6) * ricci g gi a b 0 :=
    vanvleck_hessian_c2 g gi hg2 hgi1 hgi0 hg0 hdg0 hsymm hgauge a b
  have hVb : pd (fun y => pd (fun w => (Matrix.det (g w)) ^ (-1 / 4 : ℝ)) a y) b 0
      = (1 / 6) * ricci g gi b a 0 :=
    vanvleck_hessian_c2 g gi hg2 hgi1 hgi0 hg0 hdg0 hsymm hgauge b a
  -- assemble
  rw [hLa, hLb, hVa, hVb, hTa, hTb, hRsymm, hw00]
  ring

/-- **★ R4b — the q-centered van-Vleck / DeWitt Hessian jet `hw0hessRicci`, for the exp-pullback metric
    `g̃`.**  Proves the exact carried `hw0hessRicci` shape of `near_uncutResidual_expPullback` from the
    landed `QIQTH.PullbackMetric` RNC lemmas (orthonormal frame `hframe`, ambient smoothness/symmetry/
    inverse `hg`/`hsymm0`/`hinvF`) and the single genuine van-Vleck germ identification `hfold`
    (`foldedCoeff Θ u 0 =ᶠ (det g̃)^{−¼}`, i.e. `Θ = √det g̃`, `u₀ = 1`).

    The factor-2 resolves at `s = −¼`: the contracted-Christoffel `Γ^a_{ii}` traces are `⅔Ric` (so the
    bracket is `−⅓Ric`), and `Hess((det g̃)^{−¼}) = ⅙Ric` gives the symmetric double-Hessian `⅓Ric`,
    matching `+⅓Ric·w₀(0)`.  Load-bearing `hfold` (van-Vleck normalization, not a landed transport
    identity).  NOT `a₁ = R/6`. -/
theorem hw0hessRicci_expPullback
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    (a b : Fin n) :
    pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
      + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
      = - ((1 / 3) * ricci (expPullbackMetric g₀ gi₀ hC p)
              (expPullbackMetricInv g₀ gi₀ hC p) a b 0
           - (1 / 2) * ((∑ i, pd (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
                            (expPullbackMetricInv g₀ gi₀ hC p) a i i y) b 0)
                      + (∑ i, pd (fun y => christoffel (expPullbackMetric g₀ gi₀ hC p)
                            (expPullbackMetricInv g₀ gi₀ hC p) b i i y) a 0)))
        * foldedCoeff Θ u 0 0 := by
  -- the ambient inverse relation at `p`, and `gi₀ p = δ` from the frame.
  have hinv : ∀ a' b', (∑ σ, g₀ p a' σ * gi₀ p σ b') = if a' = b' then 1 else 0 :=
    fun a' b' => hinvF p a' b'
  have hgiδ : ∀ a' b', gi₀ p a' b' = if a' = b' then 1 else 0 := by
    intro a' b'
    have h := hinvF p a' b'
    simp only [hframe, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  refine hw0hessRicci_of_vanvleck_c2
    (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) Θ u
    -- hg2 : g̃ is C² at 0
    (fun a' b' => contDiffAt2_expPullbackMetric_zero g₀ gi₀ hC p hg a' b')
    -- hgi1 : g̃⁻¹ is C¹ at 0
    (fun a' b' => expPullbackMetricInv_contDiffAt_one g₀ gi₀ hC p hinv hg a' b')
    -- hgi0 : g̃⁻¹(0) = δ
    (fun i j => by
      rw [expPullbackMetricInv_zero g₀ gi₀ hC p hinv, hgiδ, Matrix.one_apply])
    -- hg0 : g̃(0) = δ
    (fun i j => by
      rw [expPullbackMetric_at_zero, hframe, Matrix.one_apply])
    -- hdg0 : ∂g̃(0) = 0
    (fun a' b' e => pd_expPullbackMetric_at_zero g₀ gi₀ hC p hsymm0 hinv hg a' b' e)
    -- hsymm : g̃ symmetric
    (fun y a' b' => expPullbackMetric_symm g₀ gi₀ hC p hsymm0 y a' b')
    -- hgauge : cyclic RNC gauge for g̃ (solve orientation)
    (fun i a' b' c' => by
      have hg3 := gauge_pd_christoffel_expPullbackInv_zero' g₀ gi₀ hC p hsymm0 hinvF hg i a' b' c'
      linarith [hg3])
    hfold a b

end QIQTH.HeatResidualBound
