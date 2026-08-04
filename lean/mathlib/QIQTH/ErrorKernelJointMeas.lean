/-
  ErrorKernelJointMeas — J4-188 (Sol endgame plan step 10, toward F1): the GEOMETRY DISCHARGE of the
  J4-187 factor carries.  The joint `(τ,v)`-measurability of the error-kernel normal form
  `E = χ·G_τ·A − annulusTerms` is reduced by `ErrorKernelFactorization` (J4-187) to the joint
  measurability of finitely many scalar FACTOR fields; this file DISCHARGES those carries — for the
  concrete van-Vleck parametrix — from the raw metric data `{hg, hgi, hgpos}` ALONE, leaving only the
  single genuine derivative-field residue (`hDH`, the spatial gradient of the parametrix) as an honest
  carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a
  measurable-algebra reduction: it turns "the six factor fields are jointly measurable" (the J4-187
  hypotheses) into "the metric is `C^∞` with `det g > 0`", by feeding the smoothness/continuity of
  every geometric factor (`gi`, Christoffel, folded DeWitt coefficients, their `Δ_g`, radial
  derivatives, and the parametrix-polynomial gradient) through the `∞`-chain
  (`HuInftyRebase.hu_infty_closed`/`hw_discharged_infty`, `christoffel_contDiff`,
  `laplaceBeltrami_contDiff_infty`, `contDiff_pd_inf`).  No new heat-kernel content, no `sorry`, no
  new axioms, no vacuous/unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## What this file delivers (ns `QIQTH.ErrorKernelJointMeas`).

    * `pd_polySum_eq` — the pd/polynomial commutation `∂ⱼ(Σₖ wₖ·tᵏ) = Σₖ (∂ⱼwₖ)·tᵏ` (the `t`-power
      being a spatial constant): converts the parametrix-polynomial gradient carry `hpdP` into an
      EXPLICIT sum whose `t`-dependence is polynomial and whose spatial factors are honest partials of
      the smooth folded coefficients — the key to jointly-measurable `hpdP`.

    * `radialDeriv_continuous_of_inf` — `r∂_r W` is continuous for `C^∞ W` (a coordinate-weighted sum
      of the continuous partials `∂ᵢW`), discharging the `hrad` carry.

    * ★ `residualCoeffA_measurable_from_geometry` — THE MAIN DELIVERABLE.  The Seeley–DeWitt amplitude
      `A = residualCoeffA N g gi (vanVleck g) (transportCoeff …)` is jointly `(τ,v)`-measurable from
      `{hg, hgi, hgpos}` ALONE.  All six J4-187 factor carries (`hgi, hchr, hfold, hlap, hrad, hpdP`)
      are discharged from geometry; NONE remain.

    * `heatParametrix_uncurry_measurable_from_geometry` — the parametrix field `H` is jointly
      `(τ,v)`-measurable from geometry (folded form: Gaussian × Σ smooth-coeff·tᵏ), discharging the
      `hHj` carry of the cross terms.

    * `annulusTerms_measurable_from_geometry` — the two Leibniz cross terms are jointly measurable from
      geometry, with EVERY carry discharged except the single genuine spatial-gradient-of-parametrix
      field `hDH` (honestly carried — the parametrix's own `∂ⱼH` derivative field, containing the
      Gaussian's spatial derivative, is not reduced here).

    * ★ `cutoffError_normalForm_measurable_from_geometry` — THE F1 FEED (assembled).  The full residual
      normal form `χ·(G_τ·A) − annulusTerms` (which, by `cutoffError_eq_cutoff_gauss_A_sub_annulus`,
      EQUALS the diagonal cutoff error kernel `E` on `{τ>0}`) is jointly `(τ,v)`-measurable from
      `{hg, hgi, hgpos}` plus the single `hDH` carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE F1 SLOT (where this sits) and the τ-structure of `A`.

  The residue chain carries F1 as `hEmeas` (`ResidueThreading.lean`), the TRIPLE `(τ,p,q)` strong
  measurability `StronglyMeasurable (fun q => heatOp g gi H q.1 q.2.1 q.2.2)` of the gated witness.  On
  the gate the triple collapses to the DIAGONAL single-base-point residual (J4-187's
  `cutoffErrorKernel`), whose joint `(τ,v)`-measurability is exactly what this file feeds.  The residual
  `q`-regularity wall (the flow's joint base-point dependence, `GatedWitnessEmeas` W1/W2) is NOT touched
  here; this discharges the FACTOR side.

  ⚠ τ-STRUCTURE OF `A` (honest, for the hEgrad/boundedness interface).  `residualCoeffA` is a Laurent
  polynomial in `τ` with a genuine `1/τ` and `1/τ²` head: as `τ↓0` the amplitude BLOWS UP, so `A` is
  NOT bounded on `[0,t]×gate` and there is no honest compact sup bound across `τ=0`.  The honest bounded
  forms are: `A` bounded on `[ε,t]×gate` for `ε>0`, or the Gaussian-weighted product `G_τ·A` (the
  actual `E`) bounded — the `1/τ²·exp(−r²/4τ)` combination is the Gaussian-tamed object the domination
  bound (not this file) handles.  No boundedness lemma is asserted here.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ErrorKernelFactorization
import QIQTH.HuInftyRebase
import QIQTH.InnerKernelJointMeas

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatResidualBound QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.HuInftyRebase
open QIQTH.InnerKernelJointMeas QIQTH.ErrorKernelFactorization
open scoped BigOperators ContDiff

namespace QIQTH.ErrorKernelJointMeas

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ## 0.  Two scalar-analysis helpers (pd/polynomial commutation, radial-derivative continuity). -/

/-- **`pd_polySum_eq` — the parametrix-polynomial gradient in explicit form.**  For smooth folded
    coefficients, the spatial partial of the `t`-polynomial `Σ_{k≤N} w_k·tᵏ` commutes with the sum and
    factors the (spatially-constant) `tᵏ` out of each partial:
      `∂ⱼ(Σₖ w_k·tᵏ)(v) = Σₖ (∂ⱼw_k)(v)·tᵏ`.
    (`pd_sum` over the finite range, then `pd_const_mul` per term with `c = tᵏ`.)  This is what makes
    the J4-187 `hpdP` carry jointly `(t,v)`-measurable: the RHS is a finite sum of a continuous spatial
    factor times a measurable `t`-power.  NOT `a₁ = R/6`. -/
theorem pd_polySum_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (j : Fin n)
    (v : Point n) (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
      = ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j v * t ^ k := by
  have hcomm : (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k)
      = (fun y => ∑ k ∈ Finset.range (N + 1), t ^ k * foldedCoeff Θ u k y) := by
    funext y; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  rw [hcomm,
    pd_sum (Finset.range (N + 1)) (fun k y => t ^ k * foldedCoeff Θ u k y) j v
      (fun k _ => (differentiableAt_const (t ^ k)).mul
        (PdiffAt_of_contDiff_inf (foldedCoeff Θ u k) (hw k) j v))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pd_const_mul (t ^ k) (foldedCoeff Θ u k) j v
    (PdiffAt_of_contDiff_inf (foldedCoeff Θ u k) (hw k) j v)]
  ring

/-- **`radialDeriv_continuous_of_inf`.**  The radial (Euler) derivative `r∂_r W = ∑ᵢ vⁱ·∂ᵢW` of a
    `C^∞` field `W` is continuous: a finite coordinate-weighted sum of the continuous partials
    `∂ᵢW` (`contDiff_pd_inf`).  Discharges the `hrad` carry.  NOT `a₁ = R/6`. -/
theorem radialDeriv_continuous_of_inf (W : Point n → ℝ)
    (hW : ContDiff ℝ (∞ : WithTop ℕ∞) W) :
    Continuous (fun v : Point n => radialDeriv W v) := by
  simp only [radialDeriv]
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_apply i).mul (contDiff_pd_inf W hW i).continuous)

/-! ## 1.  ★ The geometry discharge of the amplitude `A` — every factor carry from `{hg,hgi,hgpos}`. -/

/-- **★ `residualCoeffA_measurable_from_geometry` — THE MAIN DELIVERABLE (J4-188).**  The Seeley–DeWitt
    residual amplitude `A = residualCoeffA N g gi (vanVleck g) (transportCoeff …)` is jointly
    `(τ,v)`-measurable from the raw metric data `{hg, hgi, hgpos}` ALONE.  ALL SIX J4-187 factor carries
    are discharged from geometry:
      • `hgi`   ⟸ `hgi.continuous` (inverse-metric components);
      • `hchr`  ⟸ `christoffel_contDiff` (`.continuous`);
      • `hfold` ⟸ `hw_discharged_infty ∘ hu_infty_closed` (`.continuous`) — the `∞`-chain closure of
        the DeWitt coefficients from geometry;
      • `hlap`  ⟸ `laplaceBeltrami_contDiff_infty` on the folded coefficients (`.continuous`);
      • `hrad`  ⟸ `radialDeriv_continuous_of_inf` on the folded coefficients;
      • `hpdP`  ⟸ `pd_polySum_eq` + per-`k` (`contDiff_pd_inf`.continuous × `τᵏ`).
    Then `ErrorKernelFactorization.residualCoeffA_measurable_of_factors` (pure measurable algebra)
    closes it.  This turns F1-for-`A` from "the factor fields are jointly measurable" into "the metric
    is `C^∞` with `det g > 0`".  NOT `a₁ = R/6`. -/
theorem residualCoeffA_measurable_from_geometry (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    Measurable (fun w : ℝ × Point n =>
      residualCoeffA N g gi (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2) := by
  -- the folded DeWitt coefficients are `C^∞` from geometry (the `∞`-chain closure).
  have hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) :=
    hw_discharged_infty g gi hg hgpos (hu_infty_closed g gi hg hgi hgpos)
  refine residualCoeffA_measurable_of_factors N g gi (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) ?_ ?_ ?_ ?_ ?_ ?_
  · -- hgi
    exact fun i j => (((hgi i j).continuous.comp continuous_snd).measurable)
  · -- hchr
    exact fun k i j =>
      (((christoffel_contDiff g gi hg hgi k i j).continuous.comp continuous_snd).measurable)
  · -- hfold
    exact fun k => (((hw k).continuous.comp continuous_snd).measurable)
  · -- hlap
    exact fun k =>
      (((laplaceBeltrami_contDiff_infty g gi hg hgi
        (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)
        (hw k)).continuous.comp continuous_snd).measurable)
  · -- hrad
    exact fun k =>
      ((radialDeriv_continuous_of_inf _ (hw k)).comp continuous_snd).measurable
  · -- hpdP
    intro j
    have hEq : (fun w : ℝ × Point n =>
        pd (fun y => ∑ k ∈ Finset.range (N + 1),
          foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k y * w.1 ^ k)
          j w.2)
        = (fun w : ℝ × Point n =>
          ∑ k ∈ Finset.range (N + 1),
            pd (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) j w.2
              * w.1 ^ k) := by
      funext w
      exact pd_polySum_eq N (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) w.1 j w.2 hw
    rw [hEq]
    exact Finset.measurable_sum _ (fun k _ =>
      (((contDiff_pd_inf _ (hw k) j).continuous.comp continuous_snd).measurable).mul
        (measurable_fst.pow_const k))

/-! ## 2.  The parametrix field `H` (the `hHj` carry) from geometry. -/

/-- **`heatParametrix_uncurry_measurable_from_geometry`.**  The parametrix field
    `H = heatParametrix N (vanVleck g) (transportCoeff …)` is jointly `(τ,v)`-measurable from geometry:
    the folded form `H(τ,·) = G_τ·Σ_{k≤N} w_k·τᵏ` is a product of the (globally Borel) heat kernel
    `gaussDdim` (`gaussDdim_uncurry_measurable`) and a finite sum of `(w_k continuous)·τᵏ`.  Discharges
    the `hHj` cross-term carry.  NOT `a₁ = R/6`. -/
theorem heatParametrix_uncurry_measurable_from_geometry (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    Measurable (fun w : ℝ × Point n =>
      heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2) := by
  have hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) :=
    hw_discharged_infty g gi hg hgpos (hu_infty_closed g gi hg hgi hgpos)
  have hrw : (fun w : ℝ × Point n =>
        heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2)
      = (fun w : ℝ × Point n => gaussDdim w.1 w.2
          * ∑ k ∈ Finset.range (N + 1),
            foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k w.2
              * w.1 ^ k) := by
    funext w
    exact heatParametrix_folded N (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2
  rw [hrw]
  exact gaussDdim_uncurry_measurable.mul
    (Finset.measurable_sum _ (fun k _ =>
      (((hw k).continuous.comp continuous_snd).measurable).mul (measurable_fst.pow_const k)))

/-! ## 3.  The Leibniz cross terms from geometry (all carries but the honest `hDH`). -/

/-- **`annulusTerms_measurable_from_geometry`.**  The two Leibniz cross terms
    `annulusTerms g gi a b (heatParametrix N (vanVleck g) …)` are jointly `(τ,v)`-measurable from
    `{hg, hgi, hgpos}` plus the SINGLE genuine derivative-field carry `hDH` (the parametrix's own
    spatial gradient `∂ⱼH`, which contains the Gaussian's spatial derivative — not reduced here, an
    honest carry).  The `χ`-side carries are all discharged: `∂ᵢχ` / `Δ_gχ` are continuous
    (`χ ∈ C^∞`, `laplaceBeltrami_contDiff_infty`), `gⁱʲ` continuous, `H` jointly measurable
    (`heatParametrix_uncurry_measurable_from_geometry`).  NOT `a₁ = R/6`. -/
theorem annulusTerms_measurable_from_geometry (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hDH : ∀ j, Measurable (fun w : ℝ × Point n =>
      pd (heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1) j w.2)) :
    Measurable (fun w : ℝ × Point n =>
      annulusTerms g gi a b
        (heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1) w.2) := by
  have hgiM : ∀ i j : Fin n, Measurable (fun w : ℝ × Point n => gi w.2 i j) :=
    fun i j => (((hgi i j).continuous.comp continuous_snd).measurable)
  have hLapChi : Measurable (fun w : ℝ × Point n =>
      laplaceBeltrami g gi (radialCutoff a b) w.2) :=
    ((laplaceBeltrami_contDiff_infty g gi hg hgi (radialCutoff a b)
      (radialCutoff_contDiff a b)).continuous.comp continuous_snd).measurable
  have hDchi : ∀ i, Measurable (fun w : ℝ × Point n => pd (radialCutoff a b) i w.2) :=
    fun i => (((contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) i).continuous.comp
      continuous_snd).measurable)
  have hHj := heatParametrix_uncurry_measurable_from_geometry N g gi hg hgi hgpos
  exact annulusTerms_measurable_of_factors g gi a b
    (fun w => heatParametrix N (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2)
    (fun w => heatParametrix N (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) w.1)
    hHj hgiM hLapChi hDchi hDH

/-! ## 4.  ★ The assembled F1 feed — the residual normal form `χ·(G·A) − annulusTerms`. -/

/-- **★ `cutoffError_normalForm_measurable_from_geometry` — THE F1 FEED (assembled, J4-188).**  The
    full residual normal form
      `χ·(G_τ·A) − annulusTerms`
    (which, by `ErrorKernelFactorization.cutoffError_eq_cutoff_gauss_A_sub_annulus`, EQUALS the diagonal
    cutoff error kernel `E = cutoffErrorKernel g gi a b (heatParametrix N …) (∂_τ heatParametrix …)` on
    `{τ>0}`) is jointly `(τ,v)`-measurable from `{hg, hgi, hgpos}` plus the single `hDH` carry:
      `χ` continuous (`radialCutoff_contDiff`), `G_τ` globally Borel (`gaussDdim_uncurry_measurable`),
      `A` from `residualCoeffA_measurable_from_geometry`, `annulusTerms` from
      `annulusTerms_measurable_from_geometry`.  This is the honest, factor-side discharge of the F1
      (`hEmeas`) diagonal residual — the residual `q`-regularity flow wall (`GatedWitnessEmeas`) is
      distinct and untouched.  NOT `a₁ = R/6`. -/
theorem cutoffError_normalForm_measurable_from_geometry (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hDH : ∀ j, Measurable (fun w : ℝ × Point n =>
      pd (heatParametrix N (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) w.1) j w.2)) :
    Measurable (fun w : ℝ × Point n =>
      radialCutoff a b w.2
          * (gaussDdim w.1 w.2 * residualCoeffA N g gi (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) w.1 w.2)
        - annulusTerms g gi a b
            (heatParametrix N (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) w.1) w.2) := by
  have hChi : Measurable (fun w : ℝ × Point n => radialCutoff a b w.2) :=
    ((radialCutoff_contDiff a b).continuous.comp continuous_snd).measurable
  have hA := residualCoeffA_measurable_from_geometry N g gi hg hgi hgpos
  have hAnn := annulusTerms_measurable_from_geometry N g gi a b hg hgi hgpos hDH
  exact (hChi.mul (gaussDdim_uncurry_measurable.mul hA)).sub hAnn

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms pd_polySum_eq
#print axioms radialDeriv_continuous_of_inf
#print axioms residualCoeffA_measurable_from_geometry
#print axioms heatParametrix_uncurry_measurable_from_geometry
#print axioms annulusTerms_measurable_from_geometry
#print axioms cutoffError_normalForm_measurable_from_geometry

end AxiomChecks

end QIQTH.ErrorKernelJointMeas
