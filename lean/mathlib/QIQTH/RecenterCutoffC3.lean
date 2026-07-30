/-
# RECENTER brick R5 — the q-centered CUTOFF residual width-2 Gaussian bound `hEboundW`.

This is the per-base-point analogue of the diagonal-chart (base `0`) template
`QIQTH.HeatResidualBound.cutoffResidual_diag_hEboundW` (`CutoffResidualAssembled.lean`), assembled at
the pulled-back metric `g̃ = expPullbackMetric g₀ gi₀ hC p`, `g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`,
using the FINITE-REGULARITY (`ContDiffAt ℝ 2`) far-field engine
`cutoffResidual_global_gaussianWide_bound_C2` (R2, `CutoffResidualFiniteReg.lean`) instead of the `C∞`
engine.  This produces, for a base point `p`, the per-base-point width-2 Gaussian residual bound — the
input the final `hEboundW ∀q` assembly (R6) needs.

══════════════════════════════════════════════════════════════════════════════════════════════════════
WHAT IS DISCHARGED vs CARRIED (honest split).

`cutoffResidual_global_gaussianWide_bound_C2` carries a long list of concrete-parametrix / metric
hypotheses.  This file INSTANTIATES that engine at the concrete q-centered parametrix
`H := heatParametrix 0 Θ u t`, `dtH := fun x => deriv (fun s => heatParametrix 0 Θ u s x) t`, and the
pulled-back metric `g̃`/`g̃⁻¹`, discharging:

  • `hEnear`             ← `near_uncutResidual_expPullback_clean`  (R4c, `RecenterConnectC3c.lean`) —
      the clean q-centered near-diagonal residual bound at `g̃`, carrying only the genuine irreducible
      near-inputs (ambient frame data, the exp `Jet₄` regularity `hfd3`, the van-Vleck normalization
      `hfold`, the pointwise nondegeneracy `hinvT`, the `t`/`M`/`W`/`L` analytic bounds);
  • `hH2` (`H ∈ ContDiffAt ℝ 2`)  ← `heatParametrix 0 Θ u t = gaussDdim t · foldedCoeff Θ u 0`
      (`heatParametrix_folded`) with `gaussDdim` smooth × the carried global smoothness `hw0smooth` of
      the folded cofactor;  `ContDiffAt ℝ 2` from `ContDiff ℝ ⊤` (`.of_le le_top`);
  • `hHann`/`hDHann`     ← `parametrixH_annulus_bounds` (`ParametrixHAnnulusBounds.lean`), cofactor
      regularity from `hw0smooth`  (identical to the base-`0` template, `H`-side is metric-independent);
  • `hDchi`             ← `pd_radialCutoff_bound_on_annulus` (`CutoffAnnulusBounds.lean`, metric-free);
  • `hgisymm`           ← the CARRIED `g̃⁻¹`-symmetry (see below).

The genuinely IRREDUCIBLE q-centered residue — CARRIED, all honest and load-bearing:

  • `hgisymm`   : `∀ w i j, g̃⁻¹ w i j = g̃⁻¹ w j i`  — symmetry of the pullback inverse metric.  A true
      geometric fact (inverse of a symmetric matrix), carried exactly as the base-`0` template
      `cutoffResidual_diag_hEboundW` carries its own `hgisymm`; no `expPullbackMetricInv_symm` lemma
      exists yet.
  • `hgi_ann`   : `∀ a b, ∃ Kg ≥ 0, |g̃⁻¹ w i j| ≤ Kg` on the annulus  — the pullback-inverse-metric
      annulus bound.  For the base metric this is discharged by `gi_bound_on_annulus` from GLOBAL
      continuity; `g̃⁻¹` is only `ContDiffOn ℝ 2`/`ContDiffAt ℝ 2` LOCALLY (on the exp-ball / at `0`),
      so global continuity is not available and this is a genuine carry (encoding local continuity of
      `g̃⁻¹` on each compact annulus inside the exp-ball).
  • `hLapChi_ann` : `∀ a b, ∃ Kc2 ≥ 0, |Δ_g̃(radialCutoff a b) w| ≤ Kc2` on the annulus  — the `Δ_g̃χ`
      annulus bound.  Same status as `hgi_ann` (needs `g̃⁻¹`/`Γ̃` continuity on the annulus, not
      globally available).
  • `hw0smooth` : `ContDiff ℝ ⊤ (foldedCoeff Θ u 0)`  — global smoothness of the folded cofactor
      profile `Θ^{−1/2}·u₀`.  `Θ`, `u` are globally-smooth profile functions whose folded coefficient
      matches the van-Vleck determinant near `0` (`hfold`); genuinely used for `hH2`/`hHann`/`hDHann`.

Plus all the genuine near-inputs of R4c, reproduced verbatim.

⚠ HONEST SCOPE (binding).  This is the PER-BASE-POINT (`p`) width-2 cutoff residual bound at the
pulled-back metric — the input R6 feeds (uniform-in-`p`) into `hEboundW_of_uniform_perBasePoint`.  The
metric-side annulus bounds `hgi_ann`/`hLapChi_ann` and `hgisymm` remain CARRIED (the global-continuity
wall for the locally-regular pullback objects).  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous
hypotheses.
-/
import Mathlib
import QIQTH.CutoffResidualFiniteReg
import QIQTH.RecenterConnectC3c
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.CutoffAnnulusBounds
import QIQTH.PullbackMetric
import QIQTH.PullbackMetricC3
import QIQTH.RecenterDeWittC3

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatParametrixAnsatz
open QIQTH.HeatParametrixOrder QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 4

/-- **★ R5 — THE q-CENTERED CUTOFF RESIDUAL WIDTH-2 GAUSSIAN BOUND `hEboundW` (per base point `p`).**
For the pulled-back metric `g̃ = expPullbackMetric g₀ gi₀ hC p`, `g̃⁻¹ = expPullbackMetricInv g₀ gi₀ hC p`,
the concrete q-centered heat parametrix `H = heatParametrix 0 Θ u t` and `dtH = ∂_t H`, the
cutoff-parametrix heat-operator residual is globally dominated by a constant times the width-2 Gaussian
on a nonempty annulus `0 < a < b`:

  `∃ a b, 0 < a ∧ a < b ∧ ∃ B ≥ 0, ∀ v,
     |χ(v)·∂_tH v − Δ_g̃(χ·H) v| ≤ B · gaussDdimWide t v`  (χ = radialCutoff a b).

Instantiation of `cutoffResidual_global_gaussianWide_bound_C2` at `g̃`/`g̃⁻¹`: `hEnear` is discharged by
the R4c clean q-centered near bound `near_uncutResidual_expPullback_clean`; `hH2`/`hHann`/`hDHann` by
the folded-parametrix smoothness (`heatParametrix_folded` + `hw0smooth` + `parametrixH_annulus_bounds`);
`hDchi` by `pd_radialCutoff_bound_on_annulus`.  The carried residue is the genuine pullback-metric
continuity data `hgisymm`/`hgi_ann`/`hLapChi_ann` (global continuity is not available for the locally
`C²` pullback objects) and the global cofactor smoothness `hw0smooth`, plus the R4c near-inputs.  NOT
`a₁ = R/6`. -/
theorem cutoffResidual_expPullback_hEboundW
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    -- global smoothness of the folded cofactor profile (for `hH2`/`hHann`/`hDHann`)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    -- exp `Jet₄` regularity (the terminal recenter wall)
    (hfd3 : ContDiffOn ℝ 1
      (fun v => fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (expMap g₀ gi₀ hC p) w) z) v)
      (Metric.ball (0 : Point n) (QIQTH.ExpMap.expRho g₀ gi₀ hC p)))
    -- van-Vleck normalization
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    -- pointwise nondegeneracy (diffeomorphism property of `exp_p`)
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    -- CARRIED metric-continuity residue: `g̃⁻¹` symmetry + annulus bounds for `g̃⁻¹` and `Δ_g̃χ`
    (hgisymm : ∀ w i j, expPullbackMetricInv g₀ gi₀ hC p w i j
        = expPullbackMetricInv g₀ gi₀ hC p w j i)
    (hgi_ann : ∀ (a b : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |expPullbackMetricInv g₀ gi₀ hC p w i j| ≤ Kg)
    (hLapChi_ann : ∀ (a b : ℝ), ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
          (radialCutoff a b) w| ≤ Kc2)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |expPullbackMetricInv g₀ gi₀ hC p v i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
        (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  classical
  -- (1) `hEnear` from the R4c clean q-centered near bound; this FIXES the outer radius `b`.
  obtain ⟨b, hb0, hEnear⟩ :=
    near_uncutResidual_expPullback_clean g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u
      hfd3 hfold hinvT ht M W L hM hW hdev hw0bd hlap
  -- (2) `a := b/2` gives a nonempty annulus `0 < a < b`.
  set a : ℝ := b / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  -- The near constant `C` and its nonnegativity.
  set C : ℝ := (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n with hC_def
  have hL : (0 : ℝ) ≤ L := by
    obtain ⟨v0, hv0⟩ := hlap.exists
    exact le_trans (abs_nonneg _) hv0
  have hCnn : 0 ≤ C := by
    rw [hC_def]
    have h32 : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2 * M * W :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM) hW
    exact mul_nonneg (by linarith) (by positivity)
  -- (3) The concrete q-centered parametrix `H = heatParametrix 0 Θ u t = gaussDdim t · (foldedCoeff Θ u 0)`.
  have hHeq : (heatParametrix 0 Θ u t : Point n → ℝ)
      = fun y => gaussDdim t y * foldedCoeff Θ u 0 y := by
    funext x
    rw [heatParametrix_folded]
    simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u t w = gaussDdim t w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  -- `H` is smooth (`gaussDdim` smooth × cofactor smooth from `hw0smooth`), hence `ContDiffAt ℝ 2`.
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u t) := by
    rw [hHeq]
    exact (gaussDdim_contDiff t).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u t) w :=
    fun w => (hH.contDiffAt).of_le le_top
  -- (4) Annulus derivative bounds `hHann`/`hDHann` via `parametrixH_annulus_bounds`.
  obtain ⟨Mann, hMann0, hHann', hDHann'⟩ :=
    parametrixH_annulus_bounds t ht a b hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u t w| ≤ Mann * gaussDdim t w := by
    intro w h1 h2
    rw [hHeqw w]
    exact hHann' w h1 h2
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u t) j w| ≤ Mann * (1 / t) * gaussDdim t w := by
    intro w j h1 h2
    rw [hHeq]
    exact hDHann' w j h1 h2
  -- (5) Metric / cutoff annulus bounds.
  --     `hDchi` is metric-free; `hgibd`/`hLapChi` come from the CARRIED pullback-metric annulus data.
  obtain ⟨Kg, hKg, hgibd⟩ := hgi_ann a b
  obtain ⟨Kc1, hKc1, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kc2, hKc2, hLapChi⟩ := hLapChi_ann a b
  -- (6) Assemble the finite-regularity engine at `g̃`/`g̃⁻¹`.
  obtain ⟨B, hBnn, hBd⟩ :=
    cutoffResidual_global_gaussianWide_bound_C2
      (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
      (heatParametrix 0 Θ u t)
      (fun x => deriv (fun s => heatParametrix 0 Θ u s x) t)
      a b t ha hab ht hH2 hgisymm
      C hCnn hEnear Mann hMann0 hHann hDHann
      Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  exact ⟨a, b, ha, hab, B, hBnn, fun v => hBd v⟩

end QIQTH.HeatResidualBound
