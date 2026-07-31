/-
# RECENTER brick J4-12 — the cutoff-residual→`hEboundW` producer with `hgi_cont`/`hchris_cont`
  DISCHARGED by choosing the cutoff radii INSIDE the nondegeneracy ball `B(0,ρ₀)`.

`cutoffResidual_expPullback_hEboundW_uncond2` (`RecenterAnnulusUncond.lean`) reduced the metric-side
annulus BOUND families `hgi_ann`/`hLapChi_ann` to the strictly-weaker CONTINUITY residue
`hgi_cont`/`hchris_cont`, but those were still carried as `∀ a b`-quantified hypotheses (they must range
over annuli reaching `b ≥ ρ₀`, where `g̃` may degenerate at conjugate points).  J4-11
(`AnnulusContinuityWithinRho.lean`) proved the two producers that supply `hgi_cont`/`hchris_cont` FOR
ANNULI WITH `b < ρ₀` — from J4-9's ball-nondegeneracy of `g̃` — but they cannot be fed to `_uncond2`
whose interface demands the full `∀ a b` range.

Because `a₁ = R/6` is a LOCAL DIAGONAL invariant, the parametrix cutoff may be supported in a small ball.
This file realizes that: it REPLAYS the concrete construction of `cutoffResidual_expPullback_hEboundW`
(the `near_uncutResidual_expPullback_clean_uncond` near bound → parametrix annulus bounds →
`cutoffResidual_global_gaussianWide_bound_C2` engine), but SHRINKS the cutoff radii to `b' := min b (ρ₀/2)`
(`< ρ₀`), `a' := b'/2`, so the required metric-side annulus bounds at `(a',b')` can be produced entirely
INTERNALLY from the J4-11 within-`ρ₀` continuity producers + the compactness bricks
`gi_bound_on_annulus_of_continuousOn` / `laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn`.

Result: `cutoffResidual_expPullback_hEboundW_uncond3` has the SAME `hEboundW`-shaped conclusion as
`_uncond2` with `hgi_cont` AND `hchris_cont` REMOVED (genuinely discharged, not carried), and every other
genuine input of `_uncond2` kept verbatim (ambient frame data `hsymm0`/`hinvF`/`hg`/`hframe`, global
cofactor smoothness `hw0smooth`, van-Vleck `hfold`, pointwise nondegeneracy `hinvT`, `g̃⁻¹` symmetry
`hgisymm`, the `t`/`M`/`W`/`L` analytic bounds `hdev`/`hw0bd`/`hlap`).

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  `hgi_cont`/`hchris_cont` are DISCHARGED via the J4-11 producers (which come
from `hg`/`hinvF`); the discharge is legitimate because the returned radii `a' < b' < ρ₀` sit inside the
nondegeneracy ball where `g̃` is a unit.  The returned annulus is nonempty (`0 < a' < b'`).  NOT
`a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses, no carried conclusion.
-/
import Mathlib
import QIQTH.RecenterAnnulusUncond
import QIQTH.AnnulusContinuityWithinRho
import QIQTH.RecenterResidualUncond
import QIQTH.RecenterCutoffC3
import QIQTH.FlatTail

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

/-- **★ J4-12 — q-centered cutoff residual width-2 Gaussian bound `hEboundW`, with the continuity residue
    `hgi_cont`/`hchris_cont` DISCHARGED via local (within-`ρ₀`) support.**  Same `hEboundW`-shaped
    conclusion as `cutoffResidual_expPullback_hEboundW_uncond2`, but BOTH continuity hypotheses are
    REMOVED.  The construction replays `cutoffResidual_expPullback_hEboundW` with the cutoff radii shrunk
    to `b' := min b (ρ₀/2) < ρ₀`, `a' := b'/2`; the metric-side annulus bounds at `(a',b')` are produced
    internally from the J4-11 within-`ρ₀` continuity producers
    (`expPullbackMetricInv_continuousOn_annulus_within` /
    `christoffel_expPullback_continuousOn_annulus_within`, both fed by `hg`/`hinvF`) composed with the
    compactness bricks.  Every other genuine input of `_uncond2` is kept.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_expPullback_hEboundW_uncond3
    (g₀ gi₀ : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g₀ gi₀ a b c y)) (p : Point n)
    (hsymm0 : ∀ y a b, g₀ y a b = g₀ y b a)
    (hinvF : ∀ y a b, (∑ σ, g₀ y a σ * gi₀ y σ b) = if a = b then 1 else 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g₀ y a b))
    (hframe : ∀ i j, g₀ p i j = (if i = j then 1 else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hfold : ∀ᶠ v in nhds (0 : Point n),
      foldedCoeff Θ u 0 v = (Matrix.det (expPullbackMetric g₀ gi₀ hC p v)) ^ (-1 / 4 : ℝ))
    (hinvT : ∀ y i j,
      (∑ σ, expPullbackMetricInv g₀ gi₀ hC p y i σ * expPullbackMetric g₀ gi₀ hC p y σ j)
        = if i = j then 1 else 0)
    (hgisymm : ∀ w i j, expPullbackMetricInv g₀ gi₀ hC p w i j
        = expPullbackMetricInv g₀ gi₀ hC p w j i)
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
  -- (0) within-`ρ₀` continuity producers (J4-11), fed by `hg` + the base-point inverse `hinvF p`.
  obtain ⟨ρ₀gi, hρ0gi, hgi_prod⟩ :=
    expPullbackMetricInv_continuousOn_annulus_within g₀ gi₀ hC p hg (fun a b => hinvF p a b)
  obtain ⟨ρ₀ch, hρ0ch, hch_prod⟩ :=
    christoffel_expPullback_continuousOn_annulus_within g₀ gi₀ hC p hg (fun a b => hinvF p a b)
  set ρ₀ : ℝ := min ρ₀gi ρ₀ch with hρ₀def
  have hρ₀pos : 0 < ρ₀ := lt_min hρ0gi hρ0ch
  have hρ₀gi : ρ₀ ≤ ρ₀gi := min_le_left _ _
  have hρ₀ch : ρ₀ ≤ ρ₀ch := min_le_right _ _
  -- (1) `hEnear` from the R4c clean q-centered near bound; this FIXES the outer radius `b`.
  obtain ⟨b, hb0, hEnear⟩ :=
    near_uncutResidual_expPullback_clean_uncond g₀ gi₀ hC p hsymm0 hinvF hg hframe Θ u
      hfold hinvT ht M W L hM hW hdev hw0bd hlap
  -- The near constant `C` and its nonnegativity (rewrites into `hEnear`).
  set C : ℝ := (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n with hC_def
  have hL : (0 : ℝ) ≤ L := by
    obtain ⟨v0, hv0⟩ := hlap.exists
    exact le_trans (abs_nonneg _) hv0
  have hCnn : 0 ≤ C := by
    rw [hC_def]
    have h32 : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2 * M * W :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM) hW
    exact mul_nonneg (by linarith) (by positivity)
  -- (2) SHRINK the radii inside the nondegeneracy ball: `b' := min b (ρ₀/2) < ρ₀`, `a' := b'/2`.
  set b' : ℝ := min b (ρ₀ / 2) with hb'_def
  have hb'0 : 0 < b' := lt_min hb0 (by linarith)
  have hb'leb : b' ≤ b := min_le_left _ _
  have hb'ρ : b' < ρ₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb'giρ : b' < ρ₀gi := lt_of_lt_of_le hb'ρ hρ₀gi
  have hb'chρ : b' < ρ₀ch := lt_of_lt_of_le hb'ρ hρ₀ch
  set a' : ℝ := b' / 2 with ha'_def
  have ha' : 0 < a' := by rw [ha'_def]; linarith
  have ha'b' : a' < b' := by rw [ha'_def]; linarith
  -- (2') `hEnear` at the shrunk outer radius `b'`, by monotonicity `rncRadialSq w ≤ b'² ⟹ ≤ b²`.
  have hEnear' : ∀ w : Point n, rncRadialSq w ≤ b' ^ 2 →
      |deriv (fun s => heatParametrix 0 Θ u s w) t
          - laplaceBeltrami (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
              (heatParametrix 0 Θ u t) w|
        ≤ C * gaussDdimWide t w := by
    intro w hw
    have hb'2 : b' ^ 2 ≤ b ^ 2 := by nlinarith [hb'0.le, hb'leb]
    exact hEnear w (le_trans hw hb'2)
  -- (3) The concrete q-centered parametrix `H = heatParametrix 0 Θ u t = gaussDdim t · (foldedCoeff Θ u 0)`.
  have hHeq : (heatParametrix 0 Θ u t : Point n → ℝ)
      = fun y => gaussDdim t y * foldedCoeff Θ u 0 y := by
    funext x
    rw [heatParametrix_folded]
    simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u t w = gaussDdim t w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u t) := by
    rw [hHeq]
    exact (gaussDdim_contDiff t).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u t) w :=
    fun w => (hH.contDiffAt).of_le le_top
  -- (4) Annulus derivative bounds `hHann`/`hDHann` at `(a',b')` via `parametrixH_annulus_bounds`.
  obtain ⟨Mann, hMann0, hHann', hDHann'⟩ :=
    parametrixH_annulus_bounds t ht a' b' hb'0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  have hHann : ∀ w : Point n, a' ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b' ^ 2 →
      |heatParametrix 0 Θ u t w| ≤ Mann * gaussDdim t w := by
    intro w h1 h2
    rw [hHeqw w]
    exact hHann' w h1 h2
  have hDHann : ∀ (w : Point n) (j : Fin n), a' ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b' ^ 2 →
      |pd (heatParametrix 0 Θ u t) j w| ≤ Mann * (1 / t) * gaussDdim t w := by
    intro w j h1 h2
    rw [hHeq]
    exact hDHann' w j h1 h2
  -- (5) Metric / cutoff annulus bounds at `(a',b')`, DISCHARGED from the within-`ρ₀` producers.
  --     `hgibd`/`hLapChi` now come from the J4-11 continuity producers + compactness bricks (no carry).
  obtain ⟨Kg, hKg, hgibd⟩ :=
    gi_bound_on_annulus_of_continuousOn (expPullbackMetricInv g₀ gi₀ hC p) a' b'
      (fun i j => hgi_prod a' b' i j hb'0.le hb'giρ)
  obtain ⟨Kc1, hKc1, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a' b'
  obtain ⟨Kc2, hKc2, hLapChi⟩ :=
    laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn
      (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p) a' b'
      (fun i j => hgi_prod a' b' i j hb'0.le hb'giρ)
      (fun k i j => hch_prod a' b' k i j hb'0.le hb'chρ)
  -- (6) Assemble the finite-regularity engine at `g̃`/`g̃⁻¹` with radii `(a',b')`.
  obtain ⟨B, hBnn, hBd⟩ :=
    cutoffResidual_global_gaussianWide_bound_C2
      (expPullbackMetric g₀ gi₀ hC p) (expPullbackMetricInv g₀ gi₀ hC p)
      (heatParametrix 0 Θ u t)
      (fun x => deriv (fun s => heatParametrix 0 Θ u s x) t)
      a' b' t ha' ha'b' ht hH2 hgisymm
      C hCnn hEnear' Mann hMann0 hHann hDHann
      Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  exact ⟨a', b', ha', ha'b', B, hBnn, fun v => hBd v⟩

end QIQTH.HeatResidualBound
