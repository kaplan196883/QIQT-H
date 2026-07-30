/-
  CutoffResidualAssembled — the C4c-ASSEMBLE step: the DIAGONAL-CHART cutoff-parametrix residual
  bound `hEboundW` with ALL carries of `cutoffResidual_global_gaussianWide_bound` discharged by the
  three already-landed input lemmas.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DELIVERS.

  `cutoffResidual_global_gaussianWide_bound` (CutoffResidualGlobalBound.lean) is the ENGINE producing
  the global width-2 Gaussian bound on the cutoff-parametrix heat-operator residual, but it CARRIES a
  long list of concrete-parametrix / metric hypotheses (`hEnear`, `hHann`, `hDHann`, `hgibd`, `hDchi`,
  `hLapChi`, …).  This file INSTANTIATES that engine at the CONCRETE parametrix
  `H := heatParametrix 0 Θ u t`, `dtH := fun x => deriv (fun s => heatParametrix 0 Θ u s x) t`,
  discharging every one of those carries by three PROVED lemmas already in the repo:

    • `hEnear`             ← `near_uncutResidual_gaussianWide_ball`   (NearResidualBound.lean);
    • `hHann` / `hDHann`   ← `parametrixH_annulus_bounds`            (ParametrixHAnnulusBounds.lean);
    • `hgibd`/`hDchi`/`hLapChi` ← `gi_bound_on_annulus`,
        `pd_radialCutoff_bound_on_annulus`,
        `laplaceBeltrami_radialCutoff_bound_on_annulus`             (CutoffAnnulusBounds.lean).

  The cofactor regularity feeding `parametrixH_annulus_bounds` (`Continuous`, `PdiffAt`, continuous
  partials) is DERIVED from the SAME `hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)` already carried for
  the near lemma (the cofactor IS `foldedCoeff Θ u 0 = Θ^{−1/2}·u₀`, and
  `heatParametrix 0 Θ u t = gaussDdim t · foldedCoeff Θ u 0` by `heatParametrix_folded`).  So NO new
  hypothesis is introduced for the `H`-side beyond what the near lemma already needs; `H`'s
  `ContDiff ℝ ∞` is likewise derived (`gaussDdim` smooth × `hw 0` smooth).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE ONLY GENUINELY NEW CARRIES (both honest, load-bearing metric facts, NEITHER vacuous):
    • `hgisymm    : ∀ w i j, gi w i j = gi w j i`                    (inverse-metric symmetry);
    • `hgi_cont   : ∀ i j, Continuous (fun w => gi w i j)`           (inverse metric continuous);
    • `hchris_cont : ∀ k i j, Continuous (fun w => christoffel g gi k i j w)` (Christoffel continuous).
  All remaining hypotheses are exactly the near lemma's genuine RNC / curvature-gauge / `O(r²)`
  deviation data, reproduced verbatim.  `a := b/2` (with `b > 0` from the near lemma) makes the
  annulus `0 < a < b` nonempty-friendly.

  ⚠ HONEST SCOPE (binding).  This is the DIAGONAL-CHART (base point `0`) `hEboundW`, the exact
  width-2 input the Levi/Neumann engine `neumann_summable_alpha0_width2` consumes.  It does NOT build
  the OFF-DIAGONAL / all-base-point recentering (`q ≠ 0`).  NOT `a₁ = R/6`.  No `sorry`, no new
  axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.NearResidualBound
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.CutoffAnnulusBounds
import QIQTH.CutoffResidualGlobalBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatParametrixAnsatz
open QIQTH.HeatParametrixOrder QIQTH.GaussianWidthTolerant
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ THE DIAGONAL-CHART CUTOFF RESIDUAL BOUND (`hEboundW`), fully assembled.**  For the concrete
    heat parametrix `H = heatParametrix 0 Θ u t` and `dtH = ∂_t H`, the cutoff-parametrix heat-operator
    residual is globally dominated by a constant times the width-2 Gaussian on a nonempty annulus
    `0 < a < b`:

      `∃ a b, 0 < a ∧ a < b ∧ ∃ B ≥ 0, ∀ v,
         |χ(v)·∂_tH v − Δ_g(χ·H) v| ≤ B · gaussDdimWide t v`  (χ = radialCutoff a b).

    Every carry of `cutoffResidual_global_gaussianWide_bound` is discharged:
    `hEnear` by `near_uncutResidual_gaussianWide_ball`; `hHann`/`hDHann` by `parametrixH_annulus_bounds`
    (cofactor regularity derived from `hw 0`); `hgibd`/`hDchi`/`hLapChi` by the compactness bounds of
    `CutoffAnnulusBounds`.  The only genuinely new carries are the honest metric facts `hgisymm`,
    `hgi_cont`, `hchris_cont`; the rest are the near lemma's RNC/curvature/deviation data.  NOT
    `a₁ = R/6`. -/
theorem cutoffResidual_diag_hEboundW
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiC : ∀ i j, ContDiff ℝ ⊤ (fun y => gi y i j))
    (hCd : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (hgi_cont : ∀ i j, Continuous (fun w => gi w i j))
    (hchris_cont : ∀ k i j, Continuous (fun w => christoffel g gi k i j w))
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  classical
  -- (1) `hEnear` from the near-diagonal residual bound; this also FIXES the outer radius `b`.
  obtain ⟨b, hb0, hEnear⟩ :=
    near_uncutResidual_gaussianWide_ball g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0
      hsymm hinv hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap
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
  -- (3) The concrete-parametrix `H = heatParametrix 0 Θ u t = gaussDdim t · (foldedCoeff Θ u 0)`.
  have hHeq : (heatParametrix 0 Θ u t : Point n → ℝ)
      = fun y => gaussDdim t y * foldedCoeff Θ u 0 y := by
    funext x
    rw [heatParametrix_folded]
    simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u t w = gaussDdim t w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  -- `H` is smooth (`gaussDdim` smooth × cofactor smooth from `hw 0`).
  have hH : ContDiff ℝ ∞ (heatParametrix 0 Θ u t) := by
    rw [hHeq]
    exact ((gaussDdim_contDiff t).mul (hw 0)).of_le le_top
  -- (4) Annulus derivative bounds `hHann`/`hDHann` via `parametrixH_annulus_bounds`.
  obtain ⟨Mann, hMann0, hHann', hDHann'⟩ :=
    parametrixH_annulus_bounds t ht a b hb0 (foldedCoeff Θ u 0)
      ((hw 0).continuous)
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) (hw 0) i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) (hw 0) j).continuous)
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
  -- (5) Metric / cutoff annulus bounds `hgibd`/`hDchi`/`hLapChi`.
  obtain ⟨Kg, hKg, hgibd⟩ := gi_bound_on_annulus gi a b hgi_cont
  obtain ⟨Kc1, hKc1, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kc2, hKc2, hLapChi⟩ :=
    laplaceBeltrami_radialCutoff_bound_on_annulus g gi a b hgi_cont hchris_cont
  -- (6) Assemble the engine.
  obtain ⟨B, hBnn, hBd⟩ :=
    cutoffResidual_global_gaussianWide_bound g gi (heatParametrix 0 Θ u t)
      (fun x => deriv (fun s => heatParametrix 0 Θ u s x) t) a b t ha hab ht hH hgisymm
      C hCnn hEnear Mann hMann0 hHann hDHann
      Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  exact ⟨a, b, ha, hab, B, hBnn, fun v => hBd v⟩

end QIQTH.HeatResidualBound
