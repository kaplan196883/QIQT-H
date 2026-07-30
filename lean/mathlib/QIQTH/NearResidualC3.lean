/-
  NearResidualC3 — brick R3c-4 of the RECENTER campaign: the FINITE-REGULARITY (`ContDiffAt`)
  twins of the near-diagonal residual SLICE (`residualN0_local_baseKernelW_slice`) and the b-ball
  `hEnear` source (`near_uncutResidual_gaussianWide_ball`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  The `⊤`-versions live in `ParametrixHEboundWiring` (`residualN0_local_baseKernelW_slice`) and
  `NearResidualBound` (`near_uncutResidual_gaussianWide_ball`).  Both are THIN wrappers over the full
  `N=0` residual Gaussian bound `residualN0_gaussian_bound`, carrying `ContDiff ℝ ⊤` on the metric
  `g`, inverse metric `gi`, Christoffel `Γ`, and ALL folded coefficients `w_k`.

  This file re-derives the SAME two conclusions with those smoothness hypotheses weakened to their
  TRUE MINIMAL finite order at the single base point `0`, exactly matching the finite-regularity
  residual bound `residualN0_gaussian_bound_C3` (R3c-3):
    • `g`  : `ContDiffAt ℝ 2` at `0`,
    • `gi` : `ContDiffAt ℝ 2` at `0`,
    • `Γ`  : `ContDiffAt ℝ 2` at `0`,
    • `w₀` : `ContDiffAt ℝ 3` at `0`  (only the `k = 0` folded coefficient is used at `N = 0`).

    • `residualN0_local_baseKernelW_slice_C3` — SAME conclusion as `residualN0_local_baseKernelW_slice`
      (explicit-ρ-ball width-2 base-kernel domination of the concrete `N=0` residual), obtained by the
      SAME regularity-free localiser `residualBound_local_baseKernelW` fed the finite-regularity
      residual bound `residualN0_gaussian_bound_C3` instead of the ⊤ one.

    • `near_uncutResidual_gaussianWide_ball_C3` — SAME conclusion as `near_uncutResidual_gaussianWide_ball`
      (the `hEnear` shape: `∃ b > 0, ∀ w, rncRadialSq w ≤ b² → |∂_t H − Δ_g H| ≤ Cslice·gaussDdimWide`
      for the concrete `H = heatParametrix 0 Θ u t`), obtained by feeding
      `residualN0_local_baseKernelW_slice_C3` through the SAME regularity-free wrapping
      (`baseKernelW ≤ gaussDdimWide`, ρ-ball → b-ball, `0 ≤ L` from `hlap`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  These are the finite-regularity NEAR/INTERIOR twins only.  Every
  regularity hypothesis is genuinely used (each order is load-bearing in the R3c-3 residual bound);
  the carried `hdev`/`hw0bd`/`hlap` are the same genuine `O(r²)`/boundedness facts as the ⊤ version;
  the van-Vleck 2-jet + RNC gauge hypotheses are inherited verbatim.  NOT the general-`N` bound, NOT
  the concrete-parametrix ANNULUS bounds, NOT the ASSEMBLY into `hEboundW`, NOT `a₁ = R/6`.

  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring
import QIQTH.NearResidualBound
import QIQTH.ResidualN0GaussianC3

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant
open QIQTH.RNCDecay

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **The near-diagonal residual SLICE, FINITE REGULARITY (R3c-4).**  The finite-regularity twin of
    `residualN0_local_baseKernelW_slice`: the concrete `N=0` parametrix residual is dominated on an
    EXPLICIT ρ-ball by the width-2 base kernel at base point `0`,
        `∃ ρ > 0, ∀ v, ‖v‖ < ρ →
           |parametrixResidualN 0 g gi Θ u t v| ≤ C'·baseKernelW 2 0 t v 0`,
    with `C' = (1 + 32·n²·M·W + L)·(√2)ⁿ`.  Proved by the SAME regularity-free localiser
    `residualBound_local_baseKernelW` fed the finite-regularity full `N=0` residual bound
    `residualN0_gaussian_bound_C3` (R3c-3) in place of the ⊤ `residualN0_gaussian_bound`.  The
    `ContDiff ⊤` metric/coefficient hypotheses are weakened to their true minimal finite order at `0`
    (`g, gi, Γ ∈ ContDiffAt ℝ 2`, `w₀ ∈ ContDiffAt ℝ 3`); only the `k = 0` folded coefficient is used.
    Curvature / RNC / `O(r²)`-deviation / coefficient hypotheses are inherited verbatim — genuine,
    load-bearing, none vacuous.  NOT `a₁ = R/6`. -/
theorem residualN0_local_baseKernelW_slice_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
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
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 0 g gi Θ u t v|
        ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n)
            * baseKernelW (2 : ℝ) (0 : ℝ) t v 0 :=
  residualBound_local_baseKernelW ht
    (residualN0_gaussian_bound_C3 g gi Θ u hg hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0 hsymm hinv hgauge
      hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap)

/-- **★ F1 (R3c-4) — the near/interior uncut-parametrix residual bound on a b-ball (`hEnear`),
    FINITE REGULARITY.**  The finite-regularity twin of `near_uncutResidual_gaussianWide_ball`: from
    the finite-regularity slice `residualN0_local_baseKernelW_slice_C3`
    (`|parametrixResidualN 0 …| ≤ Cslice·baseKernelW 2 0 t v 0` on a `‖·‖`-ball), converted to the
    wide-Gaussian dominator (`baseKernelW 2 0 ≤ gaussDdimWide`, via `gaussDdimWide_eq_scaled_baseKernelW`)
    and restricted from the slice's ρ-ball to a Euclidean b-ball (`rncRadialSq w ≤ b² ⟹ ‖w‖ ≤ b`, via
    `norm_le_rncRadial`), we obtain — for the CONCRETE parametrix `H = heatParametrix 0 Θ u t`,
    `dtH = ∂_t(heatParametrix 0 Θ u · t)` (whose `dtH − Δ_g H` is DEFINITIONALLY `parametrixResidualN 0`) —

      ∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
        |deriv (fun s => heatParametrix 0 Θ u s w) t − laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
          ≤ ((1 + 32·n²·M·W + L)·(√2)ⁿ) · gaussDdimWide t w .

    This is exactly the `hEnear` carry of `cutoffResidual_global_gaussianWide_bound` (near region),
    now at finite regularity.  The `ContDiff ⊤` metric/coefficient hypotheses are weakened to their
    true minimal finite order at `0` (`g, gi, Γ ∈ ContDiffAt ℝ 2`, `w₀ ∈ ContDiffAt ℝ 3`).  All
    remaining slice hypotheses (RNC normalisation, curvature gauge, `O(r²)` deviation `hdev`,
    coefficient bounds `hw0bd`/`hlap`) are reproduced verbatim; `0 ≤ L` is derived from `hlap`.  The
    wrapping proof is ported verbatim (only the inner slice call changes).  NOT `a₁ = R/6`. -/
theorem near_uncutResidual_gaussianWide_ball_C3
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
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
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
          ≤ ((1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n) * gaussDdimWide t w := by
  -- The finite-regularity slice: bound on the explicit ρ-ball against the width-2 base kernel.
  obtain ⟨ρ, hρ, hslice⟩ :=
    residualN0_local_baseKernelW_slice_C3 g gi Θ u hg hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
      hsymm hinv hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap
  refine ⟨ρ / 2, by linarith, fun w hw => ?_⟩
  -- (ρ-ball → b-ball): `rncRadialSq w ≤ (ρ/2)²` ⟹ `‖w‖ ≤ ρ/2 < ρ`.
  have hb0 : (0 : ℝ) ≤ ρ / 2 := by linarith
  have hnw : ‖w‖ < ρ := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  have hs := hslice w hnw
  -- Unfold `parametrixResidualN 0` into the concrete `dtH − Δ_g H` (definitional).
  simp only [parametrixResidualN] at hs
  -- (baseKernelW → gaussDdimWide): `baseKernelW 2 0 t w 0 ≤ gaussDdimWide t w`.
  have hbk_nn : (0 : ℝ) ≤ baseKernelW (2 : ℝ) (0 : ℝ) t w 0 := by
    rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt 2 ^ n :=
    one_le_pow₀ (by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt (by norm_num))
  have hbk_le : baseKernelW (2 : ℝ) (0 : ℝ) t w 0 ≤ gaussDdimWide t w := by
    rw [gaussDdimWide_eq_scaled_baseKernelW ht w]
    exact le_mul_of_one_le_left hbk_nn hsqrt_one
  -- The slice constant is nonnegative (`0 ≤ L` from `hlap` at the nonempty filter).
  have hL : (0 : ℝ) ≤ L := by
    obtain ⟨v0, hv0⟩ := hlap.exists
    exact le_trans (abs_nonneg _) hv0
  have h32 : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2 * M * W :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM) hW
  have hCpos : (0 : ℝ) ≤ (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n :=
    mul_nonneg (by linarith) (by positivity)
  -- Combine: slice bound, then base-kernel → wide-Gaussian.
  calc |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
      ≤ (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n
          * baseKernelW (2 : ℝ) (0 : ℝ) t w 0 := hs
    _ ≤ (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n * gaussDdimWide t w :=
        mul_le_mul_of_nonneg_left hbk_le hCpos

end QIQTH.HeatResidualBound
