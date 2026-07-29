/-
  NearResidualBound — discharging the last carried hypothesis `hEnear` of the C4c cutoff-residual
  global bound `cutoffResidual_global_gaussianWide_bound` from the PROVED near-diagonal slice.

  WHAT IS BUILT HERE (the honest boundary — read it).

  `cutoffResidual_global_gaussianWide_bound` (CutoffResidualGlobalBound.lean) carries, among its
  concrete-parametrix inputs, the NEAR/INTERIOR uncut-parametrix residual bound

      hEnear : ∀ w, rncRadialSq w ≤ b² → |dtH w − laplaceBeltrami g gi H w| ≤ C·gaussDdimWide t w ,

  where in the concrete instance `H = heatParametrix 0 Θ u t` and
  `dtH = fun x => deriv (fun s => heatParametrix 0 Θ u s x) t`, so that (DEFINITIONALLY)
      dtH w − laplaceBeltrami g gi H w = parametrixResidualN 0 g gi Θ u t w .

  The near-diagonal slice `residualN0_local_baseKernelW_slice` (ParametrixHEboundWiring.lean) proves,
  from the genuine RNC / curvature / O(r²)-deviation data,
      ∃ ρ > 0, ∀ v, ‖v‖ < ρ →
        |parametrixResidualN 0 g gi Θ u t v| ≤ Cslice · baseKernelW 2 0 t v 0 ,
      Cslice := (1 + 32·n²·M·W + L)·(√2)ⁿ ,
  a bound against the width-2 base kernel on a `‖·‖`-ball (sup norm on `Point n = Fin n → ℝ`).

  THIS FILE (floor F1 — the FULL `hEnear` on a b-ball):
    `near_uncutResidual_gaussianWide_ball` produces
      ∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            − laplaceBeltrami g gi (heatParametrix 0 Θ u t) w| ≤ Cslice · gaussDdimWide t w ,
    which is EXACTLY the `hEnear` shape (concrete `H`, `dtH`; the `dtH − Δ_g H = parametrixResidualN 0`
    identity is DEFINITIONAL — `simp only [parametrixResidualN]`).

  The two conversions (floor F2), both discharged here:
    • `baseKernelW → gaussDdimWide`: since `gaussDdimWide t v = (√2)ⁿ · baseKernelW 2 0 t v 0`
      (`gaussDdimWide_eq_scaled_baseKernelW`) with `(√2)ⁿ ≥ 1` and `baseKernelW ≥ 0`, we have
      `baseKernelW 2 0 t v 0 ≤ gaussDdimWide t v`, so `Cslice·baseKernelW ≤ Cslice·gaussDdimWide`
      (same constant `Cslice`).
    • ρ-ball → b-ball: `rncRadialSq w ≤ b²` (`0 ≤ b`) gives `‖w‖ ≤ rncRadial w = √(rncRadialSq w) ≤ b`
      (`norm_le_rncRadial`, sup ≤ Euclidean radial), so choosing `b := ρ/2 < ρ` puts the whole b-ball
      inside the slice's ρ-ball, where the slice bound applies.

  ALL hypotheses are the slice's genuine RNC/curvature/deviation data, reproduced verbatim; none are
  vacuous.  `0 ≤ L` is DERIVED from `hlap` (the `∀ᶠ` bound at a nonempty neighbourhood filter forces
  `0 ≤ |…| ≤ L`), so `Cslice ≥ 0` needs no extra assumption.

  ⚠ HONEST SCOPE (binding).  This is the NEAR/INTERIOR part only — the b-ball residual bound, feeding
  the `(a)` NEAR region of `cutoffResidual_global_gaussianWide_bound`.  It does NOT build:
    – the concrete-parametrix ANNULUS bounds `hHann`/`hDHann` and the metric/cutoff bounds
      `hgibd`/`hDchi`/`hLapChi` (regions `(b)`/`(c)` of the cutoff bound — separate bricks);
    – the ASSEMBLY (instantiating `cutoffResidual_global_gaussianWide_bound` with ALL carries
      discharged) ⟹ the diagonal-chart `hEboundW`;
    – `a₁ = R/6` (which stays carried until the whole C4c/C6 chain closes).
  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.ParametrixHEboundWiring
import QIQTH.ParametrixResidualN0Bound
import QIQTH.ParametrixResidualBaseKernel
import QIQTH.CutoffResidualGlobalBound
import QIQTH.RNCDecay

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.TimeSimplexBeta QIQTH.LeviSeries QIQTH.HeatDuhamel QIQTH.GaussianWidthTolerant
open QIQTH.RNCDecay

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★ F1 — the near/interior uncut-parametrix residual bound on a b-ball (`hEnear`).**  From the
    proved near-diagonal slice `residualN0_local_baseKernelW_slice`
    (`|parametrixResidualN 0 …| ≤ Cslice·baseKernelW 2 0 t v 0` on a `‖·‖`-ball), converted to the
    wide-Gaussian dominator (`baseKernelW 2 0 ≤ gaussDdimWide`, via `gaussDdimWide_eq_scaled_baseKernelW`)
    and restricted from the slice's ρ-ball to a Euclidean b-ball (`rncRadialSq w ≤ b² ⟹ ‖w‖ ≤ b`, via
    `norm_le_rncRadial`), we obtain — for the CONCRETE parametrix `H = heatParametrix 0 Θ u t`,
    `dtH = ∂_t(heatParametrix 0 Θ u · t)` (whose `dtH − Δ_g H` is DEFINITIONALLY `parametrixResidualN 0`) —

      ∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
        |deriv (fun s => heatParametrix 0 Θ u s w) t − laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
          ≤ ((1 + 32·n²·M·W + L)·(√2)ⁿ) · gaussDdimWide t w .

    This is exactly the `hEnear` carry of `cutoffResidual_global_gaussianWide_bound` (near region).
    All slice hypotheses (RNC normalisation, curvature gauge, `O(r²)` deviation `hdev`, coefficient
    bounds `hw0bd`/`hlap`) are reproduced verbatim; `0 ≤ L` is derived from `hlap`.  NOT `a₁ = R/6`. -/
theorem near_uncutResidual_gaussianWide_ball
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
  -- The slice: bound on the explicit ρ-ball against the width-2 base kernel.
  obtain ⟨ρ, hρ, hslice⟩ :=
    residualN0_local_baseKernelW_slice g gi Θ u hg hgiC hCd hw hg0 hgi0 hdg0 hdgi0 hΓ0
      hsymm hinv hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap
  refine ⟨ρ / 2, by linarith, fun w hw => ?_⟩
  -- (F2, ρ-ball → b-ball): `rncRadialSq w ≤ (ρ/2)²` ⟹ `‖w‖ ≤ ρ/2 < ρ`.
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
  -- (F2, baseKernelW → gaussDdimWide): `baseKernelW 2 0 t w 0 ≤ gaussDdimWide t w`.
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
