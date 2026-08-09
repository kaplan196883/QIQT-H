/-
  A1GaugeDischarge — J4-502: discharge the carried metric-Hessian trace `htr` in the true-kernel
  `a₁ = R/6` capstone from the RNC normal-coordinate gauge.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS DELIVERS.

  The conditional capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` carries — among its genuine,
  labeled hypotheses — the RAW metric-Hessian-trace datum
      `htr : ∀ c d, ∑_a ∂_c∂_d g_{aa}(0) = −(2/3) Ric_{cd}`.
  This looks ad hoc (a bare trace identity).  RNC3 (`RNCExpansion.rnc_htr_of_gauge`) DERIVES exactly
  this trace from the falsifiable **normal-coordinate gauge**
      `hgauge : ∀ i a b c, ∂_{(a}Γ^i_{bc)}(0) = 0`   (the totally-symmetrized Christoffel derivative
  vanishes at the origin — the geometric characterization of Riemannian normal coordinates), given
  `g(0)=δ`, `gi(0)=δ`, `∂g(0)=0`, `g` symmetric.

  `trueKernel_diagonal_a1_eq_R6_gauged` is the capstone with `htr` REPLACED by `hgauge` (+ the inverse-
  metric smoothness `hgiSmooth` and symmetry `hsymm` that `rnc_htr_of_gauge` consumes).  It applies the
  capstone ONCE as a black box with `Ric := fun c d => ricci g gi c d 0` and
  `htr := rnc_htr_of_gauge …`, so the `t¹` coefficient is the honest scalar curvature
  `R = ∑_i Ric_{ii} = ∑_i ricci g gi i i 0` over `6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  This is a QUALITATIVE reduction, NOT a full discharge.  The raw trace
  identity `htr` is replaced by the recognized geometric GAUGE `hgauge` — a more-primitive, falsifiable
  normal-coordinate condition (the file `RNCExpansion` proves it is load-bearing: drop `hgauge` and the
  `−(2/3)Ric` trace becomes false).  It is NOT eliminated: `hgauge` remains a carried geometric input
  (there is no Mathlib construction of Riemannian normal / `exp`-chart coordinates to discharge it
  against).  So the a₁ capstone's carried "big three" become `hCorrHigher / hEboundW / hgauge` — the
  metric 2-jet input is now the normal-coordinate gauge rather than a bare trace.  Still CONDITIONAL;
  NOT an unconditional `a₁ = R/6`, NOT the numerical value of G, NOT a curved heat kernel.

  Grounded in the RNC3 machinery of `QIQTH.RNCExpansion` (`rnc_htr_of_gauge`) and the capstone of
  `QIQTH.TrueKernelA1`.
-/
import Mathlib
import QIQTH.TrueKernelA1
import QIQTH.RNCExpansion

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.TrueKernelA1

namespace QIQTH.A1GaugeDischarge

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ J4-502 — the true-kernel diagonal `a₁ = R/6`, with the metric-Hessian trace `htr` DISCHARGED
    from the RNC normal-coordinate gauge.**  Identical in force to
    `TrueKernelA1.trueKernel_diagonal_a1_eq_R6`, but its carried metric 2-jet input is the falsifiable
    normal-coordinate gauge
        `hgauge : ∀ i a b c, ∂_a Γ^i_{bc}(0) + ∂_b Γ^i_{ca}(0) + ∂_c Γ^i_{ab}(0) = 0`
    (the totally-symmetrized Christoffel derivative vanishes at the origin) rather than the raw trace
    `htr : ∑_a ∂_c∂_d g_{aa}(0) = −(2/3) Ric_{cd}`.  RNC3 (`rnc_htr_of_gauge`) derives `htr` from
    `hgauge` (+ `g(0)=δ`, `gi(0)=δ`, `∂g(0)=0`, `g` symmetric), so the capstone is applied ONCE as a
    black box with `Ric := fun c d => ricci g gi c d 0`.

    The `t¹` coefficient is the honest scalar curvature `(∑_i ricci g gi i i 0)/6`.

    ⚠ CONDITIONAL (unchanged in force): `hEboundW` (the C4c off-diagonal parametrix primitive) and
    `hCorrHigher` (the `O(t²)` Levi correction) plus the analytic Duhamel/interchange/integrability
    carries remain.  The metric 2-jet input `htr` is now the more-primitive geometric GAUGE `hgauge`
    (a real qualitative reduction), but `hgauge` is still a CARRIED input (Mathlib-absent RNC chart),
    NOT eliminated.  NOT an unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_gauged
    (g gi : Point n → Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H E : ℝ → Point n → Point n → ℝ) (C cRem : ℝ) (hC : 0 ≤ C)
    -- RNC / metric-gauge / transport-source data (the parametrix diagonal `a₁ = R/6`):
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hgiSmooth : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    -- ★ the falsifiable normal-coordinate gauge that DERIVES the metric-Hessian trace `htr`:
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- the diagonal identification: `H`'s diagonal is the concrete van-Vleck parametrix diagonal:
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    -- ★ the carried Levi-correction-higher-order-on-the-diagonal fact (starts at `t²`):
    (hCorrHigher : heatConv H (leviSeries E) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * (t ^ 2 * cRem))
    -- ★ the carried C4c global width-2 residual bound (drives the Neumann convergence):
    (hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E 2 0 C)
    -- ★ the carried parametrix-residual / Duhamel / interchange facts:
    (hE : heatOp g gi H t 0 0 = E t 0 0)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries E) u p q) t 0 0
        = leviSeries E t 0 0 + heatConv E (leviSeries E) t 0 0)
    (hInter : heatConv E (leviSeries E) t 0 0
        = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t 0 0)
    -- the `heatOp`-linearity regularity side conditions:
    (hDH : DifferentiableAt ℝ (fun u => H u 0 0) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries E) u 0 0) t)
    (hCH : ContDiff ℝ ⊤ (fun p => H t p 0))
    (hCConv : ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries E) t p 0)) :
    heatOp g gi (trueHeatKernel H (leviSeries E)) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries E) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + cRem)) := by
  -- `gi(0)=δ` in `Matrix` form, as `rnc_htr_of_gauge` consumes it.
  have hgi0 : ∀ i j, gi (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hgi i j, Matrix.one_apply]
  -- Apply the capstone ONCE as a black box, with `Ric := ricci g gi · · 0` and `htr` DISCHARGED from
  -- the normal-coordinate gauge via RNC3.
  exact trueKernel_diagonal_a1_eq_R6 g gi (fun c d => ricci g gi c d 0)
    N hN t ht H E C cRem hC hg hg0 hgi hΓ hdg0
    (fun c d => rnc_htr_of_gauge g gi hg hgiSmooth hgi0 hdg0 hsymm hgauge c d)
    hsrc hHdiag hCorrHigher hEboundW hInt hE hDuhamel hInter hDH hDConv hCH hCConv

#print axioms trueKernel_diagonal_a1_eq_R6_gauged

end QIQTH.A1GaugeDischarge
