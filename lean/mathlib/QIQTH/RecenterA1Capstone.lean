/-
  RecenterA1Capstone — RECENTER brick R7, the CLOSING CAPSTONE.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE ASSEMBLES.

  `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` is the conditional true-kernel diagonal
  Seeley–DeWitt `a₁ = R/6` capstone.  Two of its carries are the analytically hardest:

    • `hEboundW` — the GLOBAL width-2 residual bound `∀ τ p q, 0<τ → |E τ p q| ≤ C·baseKernelW 2 0 τ p q`
      (the C4c off-diagonal parametrix primitive), and
    • `hInt`     — the per-step integrability family `IterConvIntegrableW E 2 0 C`.

  This file DISCHARGES both of them via the RECENTER + MEASURABILITY machinery, without touching the
  other genuine carries.  Concretely:

    • `RecenterHEboundW.hEboundW_of_perBasePoint_bound` produces `hEboundW` from the per-base-point,
      uniform-in-`q` WIDE-Gaussian bound `hunif` and the near-diagonal coordinate-change comparison
      `hcoord`, with the single constant `C = B · (√2)ⁿ · D`.
    • `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas` produces `hInt` from the SAME
      `hEboundW`, the vanishing `hEzero`, and the single base joint measurability `hEmeas` of `E`.

  Feeding both into `trueKernel_diagonal_a1_eq_R6` yields the SAME `a₁ = R/6` diagonal expansion, now
  conditional on exactly the recenter-reduced hypothesis set
  `{hunif, hcoord, hEzero, hEmeas, hE, hHdiag, hCorrHigher, hDuhamel, hInter, RNC data}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  This is STILL a CONDITIONAL capstone, NOT an unconditional `a₁ = R/6`.
  It merely trades the two analytic carries `hEboundW`/`hInt` for the geometric/measurability inputs
  `hunif`/`hcoord`/`hEzero`/`hEmeas` (each genuinely used).  The remaining genuine carries
  `hE`/`hHdiag`/`hCorrHigher`/`hDuhamel`/`hInter` and the RNC-centre data are threaded verbatim.  No
  `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.TrueKernelA1
import QIQTH.RecenterHEboundW
import QIQTH.IterEMeasurable

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.FlatHeatEquation QIQTH.ResidueBound

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ RECENTER CAPSTONE R7 — the true-kernel diagonal `a₁ = R/6`, with `hEboundW` and `hInt`
    DISCHARGED via the recenter + measurability machinery.**

    Identical conclusion to `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` — the true heat kernel solves
    the heat equation AND its diagonal expands as
      `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`, `R = ∑ᵢ Ric_{ii}`,
    the `t¹` coefficient the DERIVED `R/6` — but with the two analytic carries of that theorem
    REPLACED by the recenter-reduced inputs:

      • `hEboundW` is supplied by `hEboundW_of_perBasePoint_bound E Vmap B D hB hunif hcoord`, with the
        single constant `C = B · (√2)ⁿ · D`;
      • `hInt` is supplied by `iterConvIntegrableW_of_bound_baseMeas E C hEboundW hEzero hEmeas`.

    Thus `a₁ = R/6` is conditional on precisely `{hunif, hcoord, hEzero, hEmeas}` (the recenter /
    measurability residues) together with the remaining genuine carries
    `{hE, hHdiag, hCorrHigher, hDuhamel, hInter}` and the RNC-centre data.  `hD : 0 ≤ D` is used to
    produce `0 ≤ C`.  ⚠ NOT an unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_recenter
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H E : ℝ → Point n → Point n → ℝ) (cRem : ℝ)
    -- RECENTER inputs (⟹ `hEboundW` with `C = B·(√2)ⁿ·D`):
    (Vmap : Point n → Point n → Point n) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hunif : ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
        |E τ p q| ≤ B * gaussDdimWide τ (Vmap q p))
    (hcoord : ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
        gaussDdim (2 * τ) (Vmap q p) ≤ D * gaussDdim (2 * τ) (p - q))
    -- MEASURABILITY inputs (⟹ `hInt` from the same `hEboundW`):
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    -- RNC / metric-Hessian / transport-source data (the parametrix diagonal `a₁ = R/6`):
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- the diagonal identification: `H`'s diagonal is the concrete van-Vleck parametrix diagonal:
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    -- ★ the carried Levi-correction-higher-order-on-the-diagonal fact (starts at `t²`):
    (hCorrHigher : heatConv H (leviSeries E) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * (t ^ 2 * cRem))
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
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + cRem)) := by
  -- Discharge `hEboundW` via the recenter machinery: `C = B·(√2)ⁿ·D`.
  have hEboundW := hEboundW_of_perBasePoint_bound E Vmap B D hB hunif hcoord
  -- Discharge `hInt` from the SAME `hEboundW` + measurability.
  have hInt := iterConvIntegrableW_of_bound_baseMeas E (B * Real.sqrt 2 ^ n * D) hEboundW hEzero hEmeas
  -- `0 ≤ C`, from `0 ≤ B`, `0 ≤ (√2)ⁿ`, `0 ≤ D`.
  have hC : (0 : ℝ) ≤ B * Real.sqrt 2 ^ n * D :=
    mul_nonneg (mul_nonneg hB (by positivity)) hD
  exact QIQTH.TrueKernelA1.trueKernel_diagonal_a1_eq_R6
    g gi Ric N hN t ht H E (B * Real.sqrt 2 ^ n * D) cRem hC
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hCorrHigher hEboundW hInt
    hE hDuhamel hInter hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
