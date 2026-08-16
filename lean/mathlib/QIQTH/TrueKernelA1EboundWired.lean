/-
  TrueKernelA1EboundWired — J4-759: WIRE the fully-unconditional width-2 residual bound
  `gatedWitness_hEboundW_unconditional` (J4-100, `UniformChartRadius.lean`) into the reduced
  Seeley–DeWitt capstone `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual`, DISCHARGING
  the single C4c off-diagonal primitive `hEboundW`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DOES.

  `trueKernel_diagonal_a1_eq_R6_residual` (the stronger reduced capstone, with `hCorrHigher` and `hE`
  already discharged) still carries SEVEN hypotheses on the abstract parametrix `H`:
      `hEboundW` · `hInt` · `hDuhamel` · `hInter` · `hDH` · `hDConv` · `hCH` · `hCConv`,
  of which `hEboundW` (the width-2 Gaussian bound on the ACTUAL residual `heatOp g gi H`) is the
  single labeled C4c off-diagonal parametrix wall.

  J4-100's `gatedWitness_hEboundW_unconditional` delivers, FULLY UNCONDITIONALLY (hypotheses only the
  geometric/heat data), a CONCRETE gated witness
      `H := gatedKernel K S (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hC hK))`
  together with a constant `B ≥ 0` for which the EXACT `hEboundW` shape
      `∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ B · baseKernelW 2 0 τ p q`
  holds.  The two shapes coincide verbatim (same witness object, same domain/binder structure, same
  bound form), so this file INSTANTIATES the capstone at that concrete witness and feeds the produced
  bound into the `hEboundW` slot — no adapter needed.

  RESULT (`trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged`): for the concrete gated
  parametrix, the a₁ = R/6 diagonal expansion holds with `hEboundW` GONE.  The remaining OPEN carries
  are exactly the classical Levi/Duhamel convergence–integrability–differentiability census
      `hInt` · `hDuhamel` · `hInter` · `hDH` · `hDConv` · `hCH` · `hCConv` · `hHdiag`
  (stated for the now-CONCRETE witness), reduced from EIGHT to SEVEN.  The C4c wall is discharged.

  ⚠ HONEST SCOPE (binding).  STILL a CONDITIONAL capstone — the seven Levi/Duhamel carries are NOT
  discharged.  This is NOT an unconditional `a₁ = R/6`.  What it IS: the C4c off-diagonal primitive is
  no longer an assumed input.  No axioms beyond the standard three, no `sorry`, no vacuous hypotheses:
  the `∃` witness is CONCRETELY inhabited (via `gatedWitness_hEboundW_unconditional`), and the
  remaining implication antecedents are genuine analytic obligations, not vacuous stubs.
-/
import Mathlib
import QIQTH.TrueKernelA1Reduced
import QIQTH.UniformChartRadius

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ J4-759 — `hEboundW` DISCHARGED into the reduced Seeley–DeWitt capstone.**

    For the CONCRETE gated witness `H = gatedKernel K S (globalCutoffParametrixWitness Θ u a b
    (uniformInverseChart g gi hC hK))` produced UNCONDITIONALLY by
    `gatedWitness_hEboundW_unconditional`, the width-2 C4c primitive `hEboundW` is supplied
    internally, so it no longer appears as a hypothesis.  There EXIST the annulus radii `a < b`, the
    residual constant `B ≥ 0` and the gate `S` (the `gatedWitness` witnesses) such that, PROVIDED the
    remaining Levi/Duhamel census holds for this concrete `H` (`hHdiag`, `hInt`, `hDuhamel`, `hInter`,
    `hDH`, `hDConv`, `hCH`, `hCConv`), the true heat kernel solves the heat equation and its diagonal
    expands as `K(t,0,0) = (4πt)^{−d/2}·(1 + (R/6)·t + t²·remainder)`, `R = ∑ᵢ Ric_{ii}`, the `t¹`
    coefficient the DERIVED van-Vleck `R/6`.

    Reduces the carry count of `trueKernel_diagonal_a1_eq_R6_residual` from EIGHT to SEVEN by removing
    the single C4c off-diagonal wall `hEboundW`.  STILL CONDITIONAL; NOT unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    -- geometric/heat data of `gatedWitness_hEboundW_unconditional`:
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    -- RNC / curvature data of the capstone:
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    ∃ (a b B : ℝ), 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      -- `H` = the concrete gated witness supplied by `gatedWitness_hEboundW_unconditional`:
      (let H := gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK));
        -- remaining Levi/Duhamel census (the seven surviving carries), for this concrete `H`:
        H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n) →
        IterConvIntegrableW (heatOp g gi H) 2 0 B →
        heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
            = leviSeries (heatOp g gi H) t 0 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
        heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi H)
                (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 →
        DifferentiableAt ℝ (fun w => H w 0 0) t →
        DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
        ContDiff ℝ ⊤ (fun p => H t p 0) →
        ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) →
        heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
        ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  obtain ⟨a, b, B, ha, hab, hB, S, hbound⟩ :=
    gatedWitness_hEboundW_unconditional g gi hg hChr hK hgnd hgsymm hinvF hframeK Θ u
      hw0smooth hw0flat
  refine ⟨a, b, B, ha, hab, hB, S, ?_⟩
  intro H hHdiag hInt hDuhamel hInter hDH hDConv hCH hCConv
  exact trueKernel_diagonal_a1_eq_R6_residual g gi Ric N hN t ht H B hB
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hbound hInt hDuhamel hInter hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
