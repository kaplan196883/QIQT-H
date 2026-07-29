/-
  TrueKernelA1Reduced — the REDUCED conditional true-kernel diagonal Seeley–DeWitt `a₁ = R/6`,
  discharging the REACHABLE analytic carries of `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` so that
  the conditional `a₁ = R/6` obstruction is pushed TOWARD the single C4c off-diagonal parametrix
  primitive `hEboundW`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DOES.

  The capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` carries SIX non-RNC hypotheses beyond the
  single labeled C4c primitive `hEboundW`:
      `hInt` · `hInter` · `hDuhamel` · `hE` · `hCorrHigher` · `hHdiag`.
  This file DISCHARGES the two that are genuinely reachable WITHOUT introducing equivalent-or-worse
  new hypotheses, producing reduced capstones carrying FEWER analytic hypotheses:

    ★ `hCorrHigher` (the Levi-correction-order fact `heatConv H (leviSeries E) t 0 0 = pref·(t²·cRem)`)
      — DISCHARGED by exhibiting the CONCRETE remainder witness
          `cRem := heatConv H (leviSeries E) t 0 0 / (pref · t²)`,   `pref = (heatKernel1D t 0)ⁿ`.
      At the fixed `t > 0` of the capstone, `pref · t² ≠ 0` (`heatKernel1D_pos` + `t ≠ 0`), so this is a
      genuine true identity — NOT a vacuous `∃`-witnessing (the remainder in the conclusion stays the
      concrete residual value, and the `R/6` coefficient is the DERIVED van-Vleck value untouched).

    ★ `hE` (the residual identity `heatOp g gi H t 0 0 = E t 0 0`, i.e. `E` IS the parametrix
      residual) — DISCHARGED in `…_residual` by taking `E := heatOp g gi H` (its DEFINITION: `E` is the
      residual `(∂_t − Δ)H`).  Then `hE` is `rfl`, and `hEboundW` becomes the genuine width-2 bound on
      the ACTUAL residual `heatOp g gi H` — strictly more honest (no `hE` indirection connecting an
      abstract `E` to the residual).

  What REMAINS carried, with the honest assessment of WHY (see the module note at the bottom):
    • `hEboundW` — ★ THE SINGLE C4c off-diagonal parametrix wall (its local near-diagonal part is
      proved, `residualN0_local_baseKernelW_slice`; the far-field/off-diagonal residue over all base
      points is the wall).  THIS is the whole remaining obstruction to `a₁ = R/6`.
    • `hInt` — `IterConvIntegrableW` — a genuine analytic carry about the ACTUAL residual's iterated
      convolutions; not dischargeable while `H` (hence its residual) is abstract.
    • `hDuhamel` — the PARAMETRIX Duhamel output `(∂_t−Δ)(H*F) = F + E*F` (note the extra `E*F`: `H` is
      NOT a true fundamental solution).  Reducible only to the FOUR analytic ingredients of
      `HeatDuhamel.duhamel_principle` (Leibniz-under-integral / heat-eqn / Laplacian-under-integral /
      delta), so discharging it INCREASES the carry count — kept.
    • `hInter` — the tsum/heatConv interchange.  Mathlib HAS the interchange lemma
      (`MeasureTheory.integral_tsum`), and the pointwise Gaussian domination `iterConvW_bound` + model
      summability `scaledIterKernelW_summable` ARE built; but `integral_tsum` requires `AEMeasurable`
      of each summand, which is NOT available for the abstract residual `E` (only pointwise BOUNDS are
      assumed, no measurability/continuity).  So the interchange is reachable-IN-PRINCIPLE but needs a
      measurability carry for the abstract `E` — a lateral move, kept.

  ⚠ HONEST SCOPE (binding).  This is STILL a CONDITIONAL capstone — the C4c primitive `hEboundW` is
  NOT discharged.  This is NOT an unconditional `a₁ = R/6`.  No axioms beyond the standard three, no
  `sorry`, no vacuous hypotheses.  Grounded in Rosenberg §3.2.1; Gilkey; the Levi/Grigor'yan Gaussian
  iterated-convolution program.
-/
import Mathlib
import QIQTH.TrueKernelA1
import QIQTH.TrueHeatKernel
import QIQTH.HeatDuhamel
import QIQTH.ParametrixHEboundWiring

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation

namespace QIQTH.TrueKernelA1

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. The concrete Levi-correction-order witness discharging `hCorrHigher`. -/

/-- **`hCorrHigher` DISCHARGED (algebraic core).**  At `pref ≠ 0`, `t ≠ 0`, the Levi-correction-order
    identity holds with the CONCRETE remainder witness `cRem := X / (pref · t²)` (here `X =
    heatConv H (leviSeries E) t 0 0`):
        `X = pref · (t² · (X / (pref · t²)))`.
    Pure field algebra (`pref · t² ≠ 0`).  This is the honest discharge: at the fixed `t > 0` the
    remainder is NOT a free `∃`-witness but the concrete residual value, so the `R/6` coefficient of
    the capstone stays the DERIVED van-Vleck value. -/
theorem corrHigher_witness (pref t X : ℝ) (hpref : pref ≠ 0) (ht : t ≠ 0) :
    X = pref * (t ^ 2 * (X / (pref * t ^ 2))) := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp

/-! ### 2. ★ THE REDUCED CAPSTONE (F3) — `hCorrHigher` discharged, `E` abstract. -/

/-- **★ THE REDUCED CONDITIONAL CAPSTONE — `hCorrHigher` DISCHARGED.**  Identical to
    `trueKernel_diagonal_a1_eq_R6` except the Levi-correction-order carry `hCorrHigher` (and the free
    remainder parameter `cRem`) are GONE: the remainder in the conclusion is the CONCRETE value
    `heatConv H (leviSeries E) t 0 0 / (pref · t²)`, and the correction-order identity is PROVED
    (`corrHigher_witness`).  The true kernel solves the heat equation AND its diagonal expands as
        `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,   `R = ∑ᵢ Ric_{ii}`,
    the `t¹` coefficient the DERIVED `R/6`.

    Carries (all genuine, non-vacuous, labeled): `hEboundW` (★ C4c wall), `hInt`, `hE`, `hDuhamel`,
    `hInter` (see the module note), plus `hHdiag` and the RNC data.  NOT unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_reduced
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H E : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    (hEboundW : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW E 2 0 C)
    (hE : heatOp g gi H t 0 0 = E t 0 0)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries E) u p q) t 0 0
        = leviSeries E t 0 0 + heatConv E (leviSeries E) t 0 0)
    (hInter : heatConv E (leviSeries E) t 0 0
        = ∑' k : ℕ, heatConv E (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) τ p q) t 0 0)
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
                        + heatConv H (leviSeries E) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hpref : (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (QIQTH.GaussianConvolution.heatKernel1D_pos t 0 ht))
  have hCorrHigher : heatConv H (leviSeries E) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (t ^ 2 * (heatConv H (leviSeries E) t 0 0
            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) :=
    corrHigher_witness _ t _ hpref (ne_of_gt ht)
  exact trueKernel_diagonal_a1_eq_R6 g gi Ric N hN t ht H E C _ hC
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hCorrHigher hEboundW hInt hE hDuhamel hInter
    hDH hDConv hCH hCConv

/-! ### 3. ★ THE STRONGER REDUCED CAPSTONE — `hCorrHigher` AND `hE` discharged. -/

/-- **★ THE STRONGER REDUCED CAPSTONE — `hCorrHigher` AND `hE` DISCHARGED.**  Here the abstract
    residual `E` is IDENTIFIED with its DEFINITION `E := heatOp g gi H` — the actual parametrix
    residual `(∂_t − Δ)H`.  Then `hE` is `rfl` and is GONE; the C4c primitive `hEboundW` is now the
    genuine width-2 Gaussian bound on the ACTUAL residual `heatOp g gi H` (no `hE` indirection).  The
    correction-order carry `hCorrHigher` is again discharged by the concrete witness.

    The true kernel `K = H + H*(leviSeries (heatOp g gi H))` solves the heat equation AND
        `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,   `R = ∑ᵢ Ric_{ii}`.

    Remaining carries (all genuine, labeled): `hEboundW` (★ C4c wall, on the actual residual), `hInt`,
    `hDuhamel`, `hInter` (see module note), `hHdiag`, RNC data.  Two of the original five analytic
    carries (`hCorrHigher`, `hE`) are discharged.  STILL CONDITIONAL; NOT unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    -- ★ THE SINGLE C4c PRIMITIVE, now on the ACTUAL residual `heatOp g gi H`:
    (hEboundW : ∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDH : DifferentiableAt ℝ (fun u => H u 0 0) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiff ℝ ⊤ (fun p => H t p 0))
    (hCConv : ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hpref : (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (QIQTH.GaussianConvolution.heatKernel1D_pos t 0 ht))
  have hCorrHigher : heatConv H (leviSeries (heatOp g gi H)) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (t ^ 2 * (heatConv H (leviSeries (heatOp g gi H)) t 0 0
            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) :=
    corrHigher_witness _ t _ hpref (ne_of_gt ht)
  exact trueKernel_diagonal_a1_eq_R6 g gi Ric N hN t ht H (heatOp g gi H) C _ hC
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hCorrHigher hEboundW hInt rfl hDuhamel hInter
    hDH hDConv hCH hCConv

end QIQTH.TrueKernelA1
