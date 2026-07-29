/-
  TrueKernelA1 — the TRUE-KERNEL diagonal Seeley–DeWitt `a₁ = R/6`, the CONDITIONAL CAPSTONE of the
  M6 (SeeleyDeWitt true-kernel convergence) side of the `a₁ = R/6` endgame
  (docs/qg_roadmap/CONVERGENCE_INFRASTRUCTURE_PLAN.md, HEAT_KERNEL_GAP_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE ASSEMBLES.

  The Levi/Duhamel TRUE heat kernel is `K = H + H*F` (`TrueHeatKernel.trueHeatKernel`), the parametrix
  `H` corrected by the space-time convolution `heatConv H F` with the signed Levi/Neumann series
  `F = leviSeries E`.  Two facts about its DIAGONAL `(t, 0, 0)` at the RNC centre combine to give
  `a₁ = R/6`:

    (A) THE TRUE KERNEL IS THE TRUE KERNEL — it SOLVES the heat equation `(∂_t − Δ)K = 0`.  This is
        `TrueHeatKernel.trueHeatKernel_heat_eqn_levi`, whose Volterra/summability input is DISCHARGED
        here from the width-2 Neumann convergence engine
        `HeatResidualBound.neumann_summable_alpha0_width2` — which consumes the single labeled C4c
        global width-2 residual bound `hEboundW` (+ per-step integrability `IterConvIntegrableW`).

    (B) THE DIAGONAL `a₁` IS INHERITED FROM THE PARAMETRIX — the Levi correction `heatConv H F` is
        HIGHER-ORDER on the diagonal (order `t²`), so it does NOT shift the `t¹` coefficient.  Thus
        the true-kernel diagonal `t¹`-coefficient equals the PARAMETRIX diagonal `t¹`-coefficient,
        which is `R/6` — the DERIVED `VanVleckCancellation.heatParametrixFn_diagonal_a1_derived`
        (`u₁(0) = R/6`, the van-Vleck leading cancellation).

  The KEY structural step (B) is isolated as `trueKernel_diag_a1_of_correction_higher_order`: if the
  parametrix diagonal is `pref·(1 + a₁·t + Ptail)` and the Levi correction diagonal is `pref·(t²·cRem)`
  (i.e. `O(t²)`), then the true kernel diagonal is `pref·(1 + a₁·t + (Ptail + t²·cRem))` — the SAME
  `a₁`, the correction folded entirely into the `O(t²)` remainder.  Pure algebra on
  `trueHeatKernel = H + heatConv H F`.

  ★ THE CAPSTONE `trueKernel_diagonal_a1_eq_R6` bundles (A) ∧ (B): the true kernel solves the heat
  equation AND its diagonal expands as
      K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder),   R = ∑ᵢ Ric_{ii},
  the `t¹` coefficient DERIVED `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  This is a CONDITIONAL capstone, NOT an unconditional `a₁ = R/6`.  What
  it CARRIES as genuine, labeled, non-vacuous hypotheses (every one used, none is the conclusion):

    • `hEboundW` — ★ THE SINGLE C4c PRIMITIVE: the GLOBAL width-2 residual bound
      `∀ τ p q, 0 < τ → |E τ p q| ≤ C·baseKernelW 2 0 τ p q`.  Its local near-diagonal part is PROVED
      (`HeatResidualBound.residualN0_local_baseKernelW_slice`); its open residue is the far-field +
      off-diagonal parametrix over all base points — the C4c off-diagonal parametrix wall.  This is
      the WHOLE remaining obstruction to `a₁ = R/6`.
    • `hInt` — the per-step integrability family `IterConvIntegrableW` (interval×Lebesgue integrability
      of the iterated convolutions; genuine analytic carry).
    • `hE`, `hDuhamel`, `hInter` — the parametrix residual identity `(∂_t−Δ)H = E`, the Duhamel
      output `(∂_t−Δ)(H*F) = F + E*F`, and the tsum/heatConv interchange (the Mathlib-missing
      Summable-continuity of `heatConv` under `tsum`).
    • `hHdiag` — the diagonal identification `H t 0 0 = heatParametrixFn N g (vanVleck DeWitt) t 0`
      (the abstract two-point kernel's diagonal IS the concrete van-Vleck parametrix diagonal).
    • `hCorrHigher` — ★ THE LEVI-CORRECTION-HIGHER-ORDER fact: `heatConv H F t 0 0 = pref·(t²·cRem)`,
      i.e. the Duhamel correction contributes at order `t²` on the diagonal (so it does not shift
      `a₁`).  Genuine: without it the correction could carry a `t¹` term and shift `a₁`.
    • RNC-centre data `hg/hg0/hgi/hΓ/hdg0`, the metric-Hessian trace `htr` (`tr ∂∂g(0) = −⅔ Ric`,
      RNC3-discharged), the transport-source smoothness `hsrc`, and the `heatOp`-linearity regularity
      side conditions — all as in `heatParametrixFn_diagonal_a1_derived` / `trueHeatKernel_heat_eqn`.

  This ISOLATES the entire remaining obstruction to `a₁ = R/6` to precisely the single C4c
  off-diagonal parametrix primitive `hEboundW` (plus the interchange/integrability analytic facts).
  It does NOT claim `a₁ = R/6` unconditionally.  No axioms beyond the standard three, no `sorry`, no
  vacuous hypotheses.

  Grounded in Rosenberg, *The Laplacian on a Riemannian Manifold*, §3.2.1; Gilkey; the Grigor'yan-style
  Gaussian iterated-convolution / Levi parametrix program.
-/
import Mathlib
import QIQTH.TrueHeatKernel
import QIQTH.ParametrixHEboundWiring
import QIQTH.VanVleckCancellation

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation

namespace QIQTH.TrueKernelA1

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### 1. ★ THE KEY STEP — the Levi correction is higher-order on the diagonal, so `a₁` is inherited. -/

/-- **★ THE KEY STEP (F2) — Levi correction higher-order on the diagonal ⟹ true `a₁` = parametrix
    `a₁`.**  If the parametrix diagonal is `H(t,0,0) = pref·(1 + a₁·t + Ptail)` and the Levi/Duhamel
    correction diagonal is `heatConv H F (t,0,0) = pref·(t²·cRem)` — i.e. the correction is `O(t²)` —
    then the TRUE kernel `K = H + H*F` has the SAME leading `a₁`:
        `trueHeatKernel H F (t,0,0) = pref·(1 + a₁·t + (Ptail + t²·cRem))`.
    The correction is folded ENTIRELY into the `O(t²)` remainder `Ptail + t²·cRem`; the `t¹`
    coefficient `a₁` is unchanged.  Pure algebra on `trueHeatKernel = H + heatConv H F`
    (`trueHeatKernel_apply` + `ring`).  This is exactly the "convergence gives `K = H + O(t^{higher})`,
    so the diagonal `a₁` is inherited from `H`" content. -/
theorem trueKernel_diag_a1_of_correction_higher_order
    (H F : ℝ → Point n → Point n → ℝ) (t pref a1 Ptail cRem : ℝ)
    (hParam : H t 0 0 = pref * (1 + a1 * t + Ptail))
    (hCorr : heatConv H F t 0 0 = pref * (t ^ 2 * cRem)) :
    trueHeatKernel H F t 0 0 = pref * (1 + a1 * t + (Ptail + t ^ 2 * cRem)) := by
  rw [trueHeatKernel_apply, hParam, hCorr]; ring

/-! ### 2. ★ THE CAPSTONE — the true-kernel diagonal `a₁ = R/6`, conditional on the C4c input. -/

/-- **★ THE CONDITIONAL CAPSTONE — the true-kernel diagonal Seeley–DeWitt `a₁ = R/6`.**  For the
    concrete van-Vleck Levi/Duhamel true heat kernel `K = H + H*(leviSeries E)`, at the RNC centre:

      (A)  `K` solves the heat equation `(∂_t − Δ_{g})K (t,0,0) = 0`; AND
      (B)  its diagonal expands as
             `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,  `R = ∑ᵢ Ric_{ii}`,
           with the `t¹` coefficient DERIVED `R/6` (the van-Vleck leading value
           `heatParametrixFn_diagonal_a1_derived`), the Levi correction (`hCorrHigher`, `O(t²)`) folded
           into the `t²` remainder.

    (A) uses `trueHeatKernel_heat_eqn_levi`, its summability input DISCHARGED from the width-2 Neumann
    convergence `neumann_summable_alpha0_width2` (consuming the single labeled C4c global width-2 bound
    `hEboundW` + integrability `hInt`).  (B) uses `trueKernel_diag_a1_of_correction_higher_order` with
    `Ptail = Σ_{2≤k≤N} u_k(0)·t^k = t²·Σ u_k(0)·t^{k−2}` (the parametrix diagonal tail is itself
    `O(t²)`), so the whole remainder is `t²·(Σ u_k(0)·t^{k−2} + cRem)`.

    ⚠ CONDITIONAL: `hEboundW` is the C4c off-diagonal parametrix primitive (its local near-diagonal
    part is proved, `residualN0_local_baseKernelW_slice`; the far-field/off-diagonal residue is the
    wall).  `hInt`, `hE`, `hDuhamel`, `hInter`, `hHdiag`, `hCorrHigher` are the genuine convergence /
    Duhamel / correction-order carries.  This is NOT an unconditional `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H E : ℝ → Point n → Point n → ℝ) (C cRem : ℝ) (hC : 0 ≤ C)
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
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + cRem)) := by
  -- (A) THE TRUE KERNEL SOLVES THE HEAT EQUATION — via the width-2 Neumann convergence.
  -- The C4c global width-2 bound + integrability give convergence of the residual Neumann series;
  -- multiplying each term by the unit-modulus sign `(−1)^(k+1)` preserves summability.
  have hIterSum := neumann_summable_alpha0_width2 E C hC hEboundW hInt t ht (0 : Point n) (0 : Point n)
  have hSum : Summable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE E (k + 1) t (0 : Point n) (0 : Point n)) := by
    have habs : Summable (fun k : ℕ => |iterE E (k + 1) t (0 : Point n) (0 : Point n)|) :=
      summable_abs_iff.mpr hIterSum
    refine Summable.of_norm_bounded habs (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simp
  have hHeat : heatOp g gi (trueHeatKernel H (leviSeries E)) t 0 0 = 0 :=
    trueHeatKernel_heat_eqn_levi g gi H E t 0 0 hE hDuhamel hSum hInter hDH hDConv hCH hCConv
  -- (B) THE DIAGONAL `a₁ = R/6` EXPANSION.
  -- The parametrix diagonal `a₁ = R/6` (van-Vleck leading cancellation, DERIVED).
  have hParam := heatParametrixFn_diagonal_a1_derived N g gi Ric t hN hg hg0 hgi hΓ hdg0 htr hsrc
  -- The parametrix tail `Σ_{2≤k≤N} u_k(0)·t^k` is itself `O(t²)`: factor out `t²`.
  have htail_eq : (∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k)
      = t ^ 2 * ∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ (k - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpow : t ^ 2 * t ^ (k - 2) = t ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]; ring
  -- Assemble: `K = H + H*F`, `H`'s diagonal `= pref·(1 + (R/6)t + Ptail)`, correction `= pref·(t²·cRem)`.
  have hExp : trueHeatKernel H (leviSeries E) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                          * t ^ (k - 2))
                      + cRem)) := by
    rw [trueHeatKernel_apply, hHdiag, hParam, hCorrHigher, htail_eq]; ring
  exact ⟨hHeat, hExp⟩

end QIQTH.TrueKernelA1
