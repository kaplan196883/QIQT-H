/-
  GatedGlobalWitnessN1Capstone — J4-767: the ORDER-`N = 1` partial Seeley–DeWitt capstone.  The FIRST
  wiring of the abstract residual capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual` to the
  ORDER-1 gated cutoff-parametrix witness
      `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
                               (transportCoeff (transportOp (vanVleck g) g gi)) a b
                               (uniformInverseChart g gi hChr hK))`,
  discharging INTERNALLY the four diagonal / low-order carries that the order-0 chain could NOT close
  — crucially `hHdiag`, which was GENUINELY FALSE at order 0 (J4-761) and is the single obstruction
  that made the whole order-0 chain a dead end (J4-764).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** an unconditional `a₁ = R/6`.  It is a CONDITIONAL capstone:
  it still CARRIES the width-2 residual bound `hEboundW` at order 1 (the ≈150-site re-plumb the
  `CapstoneWiring` census scopes — NOT proven here), the base measurability `hEmeas`, and the genuine
  analytic walls `hDuhamel`/`hDConv`/`hCConv`/`hCH`.  No `sorry`, no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypotheses, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS CLOSES vs. THE ORDER-0 CHAIN.

  The order-0 chain (`GatedGlobalWitnessLeviIntInter.trueKernel_diagonal_a1_eq_R6_residual_hInt_hInter_hDH_discharged`)
  discharged `hInt`, `hInter`, `hDH` for the order-0 witness — but its `hHdiag` carry was
  STRUCTURALLY UNPROVABLE (`heatParametrixFn N` at `N ≥ 1` needs `u₁(0) = R/6 ≠ 0`, absent from the
  order-0 `gauss·u₀`-only witness, J4-761), so the whole chain fed a target it could never satisfy
  (J4-764: "order-0 capstone is a DEAD END regardless").

  Here, at the MINIMAL order-1 witness, all FOUR of those low-order carries are discharged internally:
    • `hHdiag`  ← `gatedGlobalWitnessN1_diag_hHdiag`   (★ now GENUINELY TRUE — the dead-end obstruction, removed);
    • `hDH`     ← `gatedGlobalWitnessN1_diag_hDH`;
    • `hInt`    ← `iterConvIntegrableW_of_bound_baseMeas` (from carried `hEboundW` + order-1 `hEzero` + carried `hEmeas`);
    • `hInter`  ← `heatConv_leviSeries_interchange`       (from the SAME `{hEboundW, hEzero, hEmeas}` family),
  with `hEzero` (order-1 nonpositive-time vanishing) supplied by `gatedGlobalWitnessN1_residual_hEzero`
  (needs `1 ≤ n`).

  RESULT.
    • `trueKernel_diagonal_a1_eq_R6_residual_N1_discharged` — the residual Seeley–DeWitt capstone at the
      ORDER-1 gated van-Vleck witness `H₁`, with `hHdiag`, `hDH`, `hInt`, `hInter` (+ `hEzero`) all
      supplied internally.  The surviving CARRIES are exactly `{hEboundW, hEmeas, hDuhamel, hDConv,
      hCH, hCConv}` + the RNC/gauge geometry + the gate memberships `0 ∈ K`, `0 ∈ S 0`.  Its
      conclusion is the true-kernel diagonal Seeley–DeWitt expansion
          `K(t,0,0) = (4πt)^{−d/2} · (1 + (R/6)·t + t²·remainder)`,  `R = ∑ᵢ Ric_{ii}`,
      with the `N = 1` remainder sum `∑_{k ∈ Ico 2 2}` EMPTY (so the `t²`-bracket is purely the
      convolution correction).

  ⚠ HONEST SCOPE (binding).  STILL CONDITIONAL; NOT `a₁ = R/6`.  The carried `hEboundW` at order 1 is
  the genuinely-large residual re-plumb (`CapstoneWiring` census, ≈150 sites); `hDuhamel`/`hDConv` rest
  on the still-open `hDaLimLU` loc-unif limit; `hCConv` on the `hD1` CLM lift; `hCH` on the hard
  set-gate spatial-continuity wall (order-independent).  What IS achieved relative to the order-0
  chain: the `hHdiag` obstruction — the reason the order-0 capstone was a DEAD END — is GONE at `N = 1`,
  and the same `hInt`/`hInter`/`hDH` discharge technique ports cleanly to order 1.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1Diag
import QIQTH.TrueKernelA1Reduced
import QIQTH.IterEMeasurable
import QIQTH.LeviInterchange
import QIQTH.CapstoneWiring

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.TransitionAnnulusCont
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ J4-767 — the ORDER-1 partial Seeley–DeWitt capstone (`hHdiag`/`hDH`/`hInt`/`hInter` discharged).**

    The residual capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual` instantiated at the
    ORDER-1 gated van-Vleck cutoff-parametrix witness
        `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
                 (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`.

    Four low-order carries are supplied INTERNALLY: `hHdiag` (★ now genuinely TRUE — the order-0
    dead-end obstruction), `hDH`, `hInt`, `hInter` (the last two from the carried width-2 bound
    `hEboundW` + the order-1 residual vanishing `gatedGlobalWitnessN1_residual_hEzero`, `1 ≤ n`, + the
    carried base measurability `hEmeas`).

    The remaining antecedents (`hEboundW`, `hEmeas`, `hDuhamel`, `hDConv`, `hCH`, `hCConv`) stay
    carried — each a genuine, satisfiable analytic fact about `H₁`, none the conclusion, none vacuous.
    STILL CONDITIONAL; NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (a b B : ℝ) (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (S : Point n → Set (Point n)) (hS0 : (0 : Point n) ∈ S 0) :
    (let H := gatedKernel K S
        (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK));
      (∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) →
      StronglyMeasurable (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) →
      heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
          = leviSeries (heatOp g gi H) t 0 0
            + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
      DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
      ContDiff ℝ ⊤ (fun p => H t p 0) →
      ContDiff ℝ ⊤ (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) →
      heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
      ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
          = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
            * (1 + ((∑ i, Ric i i) / 6) * t
                + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                            transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                              * t ^ (k - 2))
                          + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                              / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  intro H hEboundW hEmeas hDuhamel hDConv hCH hCConv
  -- the order-1 residual nonpositive-time vanishing (needs `1 ≤ n`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)
  -- `hInt` from the carried residual bound + vanishing + base measurability.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 B :=
    iterConvIntegrableW_of_bound_baseMeas (heatOp g gi H) B hEboundW hEzero hEmeas
  -- `hInter` (tsum/heatConv interchange) from the SAME family.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    heatConv_leviSeries_interchange (heatOp g gi H) B hB hEboundW hEzero hEmeas t ht 0 0
  -- ★ `hHdiag` at `N = 1` — GENUINELY TRUE (the order-0 dead-end obstruction, now discharged).
  have hHdiag : H t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    gatedGlobalWitnessN1_diag_hHdiag g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t
      hK0 hS0 (uniformInverseChart_zero g gi hChr hK hK0)
  -- `hDH` diagonal time-differentiability at the order-1 witness.
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitnessN1_diag_hDH g gi hChr hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b S t ht
  exact trueKernel_diagonal_a1_eq_R6_residual g gi Ric 1 (le_refl 1) t ht H B hB
    hg hg0 hgi hΓ hdg0 htr hsrc hHdiag hEboundW hInt hDuhamel hInter hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
