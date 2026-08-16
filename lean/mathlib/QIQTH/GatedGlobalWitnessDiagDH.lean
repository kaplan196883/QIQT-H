/-
  GatedGlobalWitnessDiagDH — J4-761: discharge the diagonal `t`-DIFFERENTIABILITY carry `hDH` for the
  CONCRETE J4-100 gated cutoff-parametrix witness, and wire it into the `hEboundW`-discharged reduced
  Seeley–DeWitt capstone, shrinking its surviving Levi/Duhamel census from SEVEN to SIX.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS FILE DOES.

  `TrueKernelA1EboundWired.trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged` carries SEVEN
  surviving hypotheses on the CONCRETE gated witness
      `H := gatedKernel K S (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK))`,
  namely `hHdiag · hInt · hDuhamel · hInter · hDH · hDConv · hCH · hCConv`.  Of these, `hDH`
      `DifferentiableAt ℝ (fun τ => H τ 0 0) t`
  is a comparatively ORDINARY analytic fact — the time-differentiability of the kernel at the SINGLE
  diagonal point `(0,0)` — and is now dischargeable OUTRIGHT for this concrete witness, because:

    • the set-gate `S` is `τ`-INDEPENDENT (a HARD gate), so `fun τ => H τ 0 0` is EITHER `fun τ => 0`
      (when `(0,0)` is out of the gate — trivially differentiable) OR `fun τ => W τ 0 0` (when in-gate);
    • IN the gate we have `0 ∈ K`, hence `uniformInverseChart g gi hChr hK 0 0 = 0`
      (`uniformInverseChart_zero`), so the witness collapses to
          `W τ 0 0 = radialCutoff a b 0 · heatParametrix 0 Θ u τ 0`,
      a fixed constant times the order-0 parametrix, whose `τ`-differentiability at `t > 0` is the
      banked `heatParametrix_differentiableAt_t` (the Gaussian `gaussDdim · 0` is `C^∞` for `t > 0`).

  This is NOT part of the genuinely-hard Levi/Duhamel convergence core (Neumann-series summability /
  integrability / diagonal identification): it is a one-point regularity fact about the now-concrete,
  inhabited witness, dischargeable from facts ALREADY banked about the same witness's components.

  RESULT.
    • `gatedGlobalWitness_diag_hDH` — `hDH` proved for the concrete order-0 gated cutoff-parametrix
      witness, gate-generically (any `K`, `S`, `Θ`, `u`, `a`, `b`), at any `t > 0`.
    • `trueKernel_diagonal_a1_eq_R6_residual_hDH_discharged` — the `hEboundW`-discharged capstone with
      `hDH` ALSO removed: its surviving carries drop to SIX
          `hHdiag · hInt · hDuhamel · hInter · hDConv · hCH · hCConv`.

  ⚠ HONEST SCOPE (binding).  STILL a CONDITIONAL capstone — the SIX remaining carries (the Levi/Duhamel
  convergence-trio: `hInt`, `hDuhamel`, `hInter`, `hDConv`, `hCConv`, plus the order-N diagonal
  identification `hHdiag`) are NOT discharged, and `hHdiag` in particular CANNOT hold for this ORDER-0
  witness (it needs the `N ≥ 1` re-plumb — see `CapstoneWiring`'s census).  This is NOT an
  unconditional `a₁ = R/6`.  What it IS: the one-point diagonal time-regularity antecedent is no longer
  an assumed input.  No axioms beyond the standard three, no `sorry`, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.TrueKernelA1EboundWired
import QIQTH.CapstoneWiring
import QIQTH.TransitionAnnulusCont

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.TransitionAnnulusCont

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ J4-761 — `hDH` DISCHARGED for the concrete gated cutoff-parametrix witness.**

    For the CONCRETE gated witness `H = gatedKernel K S (globalCutoffParametrixWitness Θ u a b
    (uniformInverseChart g gi hChr hK))`, the diagonal map `τ ↦ H τ 0 0` is DifferentiableAt every
    `t > 0`.  Gate-generic (any `K`, `S`, `Θ`, `u`, `a`, `b`).

    Proof.  The set-gate is `τ`-independent, so a classical case split on the two gate conditions
    `0 ∈ K` and `0 ∈ S 0` reduces `τ ↦ H τ 0 0` to either the constant `0` (out of gate, differentiable)
    or `τ ↦ W τ 0 0` (in gate).  In the in-gate branch `0 ∈ K` gives `uniformInverseChart … 0 0 = 0`
    (`uniformInverseChart_zero`), so `W τ 0 0 = radialCutoff a b 0 · heatParametrix 0 Θ u τ 0`, a
    constant times the order-0 parametrix whose `τ`-differentiability is `heatParametrix_differentiableAt_t`. -/
theorem gatedGlobalWitness_diag_hDH
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (S : Point n → Set (Point n)) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ
      (fun τ => gatedKernel K S
        (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0) t := by
  by_cases hK0 : (0 : Point n) ∈ K
  · by_cases hS0 : (0 : Point n) ∈ S 0
    · -- in-gate: `H τ 0 0 = W τ 0 0`, and `Vmap 0 0 = 0` collapses `W` to a constant × order-0 parametrix
      have hV0 : uniformInverseChart g gi hChr hK 0 0 = 0 :=
        uniformInverseChart_zero g gi hChr hK hK0
      have hfun : (fun τ => gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
          = fun τ => radialCutoff a b (0 : Point n) * heatParametrix 0 Θ u τ (0 : Point n) := by
        funext τ
        rw [gatedKernel_apply_of_mem K S _ τ hK0 hS0]
        simp only [globalCutoffParametrixWitness, hV0]
      rw [hfun]
      exact (heatParametrix_differentiableAt_t 0 Θ u t ht (0 : Point n)).const_mul _
    · have hfun : (fun τ => gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
          = fun _ => (0 : ℝ) := by
        funext τ
        exact gatedKernel_apply_of_notMem K S _ τ 0 0 (Or.inr hS0)
      rw [hfun]; exact differentiableAt_const 0
  · have hfun : (fun τ => gatedKernel K S
        (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
        = fun _ => (0 : ℝ) := by
      funext τ
      exact gatedKernel_apply_of_notMem K S _ τ 0 0 (Or.inl hK0)
    rw [hfun]; exact differentiableAt_const 0

/-- **★ J4-761 — `hDH` REMOVED from the `hEboundW`-discharged reduced capstone.**

    Identical to `trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged` except the diagonal
    time-differentiability antecedent `hDH` is GONE — it is supplied internally by
    `gatedGlobalWitness_diag_hDH` for the produced `a`, `b`, `S`.  The surviving Levi/Duhamel census
    shrinks from SEVEN to SIX: `hHdiag · hInt · hDuhamel · hInter · hDConv · hCH · hCConv`.

    STILL CONDITIONAL; NOT unconditional `a₁ = R/6`.  (`hHdiag` still cannot hold at this ORDER-0
    witness — the `N ≥ 1` re-plumb remains owed.) -/
theorem trueKernel_diagonal_a1_eq_R6_residual_hDH_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
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
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    ∃ (a b B : ℝ), 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      (let H := gatedKernel K S
          (globalCutoffParametrixWitness Θ u a b (uniformInverseChart g gi hChr hK));
        H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n) →
        IterConvIntegrableW (heatOp g gi H) 2 0 B →
        heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
            = leviSeries (heatOp g gi H) t 0 0
              + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
        heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi H)
                (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 →
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
  obtain ⟨a, b, B, ha, hab, hB, S, hmain⟩ :=
    trueKernel_diagonal_a1_eq_R6_residual_hEboundW_discharged g gi Ric N hN t ht
      hg hChr hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
      hg0 hgi hΓ hdg0 htr hsrc
  refine ⟨a, b, B, ha, hab, hB, S, ?_⟩
  intro H hHdiag hInt hDuhamel hInter hDConv hCH hCConv
  exact hmain hHdiag hInt hDuhamel hInter
    (gatedGlobalWitness_diag_hDH g gi hChr hK Θ u a b S t ht) hDConv hCH hCConv

end QIQTH.HeatResidualBound
