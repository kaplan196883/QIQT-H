/-
  GatedGlobalWitnessN1Diag — J4-766: the ORDER-`N = 1` witness re-plumb, DIAGONAL layer.  Provides,
  for the ORDER-1 gated cutoff-parametrix witness
      `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)`,
  the three diagonal / low-order facts that were STRUCTURALLY FALSE at the order-0 witness
  `globalCutoffParametrixWitness = globalCutoffParametrixWitnessN 0` (J4-761), the load-bearing one
  being the capstone's `hHdiag` identification.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It proves NOTHING new about `R/6`.  It is the
  first (diagonal) tranche of the ORDER-1 witness re-plumb.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypotheses, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS IS THE LOAD-BEARING FIX.

  The live Seeley–DeWitt capstone `TrueKernelA1Reduced.trueKernel_diagonal_a1_eq_R6_residual` (abstract
  in `H`) demands, for `1 ≤ N`,
      `hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t 0`.
  The whole J4-761→765 order-0 sub-campaign was built on the witness
  `globalCutoffParametrixWitness = globalCutoffParametrixWitnessN 0`, whose diagonal value is
  `heatParametrix 0` (`gauss·u₀` only).  Because `heatParametrixFn N` at `N ≥ 1` carries the
  `u₁(0) = R/6 ≠ 0` term (the exact content being proven), the order-0 witness CANNOT satisfy `hHdiag`
  — it is GENUINELY FALSE there, not merely hard (J4-761 negative result).  So the entire order-0
  capstone chain (`GatedGlobalWitnessDiagDH` / `GatedGlobalWitnessLeviIntInter`) is a dead end (J4-764).

  The fix, per `CapstoneWiring`'s census, is to re-instantiate the witness at the MINIMAL order-1
  parametrix `globalCutoffParametrixWitnessN 1` (whose diagonal value IS `heatParametrix 1`,
  `gauss·(u₀ + u₁·t)`), at which point `hHdiag` becomes a genuine, non-vacuously TRUE theorem.  This
  file delivers exactly that identification, plus the two other order-dependent diagonal facts the
  chain consumes (`hDH` time-differentiability, `hEzero` nonpositive-time vanishing), now ported to
  `N = 1`.

  RESULTS.
    • `gatedGlobalWitnessN1_diag_eval` — the order-1 gated witness on the diagonal at the origin
      collapses to the raw order-1 parametrix `heatParametrix 1 Θ u t 0` (gate-generic; `N = 1` sibling
      of `CapstoneWiring.gatedWitness_diag_eval`).
    • `gatedGlobalWitnessN1_diag_hHdiag` — the concrete van-Vleck order-1 diagonal identification
          `gatedKernel … t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0`.
      ★ THIS IS THE CAPSTONE'S `hHdiag` (at `N = 1`), now GENUINELY TRUE — resolving the J4-761
      structural-falseness that blocked the whole capstone.  `N = 1` sibling of
      `CapstoneWiring.gatedWitness_diag_eval_vanVleck`.
    • `gatedGlobalWitnessN1_diag_hDH` — the diagonal `τ`-differentiability of `τ ↦ H₁ τ 0 0` at `t > 0`
      (`N = 1` sibling of `GatedGlobalWitnessDiagDH.gatedGlobalWitness_diag_hDH`).
    • `gatedGlobalWitnessN1_residual_hEzero` — the residual heat operator of `H₁` vanishes at `τ ≤ 0`
      (needs `1 ≤ n`; `N = 1` sibling of `GatedGlobalWitnessLeviIntInter.gatedGlobalWitness_residual_hEzero`).

  ⚠ HONEST SCOPE (binding).  This is the DIAGONAL tranche only.  The FULL order-1 capstone additionally
  needs `hEboundW` re-proven at order 1 (the ≈150-site residual-bound re-plumb the `CapstoneWiring`
  census scopes — genuinely large, NOT attempted here), plus the still-open analytic walls
  `hDuhamel`/`hDConv` (the `hDaLimLU` loc-unif limit), `hCConv` (the `hD1` CLM lift) and `hCH` (the
  hard set-gate spatial-continuity wall, order-INDEPENDENT).  STILL CONDITIONAL; NOT `a₁ = R/6`.  What
  IS achieved: the capstone's `hHdiag` is no longer structurally false — the single obstruction that
  made the order-0 chain a dead end is removed at `N = 1`.
-/
import Mathlib
import QIQTH.CapstoneWiring
import QIQTH.TransitionAnnulusCont
import QIQTH.OrderNResidual
import QIQTH.ModelIntegrableW
import QIQTH.GlobalHunifAssembly

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

/-! ### 1. The order-1 gated witness on the diagonal — the `hHdiag` template. -/

/-- **`gatedGlobalWitnessN1_diag_eval` — the ORDER-1 gated cutoff-parametrix witness on the diagonal.**
    Where the origin lies in the base gate (`0 ∈ K`), in the spatial gate (`0 ∈ S 0`), and the inverse
    chart fixes the origin (`Vmap 0 0 = 0`), the order-1 gated global cutoff-parametrix witness
    collapses to the raw ORDER-1 parametrix at the centre:
        `gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) t 0 0 = heatParametrix 1 Θ u t 0`.
    `N = 1` sibling of `CapstoneWiring.gatedWitness_diag_eval` — the ONLY change is `heatParametrix 1`
    in place of `heatParametrix 0` after the witness swap.  NOT `a₁ = R/6`. -/
theorem gatedGlobalWitnessN1_diag_eval (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) t 0 0
      = heatParametrix 1 Θ u t 0 := by
  rw [gatedKernel_apply_of_mem K S _ t hK0 hS0]
  simp only [globalCutoffParametrixWitnessN, hV]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity), one_mul]

/-- **★ J4-766 — `hHdiag` at `N = 1`, GENUINELY TRUE.**  The concrete van-Vleck ORDER-1 diagonal
    identification: with `Θ := vanVleck g`, `u := transportCoeff (transportOp (vanVleck g) g gi)`, the
    order-1 gated van-Vleck witness on the diagonal is EXACTLY the assembled parametrix function at
    ORDER 1:
        `gatedKernel … t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0`.
    This IS the capstone's `hHdiag` shape at `N = 1` — the order at which it is a TRUE theorem
    (`heatParametrixFn 1` carries the `u₁(0) = R/6` term the order-0 witness structurally could not
    supply, J4-761).  `N = 1` sibling of `CapstoneWiring.gatedWitness_diag_eval_vanVleck`.
    NOT `a₁ = R/6` (it identifies the witness with the ansatz; it does not evaluate `u₁(0)`). -/
theorem gatedGlobalWitnessN1_diag_hHdiag (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap) t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0 := by
  rw [gatedGlobalWitnessN1_diag_eval K S (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b ha hab Vmap t hK0 hS0 hV,
      heatParametrixFn_eq]

/-! ### 2. The diagonal `τ`-differentiability `hDH` at `N = 1`. -/

/-- **★ J4-766 — `hDH` at the ORDER-1 gated cutoff-parametrix witness.**  For the concrete order-1
    gated witness `H₁ = gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b
    (uniformInverseChart g gi hChr hK))`, the diagonal map `τ ↦ H₁ τ 0 0` is `DifferentiableAt` every
    `t > 0`.  Gate-generic.  `N = 1` sibling of `GatedGlobalWitnessDiagDH.gatedGlobalWitness_diag_hDH`
    — same τ-independent set-gate case split, with `heatParametrix_differentiableAt_t 1` (the order-1
    Gaussian-times-`(u₀+u₁·τ)` polynomial, `C^∞` for `t > 0`).  NOT `a₁ = R/6`. -/
theorem gatedGlobalWitnessN1_diag_hDH
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ)
    (S : Point n → Set (Point n)) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ
      (fun τ => gatedKernel K S
        (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0) t := by
  by_cases hK0 : (0 : Point n) ∈ K
  · by_cases hS0 : (0 : Point n) ∈ S 0
    · have hV0 : uniformInverseChart g gi hChr hK 0 0 = 0 :=
        uniformInverseChart_zero g gi hChr hK hK0
      have hfun : (fun τ => gatedKernel K S
          (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
          = fun τ => radialCutoff a b (0 : Point n) * heatParametrix 1 Θ u τ (0 : Point n) := by
        funext τ
        rw [gatedKernel_apply_of_mem K S _ τ hK0 hS0]
        simp only [globalCutoffParametrixWitnessN, hV0]
      rw [hfun]
      exact (heatParametrix_differentiableAt_t 1 Θ u t ht (0 : Point n)).const_mul _
    · have hfun : (fun τ => gatedKernel K S
          (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
          = fun _ => (0 : ℝ) := by
        funext τ
        exact gatedKernel_apply_of_notMem K S _ τ 0 0 (Or.inr hS0)
      rw [hfun]; exact differentiableAt_const 0
  · have hfun : (fun τ => gatedKernel K S
        (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hChr hK)) τ 0 0)
        = fun _ => (0 : ℝ) := by
      funext τ
      exact gatedKernel_apply_of_notMem K S _ τ 0 0 (Or.inl hK0)
    rw [hfun]; exact differentiableAt_const 0

/-! ### 3. The residual nonpositive-time vanishing `hEzero` at `N = 1`. -/

/-- **★ J4-766 — `hEzero` for the concrete ORDER-1 gated witness.**  For `1 ≤ n`, the heat operator of
    the order-1 gated cutoff-parametrix witness
    `H₁ = gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)` VANISHES at nonpositive time:
        `∀ τ ≤ 0, ∀ p q, heatOp g gi H₁ τ p q = 0`.
    `N = 1` sibling of `GatedGlobalWitnessLeviIntInter.gatedGlobalWitness_residual_hEzero`.  The order
    is irrelevant to the vanishing — for `1 ≤ n` the Gaussian `gaussDdim τ` is `0` at `τ ≤ 0`, so the
    whole gated witness vanishes on `Iic 0` REGARDLESS of the polynomial degree in `t`; the ONLY change
    from the order-0 proof is `globalCutoffParametrixWitnessN 1` (with `heatParametrix 1`) in place of
    the order-0 witness.  NOT `a₁ = R/6`. -/
theorem gatedGlobalWitnessN1_residual_hEzero (g gi : Point n → Fin n → Fin n → ℝ)
    (hn : 1 ≤ n) (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (Vmap : Point n → Point n → Point n) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap)) τ p q = 0 := by
  have hker0 : ∀ s : ℝ, s ≤ 0 → ∀ p' q' : Point n,
      gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) s p' q' = 0 := by
    intro s hs p' q'
    have hwit : globalCutoffParametrixWitnessN 1 Θ u a b Vmap s p' q' = 0 := by
      simp only [globalCutoffParametrixWitnessN, heatParametrix,
        gaussDdim_eq_zero_of_nonpos hn hs, zero_mul, mul_zero]
    simp only [gatedKernel]
    split_ifs <;> simp [hwit]
  intro τ hτ p q
  set Kn : ℝ → Point n → Point n → ℝ :=
    gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) with hKn
  have hlap : laplaceBeltrami g gi (fun x => Kn τ x q) p = 0 := by
    have hzero : (fun x => Kn τ x q) = (fun _ => (0 : ℝ)) := by
      funext x; exact hker0 τ hτ x q
    rw [hzero]; exact QIQTH.HeatTransportRecursion.laplaceBeltrami_const g gi 0 p
  have hderiv : deriv (fun s => Kn s p q) τ = 0 := by
    set φ : ℝ → ℝ := fun s => Kn s p q with hφ
    rcases lt_or_eq_of_le hτ with hτ0 | hτ0
    · have hnbhd : Set.Iio (0 : ℝ) ∈ 𝓝 τ := isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hτ0)
      have heq : φ =ᶠ[𝓝 τ] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnbhd] with s hs using hker0 s (le_of_lt (Set.mem_Iio.mp hs)) p q
      rw [heq.deriv_eq, deriv_const]
    · subst hτ0
      by_cases hd : DifferentiableAt ℝ φ 0
      · have huniq := uniqueDiffWithinAt_Iic (0 : ℝ)
        have hbase : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic (0 : ℝ)) 0 :=
          hasDerivWithinAt_const (0 : ℝ) (Set.Iic (0 : ℝ)) (0 : ℝ)
        have hwithin : HasDerivWithinAt φ 0 (Set.Iic (0 : ℝ)) 0 :=
          hbase.congr (fun s hs => hker0 s hs p q) (hker0 0 le_rfl p q)
        rw [← hd.derivWithin huniq]
        exact hwithin.derivWithin huniq
      · exact deriv_zero_of_not_differentiableAt hd
  simp only [heatOp, hderiv, hlap, sub_zero]

end QIQTH.HeatResidualBound
