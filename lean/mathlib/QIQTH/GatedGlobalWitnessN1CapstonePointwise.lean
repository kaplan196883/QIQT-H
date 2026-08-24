/-
  GatedGlobalWitnessN1CapstonePointwise — J4-1173: Phase 4 of the capstone-signature redesign plan
  (`docs/qg_roadmap/CAPSTONE_SIGNATURE_REDESIGN_PLAN.md`, J4-1168), per the phase table's Phase 4 line:
  "Factor the J4-774 discharge theorem into a pointwise version (concrete `a,b,Cpkg,S` + package certs,
  existential-opening moved to a thin corollary) → D6 green".

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS IS.  A pure REFACTOR of `GatedGlobalWitnessN1CapstoneEbdDischarged
  .trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged` (J4-774) into two pieces:

    • `trueKernel_diagonal_a1_eq_R6_residual_N1_pointwise` — the SAME proof body, but taking the
      package's outputs `(a, b, C, S, hbound, hS0)` as DIRECT EXTERNAL INPUTS instead of obtaining them
      from `gatedWitnessN1_package_open` internally.  Consequently the five geometric inputs that J4-774
      needed ONLY to invoke the package (`hgnd, hgsymm, hinvF, hframeK, hw`) are DROPPED from this
      theorem's signature — they play no role once `(a,b,C,S,hbound,hS0)` are supplied directly.  This
      is the exact "pointwise, concrete `a,b,Cpkg,S` + package certs" shape the plan specifies, and is
      precisely the shape a future Layer-C `a1_R6_assembled_v3` (Phase 5) needs to consume AFTER
      destructuring `gatedWitnessN1_package_open`'s existential exactly once.

    • `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged_via_pointwise` — a THIN COROLLARY,
      literally J4-774's original existential-quantified statement, reproved by opening
      `gatedWitnessN1_package_open` EXACTLY ONCE and handing its output straight to the pointwise
      theorem above.  This is Canary D6 (SingleOpening): the corollary's proof performs the package
      existential-elimination exactly once, with no second/unrelated existential selection anywhere in
      the proof.

  Net effect: the SAME mathematical content as J4-774, split so that a future consumer wanting the
  pointwise shape (e.g. Layer C's `v3`) no longer has to re-derive it from inside an `obtain`.

  `a₁=R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}` (plus the still-carried `hEmeas`
  here), UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1CapstoneEbdDischarged

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.TransitionAnnulusCont
open QIQTH.GateOpennessExport QIQTH.InterchangeLocalRebase
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★ J4-1173 (Phase 4) — the POINTWISE factoring of the J4-774 discharge theorem.**  Same content as
    `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged`, EXCEPT `(a, b, C, S)` and the
    package's local affine bound `hbound` / origin membership `hS0` are DIRECT EXTERNAL INPUTS rather
    than sourced internally from `gatedWitnessN1_package_open` — so the five package-only geometric
    inputs (`hgnd, hgsymm, hinvF, hframeK, hw`) are DROPPED.  This is the exact shape a future
    existential-opened consumer (Layer C, Phase 5) needs. NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_pointwise
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- ★ pointwise inputs, replacing the internal `gatedWitnessN1_package_open` call:
    (a b C : ℝ) (ha : 0 < a) (hab : a < b) (hC0 : 0 ≤ C)
    (S : Point n → Set (Point n))
    (hbound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)))
          τ p q| ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hS0 : (0 : Point n) ∈ S 0) :
    (let H := gatedKernel K S
        (globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK));
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
  intro H hEmeas hDuhamel hDConv hCH hCConv
  -- The effective (0,t]-restricted constant.
  have hCeff0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hC0 (by linarith)
  -- ★ `hEboundW_le` — the `(0,t]`-restricted affine bound, at ceiling `t`.
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun τ p q hτ hτt => hbound t τ p q hτ hτt
  -- the order-1 residual nonpositive-time vanishing (needs `1 ≤ n`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)
  -- the every-ceiling `(0,T]`-local bound family (constant `C·(1+T)` per window `T`).
  have hlocal : ∀ T : ℝ, 0 < T → ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ τ p q, 0 < τ → τ ≤ T →
        |heatOp g gi H τ p q| ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun T hT => ⟨C * (1 + T), mul_nonneg hC0 (by linarith),
      fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩
  -- `hInt` — the FULL `IterConvIntegrableW`, from the `(0,T]`-LOCAL bound via the `timeCap` producer.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 (C * (1 + t)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas (heatOp g gi H) (C * (1 + t))
      hEzero hEmeas hlocal
  -- `hInter` — the tsum/heatConv interchange from the `(0,T]`-LOCAL data.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    hInter_from_local_data (heatOp g gi H) (C * (1 + t)) t hCeff0 ht
      (fun τ p q hτ hτt => hbound t τ p q hτ hτt) hEzero hEmeas hlocal t ht le_rfl 0 0
  -- ★ `hHdiag` at `N = 1` — GENUINELY TRUE; `hS0` supplied directly (no `hmemS0 hK0` step needed).
  have hHdiag : H t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    gatedGlobalWitnessN1_diag_hHdiag g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t
      hK0 hS0 (uniformInverseChart_zero g gi hChr hK hK0)
  -- `hDH` diagonal time-differentiability at the order-1 witness.
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitnessN1_diag_hDH g gi hChr hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b S t ht
  -- Matrix-`1` form of `g 0 = δ` for the restricted capstone.
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- Close with the `(0,t]`-RESTRICTED capstone.
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted g gi Ric 1 (le_refl 1) t ht H
    (C * (1 + t)) hCeff0 hg hg0' hgi hΓ hdg0 htr hsrc hHdiag hEboundW_le hInt hDuhamel hInter
    hDH hDConv hCH hCConv

/-- **★ J4-1173 (Phase 4, Canary D6 — SingleOpening) —
    `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged_via_pointwise`.**  A THIN COROLLARY:
    the SAME statement as J4-774's
    `trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged`, reproved by opening
    `gatedWitnessN1_package_open` EXACTLY ONCE (Canary D6) and handing its output straight to
    `trueKernel_diagonal_a1_eq_R6_residual_N1_pointwise`.  Confirms the factoring is faithful — the
    pointwise theorem plus a single existential-opening reproduces J4-774's original conclusion exactly.
    NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged_via_pointwise
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ S : Point n → Set (Point n),
      (let H := gatedKernel K S
          (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK));
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
  -- Canary D6 — EXACTLY ONE opening of the package existential, no second selection anywhere below.
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  exact ⟨a, b, ha, hab, S,
    trueKernel_diagonal_a1_eq_R6_residual_N1_pointwise g gi Ric t ht hn hg hChr hK hK0 hg0 hgi hΓ
      hdg0 htr hsrc a b C ha hab hC0 S hbound (hmemS0 hK0)⟩

end QIQTH.HeatResidualBound
