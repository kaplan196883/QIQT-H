/-
  GatedGlobalWitnessN1CapstoneEbdDischarged — J4-774: the ORDER-`N = 1` partial Seeley–DeWitt capstone
  with `hEboundW` GENUINELY DISCHARGED (the wiring adapter flagged by J4-772).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS IS.  A pure WIRING ADAPTER (Sol checkpoint J4-773, item flagged in J4-772).  The banked
  order-1 capstone `GatedGlobalWitnessN1Capstone.trueKernel_diagonal_a1_eq_R6_residual_N1_discharged`
  (J4-767) CARRIES the pure all-`τ` single-constant width-2 residual bind
      `hEboundW : ∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ B · baseKernelW 2 0 τ p q`,
  threading it into `iterConvIntegrableW_of_bound_baseMeas` (`hInt`) and
  `heatConv_leviSeries_interchange` (`hInter`), and — one layer down inside
  `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` — into `neumann_summable_alpha0_width2` for the diagonal
  Neumann summability.

  J4-772's MAJOR CORRECTION: that pure all-`τ` shape is NOT proven for the order-1 witness and is not
  even the right target (the residual genuinely IS affine-in-`τ`, `AffineGateTransport.lean`).  What IS
  proven, UNCONDITIONALLY FROM GEOMETRY, is the `(0,t]`-LOCAL affine-in-`τ` bound
      `∀ t, ∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi H τ p q| ≤ (C·(1+t)) · baseKernelW 2 0 τ p q`
  at the EXACT live order-1 gated van-Vleck witness — exported by
  `GateOpennessExport.gatedWitnessN1_package_open` (J4-204) TOGETHER with the origin gate membership
  `0 ∈ K → 0 ∈ S 0`.

  THE ADAPTER (this file).  Source `a, b, C, S` + the affine bound + `0 ∈ S 0` from
  `gatedWitnessN1_package_open`, then feed the affine bound into the LOCAL-form consumers instead of
  the pure-all-`τ` ones:
    • `hInt`   ← `iterConvIntegrableW_of_locally_bound_baseMeas` (J4-109, GatedWitnessMeas.lean) — the
                 `timeCap` producer, which builds the FULL `IterConvIntegrableW` from the `(0,T]`-local
                 bound family + `hEzero` + `hEmeas`;
    • `hInter` ← `InterchangeLocalRebase.hInter_from_local_data` (J4-206) — the interchange from the
                 `(0,T]`-local bound + `hEzero` + `hEmeas` + the every-ceiling family;
    • the whole assembly is closed by `trueKernel_diagonal_a1_eq_R6_residual_restricted`
      (RestrictedEboundW.lean, J4-104) — the `(0,t]`-restricted capstone, whose diagonal summability
      runs through `neumann_summable_alpha0_width2_le` (the local-bound sibling), so the pure all-`τ`
      `hEboundW` never appears anywhere in the chain.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  NET REDUCTION vs. J4-767.  The order-1 capstone `trueKernel_diagonal_a1_eq_R6_residual_N1_discharged`
  carries `{hEboundW, hEmeas, hDuhamel, hDConv, hCH, hCConv}`.  Here `hEboundW` is DISCHARGED
  (internally from geometry, via the package's affine bound) AND `hS0` is discharged (from the
  package's exported gate membership).  The surviving carries are exactly
      `{hEmeas, hDuhamel, hDConv, hCH, hCConv}`
  — ONE fewer open hypothesis (`hEboundW`) on the live order-1 chain, plus the origin-membership side
  condition removed.  The cost is the extra geometric inputs `gatedWitnessN1_package_open` needs
  (`hgnd`/`hgsymm`/`hinvF`/`hframeK`/`hw`) — all standard, satisfiable metric facts, none vacuous,
  none the conclusion (mirrors `a1_R6_of_residue_inf_v4`).

  ⚠ HONEST FIREWALL.  STILL CONDITIONAL; NOT `a₁ = R/6`.  The remaining carries `hEmeas` (base joint
  strong measurability), `hDuhamel`/`hDConv` (Duhamel / diagonal-convolution differentiability),
  `hCH`/`hCConv` (spatial `C^∞` regularity) are genuine, satisfiable analytic facts about the order-1
  residual — none the conclusion, none vacuous.  No `sorry`, no new axioms, no `:= True`, no existing
  file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1Diag
import QIQTH.RestrictedEboundW
import QIQTH.GatedWitnessMeas
import QIQTH.GateOpennessExport
import QIQTH.InterchangeLocalRebase
import QIQTH.CapstoneWiring

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

/-- **★ J4-774 — the ORDER-1 partial Seeley–DeWitt capstone with `hEboundW` GENUINELY DISCHARGED.**

    Wiring adapter over `trueKernel_diagonal_a1_eq_R6_residual_N1_discharged` (J4-767): the order-1
    gated van-Vleck cutoff-parametrix witness
        `H₁ := gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
                 (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))`,
    with `a, b, S` (and the affine bound + origin gate membership `0 ∈ S 0`) sourced from
    `gatedWitnessN1_package_open`.  The four low-order carries `hHdiag`/`hDH`/`hInt`/`hInter` are
    supplied internally exactly as in J4-767 — EXCEPT `hInt` and `hInter` are now built from the
    `(0,t]`-LOCAL affine bound (via `iterConvIntegrableW_of_locally_bound_baseMeas` and
    `hInter_from_local_data`) rather than a carried pure all-`τ` `hEboundW`, and the whole assembly is
    closed by the `(0,t]`-restricted capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted`.

    RESULT vs. J4-767: `hEboundW` (the pure all-`τ` width-2 bound) is DISCHARGED, and the origin
    membership `hS0` is discharged.  The surviving carries are exactly
    `{hEmeas, hDuhamel, hDConv, hCH, hCConv}` — one fewer open hypothesis.  STILL CONDITIONAL;
    NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_hEboundW_discharged
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
  -- Source `a, b, C, S` + the `(0,t]`-affine bound + origin gate membership from the package.
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, ha, hab, S, ?_⟩
  intro H hEmeas hDuhamel hDConv hCH hCConv
  -- The effective (0,t]-restricted constant.
  have hCeff0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hC0 (by linarith)
  -- ★ `hEboundW_le` — the `(0,t]`-restricted affine bound, DISCHARGED from the package (at ceiling `t`).
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
  -- `hInt` — the FULL `IterConvIntegrableW`, from the `(0,T]`-LOCAL bound via the `timeCap` producer
  -- (J4-109), NOT from a carried pure all-`τ` `hEboundW`.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 (C * (1 + t)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas (heatOp g gi H) (C * (1 + t))
      hEzero hEmeas hlocal
  -- `hInter` — the tsum/heatConv interchange from the `(0,T]`-LOCAL data (J4-206), NOT the global one.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    hInter_from_local_data (heatOp g gi H) (C * (1 + t)) t hCeff0 ht
      (fun τ p q hτ hτt => hbound t τ p q hτ hτt) hEzero hEmeas hlocal t ht le_rfl 0 0
  -- ★ `hHdiag` at `N = 1` — GENUINELY TRUE; `hS0` supplied by the package's exported gate membership.
  have hHdiag : H t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    gatedGlobalWitnessN1_diag_hHdiag g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t
      hK0 (hmemS0 hK0) (uniformInverseChart_zero g gi hChr hK hK0)
  -- `hDH` diagonal time-differentiability at the order-1 witness.
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitnessN1_diag_hDH g gi hChr hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b S t ht
  -- Matrix-`1` form of `g 0 = δ` for the restricted capstone.
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- Close with the `(0,t]`-RESTRICTED capstone (its Neumann summability runs through
  -- `neumann_summable_alpha0_width2_le` — the pure all-`τ` `hEboundW` never appears).
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted g gi Ric 1 (le_refl 1) t ht H
    (C * (1 + t)) hCeff0 hg hg0' hgi hΓ hdg0 htr hsrc hHdiag hEboundW_le hInt hDuhamel hInter
    hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound
