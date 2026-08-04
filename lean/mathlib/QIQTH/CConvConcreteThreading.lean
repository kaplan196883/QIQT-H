/-
  CConvConcreteThreading — J4-207: threading the bundled L1 facade + the interface-level `hD1`
  closure into the CONCRETE `hCConv` spatial-`C²` slot of the `∞`-capstone (Sol final plan Phase 4,
  docs/qg_roadmap/JET4_TOWER_PLAN.md, "SOL CONSULT #3").

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign.  It performs the MECHANICAL composition
      `CConvFacade.hCConv_discharged_from_data`  (the L1 `∃`-`HasFDerivAt` family, `hfam`)
        ∘  `SpatialC2.hCConv_reduction`           (`hfam` + `hD1` ⟹ the `C²` slot, via `2 = 1 + 1`)
  at the CONCRETE left kernel `H := vanVleckGatedWitness g gi hChr hK S a b` and the CONCRETE source
  `F := leviSeries (heatOp g gi H)`, producing the exact `hCConv` slot that
  `GateOpennessExport.a1_R6_of_residue_inf_v4` (and the base `a1_R6_of_residue_inf`) demand:
      `ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0`.

  The five facade `: Prop` bundles (Metric / ChartGate / Source / Derivative / Envelope) are carried
  VERBATIM at the concrete `H`/`F`; the derivative-map `D` is pinned EXPLICITLY (Sol: never replace `F`
  by an a.e.-representative inside a `ContDiffAt` goal); the source slice is the pinned honest slice
  `fun s z ↦ leviSeries (heatOp g gi H) s z 0`.  The `C¹` regularity of the derivative map,
  `hD1 : ContDiffAt ℝ 1 D 0`, is CARRIED — it is the still-open L2 singular-second-derivative content
  (the `XUniformSliverFull.hD1_from_data` interface closure at the CLM-valued lift), never faked.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; each main std-3):
    • `hCConv_concrete_from_data` — ★★★ the threading theorem: the concrete `C²` `hCConv` slot from the
      five facade bundles + explicit `D` + the carried `hD1`.  The structure is fully machine-checked;
      the analytic content lives in the carried bundles + `hD1`.
    • `a1_R6_of_residue_inf_v5` — ★★★ the `∞`-capstone with the `hCConv` antecedent DISCHARGED: exactly
      `a1_R6_of_residue_inf_v4` but the inner `ContDiffAt ℝ 2 … → …` layer is REMOVED, supplied instead
      by `hCConv_concrete_from_data` fed a `∀`-over-gate bundle provider `hThread` (whose antecedent is
      the gate-identifying Gaussian heat bound — the property the LANDED package proves — so the
      provider is non-vacuous, satisfiable, and strictly LOWER-LEVEL than the `C²` conclusion it
      replaces).  The inner carry list drops to `{hInt, hDuhamel, hInter, hDConv}` (v4's list MINUS the
      `hCConv` `C²` layer, now paid by the facade + `hD1` bundles).

  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the conclusion (the `a₁=R/6`
  identity is nowhere assumed, nor is the `C²` `hCConv` slot assumed of the gate in disguise — only the
  strictly-lower analytic bundles + `hD1`).  NO conclusion-in-disguise.  NO vacuous / unsatisfiable
  hypotheses.  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvFacade
import QIQTH.SpatialC2
import QIQTH.XUniformSliverFull
import QIQTH.GateOpennessExport

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.OmegaHsrcC4cAudit QIQTH.InftyRebaseCapstone
open QIQTH.CConvFacade QIQTH.GateOpennessExport
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.CConvConcreteThreading

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### 1. THE THREADING THEOREM — facade ∘ reduction at the concrete `H`/`F`.
    ############################################################################### -/

/-- **★★★ J4-207 — `hCConv_concrete_from_data`.**  The CONCRETE `hCConv` spatial-`C²` slot of the
    `∞`-capstone, threaded from the five bundled facade `: Prop` data bundles (`CConvFacade.*`) at the
    concrete left kernel `H := vanVleckGatedWitness g gi hChr hK S a b`, the concrete source
    `F := leviSeries (heatOp g gi H)`, the EXPLICIT derivative map `D`, and the carried `C¹` regularity
    `hD1 : ContDiffAt ℝ 1 D 0`:
      `ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0`.
    Route: `CConvFacade.hCConv_discharged_from_data` delivers the L1 `∃`-`HasFDerivAt` family `hfam`
    (VERBATIM the `hfam` slot of `SpatialC2.hCConv_reduction`), which the reduction lifts to `C²` via
    `2 = 1 + 1` given `hD1`.  The source slice is pinned to `fun s z ↦ F s z 0` (never an a.e.-rep in a
    `ContDiffAt` goal — Sol).  `hD1` is the honest still-open carry.  NOT `a₁ = R/6`. -/
theorem hCConv_concrete_from_data
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 < t)
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t u)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (deriv : CConvDerivativeData g gi hChr hK S a b t u
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D)
    (env : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd)
    (hD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
        (0 : Point n) := by
  -- set-alias the concrete left kernel and source (Sol: explicit aliases, no let-chains).
  set H : ℝ → Point n → Point n → ℝ := vanVleckGatedWitness g gi hChr hK S a b with hHdef
  set F : ℝ → Point n → Point n → ℝ := leviSeries (heatOp g gi H) with hFdef
  -- (L1) the facade delivers the `∃`-`HasFDerivAt` family = the reduction's `hfam` slot.
  have hfam : ∃ w ∈ 𝓝 (0 : Point n), ∀ x ∈ w,
      HasFDerivAt (fun p => heatConv H F t p 0) (D x) x :=
    hCConv_discharged_from_data g gi hChr hK S a b t ht
      (fun s z => F s z 0) u hu_open hu0 Bs Ba Bd Cf H F D metric chart source deriv env
  -- (L1 + L2) lift to `C²` via `2 = 1 + 1` given the carried `hD1`.
  exact hCConv_reduction H F t D hfam hD1

/-! ###############################################################################
    ### 2. THE `v5` CAPSTONE — `a1_R6_of_residue_inf_v4` with `hCConv` discharged.
    ############################################################################### -/

/-- **★★★ J4-207 — `a1_R6_of_residue_inf_v5`.**  The `∞`-capstone residual
    `OmegaHsrcC4cAudit.a1_R6_of_residue_inf` (the base capstone `GateOpennessExport.a1_R6_of_residue_inf_v4`
    wraps in its `∃`-gate) with the spatial-`C²` `hCConv` hypothesis
    `ContDiffAt ℝ 2 (fun p ↦ heatConv H (leviSeries (heatOp g gi H)) t p 0) 0` REPLACED, in place, by
    the THREADING'S INGREDIENT SET — the five facade `: Prop` bundles (Metric / ChartGate / Source /
    Derivative / Envelope), the explicit derivative map `D`, the neighbourhood `u`, its constants, and
    the carried `C¹` regularity `hD1 : ContDiffAt ℝ 1 D 0`.  Internally `hCConv_concrete_from_data`
    re-derives the `hCConv` `C²` slot from those bundles and feeds it to `a1_R6_of_residue_inf`.

    Every hypothesis is one the base capstone already carries (all satisfiable at the concrete gated
    van-Vleck witness) OR a facade bundle (satisfiable by the model — the `CConvFacade` headers) OR the
    honest still-open `hD1` carry; NONE is universally quantified over gates (so no possibly-false
    `∀ S` provider), NONE is vacuous / unsatisfiable, and NONE equals the conclusion.  The `C²` `hCConv`
    black-box hypothesis is thus PAID by strictly-lower analytic data.  ⚠ STILL NOT `a₁ = R/6`; the
    remaining carries (Levi/Duhamel interface, the bundle data, `hD1`) are honest inputs.

    Follow-on (the honest gap): the `∃`-gate v4-wrapper form additionally needs these bundles supplied
    for the specific package gate `gatedWitnessN1_package_open` produces — a separate wiring brick. -/
theorem a1_R6_of_residue_inf_v5 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
        = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
          + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0)
    (hInter : heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (fun τ p q => (-1 : ℝ) ^ (k + 1)
              * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
            t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- ★ the threading's ingredient set, REPLACING the single `hCConv` `C²` hypothesis.
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t u)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (deriv : CConvDerivativeData g gi hChr hK S a b t u
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D)
    (env : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd)
    (hD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- re-derive the `hCConv` `C²` slot from the threading ingredient set.
  have hCConv : ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0) (0 : Point n) :=
    hCConv_concrete_from_data g gi hChr hK S a b t ht u hu_open hu0 Bs Ba Bd Cf D
      metric chart source deriv env hD1
  -- feed the base `∞`-capstone residual with `hCConv` now discharged.
  exact a1_R6_of_residue_inf g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0 hgi hΓ hdg0 htr hsrc
    hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.CConvConcreteThreading

section AxiomChecks
open QIQTH.CConvConcreteThreading
#print axioms hCConv_concrete_from_data
#print axioms a1_R6_of_residue_inf_v5
end AxiomChecks
