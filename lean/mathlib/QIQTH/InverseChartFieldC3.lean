/-
  InverseChartFieldC3 — sub-brick 3a of the a₁ = R/6 `hCConv` chain (Brick 3, JET4_TOWER_PLAN J4-826).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  derivative-layer brick of the convergence campaign.  No `sorry` (header prose excepted), no
  `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-
  disguise.  std-3 only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE STALE-PREMISE CORRECTION (don't-undercredit-the-repo).

  Sub-brick 3a was scoped (JET4_TOWER_PLAN J4-826) as: "upgrade the inverse chart
  `uniformInverseChart`'s FIELD-SLOT regularity from `C²` (`ChartJetBounds.chartField_contDiffAt_center`,
  'the current ceiling') to `C³` by transporting the forward `C³` exp map
  (`ExpMapContDiff3.expMap_contDiffOn_three`) through the inverse-function step."

  ── ON INSPECTION THE `C²` 'CEILING' IS STALE.  `ChartThirdJet` (J4-192) ALREADY banked the inverse
     chart's field-slot `C⁴` at the base and reachable points — `chartField_contDiffAt_four_basePoint`
     (`ContDiffAt ℝ 4 (uniformInverseChart g gi hC hK z) z` for every `z ∈ K`) and
     `chartField_contDiffAt_four_reachable` (uniform-radius `C⁴` at reachable image points) — by feeding
     the forward `C⁴` map (`uniformFlowExp_contDiffAt_four`, itself the unconditional `exp∈C⁴` tower
     `ExpMap.expMap_contDiffOn_four` transported through the `expMap ↔ uniformFlowExp` overlap bridge)
     into the SAME abstract inverse-function identification core
     `ChartFieldC2General.chartField_contDiffAt_of_leftInverse_germ`, which is GENERIC in the
     regularity order `N`.  So field-`C³` is UNCONDITIONALLY available as a one-line `.of_le (3 ≤ 4)`
     downgrade — NO new ODE / inverse-function work is required, and the forward `C³` map of the
     scoping was never the binding constraint (the tower already has forward `C⁴`).

  This file exposes the exact `C³` interface sub-brick 3a's downstream `Φ ∈ C¹` consumer expects:
  the field-slot `C³` of the inverse chart AND, one level up, the field-slot `C³` of the concrete
  gated van-Vleck witness (`SpatialC2.hCH_discharge`'s assembly one order higher) — which is exactly
  the regularity that makes the witness's SECOND field-partial `Φ` be `C¹`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).

    * `chartField_contDiffAt3_center`    — ★ `ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK 0) 0`,
        the exact `C³` upgrade of `chartField_contDiffAt_center`.  `.of_le (3 ≤ 4)` of the banked
        base-point `C⁴` (`ChartThirdJet.chartField_contDiffAt_four_basePoint` at `z = 0`).
    * `chartField_contDiffAt3_basePoint` — `ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK z) z`,
        general base `z ∈ K`.
    * `chartField_contDiffAt3_reachable` — a single uniform radius `δ > 0` over `K` giving field-`C³`
        of the inverse chart at every reachable image point (`‖v‖ < δ`, `‖v‖ < expRho g gi hC z`).
    * `witnessField_contDiffAt3_center`  — ★★ `ContDiffAt ℝ 3 (fun p ↦ vanVleckGatedWitness … t p 0) 0`,
        the `SpatialC2.hCH_discharge` witness-diagonal assembly ONE ORDER UP: the field-slot `C³` of
        the concrete `N = 1` gated van-Vleck witness at the field centre.  Each amplitude/kernel factor
        is `C^∞` (`radialCutoff_contDiff` / `gaussDdim_contDiff` / `vanVleck_contDiffAt` / `hu`), so the
        only order-sensitive input is the chart's field-`C³` (`chartField_contDiffAt3_center`).  This is
        precisely the input `Φ ∈ C¹` needs (`Φ` = a second field-partial of this witness).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL on `{hDuhamel, hDConv,
  hCConv}`.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartThirdJet
import QIQTH.SpatialC2

open MeasureTheory
open QIQTH.Curvature QIQTH.ExpMap QIQTH.ChartThirdJet
open QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation QIQTH.HeatParametrixOrder
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound QIQTH.PullbackMetric
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE FIELD-SLOT `C³` OF THE INVERSE CHART — `.of_le` of the banked `C⁴`.
    ############################################################################### -/

/-- **★ `chartField_contDiffAt3_center` — the `C³` UPGRADE of `chartField_contDiffAt_center`.**
    At the assembly base `z = 0 ∈ K`, the field-slot inverse chart `V_0 = uniformInverseChart g gi hC hK 0`
    is `ContDiffAt ℝ 3` at the field centre `0`.  A one-line `.of_le (3 ≤ 4)` downgrade of the banked
    base-point `C⁴` `ChartThirdJet.chartField_contDiffAt_four_basePoint` at `z = 0`, showing the former
    `C²` 'ceiling' (`chartField_contDiffAt_center`) was STALE.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt3_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK 0) 0 :=
  (chartField_contDiffAt_four_basePoint g gi hC hK 0 h0K).of_le (by norm_num)

/-- **★ `chartField_contDiffAt3_basePoint` — general base.**  For any base `z ∈ K`, the field-slot
    inverse chart is `ContDiffAt ℝ 3` at the base point `z = φ_z 0`.  `.of_le (3 ≤ 4)` of
    `ChartThirdJet.chartField_contDiffAt_four_basePoint`.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt3_basePoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) :
    ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK z) z :=
  (chartField_contDiffAt_four_basePoint g gi hC hK z hz).of_le (by norm_num)

/-- **★ `chartField_contDiffAt3_reachable` — uniform-radius field-`C³` at reachable points.**  A single
    uniform radius `δ > 0` over `K` such that for every base `z ∈ K` and reachable image point `φ_z v`
    with `‖v‖ < δ` AND `‖v‖ < expRho g gi hC z`, the inverse chart is `ContDiffAt ℝ 3` there.
    `.of_le (3 ≤ 4)` of `ChartThirdJet.chartField_contDiffAt_four_reachable`.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt3_reachable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n, ‖v‖ < δ → ‖v‖ < expRho g gi hC z →
      ContDiffAt ℝ 3 (uniformInverseChart g gi hC hK z) (uniformFlowExp g gi hC hK z v) := by
  obtain ⟨δ, hδ, hreach⟩ := chartField_contDiffAt_four_reachable g gi hC hK
  exact ⟨δ, hδ, fun z hz v hvδ hvexp => (hreach z hz v hvδ hvexp).of_le (by norm_num)⟩

/-! ###############################################################################
    ### ★★ THE FIELD-SLOT `C³` OF THE WITNESS — `SpatialC2.hCH_discharge` one order up.
    ############################################################################### -/

/-- **★★ `witnessField_contDiffAt3_center` — the witness field-`C³`, the input `Φ ∈ C¹` needs.**
    The concrete `N = 1` gated van-Vleck witness diagonal slice `p ↦ vanVleckGatedWitness g gi hC hK S a b t p 0`
    is `ContDiffAt ℝ 3` at the field centre `0`.  This is `SpatialC2.hCH_discharge`
    (`ContDiffAt ℝ 2 …`) raised ONE ORDER: on the open gate `S 0` the witness equals the amplitude
    product `radialCutoff a b (W p) · gaussDdim t (W p) · vanVleck g (W p)^(−1/2) · (u₀(W p) + u₁(W p)·t)`
    through the base-`0` inverse chart `W = uniformInverseChart g gi hC hK 0`; every amplitude/kernel
    factor is `C^∞` (`radialCutoff_contDiff` / `gaussDdim_contDiff` / `vanVleck_contDiffAt` / the
    transport-coefficient smoothness `hu`), so the ONLY order-sensitive input is the chart's field-`C³`
    (`chartField_contDiffAt3_center`, itself the `.of_le` of the banked `C⁴`).  A second field-partial
    `Φ` of this `C³` witness is therefore `C¹`.  Hypotheses are exactly those of `hCH_discharge`
    (satisfiable, non-vacuous, never the conclusion).  NOT `a₁ = R/6`. -/
theorem witnessField_contDiffAt3_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hSopen : IsOpen (S 0))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 3 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) := by
  -- the BASE-0 field chart and its center facts (chart field-`C³` = the `.of_le` of the banked `C⁴`).
  set W := uniformInverseChart g gi hChr hK 0 with hWdef
  have hW3 : ContDiffAt ℝ 3 W (0 : Point n) := chartField_contDiffAt3_center g gi hChr hK hK0
  have hW0 : W (0 : Point n) = 0 := chartField_centerValue_base0 g gi hChr hK hK0
  -- RNC gauge:  det g(0) = 1  ⟹  vanVleck g 0 = 1 > 0.
  have hgmat : (fun i j => g 0 i j) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; exact hg0 i j
  have hdet0 : Matrix.det (g 0) = 1 := by
    rw [show (g 0) = (1 : Matrix (Fin n) (Fin n) ℝ) from hgmat, Matrix.det_one]
  have hvv0 : vanVleck g 0 = 1 := vanVleck_zero g hdet0
  -- the target factored form.
  set F : Point n → ℝ := fun p =>
    radialCutoff a b (W p)
      * (gaussDdim t (W p) * vanVleck g (W p) ^ (-(1 : ℝ) / 2)
          * (transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
            + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * t)) with hFdef
  -- germ equality on the OPEN gate `S 0`.
  have heq : (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) =ᶠ[𝓝 (0 : Point n)] F := by
    refine eventually_nhds_iff.mpr ⟨S 0, ?_, hSopen, hS0⟩
    intro x' hx'
    show vanVleckGatedWitness g gi hChr hK S a b t x' 0 = F x'
    rw [vanVleckGatedWitness_gate_apply g gi hChr hK S a b t hK0 hx']
  -- each factor is `ContDiffAt ℝ 3` at `0`.
  have hcut : ContDiffAt ℝ 3 (fun p => radialCutoff a b (W p)) (0 : Point n) :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp 0 hW3
  have hgauss : ContDiffAt ℝ 3 (fun p => gaussDdim t (W p)) (0 : Point n) :=
    ((gaussDdim_contDiff t).contDiffAt.of_le le_top).comp 0 hW3
  -- van-Vleck smoothness at `W 0`  (`det g(W 0) = det g(0) = 1 > 0`).
  have hdetW : 0 < Matrix.det (g (W (0 : Point n))) := by rw [hW0, hdet0]; norm_num
  have hvv : ContDiffAt ℝ 3 (fun p => vanVleck g (W p)) (0 : Point n) :=
    (vanVleck_contDiffAt g hg (W (0 : Point n)) hdetW (k := 3)).comp 0 hW3
  -- its `−1/2` rpow branch  (`vanVleck g (W 0) = 1 ≠ 0`).
  have hne : (fun p => vanVleck g (W p)) (0 : Point n) ≠ 0 := by
    show vanVleck g (W (0 : Point n)) ≠ 0
    rw [hW0, hvv0]; norm_num
  have hrpow : ContDiffAt ℝ 3 (fun p => vanVleck g (W p) ^ (-(1 : ℝ) / 2)) (0 : Point n) :=
    hvv.rpow_const_of_ne hne
  -- the two transport coefficients through the chart (`hu` at `∞`; downcast `3 ≤ ∞`).
  have h3inf : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
    simpa using h
  have hu0 : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)) (0 : Point n) :=
    (((hu 0).contDiffAt).of_le h3inf).comp 0 hW3
  have hu1 : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1 (W p)) (0 : Point n) :=
    (((hu 1).contDiffAt).of_le h3inf).comp 0 hW3
  -- assemble the amplitude and the product.
  have hsum : ContDiffAt ℝ 3
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * t) (0 : Point n) :=
    hu0.add (hu1.mul contDiffAt_const)
  have hF : ContDiffAt ℝ 3 F (0 : Point n) := hcut.mul ((hgauss.mul hrpow).mul hsum)
  exact hF.congr_of_eventuallyEq heq

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms chartField_contDiffAt3_center
#print axioms chartField_contDiffAt3_basePoint
#print axioms chartField_contDiffAt3_reachable
#print axioms witnessField_contDiffAt3_center
end AxiomChecks
