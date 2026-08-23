/-
  ConstRadiusPkgPrescribed — J4-1037 (part 1): the CONSTANT-RADIUS package producer
  (`ConstRadiusGateExport.gatedWitnessN1_package_open_CONSTRADIUS`) REPLAYED with an externally
  PRESCRIBED radius ceiling `ε`, so the exposed gate radius `c` satisfies `c < ε` BY CONSTRUCTION.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  No `sorry`,
  no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no
  existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM THIS SETS UP (part 1 of the fb `hBLgauss` `c < δ₀` discharge).

  `ConstRadiusGateExport.constRadius_package_and_S1` derives its gate parameters `a, b, c` FIRST (via
  `gatedWitnessN1_package_open_CONSTRADIUS`, from purely chart/coefficient geometry), and only THEN
  calls `tripleHEmeas_AT_CONSTRADIUS_GATE a b c …`, which derives its OWN S1/jet reach `δ₀` AFTER `c`
  is already fixed.  Since `c` and `δ₀` are independently-produced opaque existential witnesses, the
  compatibility `c < δ₀` is a bare, unprovable-in-general antecedent (an explicit countermodel exists:
  `ρc = 4, a = 1, b = 2, c = 3, δ₀ = 1` satisfies every OTHER stated fact).

  `CurvedA1ReachAlign.gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` (J4-599, banked 2026-08-11, for
  a DIFFERENT consumer — the curved capstone's `hBdom`) already solves EXACTLY this shape of problem:
  it replays `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST` with ONE change — the internal
  availability radius `ρc := min (min (min rN δ₀) r₁) ε` for a PRESCRIBED `ε > 0` — so the exposed
  `c = (b + ρc) / 2` additionally satisfies `c < ε`.  This replay is fully GENERIC in `g, gi, Θ, u` (no
  curved-specific instantiation anywhere in its statement or proof), so it is reusable here verbatim.

  ## THE FIX (this file).

  `gatedWitnessN1_package_open_CONSTRADIUS_prescribed` replays
  `ConstRadiusGateExport.gatedWitnessN1_package_open_CONSTRADIUS` with ONE change: its final call to
  the UNPRESCRIBED `gatedWitnessN1_hEboundW_le_lin_CONST` is replaced by a call to the PRESCRIBED
  `CurvedA1ReachAlign.gatedWitnessN1_hEboundW_le_lin_CONST_prescribed`, threading through the SAME
  externally-supplied `ε`, with `Θ := vanVleck g`, `u := transportCoeff (transportOp (vanVleck g) g gi)`
  (the fixed choices the unprescribed package producer already hard-codes).  The coefficient data
  `ρ_c, C0, C1, hCoeffU0, hCoeffLin1` is derived EXACTLY as in the unprescribed original, from
  `CoeffBoundsN1.hCoeffU0_vanVleck` and `CoeffU1Fix.uniformCoeffLinear_bound` — these suppliers do not
  reference `ε` or `δ₀` at all, so no new mathematical content is needed for them.  The result: the SAME
  package conclusions as before, PLUS the extra conjunct `c < ε`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConstRadiusGateExport
import QIQTH.CurvedA1ReachAlign
import QIQTH.CoeffBoundsN1
import QIQTH.CoeffU1Fix

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.GateOpennessExport QIQTH.S1TripleHEmeasGate QIQTH.ConstRadiusGateExport
open QIQTH.CurvedA1ReachAlign
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.ConstRadiusPkgPrescribed

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★★ J4-1037 (part 1) — `gatedWitnessN1_package_open_CONSTRADIUS_prescribed`.**  Verbatim
    `ConstRadiusGateExport.gatedWitnessN1_package_open_CONSTRADIUS`, with ONE change: an externally
    PRESCRIBED radius ceiling `ε > 0`, routed through `CurvedA1ReachAlign`'s prescribed CONST producer,
    so the exposed gate radius `c` additionally satisfies `c < ε`.  The coefficient-bound derivation
    (`hCoeffU0_vanVleck`, `uniformCoeffLinear_bound`) is untouched — identical to the unprescribed
    original.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_package_open_CONSTRADIUS_prescribed (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧ c < ε ∧
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K →
          (0 : Point n) ∈ uniformFlowExp g gi hC hK 0 '' Metric.ball (0 : Point n) c)
      ∧ ((0 : Point n) ∈ K →
          IsOpen (uniformFlowExp g gi hC hK 0 '' Metric.ball (0 : Point n) c)) := by
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  obtain ⟨a, b, C, c, ha, hab, hC0', hbc, hcε, hbound, hgate, hmemS, hopenS⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST_prescribed g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
      ε hε
  refine ⟨a, b, C, c, ha, hab, hC0', hbc, hcε, hbound, ?_, ?_⟩
  · intro h0; exact hmemS 0 h0
  · intro h0; exact hopenS 0 h0

end QIQTH.ConstRadiusPkgPrescribed

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ConstRadiusPkgPrescribed
#print axioms gatedWitnessN1_package_open_CONSTRADIUS_prescribed
end AxiomChecks
