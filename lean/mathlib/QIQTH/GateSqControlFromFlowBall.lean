/-
  GateSqControlFromFlowBall — J4-900: DISCHARGE the surviving `hgate : GateSqControl` carry of
  `HAdomHWDomFromConcreteDominations` for the LIVE order-1 capstone's CONCRETE flow-ball gate
  `constGate g gi hChr hK c = fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure GEOMETRY-WIRING brick.  It threads the banked, fully-abstract flow-ball geometry lemma
  `ConcreteDominations.gateSqControl_of_flowBall` (in `QIQTH.HeatResidualBound`) — the near-isometry
  square-comparison producer — at the CONCRETE tower flow `φ = uniformFlowExp g gi hChr hK`, inverse
  chart `W = uniformInverseChart g gi hChr hK`, using:
    * `OnGateGlue.uniformInverseChart_leftInverse_of_lt` — the chart-inverse germ `W_q (φ_q v) = v` on a
      radius-`δ₀` ball over `K` (`hinv`);
    * `NearIsometryBudget.uniformFlowExp_hdisp_ball` (J4-96) — the UNIFORM near-isometry width budget
      `(3/2)·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v` on a radius-`r₁` ball over `K` (`hdisp`).
  The two radius windows are intersected (`c ≤ min δ₀ r₁`), so for every small enough gate radius `c`
  the SATISFIABLE certificate `hgate : GateSqControl K (constGate g gi hChr hK c) (uniformInverseChart
  g gi hChr hK)` — exactly the surviving carry of `HAdomHWDomFromConcreteDominations` at the live
  capstone's own gate `S = constGate …` — is PRODUCED from geometry alone.  No `hgate` assumption.

  Then `hAdom_hWDom_from_gateSqControl_constGate` FEEDS this certificate into the banked ABSTRACT-`S`
  bundle `HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl` (specialised at
  `S := constGate g gi hChr hK c`), removing the `hgate` carry entirely: the `hAdom`/`hWDom` census
  binders now hold for the live flow-ball gate from geometry + the SINGLE remaining mainline-standard
  amplitude-smoothness carry `hw`.

  ## HONEST SURVIVING CARRY.  Exactly ONE:
    * `hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff (vanVleck g) (transportCoeff …) k)` — the mainline-standard
      van-Vleck amplitude-coefficient smoothness carried repo-wide (feeds the compact-support amplitude
      sups `exists_cutoff_foldedCoeff_bound`).  NOT the conclusion.  (Its own generic supplier —
      `HuInftyRebase.hu_infty_closed` + `hw_discharged_infty` from `hg`/`hgi`/`hgpos` — delivers the
      `∞`-level version; the `⊤`-level carry stays the standard threaded input, see note below.)

  No `sorry` (header prose excepted), no new axiom (`std-3` only), no `:= True`, no vacuous /
  unsatisfiable hypothesis (the produced `c`-window is inhabited, `0 < min δ₀ r₁`), no hypothesis
  equal to (or trivially yielding) the conclusion, no existing file edited.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConcreteDominations
import QIQTH.A1R6CoreAtGate
import QIQTH.OnGateGlue
import QIQTH.NearIsometryBudget
import QIQTH.HAdomHWDomFromConcreteDominations

open Set Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.OnGateGlue
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.A1R6CoreAtGate
open scoped Topology BigOperators

namespace QIQTH.GateSqControlFromFlowBall

variable {n : ℕ}

/-! ###############################################################################
    ### The concrete `GateSqControl` discharge for the tower flow-ball gate.
    ############################################################################### -/

/-- **★★ `gateSqControl_constGate` — the SATISFIABLE gate certificate for the live flow-ball gate.**
    For the CONCRETE tower flow-ball gate `constGate g gi hChr hK c`
    (`= fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`) and inverse chart
    `uniformInverseChart g gi hChr hK`, there is a radius threshold `c₀ > 0` such that for EVERY
    positive gate radius `c ≤ c₀` the `ConcreteDominations.GateSqControl` square-comparison certificate
    holds — from geometry alone, NO `hgate` assumption.

    Proof: instantiate the abstract `gateSqControl_of_flowBall` (`QIQTH.HeatResidualBound`) at
    `φ = uniformFlowExp …`, `W = uniformInverseChart …`, with the chart-inverse germ
    `uniformInverseChart_leftInverse_of_lt` (window `δ₀`) as `hinv` and the near-isometry width budget
    `uniformFlowExp_hdisp_ball` (window `r₁`) as `hdisp`, over the intersected window `c ≤ min δ₀ r₁`.
    ⚠ NOT `a₁ = R/6`. -/
theorem gateSqControl_constGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      GateSqControl K (constGate g gi hChr hK c) (uniformInverseChart g gi hChr hK) := by
  obtain ⟨δ₀, hδ₀, hinv⟩ := uniformInverseChart_leftInverse_of_lt g gi hChr hK
  obtain ⟨r₁, hr₁, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hChr hK
  refine ⟨min δ₀ r₁, lt_min hδ₀ hr₁, ?_⟩
  intro c hc hcle
  have hcδ : c ≤ δ₀ := le_trans hcle (min_le_left _ _)
  have hcr : c ≤ r₁ := le_trans hcle (min_le_right _ _)
  -- `constGate g gi hChr hK c` is DEFINITIONALLY `fun q => uniformFlowExp g gi hChr hK q '' ball 0 c`,
  -- exactly the gate produced by `gateSqControl_of_flowBall`.
  exact gateSqControl_of_flowBall K (uniformInverseChart g gi hChr hK)
    (uniformFlowExp g gi hChr hK) c r₁ hcr
    (fun q hq v hv => hinv q hq v (lt_of_lt_of_le hv hcδ))
    (fun q hq v hv => hdisp q hq v hv)

/-! ###############################################################################
    ### Thread it in — the `hAdom`+`hWDom` bundle at the live gate, `hgate` DISCHARGED.
    ############################################################################### -/

/-- **★★★ `hAdom_hWDom_from_gateSqControl_constGate` — the `hgate`-free `hAdom`+`hWDom` bundle at the
    live flow-ball gate.**  Feeding `gateSqControl_constGate` into the banked ABSTRACT-`S` bundle
    `HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl` (at `S := constGate g gi hChr hK
    c`), the two exact census binders of the LIVE order-1 capstone
    (`HDuhamelExportRethread.truncatedDuhamelCore_AT_GATE_FULL`) hold for the CONCRETE flow-ball gate,
    for every small enough gate radius `c ≤ c₀`, from geometry + the SINGLE surviving mainline
    amplitude-smoothness carry `hw`.  The `hgate : GateSqControl` carry is DISCHARGED (no longer
    assumed).

    * `hAdom` (base-point-varying): `∀ τ>0, ∀ p q, |vanVleckGatedWitness … τ p q| ≤
        (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim ((3/2)τ) (p−q)`;
    * `hWDom` (frozen `p=0` window): `∀ τ ∈ (0,τ₀], ∀ z, |vanVleckGatedWitness … τ 0 z| ≤
        CW·gaussDdim (lam·τ) z`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hAdom_hWDom_from_gateSqControl_constGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k : Point n → ℝ)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∃ CW lam : ℝ, 0 ≤ CW ∧ 0 < lam ∧
        (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
          |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ p q|
            ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
        (∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
          |vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b τ (0 : Point n) z|
            ≤ CW * gaussDdim (lam * τ) z) := by
  obtain ⟨c₀, hc₀, hgateOf⟩ := gateSqControl_constGate g gi hChr hK
  refine ⟨c₀, hc₀, fun c hc hcle => ?_⟩
  exact QIQTH.HAdomHWDomFromConcreteDominations.hAdom_hWDom_from_gateSqControl
    g gi hChr hK (constGate g gi hChr hK c) a b ha hab τ₀ hτ₀ hw (hgateOf c hc hcle)

end QIQTH.GateSqControlFromFlowBall

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GateSqControlFromFlowBall
#print axioms gateSqControl_constGate
#print axioms hAdom_hWDom_from_gateSqControl_constGate
end AxiomChecks
