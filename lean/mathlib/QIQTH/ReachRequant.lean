/-
  ReachRequant — J4-599 (part 1): the JET-REACH δ₀ of the S1/`tripleHEmeas` supplier chain
  REQUANTIFIED BEFORE the cutoff parameters `(a, b)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the J4-598 residual).  The banked S1 chain
  (`JetsGcUnification.tripleHEmeas_Gc_concrete` → `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry`
  → `ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE`) produces its jet reach `δ₀` AFTER the
  cutoff parameters `(a, b)` (`∀ a b, ∃ δ₀, …`), while the heatOp domination pkg
  (`CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg`) produces `(a, b, c)` by its own independent
  ∃-chain — so nothing banked could compare the pkg's gate radius `c` with `δ₀(a,b)`, and J4-598's
  `curved_hBdom_of_reach` carried the OPEN arithmetic antecedent `c < δ₀`.

  ── ★★ THE δ₀-PROVENANCE AUDIT (this brick's verified finding).  In EVERY member of the supplier
  chain, the produced reach is a `min` of radii obtained from `(a,b)`-FREE geometry lemmas only:
      • `ImageSupportDischarge.hWG_gate_concrete`              (guarded chart agreement `ρ`),
      • `ConcreteGateInstantiation.hKSmeas_concrete`           (gate-set measurability `δm`),
      • `ChartFieldC2General.chartField_contDiffAt_reachable_uniform` (chart `C²` reach `δr`),
      • `UniformChartRadius.uniformInverseChart_huniformChart` (chart germ/openness reach `δo`),
      • `FlowDerivMeasurable.flowInverse(Second)Jet_measurable_component` (per-direction jet radii);
  the cutoff parameters `(a, b)` enter ONLY the per-`c` bodies (amplitude values, cutoff supports),
  NEVER the radius production.  Hence the honest ∃∀-swap is PROVABLE by replaying each supplier with
  the radius `obtain`s hoisted above `(a, b)` — which is exactly what this file does, level by level,
  ending at `tripleHEmeas_flowball_requant`:
      `∃ δ₀ > 0, ∀ a b, 0 < a → a < b → ∀ c, b < c → c < δ₀ → tripleHEmeas … (flowball gate c) a b`
  — the S1 jet reach available BEFORE the gate parameters.  Part 2 (`CurvedA1ReachAlign`) feeds this
  δ₀ into the pkg's prescribed radius ceiling, closing the `c < δ₀` reach antecedent for real.

  Every proof below is a hoisted replay of the corresponding banked theorem (named in each
  docstring); no new mathematical content, no new axioms, no `sorry`, no `:= True`.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`.  This file only re-quantifies PROVED measurability suppliers;
  the transport-coefficient smoothness `hu` remains the carried labelled geometric input, and the
  a₁ capstone still owes its census/domination piles, convergence trio, `hmassone` pre-ρ carriers
  and `hjets` residual.  Nothing here touches the `R/6` value.
-/
import Mathlib
import QIQTH.JetsGcUnification

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.RadialDistance QIQTH.RNCDecay
open scoped Topology BigOperators ContDiff

namespace QIQTH.ReachRequant

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1 — the amplitude-`Gc` agreement, radius before `(a,b)`
    (hoisted replay of `ChartRepFinal.chartFieldAmp_eq_chartFieldAmpGc_on_gate` /
     `AmpPdComposition.exists_measurable_ampGc`). -/

/-- **★ J4-599 (R1) — `ampGc_agree_requant`.**  The `Gc`-amplitude agreement radius of
    `AmpPdComposition.exists_measurable_ampGc`, requantified BEFORE `(a, b)`: a single `ρ > 0` and a
    single measurable joint chart representative `Gc` (both from the `(a,b)`-free
    `ImageSupportDischarge.hWG_gate_concrete`) such that for EVERY `(a, b)` the `Gc`-composed
    amplitude twin is measurable and agrees with the raw amplitude on every flow-ball gate of radius
    `c ≤ ρ`.  NOT `a₁ = R/6`. -/
theorem ampGc_agree_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∃ ρ > (0 : ℝ), ∃ Gc : Point n × Point n → Point n, Measurable Gc ∧
      (∀ c : ℝ, c ≤ ρ →
        ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
          w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
          uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1)) ∧
      ∀ a b : ℝ,
        Measurable (fun w : ℝ × Point n × Point n =>
          QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc w.1 w.2.2 w.2.1)
        ∧ ∀ c : ℝ, c ≤ ρ → ∀ (τ : ℝ) (q x' : Point n), q ∈ K →
            x' ∈ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c →
            chartFieldAmp g gi hC hK a b τ q x'
              = QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc τ q x' := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hWG⟩ := QIQTH.ImageSupportDischarge.hWG_gate_concrete g gi hC hK
  refine ⟨ρ, hρ, Gc, hGmeas, hWG, ?_⟩
  intro a b
  refine ⟨QIQTH.ChartRepFinal.chartFieldAmpGc_prod_measurable g gi hg hgi hgpos a b Gc hGmeas, ?_⟩
  intro c hc τ q x' hq hx'
  exact QIQTH.ChartRepFinal.chartFieldAmp_eq_chartFieldAmpGc_of_agree g gi hC hK a b τ q x' Gc
    (hWG c hc (τ, x', q) hq hx')

/-! ### §2 — the `Gc`/`AmpGc` supplier bundle, radius before `(a,b)`
    (hoisted replay of `AmpPdComposition.concreteGate_ampPd_Gc_supplier_FINAL`). -/

/-- **★★ J4-599 (R2) — `ampPd_Gc_supplier_requant`.**  Hoisted replay of
    `AmpPdComposition.concreteGate_ampPd_Gc_supplier_FINAL`: the single uniform radius `δ₀ > 0` now
    quantified BEFORE `(a, b)`.  Radius = `min` of the `(a,b)`-free `hWG_gate_concrete` and
    `hKSmeas_concrete` radii; `(a, b)` enter only the amplitude twin's VALUE.  NOT `a₁ = R/6`. -/
theorem ampPd_Gc_supplier_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ (Gc : Point n × Point n → Point n) (AmpGc : ℝ → Point n → Point n → ℝ),
          MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          ∧ Measurable Gc
          ∧ Measurable (fun w : ℝ × Point n × Point n => AmpGc w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = AmpGc w.1 w.2.2 w.2.1) := by
  classical
  obtain ⟨ρ, hρ, Gc, hGmeas, hWG, hAmp⟩ := ampGc_agree_requant g gi hC hK hg hgi hgpos
  obtain ⟨δm, hδm, hKSm⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  refine ⟨min ρ δm, lt_min hρ hδm, ?_⟩
  intro a b c hc0 hcδ S hSeq
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (min_le_left _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  obtain ⟨hAGmeas, hAGagree⟩ := hAmp a b
  have hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := by
    have hset : {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
        = {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧
            w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c} := by
      simp only [hSeq]
    rw [hset]; exact hKSm c hc0 hcδm
  refine ⟨Gc, QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc, hKSmeas, hGmeas, hAGmeas, ?_, ?_⟩
  · intro w hqK hpS
    have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
        rw [hSeq]
      rwa [hSq] at hpS
    exact hWG c hcρ (w.1, w.2.1, w.2.2) hqK hpImg
  · intro w hqK hpS
    have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
        rw [hSeq]
      rwa [hSq] at hpS
    exact hAGagree c hcρ w.1 w.2.2 w.2.1 hqK hpImg

/-! ### §3 — the FIRST amp-`pd` twin, radius before `(a,b)`
    (hoisted replay of `AmpPdComposition.ampFieldPd_measurable`). -/

/-- **★★ J4-599 (R3) — `ampFieldPd_requant`.**  Hoisted replay of
    `AmpPdComposition.ampFieldPd_measurable`: the four availability radii (`hWG` agreement,
    `hKSmeas`, chart `C²` reach, chart openness) are all `(a,b)`-free and now produced BEFORE
    `(a, b, k)`.  NOT `a₁ = R/6`. -/
theorem ampFieldPd_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ (a b : ℝ) (k : Fin n), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Afield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Afield w.1 w.2.2 w.2.1 = pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hWG, hAmp⟩ := ampGc_agree_requant g gi hC hK hg hgi hgpos
  obtain ⟨δm, hδm, hKSm⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min (min ρ δm) (min δr δo), lt_min (lt_min hρ hδm) (lt_min hδr hδo), ?_⟩
  intro a b k c hc0 hcδ S hSeq
  have hcρ : c ≤ ρ :=
    le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hAGmeas, hAGagree⟩ := hAmp a b
  -- discharge the per-point `PdiffAt` of the amplitude field function.
  have hPd : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      PdiffAt ((fun τ q => chartFieldAmp g gi hC hK a b τ q) w.1 w.2.2) k w.2.1 := by
    intro w hqK hpImg
    obtain ⟨v, hv, hvp⟩ := hpImg
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := by
      rw [← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
    exact QIQTH.OnGateJets.ampField_pdiffAt g gi hC hK a b w.1 w.2.2 w.2.1 k hg hu hCp (hgpos _)
  -- the on-gate value swap.
  have hAg : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      ∀ p : Point n, p ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      (fun τ q => chartFieldAmp g gi hC hK a b τ q) w.1 w.2.2 p
        = QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc w.1 w.2.2 p := by
    intro w hqK p hp
    exact hAGagree c hcρ w.1 w.2.2 p hqK hp
  obtain ⟨Afield, hAmeas, hAval⟩ :=
    QIQTH.AmpPdComposition.measurable_dq_witness (uniformFlowExp g gi hC hK) c k
      (fun τ q => chartFieldAmp g gi hC hK a b τ q)
      (fun τ q p => QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc τ q p) hAGmeas
      (hKSm c hc0 hcδm)
      (fun q hq => ((hopen q hq).2 c hc0 hcδo).1) hPd hAg
  refine ⟨Afield, hAmeas, ?_⟩
  intro w hqK hpS
  have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      rw [hSeq]
    rwa [hSq] at hpS
  exact hAval w hqK hpImg

/-! ### §4 — the MIXED SECOND amp-`pd` twin, radius before `(a,b)`
    (hoisted replay of `AmpPdComposition.ampFieldSecondPd_measurable`). -/

/-- **★★ J4-599 (R4) — `ampFieldSecondPd_requant`.**  Hoisted replay of
    `AmpPdComposition.ampFieldSecondPd_measurable`, with the FIRST-witness radius taken from
    `ampFieldPd_requant` (already `(a,b)`-hoisted) and the remaining three radii `(a,b)`-free.
    NOT `a₁ = R/6`. -/
theorem ampFieldSecondPd_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ (a b : ℝ) (i j : Fin n), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Bfield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Bfield w.1 w.2.2 w.2.1
                = pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hspecA⟩ := ampFieldPd_requant g gi hC hK hg hgi hgpos hu
  obtain ⟨δm, hδm, hKSm⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min (min δ₁ δm) (min δr δo), lt_min (lt_min hδ₁ hδm) (lt_min hδr hδo), ?_⟩
  intro a b i j c hc0 hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Afield, hAmeas, hAval⟩ := hspecA a b j c hc0 hcδ₁ S hSeq
  -- per-point `PdiffAt` of the first amp-`pd` field function (second-order regularity).
  have hPd : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      PdiffAt ((fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) w.1 w.2.2) i
        w.2.1 := by
    intro w hqK hpImg
    obtain ⟨v, hv, hvp⟩ := hpImg
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := by
      rw [← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
    have hAmpC2 : ContDiffAt ℝ 2 (chartFieldAmp g gi hC hK a b w.1 w.2.2) w.2.1 :=
      QIQTH.OnGateJets.ampField_contDiffAt g gi hC hK a b w.1 w.2.2 w.2.1 hg hu hCp (hgpos _)
    exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
      (chartFieldAmp g gi hC hK a b w.1 w.2.2) j i w.2.1 hAmpC2
  -- on-gate value swap against the first witness.
  have hAg : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      ∀ p : Point n, p ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      (fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) w.1 w.2.2 p
        = Afield w.1 w.2.2 p := by
    intro w hqK p hp
    exact (hAval (w.1, p, w.2.2) hqK (by rw [hSeq]; exact hp)).symm
  obtain ⟨Bfield, hBmeas, hBval⟩ :=
    QIQTH.AmpPdComposition.measurable_dq_witness (uniformFlowExp g gi hC hK) c i
      (fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) Afield hAmeas
      (hKSm c hc0 hcδm) (fun q hq => ((hopen q hq).2 c hc0 hcδo).1) hPd hAg
  refine ⟨Bfield, hBmeas, ?_⟩
  intro w hqK hpS
  have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      rw [hSeq]
    rwa [hSq] at hpS
  exact hBval w hqK hpImg

/-! ### §5 — the on-gate first-jet `hgate` block, radius before `(a,b)`
    (hoisted replay of `OnGateJets.hcarField_hgate_concrete`). -/

/-- **★★ J4-599 (R5) — `hcarField_hgate_requant`.**  Hoisted replay of
    `OnGateJets.hcarField_hgate_concrete` (radii `δr`, `δo`, both `(a,b)`-free).  NOT `a₁ = R/6`. -/
theorem hcarField_hgate_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
        ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1 := by
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hChr hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hChr hK
  refine ⟨min δr δo, lt_min hδr hδo, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq k
  refine ⟨fun q p j =>
    fderiv ℝ (uniformInverseChart g gi hChr hK q) p (Pi.single k (1 : ℝ)) j, ?_⟩
  intro w hzK hτ hpS
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδo : c < δo := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hSq : S w.2.2 = uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rw [hSeq]
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hpS' : w.2.1 ∈ uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rwa [hSq] at hpS
  obtain ⟨v, hv, hvp⟩ := hpS'
  have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
  have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK w.2.2) w.2.1 := by
    rw [← hvp]; exact hreach w.2.2 hzK v (lt_trans hvc hcδr)
  have hdetp : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w.2.2 w.2.1)) := hgpos _
  refine ⟨?_, ?_, ?_⟩
  · rw [hSq]; exact (hopen w.2.2 hzK).2 c hc0 hcδo |>.1
  · intro j
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hChr hK w.2.2 w.2.1 k j hCp
  · exact QIQTH.OnGateJets.ampField_pdiffAt g gi hChr hK a b w.1 w.2.2 w.2.1 k hg hu hCp hdetp

/-! ### §6 — the off-gate collar + the two off-`S` vanishings, radius before `(a,b)`
    (hoisted replays of `OffSVanishing.witness_eventuallyEq_zero_offGate` /
     `hOffS_concrete` / `hOffS2_concrete`). -/

/-- **★★ J4-599 (R6) — `witness_offGate_requant`.**  Hoisted replay of
    `OffSVanishing.witness_eventuallyEq_zero_offGate` (radius = the `(a,b)`-free chart reach `δ₀` of
    `uniformInverseChart_huniformChart`).  NOT `a₁ = R/6`. -/
theorem witness_offGate_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (τ : ℝ) (q : Point n), q ∈ K → ∀ p : Point n, p ∉ S q →
          (fun x => vanVleckGatedWitness g gi hC hK S a b τ x q) =ᶠ[nhds p] (fun _ => 0) := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq τ q hq p hpS
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hbδ : b < δ₀ := lt_trans hbc hcδ
  obtain ⟨hgerm, hball⟩ := hspec q hq
  obtain ⟨_hOpenb, hclosb⟩ := hball b hb0 hbδ
  have hSq : S q = uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c := by rw [hSeq]
  have hsub : closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b) ⊆ S q := by
    rw [hSq]
    exact hclosb.trans (Set.image_mono (Metric.closedBall_subset_ball hbc))
  set U := (closure (uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b))ᶜ with hUdef
  have hUopen : IsOpen U := isOpen_compl_iff.mpr isClosed_closure
  have hpU : p ∈ U := fun h => hpS (hsub h)
  refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hpU) ?_
  intro x hxU
  have hxNotBall : x ∉ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) b :=
    fun h => hxU (subset_closure h)
  show vanVleckGatedWitness g gi hC hK S a b τ x q = 0
  unfold vanVleckGatedWitness
  by_cases hxS : x ∈ S q
  · rw [gatedKernel_apply_of_mem K S _ τ hq hxS]
    rw [hSq] at hxS
    obtain ⟨v, hv, hvx⟩ := hxS
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hWqv : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
      have hh := ((hgerm v (lt_trans hvc hcδ)).1).eq_of_nhds
      simpa using hh
    have hWqx : uniformInverseChart g gi hC hK q x = v := by rw [← hvx]; exact hWqv
    have hcut0 : radialCutoff a b v = 0 := by
      by_contra hne
      have hlt : rncRadialSq v < b ^ 2 := by
        by_contra hge
        exact hne (radialCutoff_eq_zero ha hab (not_lt.mp hge))
      have hsqle : ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
        mul_le_mul (norm_le_rncRadial v) (norm_le_rncRadial v) (norm_nonneg v)
          (rncRadial_nonneg v)
      have hnv2 : ‖v‖ ^ 2 < b ^ 2 := by
        have hsq := rncRadial_sq v
        nlinarith [hsqle, hlt, hsq]
      have hnvb : ‖v‖ < b := lt_of_pow_lt_pow_left₀ 2 hb0.le hnv2
      exact hxNotBall ⟨v, mem_ball_zero_iff.mpr hnvb, hvx⟩
    unfold globalCutoffParametrixWitnessN
    rw [hWqx, hcut0, zero_mul]
  · rw [gatedKernel_apply_of_notMem K S _ τ x q (Or.inr hxS)]

/-- **★ J4-599 (R7) — `hOffS_requant`.**  Hoisted replay of `OffSVanishing.hOffS_concrete`.
    NOT `a₁ = R/6`. -/
theorem hOffS_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := witness_offGate_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq k w hzK hτ hpS
  have hEq := hcollar a b ha hab c hbc hcδ S hSeq w.1 w.2.2 hzK w.2.1 hpS
  show pd (fun x' => vanVleckGatedWitness g gi hC hK S a b w.1 x' w.2.2) k w.2.1 = 0
  rw [QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq _ _ k w.2.1 hEq]
  exact QIQTH.OffSVanishing.pd_zero_fun k w.2.1

/-- **★ J4-599 (R8) — `hOffS2_requant`.**  Hoisted replay of `OffSVanishing.hOffS2_concrete`.
    NOT `a₁ = R/6`. -/
theorem hOffS2_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y) i w.2.1
            = 0 := by
  obtain ⟨δ₀, hδ₀pos, hcollar⟩ := witness_offGate_requant g gi hC hK
  refine ⟨δ₀, hδ₀pos, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i j w hzK hτ hpS
  have hEq := hcollar a b ha hab c hbc hcδ S hSeq w.1 w.2.2 hzK w.2.1 hpS
  have hEq2 : (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y)
      =ᶠ[nhds w.2.1] (fun _ => 0) := by
    have hnest := (eventually_eventually_nhds (p := fun x =>
      (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) x
        = (fun _ => (0 : ℝ)) x)).mpr hEq
    filter_upwards [hnest] with y hy
    rw [QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq _ _ j y hy]
    exact QIQTH.OffSVanishing.pd_zero_fun j y
  rw [QIQTH.HeatResidualBound.pd_congr_of_eventuallyEq _ _ i w.2.1 hEq2]
  exact QIQTH.OffSVanishing.pd_zero_fun i w.2.1

/-! ### §7 — the on-gate SECOND-jet `hgate` block, radius before `(a,b)`
    (hoisted replay of `Field2NbhdReshape.hcarField2_hgate_concrete`). -/

/-- **★★ J4-599 (R9) — `hcarField2_hgate_requant`.**  Hoisted replay of
    `Field2NbhdReshape.hcarField2_hgate_concrete` (radii `δr`, `δo`, both `(a,b)`-free).
    NOT `a₁ = R/6`. -/
theorem hcarField2_hgate_requant (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            IsOpen (S w.2.2) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1 := by
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min δr δo, lt_min hδr hδo, ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i j
  refine ⟨fun q y k => fderiv ℝ (uniformInverseChart g gi hC hK q) y (Pi.single i (1 : ℝ)) k,
    fun q y k => fderiv ℝ (uniformInverseChart g gi hC hK q) y (Pi.single j (1 : ℝ)) k,
    fun q p k => fderiv ℝ
        (fun y => (fderiv ℝ (uniformInverseChart g gi hC hK q) y) (Pi.single j (1 : ℝ))) p
        (Pi.single i (1 : ℝ)) k, ?_⟩
  intro w hzK hτ hpS
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδo : c < δo := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    rw [hSeq]
  have hC2 : ∀ y ∈ S w.2.2, ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) y := by
    intro y hyS
    have hyS' : y ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      rwa [hSq] at hyS
    obtain ⟨v, hv, hvy⟩ := hyS'
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    rw [← hvy]; exact hreach w.2.2 hzK v (lt_trans hvc hcδr)
  have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := hC2 w.2.1 hpS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSq]; exact (hopen w.2.2 hzK).2 c hc0 hcδo |>.1
  · intro y hyS k
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 y i k (hC2 y hyS)
  · intro y hyS k
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 y j k (hC2 y hyS)
  · intro k
    exact QIQTH.Field2NbhdReshape.chartFieldSecondJet_hasDerivAt g gi hC hK w.2.2 w.2.1 i j hCp k
  · intro y hyS
    exact QIQTH.OnGateJets.ampField_pdiffAt g gi hC hK a b w.1 w.2.2 y j hg hu (hC2 y hyS) (hgpos _)
  · exact QIQTH.OnGateJets.ampField_pdiffAt g gi hC hK a b w.1 w.2.2 w.2.1 i hg hu hCp (hgpos _)
  · exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
      (chartFieldAmp g gi hC hK a b w.1 w.2.2) j i w.2.1
      (QIQTH.OnGateJets.ampField_contDiffAt g gi hC hK a b w.1 w.2.2 w.2.1 hg hu hCp (hgpos _))

/-! ### §8 — the two jet-carrier existentials, radius before `(a,b)`
    (hoisted replays of `JetsGcUnification.hcarField_Gc_concrete` / `hcarField2_Gc_concrete`). -/

/-- **★★ J4-599 (R10) — `hcarField_Gc_requant`.**  Hoisted replay of
    `JetsGcUnification.hcarField_Gc_concrete` with all four leg radii produced before `(a,b)`.
    NOT `a₁ = R/6`. -/
theorem hcarField_Gc_requant (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ k : Fin n, ∃ (Pfield : Point n → Point n → Fin n → ℝ)
          (Afield : ℝ → Point n → Point n → ℝ),
          (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
          ∧ Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 = Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              IsOpen (S w.2.2) ∧
              (∀ jj, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
                (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
              witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- (a) the per-`k` measurable jet twin + on-gate `HasDerivAt`, uniform radius ((a,b)-free).
  obtain ⟨δP, hδP0, hδPspec⟩ := QIQTH.JetsGcUnification.exists_forall_radius
    (fun k c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              ∀ j, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
                (Pfield w.2.2 w.2.1 j) (w.2.1 k)))
    (fun k => QIQTH.FlowDerivMeasurable.flowInverseJet_measurable_component g gi hC hK k)
  -- (b) the amp-`pd` twin radius (R3, already (a,b)-hoisted).
  obtain ⟨δA, hδA0, hδAspec⟩ := ampFieldPd_requant g gi hC hK hg hgi hgpos hu
  -- (c) the on-gate `IsOpen`/`PdiffAt` block radius (R5).
  obtain ⟨δH, hδH0, hδHspec⟩ := hcarField_hgate_requant g gi hC hK hg hgpos hu
  -- (d) the off-`S` vanishing radius (R7).
  obtain ⟨δO, hδO0, hδOspec⟩ := hOffS_requant g gi hC hK
  refine ⟨min (min δP δA) (min δH δO), lt_min (lt_min hδP0 hδA0) (lt_min hδH0 hδO0), ?_⟩
  intro a b ha hab c hbc hcδ S hSeq k
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcP : c < δP := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcA : c < δA := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcH : c < δH := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcO : c < δO := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Pfield, hPmeas, hPgate⟩ := hδPspec c hc0 hcP k S hSeq
  obtain ⟨Afield, hAmeas, hAval⟩ := hδAspec a b k c hc0 hcA S hSeq
  have hH := hδHspec a b ha hab c hbc hcH S hSeq k
  have hO := hδOspec a b ha hab c hbc hcO S hSeq k
  obtain ⟨PfieldH, hHgate⟩ := hH
  refine ⟨Pfield, Afield, hPmeas, hAmeas, ?_, ?_, ?_⟩
  · intro w hqK hpS
    exact (hAval w hqK hpS).symm
  · intro w hqK hτ hpS
    exact ⟨(hHgate w hqK hτ hpS).1, hPgate w hqK hτ hpS, (hHgate w hqK hτ hpS).2.2⟩
  · intro w hqK hτ hpS
    exact hO w hqK hτ hpS

/-- **★★ J4-599 (R11) — `hcarField2_Gc_requant`.**  Hoisted replay of
    `JetsGcUnification.hcarField2_Gc_concrete` with all six leg radii produced before `(a,b)`.
    NOT `a₁ = R/6`. -/
theorem hcarField2_Gc_requant (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∀ i j : Fin n, ∃ (Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ)
          (AfieldI AfieldJ Bfield : ℝ → Point n → Point n → ℝ),
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
          ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
          ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
          ∧ Measurable (fun w : ℝ × Point n × Point n => AfieldI w.1 w.2.2 w.2.1)
          ∧ Measurable (fun w : ℝ × Point n × Point n => AfieldJ w.1 w.2.2 w.2.1)
          ∧ Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 = AfieldI w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j w.2.1 = AfieldJ w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1
                = Bfield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              IsOpen (S w.2.2) ∧
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y i s) k)
                (Pifield w.2.2 y k) (y i)) ∧
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
                (Pjfield w.2.2 y k) (y j)) ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
                (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
              (∀ y ∈ S w.2.2, PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) i w.2.1 ∧
              PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
              pd (fun y => pd (fun x => vanVleckGatedWitness g gi hC hK S a b w.1 x w.2.2) j y)
                  i w.2.1
                = 0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  -- (a) per-pair mixed second-jet block ((a,b)-free).
  obtain ⟨δM, hδM0, hδMspec⟩ := QIQTH.JetsGcUnification.exists_forall_radius
    (fun p : Fin n × Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
          ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              IsOpen (S w.2.2) ∧
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y p.2 s) k)
                (Pjfield w.2.2 y k) (y p.2)) ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 p.1 s) k)
                (Qfield w.2.2 w.2.1 k) (w.2.1 p.1))))
    (fun p => QIQTH.FlowDerivMeasurable.flowInverseSecondJet_measurable_component g gi hC hK p.1 p.2)
  -- (b) per-direction first-jet ∀y block ((a,b)-free, from the `(d,d)` second-jet component).
  obtain ⟨δF, hδF0, hδFspec⟩ := QIQTH.JetsGcUnification.exists_forall_radius
    (fun d : Fin n => fun c => ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y d s) k)
                (Pfield w.2.2 y k) (y d))))
    (fun d => by
      obtain ⟨δ, hδ, hspec⟩ :=
        QIQTH.FlowDerivMeasurable.flowInverseSecondJet_measurable_component g gi hC hK d d
      refine ⟨δ, hδ, fun c hc0 hcδ S hSeq => ?_⟩
      obtain ⟨Pj, Q', hPjm, _hQ'm, hb⟩ := hspec c hc0 hcδ S hSeq
      exact ⟨Pj, hPjm, fun w hqK hτ hpS => (hb w hqK hτ hpS).2.1⟩)
  -- (c) the amp-`pd` twin radius (R3).
  obtain ⟨δA, hδA0, hδAspec⟩ := ampFieldPd_requant g gi hC hK hg hgi hgpos hu
  -- (d) the mixed `pd²` twin radius (R4).
  obtain ⟨δB, hδB0, hδBspec⟩ := ampFieldSecondPd_requant g gi hC hK hg hgi hgpos hu
  -- (e) the `(i,j)`-uniform amplitude `PdiffAt` block radius (R9).
  obtain ⟨δH, hδH0, hδHspec⟩ := hcarField2_hgate_requant g gi hC hK hg hgpos hu
  -- (f) the `(i,j)`-uniform off-`S` vanishing radius (R8).
  obtain ⟨δO, hδO0, hδOspec⟩ := hOffS2_requant g gi hC hK
  refine ⟨min (min (min δM δF) (min δA δB)) (min δH δO),
    lt_min (lt_min (lt_min hδM0 hδF0) (lt_min hδA0 hδB0)) (lt_min hδH0 hδO0), ?_⟩
  intro a b ha hab c hbc hcδ S hSeq i j
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcM : c < δM := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcF : c < δF := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hcA : c < δA := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hcB : c < δB := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hcH : c < δH := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcO : c < δO := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Pjfield, Qfield, hPjmeas, hQmeas, hMblock⟩ := hδMspec c hc0 hcM (i, j) S hSeq
  obtain ⟨Pifield, hPimeas, hFblock⟩ := hδFspec c hc0 hcF i S hSeq
  obtain ⟨AfieldI, hAImeas, hAIval⟩ := hδAspec a b i c hc0 hcA S hSeq
  obtain ⟨AfieldJ, hAJmeas, hAJval⟩ := hδAspec a b j c hc0 hcA S hSeq
  obtain ⟨Bfield, hBmeas, hBval⟩ := hδBspec a b i j c hc0 hcB S hSeq
  have hH := hδHspec a b ha hab c hbc hcH S hSeq i j
  have hO := hδOspec a b ha hab c hbc hcO S hSeq i j
  obtain ⟨PiH, PjH, QH, hHblock⟩ := hH
  refine ⟨Pifield, Pjfield, Qfield, AfieldI, AfieldJ, Bfield,
    hPimeas, hPjmeas, hQmeas, hAImeas, hAJmeas, hBmeas, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hqK hpS; exact (hAIval w hqK hpS).symm
  · intro w hqK hpS; exact (hAJval w hqK hpS).symm
  · intro w hqK hpS; exact (hBval w hqK hpS).symm
  · intro w hqK hτ hpS
    refine ⟨(hMblock w hqK hτ hpS).1, hFblock w hqK hτ hpS,
      (hMblock w hqK hτ hpS).2.1, (hMblock w hqK hτ hpS).2.2,
      (hHblock w hqK hτ hpS).2.2.2.2.1,
      (hHblock w hqK hτ hpS).2.2.2.2.2.1,
      (hHblock w hqK hτ hpS).2.2.2.2.2.2⟩
  · intro w hqK hτ hpS; exact hO w hqK hτ hpS

/-! ### §9 — the S1 triple with the jet reach BEFORE `(a,b)` (hoisted replays of
    `JetsGcUnification.tripleHEmeas_Gc_concrete` /
    `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry`). -/

/-- **★★★ J4-599 (R12) — `tripleHEmeas_requant`.**  THE HOISTED S1 TRIPLE: a single jet reach
    `δ₀ > 0` produced BEFORE the cutoff parameters, such that for ALL `0 < a < b` and every gate
    radius `c ∈ (b, δ₀)` the base joint strong measurability `HEmeasBorelAudit.tripleHEmeas` holds
    for the gated van-Vleck witness at the concrete flow-ball gate.  This is the honest ∃∀-swap of
    `JetsGcUnification.tripleHEmeas_Gc_concrete`, provable because every supplier radius is
    `(a,b)`-free (the audit in the header).  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_requant (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        QIQTH.HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness g gi hC hK S a b) := by
  obtain ⟨δF, hδF0, hδFspec⟩ := ampPd_Gc_supplier_requant g gi hC hK hg hgi hgpos
  obtain ⟨δcF, hδcF0, hδcFspec⟩ := hcarField_Gc_requant hn g gi hC hK hg hgi hgpos hu
  obtain ⟨δcF2, hδcF20, hδcF2spec⟩ := hcarField2_Gc_requant hn g gi hC hK hg hgi hgpos hu
  refine ⟨min δF (min δcF δcF2), lt_min hδF0 (lt_min hδcF0 hδcF20), ?_⟩
  intro a b ha hab c hbc hcδ S hSeq
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hcF : c < δF := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hccF : c < δcF := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hccF2 : c < δcF2 := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Gc, AmpGc, hKSmeas, hGcMeas, hAmpGcMeas, hChartAgree, hAmpAgree⟩ :=
    hδFspec a b c hc0 hcF S hSeq
  have hcarTau := QIQTH.JetsGcUnification.hcarTau_Gc_concrete g gi hC hK S a b hg hgi hgpos
    Gc hGcMeas hChartAgree
  have hcarField := hδcFspec a b ha hab c hbc hccF S hSeq
  have hcarField2 := hδcF2spec a b ha hab c hbc hccF2 S hSeq
  exact QIQTH.GcConsumerMirror.tripleHEmeas_Gc hn g gi hC hK S a b Gc AmpGc hKSmeas hGcMeas
    hAmpGcMeas hChartAgree hAmpAgree hcarTau hcarField hcarField2 hgiMeas hchr

/-- **★★★ J4-599 (R13) — `tripleHEmeas_flowball_requant`.**  The streamlined flow-ball form: the S1
    jet reach `δ₀ > 0` available BEFORE the gate parameters — for ALL `0 < a < b < c < δ₀`, S1 holds
    at the literal constant-radius flow-ball gate.  This is exactly what the pkg-side alignment
    (`CurvedA1ReachAlign`) consumes: prescribe the pkg's radius ceiling `≤ δ₀` and the J4-598 reach
    antecedent `c < δ₀` closes for real.  NOT `a₁ = R/6`. -/
theorem tripleHEmeas_flowball_requant (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), ∀ a b : ℝ, 0 < a → a < b → ∀ c : ℝ, b < c → c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
        (vanVleckGatedWitness g gi hC hK
          (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) := by
  obtain ⟨δ₀, hδ0, hspec⟩ :=
    tripleHEmeas_requant hn g gi hC hK hg hgi hgpos hu hgiMeas hchr
  exact ⟨δ₀, hδ0, fun a b ha hab c hbc hcδ => hspec a b ha hab c hbc hcδ _ rfl⟩

end QIQTH.ReachRequant

/-! ## Axiom checks — std-3 expected (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ReachRequant
#print axioms ampGc_agree_requant
#print axioms ampPd_Gc_supplier_requant
#print axioms ampFieldPd_requant
#print axioms ampFieldSecondPd_requant
#print axioms hcarField_hgate_requant
#print axioms witness_offGate_requant
#print axioms hOffS_requant
#print axioms hOffS2_requant
#print axioms hcarField2_hgate_requant
#print axioms hcarField_Gc_requant
#print axioms hcarField2_Gc_requant
#print axioms tripleHEmeas_requant
#print axioms tripleHEmeas_flowball_requant
end AxiomChecks
