/-
  ConcreteGateResidualization — J4-1143: the K-vs-K₀ mismatch is an ARTIFACT of the `S_∩` fiber-glued
  detour, NOT of the concrete flow-ball gate `S_c`; `tripleHEmeas_concrete_v4`'s `hcarTau`/`hcarField`
  suppliers, instantiated at `S := S_c`, reduce to EXACTLY the raw-chart / derived-witness measurability
  residue (the `hChartRep` wall) — no `K₀` anywhere.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`. It is a
  pure RESIDUALIZATION brick: it instantiates `GatedRepSFix.tripleHEmeas_concrete_v4` at the concrete
  flow-ball gate `S_c z := uniformFlowExp g gi hChr hK z '' Metric.ball 0 c` and discharges its
  `hKSmeas` / `hOffS` / `hOffS2` / `hcarField`'s on-gate `hgate` / `hcarTau`'s `∂_τ HasDerivAt` conjuncts
  from the ALREADY-BANKED §A/§B/§C step lemmas of `OnGateJets` (J4-236) and `OffSVanishing` (J4-235) —
  both of which hold for the FULL `K` (only `hK0 : 0 ∈ K` needed, no `K₀` anywhere). What remains as
  genuine hypotheses is EXACTLY the measurability of the raw chart (`hWmeas`, the shared
  `hChartRep`-style wall, S-INDEPENDENT — literally the same fact regardless of which gate `S` is
  finally chosen) plus the derived-witness measurability conjuncts (`hCfieldMeas`, `hAmpMeas`,
  `hDAmpMeas`, `hPfieldMeas`) for the CONCRETE witnesses `OnGateJets` already names (`fderiv`-built
  `Pfield`, the affine-slope `Cfield`), plus `hcarField2` passed through VERBATIM (its own on-gate
  `hgate` block is a genuinely separate, S-independent "global-in-the-field-point-`y`" wall per
  `OnGateJets`'s own header — NOT touched here).

  ## WHY THIS FILE (context — J4-1142's union-gate audit).
  J4-1140–1142 found a genuine `K`-vs-`K₀` domain mismatch for the `S_∩` fiber-glued-family gate
  (`ChartGateConcreteInstantiation`/`ChartGateUniformTube`): its diagonal-cover / tube-containment
  machinery is only established for `q ∈ K₀ ⊊ interior K`, while `hOffS`/`hOffS2` are needed for ALL
  `q ∈ K` (confirmed by a twenty-first `gpt-5.6-sol` (high) consult, done this dispatch: a direct read
  of `AssemblyV7Rethread`/`RightInverseGeneral.a1_R6_assembled_v2'` shows the base/chart-center argument
  IS the outer Duhamel/Levi integration variable — `hgD1`/`hAdom`/`hAzero`/`hBdom`/`hEboundFull` range
  `∀ z, p, q : Point n` over plain unrestricted `volume`, so `K` genuinely must be as large as the
  integration domain calls for, NOT the tiny IFT-margin `K₀`). Sol's proposed fix was a union gate
  `S⁺ := S_∩ ∪ S_c`.

  A SECOND direct-read cross-check (this file), presented to a twenty-second `gpt-5.6-sol` (high)
  consult, found that `OffSVanishing.lean` (J4-235) and `OnGateJets.lean` (J4-236) — BOTH built
  chronologically BEFORE the `S_∩` detour (J4-1122+), directly against `S_c` (not `S_∩`) — ALREADY
  discharge `hKSmeas`/`hOffS`/`hOffS2`/`hcarField`'s on-gate `hgate`/`hcarTau`'s `∂_τ HasDerivAt` for
  the FULL `K` with NO `K₀` restriction whatsoever. Sol's verdict (2026-08-24, this dispatch): the
  union gate `S⁺` is POINTLESS for these conjuncts (`S_c` alone already covers them at full `K`;
  unioning with `S_∩` can only make the ON-gate obligations STRICTLY HARDER, since it forces handling
  every point of `S_∩` too); the genuinely open residues — (i) the raw-chart joint-measurability
  `hChartRep` wall and (ii) `hcarField2`'s global-in-`y` on-gate `hgate` block — are BOTH
  S-INDEPENDENT (exactly as open whether `S := S_c`, `S := S_∩`, or `S := S⁺`), so the `S_∩`
  fiber-glued detour is NOT currently load-bearing progress toward either residue absent an explicit
  bridge from "measurable on `S_∩`" to the LITERAL unconditional/global `hcarTau`/`hcarField`
  measurability conjunct (which `S_∩`'s own gated/fiberwise construction does not supply).
  Recommendation: drop the union-gate construction; bank one compile-checked residualization theorem
  cutting the dependency at exactly the genuine residues; retarget effort to walls (i)/(ii) directly.
  This file is that residualization theorem.

  ## WHAT LANDS.
    `tripleHEmeas_concrete_v4_residual_at_flowBallGate` — for the concrete flow-ball gate (any radius
    `c` with `b < c < δ₀`, `δ₀` the shared radius from `OnGateJets`'s step lemmas), GIVEN the raw-chart
    measurability `hWmeas` (S-independent, the `hChartRep` wall) and the four derived-witness
    measurability facts for the CONCRETE `Cfield`/`Pfield` witnesses `OnGateJets` names, PLUS
    `hcarField2` passed through verbatim (untouched, genuinely open, quantified over every admissible
    radius `c`), the conclusion of `tripleHEmeas_concrete_v4` holds at `S := S_c`. NO `K₀`, NO `S_∩`,
    NO union gate anywhere in the statement or proof. This is a strict NARROWING of the open surface:
    before this file, closing `tripleHEmeas_concrete_v4` at any gate needed
    `hKSmeas`+`hOffS`+`hOffS2`+ALL of `hcarField`'s on-gate content+ALL of `hcarTau`, PLUS the
    measurability walls; after this file, at `S := S_c`, only the measurability walls
    (`hWmeas`/`hCfieldMeas`/`hAmpMeas`/`hDAmpMeas`/`hPfieldMeas`) and `hcarField2` remain.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GatedRepSFix
import QIQTH.OnGateJets

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GatedRepSFix QIQTH.OnGateJets QIQTH.OffSVanishing
open scoped Topology BigOperators ContDiff

namespace QIQTH.ConcreteGateResidualization

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The residualization theorem.
    ############################################################################### -/

/-- **★★★ J4-1143 — `tripleHEmeas_concrete_v4_residual_at_flowBallGate`.**  See file header. -/
theorem tripleHEmeas_concrete_v4_residual_at_flowBallGate
    (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ y : Point n, 0 < Matrix.det (g y))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgi : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ★ the residue: raw-chart joint measurability (the `hChartRep` wall, S-independent).
    (hWmeas : Measurable
      (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1))
    -- ★ the residue: derived-witness measurability for `hcarTau`/`hcarField`'s concrete witnesses.
    (hAmpMeas : Measurable
      (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1))
    (hCfieldMeas : Measurable
      (fun w : ℝ × Point n × Point n =>
        radialCutoff a b (uniformInverseChart g gi hChr hK w.2.2 w.2.1)
          * (vanVleck g (uniformInverseChart g gi hChr hK w.2.2 w.2.1) ^ (-(1 : ℝ) / 2)
              * transportCoeff (transportOp (vanVleck g) g gi) 1
                  (uniformInverseChart g gi hChr hK w.2.2 w.2.1))))
    (hDAmpMeas : ∀ k : Fin n, Measurable
      (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hPfieldMeas : ∀ k j : Fin n, Measurable
      (fun w : ℝ × Point n × Point n =>
        fderiv ℝ (uniformInverseChart g gi hChr hK w.2.2) w.2.1 (Pi.single k (1 : ℝ)) j))
    -- ★ `hcarField2` passed through verbatim (∀ admissible radius `c`) — a genuinely separate,
    --   S-independent open wall (untouched by this file).
    (hcarField2 : ∀ c : ℝ, b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
              w.2.1 ∈ uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c →
            IsOpen (uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
              w.2.1 ∉ uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c →
            pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK
                (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c)
                a b w.1 x w.2.2) j y) i w.2.1 = 0)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, b < c → c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
        (vanVleckGatedWitness g gi hChr hK
          (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) a b) := by
  -- shared radius from the on-gate/off-gate/measurability step lemmas.
  obtain ⟨δr, hδr, hreach⟩ := QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hChr hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hChr hK
  obtain ⟨δc, hδc, hcollar⟩ := witness_eventuallyEq_zero_offGate g gi hChr hK a b ha hab
  obtain ⟨δm, hδm, hmeas⟩ := QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hChr hK
  refine ⟨min δr (min δo (min δc δm)), lt_min hδr (lt_min hδo (lt_min hδc hδm)), ?_⟩
  intro c hbc hcδ
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδo : c < δo := lt_of_lt_of_le hcδ ((min_le_right _ _).trans (min_le_left _ _))
  have hcδc : c < δc := lt_of_lt_of_le hcδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c with hSdef
  -- `hOffS`/`hOffS2` at `S`, full `K`.
  have hOffS : ∀ (k : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
      witnessFieldDeriv g gi hChr hK S a b k w.1 w.2.1 w.2.2 = 0 := by
    obtain ⟨δ', hδ', hoff1⟩ := hOffS_concrete g gi hChr hK a b ha hab
    -- reuse the SAME collar witness at radius `min δr (min δo δc)`; recompute directly instead.
    intro k w hzK hτ hpS
    have hEq := hcollar c hbc hcδc S hSdef w.1 w.2.2 hzK w.2.1 hpS
    show pd (fun x' => vanVleckGatedWitness g gi hChr hK S a b w.1 x' w.2.2) k w.2.1 = 0
    rw [pd_congr_of_eventuallyEq _ _ k w.2.1 hEq]
    exact pd_zero_fun k w.2.1
  have hOffS2 : ∀ (i j : Fin n) (w : ℝ × Point n × Point n), w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
      pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) j y) i w.2.1
        = 0 := by
    intro i j w hzK hτ hpS
    have hEq := hcollar c hbc hcδc S hSdef w.1 w.2.2 hzK w.2.1 hpS
    have hEq2 : (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) j y)
        =ᶠ[nhds w.2.1] (fun _ => 0) := by
      have hnest := (eventually_eventually_nhds (p := fun x =>
        (fun x => vanVleckGatedWitness g gi hChr hK S a b w.1 x w.2.2) x = (fun _ => (0 : ℝ)) x)).mpr hEq
      filter_upwards [hnest] with y hy
      rw [pd_congr_of_eventuallyEq _ _ j y hy]
      exact pd_zero_fun j y
    rw [pd_congr_of_eventuallyEq _ _ i w.2.1 hEq2]
    exact pd_zero_fun i w.2.1
  -- `hcarTau` at `S`, full `K` — closed-form `Cfield` matching `hCfieldMeas`.
  have hcarTauVal : ∃ Cfield : Point n → Point n → ℝ,
      Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
      ∧ Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
      ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
      ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
          HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
            (Cfield w.2.2 w.2.1) w.1) := by
    refine ⟨fun q p =>
      radialCutoff a b (uniformInverseChart g gi hChr hK q p)
        * (vanVleck g (uniformInverseChart g gi hChr hK q p) ^ (-(1 : ℝ) / 2)
            * transportCoeff (transportOp (vanVleck g) g gi) 1
                (uniformInverseChart g gi hChr hK q p)), hWmeas, hAmpMeas, hCfieldMeas, ?_⟩
    intro w _ _ _
    exact chartFieldAmp_hasDerivAt_tau g gi hChr hK a b w.2.2 w.2.1 w.1
  -- `hcarField` at `S`, full `K` — closed-form `Pfield` matching `hPfieldMeas`.
  have hcarFieldVal : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
      Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
      ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
      ∧ Measurable
          (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
      ∧ Measurable
          (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
      ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
          IsOpen (S w.2.2) ∧
          (∀ j, HasDerivAt
            (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
            (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
          PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
      ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
          witnessFieldDeriv g gi hChr hK S a b k w.1 w.2.1 w.2.2 = 0) := by
    intro k
    refine ⟨fun q p j => fderiv ℝ (uniformInverseChart g gi hChr hK q) p (Pi.single k (1 : ℝ)) j,
      hWmeas, hPfieldMeas k, hAmpMeas, hDAmpMeas k, ?_, hOffS k⟩
    intro w hzK hτ hpS
    have hSq : S w.2.2 = uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := rfl
    have hpS' : w.2.1 ∈ uniformFlowExp g gi hChr hK w.2.2 '' Metric.ball (0 : Point n) c := by
      rwa [hSq] at hpS
    obtain ⟨v, hv, hvp⟩ := hpS'
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hChr hK w.2.2) w.2.1 := by
      rw [← hvp]; exact hreach w.2.2 hzK v (lt_trans hvc hcδr)
    have hdetp : 0 < Matrix.det (g (uniformInverseChart g gi hChr hK w.2.2 w.2.1)) := hgpos _
    refine ⟨?_, ?_, ?_⟩
    · rw [hSq]; exact (hopen w.2.2 hzK).2 c (lt_trans (lt_trans ha hab) hbc) hcδo |>.1
    · intro j; exact chartFieldFirstJet_hasDerivAt g gi hChr hK w.2.2 w.2.1 k j hCp
    · exact ampField_pdiffAt g gi hChr hK a b w.1 w.2.2 w.2.1 k hg hu hCp hdetp
  -- `hKSmeas` at `S`, full `K` — `ConcreteGateInstantiation.hKSmeas_concrete`.
  have hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} :=
    hmeas c hc0 hcδm
  exact tripleHEmeas_concrete_v4 hn g gi hChr hK S a b hKSmeas hcarTauVal hcarFieldVal
    (hcarField2 c hbc) hgi hchr

end QIQTH.ConcreteGateResidualization

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ConcreteGateResidualization
#print axioms tripleHEmeas_concrete_v4_residual_at_flowBallGate
end AxiomChecks
