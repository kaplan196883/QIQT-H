/-
  ChartRepFinal — J4-238: the hChartRep DECISION BRICK (the last v7 supplier obligation, audited).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is the
  measurability-conjunct audit + the value-side discharges of the three v7 supplier existentials
  (`hcarTau` / `hcarField` / `hcarField2`).  No `sorry` (prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypotheses.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE STANDING (post J4-234..237).  Every derivative / jet / on-gate / off-gate conjunct of the
  three v7 supplier existentials is discharged at the concrete flow-ball gate
  (`Field2NbhdReshape.concreteGate_carriers_discharged_v4`).  The ONE remaining obligation is the
  MEASURABILITY block.  This file audits it CONJUNCT BY CONJUNCT and lands the value-side discharges.

  ## ★ THE PER-CONJUNCT AUDIT VERDICT.  Each of the three existentials (as consumed by
  `GatedRepSFix.tripleHEmeas_concrete_v4`, resp. `HgateSatAudit.tauDeriv_prod_stronglyMeasurable_v4`)
  carries a fixed list of MEASURABILITY conjuncts.  Classifying each:

    (1)  `Measurable (fun w => uniformInverseChart g gi hC hK w.2.2 w.2.1)`  — the RAW joint chart.
         VERDICT = **SWAPPABLE**.  Globally UNPROVABLE (`.choose` junk off the flow image;
         `ChartRepConstruction` firewall), but ELIMINABLE: on the S-gate `{w.2.1 ∈ S w.2.2}` the chart
         agrees with the banked measurable `Gc` (`ImageSupportDischarge.hWG_gate_concrete` — the
         S-MEMBERSHIP guard makes the image-support obligation PURE RADII, NO surjectivity wall).  The
         `Gc`-substituted S-gated representative is measurable from `Measurable Gc` alone; the raw-chart
         conjunct is replaced by `(Measurable Gc ∧ hWG-S-guard-agreement)`.  This is the combined S+Gc
         route = `GatedChartMeasAudit`'s v2 chart-drop composed with the SATISFIABLE S-gate of
         `GatedRepSFix` (v2 alone uses the AMPLITUDE guard, needing the surjectivity wall; the S-guard
         of `hWG_gate_concrete` avoids it).

    (2)  `Measurable (fun w => chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1)`  — the amplitude VALUE
         (and `Measurable (Cfield …)` = the amplitude's `∂_τ`, a chart-VALUE quantity).
         VERDICT = **SWAPPABLE** (a chart-VALUE, no field derivative).  `chartFieldAmp` is a CONTINUOUS
         function of the chart value `W z x'` alone (`radialCutoff · vanVleck^{-½} · (tc₀ + tc₁·τ)`).
         Off the gate this is `.choose` junk, but ON the S-gate `W = Gc`, so it equals the
         `Gc`-composed amplitude `chartFieldAmpGc`, which is GLOBALLY measurable from `Measurable Gc`
         + the BANKED continuities (`CoeffContWdiffLift.vanVleck_continuous`, `vanVleck_ne_zero`,
         `huc_discharged`; `SmoothCutoff.radialCutoff_contDiff`).  §A/§B land exactly this: the
         `Gc`-amplitude measurability + the on-gate agreement.  Ditto `Cfield` (§C).

    (3)  `∀ j, Measurable (fun w => Pfield/Pifield/Pjfield/Qfield w.2.2 w.2.1 j)` — the chart FIELD JETS,
         and `Measurable (fun w => pd (chartFieldAmp …) k w.2.1)` (+ mixed `pd_i pd_j`) — the amplitude
         FIELD DERIVATIVES.
         VERDICT = **LITERAL-RAW residue.**  These are FIELD DERIVATIVES of the chart / amplitude, NOT
         chart values.  A merely-MEASURABLE `Gc` (Lusin–Souslin, value-only) does NOT expose a
         derivative, so the value-side swap of (1)/(2) does NOT reach them: `pd(chartFieldAmp)` and the
         jets `P` genuinely require the measurable joint FIELD-DERIVATIVE of the flow inverse — a
         Lusin–Souslin construction ONE LAYER BEYOND the banked value-only
         `ChartRepConstruction.flowInverse_jointMeasurable_regional`.  This is the precisely-named
         residue.  (It is plausibly attackable by the difference-quotient route — on the OPEN gate the
         chart is `C²` and its field-derivative is a pointwise limit of `Gc`-difference-quotients,
         hence measurable — but that is a separate construction, NOT discharged here.)

  ## CONSEQUENCE FOR THE PAYOFF.  Because conjunct class (3) is a genuine residue, the three v4/v3
  existentials are NOT fully witnessable at the concrete gate as currently SHAPED (they demand GLOBAL
  raw measurabilities that are `.choose`-tied).  The honest closable target is a v5/v6 assembly whose
  S-gated `Gc`-substituted representatives demand only: `Measurable Gc` (banked), the `Gc`-amplitude /
  `Gc`-`Cfield` measurabilities (§A/§C, landed here), and the FIELD-JET measurabilities (residue (3)).
  This file discharges the VALUE half and isolates residue (3) — it does NOT re-shape the ~130-binder
  capstone (kernel-freeze avoidance).

  ## WHAT LANDS.
    §A — `chartFieldAmpGc` (the `Gc`-composed amplitude) + `chartFieldAmpGc_prod_measurable`
         (globally measurable from `Measurable Gc` + banked continuities).
    §B — `chartFieldAmp_eq_chartFieldAmpGc_of_agree` (pointwise, under `W = Gc`) +
         `chartFieldAmp_eq_chartFieldAmpGc_on_gate` (∃ ρ, Gc measurable, on the concrete S-gate the raw
         amplitude EQUALS the measurable `Gc`-amplitude) — the amplitude-VALUE swap, DISCHARGED.
    §C — `chartTauAmpGc` (the `Gc`-composed `∂_τ` amplitude `Cfield`) + `chartTauAmpGc_prod_measurable`
         + `chartFieldTauAmp_eq_chartTauAmpGc_of_agree` — the `Cfield`-VALUE swap, DISCHARGED.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ImageSupportDischarge
import QIQTH.CoeffContWdiffLift
import QIQTH.NormalFormDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open scoped Topology ContDiff

namespace QIQTH.ChartRepFinal

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the `Gc`-composed amplitude and its JOINT measurability (conjunct (2), VALUE half).
    ############################################################################### -/

/-- **`chartFieldAmpGc` — the `Gc`-substituted field amplitude.**  Verbatim `chartFieldAmp` with the
    inverse chart value `uniformInverseChart g gi hC hK z x'` replaced by a joint representative
    `Gc (z, x')`.  On the flow image (where `W = Gc`) it equals `chartFieldAmp`; unlike `chartFieldAmp`
    it is a CONTINUOUS-in-`Gc` composition, hence globally measurable from `Measurable Gc`.
    NOT `a₁ = R/6`. -/
noncomputable def chartFieldAmpGc (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (Gc : Point n × Point n → Point n) (τ : ℝ) (z x' : Point n) : ℝ :=
  radialCutoff a b (Gc (z, x'))
    * (vanVleck g (Gc (z, x')) ^ (-(1 : ℝ) / 2)
        * (transportCoeff (transportOp (vanVleck g) g gi) 0 (Gc (z, x'))
          + transportCoeff (transportOp (vanVleck g) g gi) 1 (Gc (z, x')) * τ))

/-- **★★ `chartFieldAmpGc_prod_measurable` — the amplitude VALUE, `Gc`-route, GLOBALLY measurable.**
    The joint `(τ, z, p)`-Borel measurability of the `Gc`-composed amplitude, from `Measurable Gc` and
    the BANKED continuities of the amplitude building blocks: `radialCutoff` (`radialCutoff_contDiff`),
    `vanVleck` (`vanVleck_continuous`, nonvanishing `vanVleck_ne_zero` for the `^(-½)` `rpow`), and the
    transport coefficients (`huc_discharged`).  This is the VALUE-side discharge of the amplitude
    measurability conjunct — the raw off-image `.choose` amplitude is replaced by this genuinely
    measurable twin.  NOT `a₁ = R/6`. -/
theorem chartFieldAmpGc_prod_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) (a b : ℝ)
    (Gc : Point n × Point n → Point n) (hGc : Measurable Gc) :
    Measurable (fun w : ℝ × Point n × Point n => chartFieldAmpGc g gi a b Gc w.1 w.2.2 w.2.1) := by
  -- the joint chart representative `w ↦ Gc (w.2.2, w.2.1)`.
  have hV : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGc.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  -- radialCutoff ∘ Gc.
  have hRC : Measurable
      (fun w : ℝ × Point n × Point n => radialCutoff a b (Gc (w.2.2, w.2.1))) :=
    ((radialCutoff_contDiff a b).continuous.measurable).comp hV
  -- vanVleck^{-½} ∘ Gc  (continuous since vanVleck never vanishes).
  have hVVc : Continuous (fun v : Point n => vanVleck g v ^ (-(1 : ℝ) / 2)) :=
    (QIQTH.CoeffContWdiffLift.vanVleck_continuous g hg hgpos).rpow_const
      (fun v => Or.inl (QIQTH.CoeffContWdiffLift.vanVleck_ne_zero g hgpos v))
  have hVV : Measurable
      (fun w : ℝ × Point n × Point n => vanVleck g (Gc (w.2.2, w.2.1)) ^ (-(1 : ℝ) / 2)) :=
    hVVc.measurable.comp hV
  -- transport coefficients ∘ Gc.
  have htc0 : Measurable
      (fun w : ℝ × Point n × Point n =>
        transportCoeff (transportOp (vanVleck g) g gi) 0 (Gc (w.2.2, w.2.1))) :=
    ((QIQTH.CoeffContWdiffLift.huc_discharged g gi hg hgi hgpos 0).measurable).comp hV
  have htc1 : Measurable
      (fun w : ℝ × Point n × Point n =>
        transportCoeff (transportOp (vanVleck g) g gi) 1 (Gc (w.2.2, w.2.1))) :=
    ((QIQTH.CoeffContWdiffLift.huc_discharged g gi hg hgi hgpos 1).measurable).comp hV
  have hsum : Measurable
      (fun w : ℝ × Point n × Point n =>
        transportCoeff (transportOp (vanVleck g) g gi) 0 (Gc (w.2.2, w.2.1))
          + transportCoeff (transportOp (vanVleck g) g gi) 1 (Gc (w.2.2, w.2.1)) * w.1) :=
    htc0.add (htc1.mul measurable_fst)
  exact hRC.mul (hVV.mul hsum)

/-! ###############################################################################
    ### §B — the on-gate agreement: raw amplitude = `Gc`-amplitude where the chart = `Gc`.
    ############################################################################### -/

/-- **`chartFieldAmp_eq_chartFieldAmpGc_of_agree` — pointwise value swap.**  Wherever the inverse chart
    value equals the joint representative, `W z x' = Gc (z, x')`, the raw amplitude equals its
    `Gc`-composed twin.  Pure substitution (both sides are the SAME continuous function of the chart
    value).  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_eq_chartFieldAmpGc_of_agree (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z x' : Point n)
    (Gc : Point n × Point n → Point n)
    (hagree : uniformInverseChart g gi hC hK z x' = Gc (z, x')) :
    chartFieldAmp g gi hC hK a b τ z x' = chartFieldAmpGc g gi a b Gc τ z x' := by
  simp only [chartFieldAmp, chartFieldAmpGc, hagree]

/-- **★★ `chartFieldAmp_eq_chartFieldAmpGc_on_gate` — the amplitude-VALUE swap, DISCHARGED on the
    concrete gate.**  From the banked S-membership guarded agreement (`ImageSupportDischarge`), there is
    a uniform radius `ρ > 0` and a GLOBALLY MEASURABLE joint `Gc` such that, for every ball radius
    `c ≤ ρ`, at every base `q ∈ K` and every field point in the concrete flow-ball gate
    `φ_q '' Metric.ball 0 c`, the raw amplitude equals the (globally measurable) `Gc`-amplitude.
    Composed with `chartFieldAmpGc_prod_measurable`, this ELIMINATES the raw off-image amplitude
    measurability on the gate — the VALUE-side discharge of conjunct (2).  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_eq_chartFieldAmpGc_on_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ Gc : Point n × Point n → Point n, Measurable Gc ∧
      ∀ c : ℝ, c ≤ ρ → ∀ (τ : ℝ) (q x' : Point n), q ∈ K →
        x' ∈ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c →
        chartFieldAmp g gi hC hK a b τ q x' = chartFieldAmpGc g gi a b Gc τ q x' := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hagree⟩ := QIQTH.ImageSupportDischarge.hWG_gate_concrete g gi hC hK
  refine ⟨ρ, hρ, Gc, hGmeas, ?_⟩
  intro c hc τ q x' hq hx'
  -- the S-membership guard makes the chart agree with `Gc` at `(τ, x', q)` (pure radii, no wall).
  have hWG := hagree c hc (τ, x', q) hq hx'
  exact chartFieldAmp_eq_chartFieldAmpGc_of_agree g gi hC hK a b τ q x' Gc hWG

/-! ###############################################################################
    ### §C — the `Cfield` (`∂_τ` amplitude) VALUE swap (conjunct (3)'s VALUE sub-case for `hcarTau`).
    ############################################################################### -/

/-- **`chartTauAmpGc` — the `Gc`-substituted `∂_τ` amplitude.**  The time-derivative of `chartFieldAmp`
    (affine in `τ`), `Gc`-substituted: `radialCutoff · vanVleck^{-½} · tc₁`.  A chart-VALUE quantity (no
    field derivative), hence globally measurable from `Measurable Gc`.  NOT `a₁ = R/6`. -/
noncomputable def chartTauAmpGc (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (Gc : Point n × Point n → Point n) (z x' : Point n) : ℝ :=
  radialCutoff a b (Gc (z, x'))
    * (vanVleck g (Gc (z, x')) ^ (-(1 : ℝ) / 2)
        * transportCoeff (transportOp (vanVleck g) g gi) 1 (Gc (z, x')))

/-- **★ `chartTauAmpGc_prod_measurable` — the `∂_τ` amplitude VALUE, `Gc`-route, GLOBALLY measurable.**
    Same composition as `chartFieldAmpGc_prod_measurable`, one transport coefficient (`tc₁`), no `τ`.
    NOT `a₁ = R/6`. -/
theorem chartTauAmpGc_prod_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) (a b : ℝ)
    (Gc : Point n × Point n → Point n) (hGc : Measurable Gc) :
    Measurable (fun w : ℝ × Point n × Point n => chartTauAmpGc g gi a b Gc w.2.2 w.2.1) := by
  have hV : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGc.comp (measurable_snd.snd.prodMk measurable_snd.fst)
  have hRC : Measurable
      (fun w : ℝ × Point n × Point n => radialCutoff a b (Gc (w.2.2, w.2.1))) :=
    ((radialCutoff_contDiff a b).continuous.measurable).comp hV
  have hVVc : Continuous (fun v : Point n => vanVleck g v ^ (-(1 : ℝ) / 2)) :=
    (QIQTH.CoeffContWdiffLift.vanVleck_continuous g hg hgpos).rpow_const
      (fun v => Or.inl (QIQTH.CoeffContWdiffLift.vanVleck_ne_zero g hgpos v))
  have hVV : Measurable
      (fun w : ℝ × Point n × Point n => vanVleck g (Gc (w.2.2, w.2.1)) ^ (-(1 : ℝ) / 2)) :=
    hVVc.measurable.comp hV
  have htc1 : Measurable
      (fun w : ℝ × Point n × Point n =>
        transportCoeff (transportOp (vanVleck g) g gi) 1 (Gc (w.2.2, w.2.1))) :=
    ((QIQTH.CoeffContWdiffLift.huc_discharged g gi hg hgi hgpos 1).measurable).comp hV
  exact hRC.mul (hVV.mul htc1)

/-- **`chartFieldTauAmp_eq_chartTauAmpGc_of_agree` — the `∂_τ`-amplitude value swap.**  Wherever
    `W z x' = Gc (z, x')`, the raw `∂_τ` amplitude coefficient equals its `Gc` twin.  The raw
    coefficient is `radialCutoff · vanVleck^{-½} · tc₁` at the chart value; pure substitution.
    NOT `a₁ = R/6`. -/
theorem chartFieldTauAmp_eq_chartTauAmpGc_of_agree (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (z x' : Point n)
    (Gc : Point n × Point n → Point n)
    (hagree : uniformInverseChart g gi hC hK z x' = Gc (z, x')) :
    radialCutoff a b (uniformInverseChart g gi hC hK z x')
        * (vanVleck g (uniformInverseChart g gi hC hK z x') ^ (-(1 : ℝ) / 2)
            * transportCoeff (transportOp (vanVleck g) g gi) 1
                (uniformInverseChart g gi hC hK z x'))
      = chartTauAmpGc g gi a b Gc z x' := by
  simp only [chartTauAmpGc, hagree]

end QIQTH.ChartRepFinal

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ChartRepFinal
#print axioms chartFieldAmpGc_prod_measurable
#print axioms chartFieldAmp_eq_chartFieldAmpGc_of_agree
#print axioms chartFieldAmp_eq_chartFieldAmpGc_on_gate
#print axioms chartTauAmpGc_prod_measurable
#print axioms chartFieldTauAmp_eq_chartTauAmpGc_of_agree
end AxiomChecks
