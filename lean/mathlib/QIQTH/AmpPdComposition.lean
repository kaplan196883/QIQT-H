/-
  AmpPdComposition — J4-240: the AMPLITUDE FIELD-`pd` composition (v7 supplier payoff, piece (2)).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It discharges
  the amplitude FIELD-`pd` measurability conjuncts of the three v7 supplier existentials
  (`hcarField` / `hcarField2`), the last VALUE-side residue class isolated by `ChartRepFinal` (J4-238)
  and complementary to the chart FIELD-JETS of `FlowDerivMeasurable` (J4-239).  No `sorry` (prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses.  No existing file is
  edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RESIDUE.  The supplier existentials carry the amplitude field-`pd` measurability conjuncts
  `Measurable (fun w => pd (chartFieldAmp … w.1 w.2.2) k w.2.1)` (and the mixed second
  `pd_i pd_j`).  These are junk off the flow image (the chart is `.choose`), so the RAW conjuncts are
  globally unprovable.  The eliminable route (mirroring `FlowDerivMeasurable`'s field-jets) is the
  DIFFERENCE-QUOTIENT LIMIT of a globally measurable ON-GATE TWIN of the field function, whose value
  equals the true amplitude on the open flow-ball gate.

  ## THE ABSTRACT ENGINE (`measurable_dq_witness`).  The whole difference-quotient machinery is proven
  ONCE over ABSTRACT OPAQUE functions `fld` (the true field function) and `AG` (its measurable on-gate
  twin), so the heavy `chartFieldAmp` def is NEVER unfolded inside the hot tendsto loop (the decisive
  heartbeat firewall).  Both amp-`pd` layers instantiate this single engine.

  ## WHAT LANDS.
    §0 — `exists_measurable_ampGc`  — packages `ChartRepFinal.chartFieldAmpGc` as an OPAQUE measurable
         twin with the on-gate value swap.
         `measurable_dq_witness`     — the abstract difference-quotient measurable-witness engine.
    §A — `ampFieldPd_measurable`        — ★ item 1: the FIRST amp-`pd`, measurable witness + on-gate value.
    §B — `ampFieldSecondPd_measurable`  — ★ item 2: the MIXED SECOND amp-`pd`, one d-q up.

  Radii carried HONESTLY: `0 < c < δ₀`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartRepFinal
import QIQTH.FlowDerivMeasurable
import QIQTH.GatedRepSFix
import QIQTH.LaplaceBeltramiFiniteReg

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open scoped Topology BigOperators ContDiff

namespace QIQTH.AmpPdComposition

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the OPAQUE measurable `Gc`-amplitude twin + the abstract difference-quotient engine.
    ############################################################################### -/

/-- **`exists_measurable_ampGc` — package `chartFieldAmpGc` as an OPAQUE measurable function.**
    Bundles `ChartRepFinal.chartFieldAmpGc_prod_measurable` (global measurability) with
    `chartFieldAmp_eq_chartFieldAmpGc_on_gate` (on-gate value swap) behind an EXISTENTIAL, so the
    downstream difference-quotient loop obtains `AG` as a `Pi`-bound (truly opaque) hypothesis rather
    than an unfolding of the heavy amplitude def.  NOT `a₁ = R/6`. -/
theorem exists_measurable_ampGc (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∃ AG : ℝ → Point n → Point n → ℝ,
      Measurable (fun w : ℝ × Point n × Point n => AG w.1 w.2.2 w.2.1)
      ∧ ∃ ρ > (0 : ℝ), ∀ c : ℝ, c ≤ ρ → ∀ (τ : ℝ) (q x' : Point n), q ∈ K →
          x' ∈ uniformFlowExp g gi hC hK q '' Metric.ball (0 : Point n) c →
          chartFieldAmp g gi hC hK a b τ q x' = AG τ q x' := by
  obtain ⟨ρ, hρ, Gc, hGmeas, hAgree⟩ :=
    QIQTH.ChartRepFinal.chartFieldAmp_eq_chartFieldAmpGc_on_gate g gi hC hK a b
  exact ⟨QIQTH.ChartRepFinal.chartFieldAmpGc g gi a b Gc,
    QIQTH.ChartRepFinal.chartFieldAmpGc_prod_measurable g gi hg hgi hgpos a b Gc hGmeas,
    ρ, hρ, hAgree⟩

/-- **★★ `measurable_dq_witness` — the abstract difference-quotient measurable-witness engine.**
    For ABSTRACT (opaque) functions `fld` (the true `(τ,q)`-parametrised field function) and `AG` (a
    globally measurable twin) that AGREE on the open flow-ball gate, the coordinate-`k` partial
    `pd (fld τ q) k p` admits a GLOBALLY MEASURABLE witness `Afield` agreeing with it on the gate.
    Route: the difference-quotient of `AG` (measurable) converges pointwise on the gate to
    `pd (fld τ q) k p` (via `PdiffAt (fld τ q) k p` + the on-gate value swap + open-gate eventual
    shift), limit taken by `measurable_of_tendsto_metrizable`.  Because `fld`/`AG` are opaque, the heavy
    concrete amplitude is never unfolded here.  NOT `a₁ = R/6`. -/
theorem measurable_dq_witness {K : Set (Point n)}
    (φ : Point n → Point n → Point n) (c : ℝ) (k : Fin n)
    (fld AG : ℝ → Point n → Point n → ℝ)
    (hAGmeas : Measurable (fun w : ℝ × Point n × Point n => AG w.1 w.2.2 w.2.1))
    (hgate_meas : MeasurableSet
        {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c})
    (hopen : ∀ q ∈ K, IsOpen (φ q '' Metric.ball (0 : Point n) c))
    (hPd : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c → PdiffAt (fld w.1 w.2.2) k w.2.1)
    (hAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
        ∀ p : Point n, p ∈ φ w.2.2 '' Metric.ball (0 : Point n) c →
        fld w.1 w.2.2 p = AG w.1 w.2.2 p) :
    ∃ Afield : ℝ → Point n → Point n → ℝ,
      Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
      ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
          w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c →
          Afield w.1 w.2.2 w.2.1 = pd (fld w.1 w.2.2) k w.2.1) := by
  classical
  set gateSet : Set (ℝ × Point n × Point n) :=
    {w | w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c} with hgateSetDef
  set hm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hmdef
  have hm_pos : ∀ m, 0 < hm m := fun m => by
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    simpa [hmdef] using one_div_pos.mpr this
  have hm_tendsto : Tendsto hm atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hsnd2 : Measurable (fun w : ℝ × Point n × Point n => w.2.2) :=
    measurable_snd.comp measurable_snd
  have hfst2 : Measurable (fun w : ℝ × Point n × Point n => w.2.1) :=
    measurable_fst.comp measurable_snd
  set DQw : ℕ → (ℝ × Point n × Point n) → ℝ :=
    fun m w => (AG w.1 w.2.2 (w.2.1 + hm m • Pi.single k (1 : ℝ)) - AG w.1 w.2.2 w.2.1) / hm m
    with hDQwdef
  have hDQw_meas : ∀ m, Measurable (DQw m) := by
    intro m
    simp only [hDQwdef]
    have hσ : Measurable (fun w : ℝ × Point n × Point n =>
        ((w.1, w.2.1 + hm m • Pi.single k (1 : ℝ), w.2.2) : ℝ × Point n × Point n)) :=
      measurable_fst.prodMk ((hfst2.add_const _).prodMk hsnd2)
    exact ((hAGmeas.comp hσ).sub hAGmeas).div_const _
  set seqW : ℕ → (ℝ × Point n × Point n) → ℝ :=
    fun m => gateSet.indicator (DQw m) with hseqWdef
  set trueAmpPd : (ℝ × Point n × Point n) → ℝ :=
    fun w => pd (fld w.1 w.2.2) k w.2.1 with htrueAmpPddef
  set Fw : (ℝ × Point n × Point n) → ℝ := gateSet.indicator trueAmpPd with hFwdef
  have hseqW_meas : ∀ m, Measurable (seqW m) := fun m =>
    (hDQw_meas m).indicator hgate_meas
  have hconv : ∀ w, Tendsto (fun m => seqW m w) atTop (𝓝 (Fw w)) := by
    intro w
    by_cases hw : w ∈ gateSet
    · have hqK : w.2.2 ∈ K := hw.1
      have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw.2
      have hPdw : PdiffAt (fld w.1 w.2.2) k w.2.1 := hPd w hqK hpImg
      have hHD : HasDerivAt (fun s : ℝ => fld w.1 w.2.2 (Function.update w.2.1 k s))
          (pd (fld w.1 w.2.2) k w.2.1) (w.2.1 k) := hPdw.hasDerivAt
      have hslope : Tendsto
          (slope (fun s : ℝ => fld w.1 w.2.2 (Function.update w.2.1 k s)) (w.2.1 k))
          (𝓝[≠] (w.2.1 k)) (𝓝 (pd (fld w.1 w.2.2) k w.2.1)) :=
        hasDerivAt_iff_tendsto_slope.mp hHD
      have hxm_tendsto : Tendsto (fun m => w.2.1 k + hm m) atTop (𝓝[≠] (w.2.1 k)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun m => w.2.1 k + hm m) atTop (𝓝 (w.2.1 k + 0)) :=
            tendsto_const_nhds.add hm_tendsto
          simpa using this
        · exact Eventually.of_forall (fun m =>
            (Set.mem_compl_singleton_iff).mpr (lt_add_of_pos_right _ (hm_pos m)).ne')
      have hslope_seq : Tendsto
          (fun m => slope (fun s : ℝ => fld w.1 w.2.2 (Function.update w.2.1 k s))
              (w.2.1 k) (w.2.1 k + hm m))
          atTop (𝓝 (pd (fld w.1 w.2.2) k w.2.1)) :=
        hslope.comp hxm_tendsto
      have hOpenSet : IsOpen (φ w.2.2 '' Metric.ball (0 : Point n) c) := hopen w.2.2 hqK
      have hshift_tendsto :
          Tendsto (fun m => w.2.1 + hm m • Pi.single k (1 : ℝ)) atTop (𝓝 w.2.1) := by
        have h0 : Tendsto (fun m => hm m • Pi.single k (1 : ℝ)) atTop (𝓝 (0 : Point n)) := by
          simpa using (hm_tendsto.smul_const (Pi.single k (1 : ℝ)))
        have h1 : Tendsto (fun m => w.2.1 + hm m • Pi.single k (1 : ℝ)) atTop
            (𝓝 (w.2.1 + (0 : Point n))) := (tendsto_const_nhds (x := w.2.1)).add h0
        simpa using h1
      have hev_in : ∀ᶠ m in atTop, (w.2.1 + hm m • Pi.single k (1 : ℝ))
          ∈ φ w.2.2 '' Metric.ball (0 : Point n) c :=
        hshift_tendsto.eventually_mem (hOpenSet.mem_nhds hpImg)
      have hAmp_p : fld w.1 w.2.2 w.2.1 = AG w.1 w.2.2 w.2.1 := hAgree w hqK w.2.1 hpImg
      have hev_eq : ∀ᶠ m in atTop,
          slope (fun s : ℝ => fld w.1 w.2.2 (Function.update w.2.1 k s))
            (w.2.1 k) (w.2.1 k + hm m) = DQw m w := by
        filter_upwards [hev_in] with m hm_in
        have hAmp_shift : fld w.1 w.2.2 (w.2.1 + hm m • Pi.single k (1 : ℝ))
            = AG w.1 w.2.2 (w.2.1 + hm m • Pi.single k (1 : ℝ)) :=
          hAgree w hqK (w.2.1 + hm m • Pi.single k (1 : ℝ)) hm_in
        have hupd1 : Function.update w.2.1 k (w.2.1 k + hm m)
            = w.2.1 + hm m • Pi.single k (1 : ℝ) :=
          QIQTH.FlowDerivMeasurable.update_eq_add_smul_single w.2.1 k (hm m)
        have hupd0 : Function.update w.2.1 k (w.2.1 k) = w.2.1 := Function.update_eq_self k w.2.1
        have hsc : (w.2.1 k + hm m) - w.2.1 k = hm m := by ring
        rw [slope_def_field]
        simp only [hDQwdef]
        rw [hsc, hupd1, hupd0, hAmp_shift, hAmp_p]
      have hDQw_conv : Tendsto (fun m => DQw m w) atTop (𝓝 (pd (fld w.1 w.2.2) k w.2.1)) :=
        hslope_seq.congr' hev_eq
      rw [hseqWdef, hFwdef]
      simp only [Set.indicator_of_mem hw]
      rw [htrueAmpPddef]
      exact hDQw_conv
    · rw [hseqWdef, hFwdef]
      simp only [Set.indicator_of_notMem hw]
      exact tendsto_const_nhds
  have hFw_meas : Measurable Fw :=
    measurable_of_tendsto_metrizable hseqW_meas (tendsto_pi_nhds.mpr hconv)
  refine ⟨fun τ q p =>
    (if (q ∈ K ∧ p ∈ φ q '' Metric.ball (0 : Point n) c) then pd (fld τ q) k p else (0 : ℝ)),
    ?_, ?_⟩
  · have hrw : (fun w : ℝ × Point n × Point n =>
        (if (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c)
          then pd (fld w.1 w.2.2) k w.2.1 else (0 : ℝ)))
        = Fw := by
      funext w
      by_cases hw : w ∈ gateSet
      · have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw
        simp only [if_pos hcond, hFwdef, Set.indicator_of_mem hw, htrueAmpPddef]
      · have hcond : ¬ (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c) := hw
        simp only [if_neg hcond, hFwdef, Set.indicator_of_notMem hw]
    rw [hrw]; exact hFw_meas
  · intro w hqK hpImg
    have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := ⟨hqK, hpImg⟩
    simp only [if_pos hcond]

/-! ###############################################################################
    ### §A — the FIRST amplitude field-`pd`, measurable witness.
    ############################################################################### -/

/-- **★★ `ampFieldPd_measurable` — item 1: the measurable FIRST amplitude field-`pd`.**  A single
    uniform radius `δ₀ > 0` such that for every `0 < c < δ₀` and the concrete flow-ball gate, for every
    direction `k` there is a GLOBALLY MEASURABLE amp-`pd` witness `Afield` with:
      • `Measurable (fun w => Afield w.1 w.2.2 w.2.1)`;
      • on the gate, `Afield τ q p = pd (chartFieldAmp … τ q) k p`.
    Instantiates the abstract `measurable_dq_witness` engine with `fld := chartFieldAmp …`, discharging
    the per-point `PdiffAt` from `OnGateJets.ampField_pdiffAt` (chart-`C²` at reachable points) and the
    on-gate value swap from `exists_measurable_ampGc`.  NOT `a₁ = R/6`. -/
theorem ampFieldPd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (k : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Afield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Afield w.1 w.2.2 w.2.1 = pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1) := by
  obtain ⟨AG, hAGmeas, ρ, hρ, hAGagree⟩ :=
    exists_measurable_ampGc g gi hC hK a b hg hgi hgpos
  obtain ⟨δm, hδm, hKSm⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min (min ρ δm) (min δr δo), lt_min (lt_min hρ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ S hSeq
  have hcρ : c ≤ ρ :=
    le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
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
      (fun τ q => chartFieldAmp g gi hC hK a b τ q) w.1 w.2.2 p = AG w.1 w.2.2 p := by
    intro w hqK p hp
    exact hAGagree c hcρ w.1 w.2.2 p hqK hp
  obtain ⟨Afield, hAmeas, hAval⟩ :=
    measurable_dq_witness (uniformFlowExp g gi hC hK) c k
      (fun τ q => chartFieldAmp g gi hC hK a b τ q) AG hAGmeas (hKSm c hc0 hcδm)
      (fun q hq => ((hopen q hq).2 c hc0 hcδo).1) hPd hAg
  refine ⟨Afield, hAmeas, ?_⟩
  intro w hqK hpS
  have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
    rwa [hSq] at hpS
  exact hAval w hqK hpImg

/-! ###############################################################################
    ### §B — the MIXED SECOND amplitude field-`pd`, one difference-quotient up.
    ############################################################################### -/

/-- **★★ `ampFieldSecondPd_measurable` — item 2: the measurable MIXED SECOND amplitude field-`pd`.**
    For every index pair `(i, j)` a single uniform radius `δ₀ > 0` such that for every `0 < c < δ₀` and
    the concrete flow-ball gate there is a GLOBALLY MEASURABLE mixed second amp-`pd` witness `Bfield`
    with:
      • `Measurable (fun w => Bfield w.1 w.2.2 w.2.1)`;
      • on the gate, `Bfield τ q p = pd (fun y => pd (chartFieldAmp … τ q) j y) i p`.
    Instantiates `measurable_dq_witness` in direction `i` with `fld τ q := pd (chartFieldAmp … τ q) j`
    (the FIRST amp-`pd` field function) and `AG := Afield` (the measurable first-witness of
    `ampFieldPd_measurable`); the per-point `PdiffAt` is `PdiffAt_pd_of_contDiffAt` of the amplitude-`C²`
    (`OnGateJets.ampField_contDiffAt`), and the on-gate value swap is the FIRST-witness on-gate value.
    NOT `a₁ = R/6`. -/
theorem ampFieldSecondPd_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i j : Fin n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Bfield : ℝ → Point n → Point n → ℝ,
          Measurable (fun w : ℝ × Point n × Point n => Bfield w.1 w.2.2 w.2.1)
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              Bfield w.1 w.2.2 w.2.1
                = pd (fun y => pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) j y) i w.2.1) := by
  obtain ⟨δ₁, hδ₁, hspecA⟩ := ampFieldPd_measurable g gi hC hK a b j hg hgi hgpos hu
  obtain ⟨δm, hδm, hKSm⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min (min δ₁ δm) (min δr δo), lt_min (lt_min hδ₁ hδm) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨Afield, hAmeas, hAval⟩ := hspecA c hc0 hcδ₁ S hSeq
  -- discharge the per-point `PdiffAt` of the first amp-`pd` field function (second-order regularity).
  have hPd : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      PdiffAt ((fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) w.1 w.2.2) i w.2.1 := by
    intro w hqK hpImg
    obtain ⟨v, hv, hvp⟩ := hpImg
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := by
      rw [← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
    have hAmpC2 : ContDiffAt ℝ 2 (chartFieldAmp g gi hC hK a b w.1 w.2.2) w.2.1 :=
      QIQTH.OnGateJets.ampField_contDiffAt g gi hC hK a b w.1 w.2.2 w.2.1 hg hu hCp (hgpos _)
    exact QIQTH.LaplaceBeltrami.PdiffAt_pd_of_contDiffAt
      (chartFieldAmp g gi hC hK a b w.1 w.2.2) j i w.2.1 hAmpC2
  -- the on-gate value swap: the first witness `Afield` agrees with the first amp-`pd` field function.
  have hAg : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
      ∀ p : Point n, p ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c →
      (fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) w.1 w.2.2 p
        = Afield w.1 w.2.2 p := by
    intro w hqK p hp
    exact (hAval (w.1, p, w.2.2) hqK (by rw [hSeq]; exact hp)).symm
  obtain ⟨Bfield, hBmeas, hBval⟩ :=
    measurable_dq_witness (uniformFlowExp g gi hC hK) c i
      (fun τ q => fun y => pd (chartFieldAmp g gi hC hK a b τ q) j y) Afield hAmeas
      (hKSm c hc0 hcδm) (fun q hq => ((hopen q hq).2 c hc0 hcδo).1) hPd hAg
  refine ⟨Bfield, hBmeas, ?_⟩
  intro w hqK hpS
  have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
    rwa [hSq] at hpS
  exact hBval w hqK hpImg

/-! ###############################################################################
    ### §C — ★ THE PAYOFF: the `Gc`-route first field-`pd` measurability (chart-wall-free).
    ############################################################################### -/

/-- **★★★ `firstFieldPd_prod_measurable_Gc` — the downstream `witnessFieldDeriv` measurability WITHOUT
    the raw chart wall.**  Produces exactly the conclusion of
    `GatedRepSFix.firstFieldPd_prod_measurable_v4` — the joint Borel measurability of the first
    field-`pd` kernel `w ↦ witnessFieldDeriv … k w.1 w.2.1 w.2.2` — but from the `Gc`-ROUTE inputs:
      • `Measurable Gc` (banked `ImageSupportDischarge.hWG_gate_concrete`) instead of the UNPROVABLE
        raw `Measurable (fun w => uniformInverseChart …)` (`.choose` wall);
      • `AmpGc` / `Afield` measurable twins (this file's §0/§A) instead of the raw amp / amp-`pd`
        measurabilities;
      • the three ON-GATE AGREEMENTS (`hChartAgree` / `hAmpAgree` / `hPdAgree`) that make the raw
        gated representative EQUAL the `Gc`-substituted (globally measurable) one on the gate.
    Route: `witnessFieldDeriv = gatedDerivRepProdS` (`witnessFieldDeriv_eq_gatedDerivRepProdS`, `hgate`
    + `hOffS`); on the gate the raw `Set.indicator` body equals the `Gc`-substituted body (the three
    agreements), off the gate both `0`; the `Gc`-body is globally measurable (composition of
    `Measurable Gc`, `Pfield`, `AmpGc`, `Afield`).  This is the object that CONSUMES the witnessed
    amp-`pd`/chart bundle — the raw-chart-measurability hypothesis of the v4 consumer is ELIMINATED.
    NOT `a₁ = R/6`. -/
theorem firstFieldPd_prod_measurable_Gc (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) (k : Fin n)
    (Pfield : Point n → Point n → Fin n → ℝ)
    (Gc : Point n × Point n → Point n) (AmpGc Afield : ℝ → Point n → Point n → ℝ)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hGcMeas : Measurable Gc)
    (hPmeas : ∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
    (hAmpGcMeas : Measurable (fun w : ℝ × Point n × Point n => AmpGc w.1 w.2.2 w.2.1))
    (hAfieldMeas : Measurable (fun w : ℝ × Point n × Point n => Afield w.1 w.2.2 w.2.1))
    (hChartAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        uniformInverseChart g gi hC hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
    (hAmpAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        chartFieldAmp g gi hC hK a b w.1 w.2.2 w.2.1 = AmpGc w.1 w.2.2 w.2.1)
    (hPdAgree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
        pd (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1 = Afield w.1 w.2.2 w.2.1)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
        IsOpen (S w.2.2) ∧
        (∀ jj, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) jj)
          (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b w.1 w.2.2) k w.2.1)
    (hOffS : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∉ S w.2.2 →
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2 = 0) :
    Measurable (fun w : ℝ × Point n × Point n =>
      witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2) := by
  classical
  have hrw : (fun w : ℝ × Point n × Point n =>
        witnessFieldDeriv g gi hC hK S a b k w.1 w.2.1 w.2.2)
      = QIQTH.GatedRepSFix.gatedDerivRepProdS g gi hC hK S a b k Pfield := by
    funext w
    exact QIQTH.GatedRepSFix.witnessFieldDeriv_eq_gatedDerivRepProdS hn g gi hC hK S a b k Pfield
      hgate hOffS w
  rw [hrw]
  -- On the gate the raw representative equals the `Gc`-substituted (globally measurable) body.
  have hEq : QIQTH.GatedRepSFix.gatedDerivRepProdS g gi hC hK S a b k Pfield
      = Set.indicator {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
          (fun w => gaussDdim w.1 (Gc (w.2.2, w.2.1))
              * (-(∑ jj, Gc (w.2.2, w.2.1) jj * Pfield w.2.2 w.2.1 jj) / (2 * w.1))
              * AmpGc w.1 w.2.2 w.2.1
            + gaussDdim w.1 (Gc (w.2.2, w.2.1)) * Afield w.1 w.2.2 w.2.1) := by
    funext w
    unfold QIQTH.GatedRepSFix.gatedDerivRepProdS
    by_cases hw : w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2
    · have hmem : w ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
          hChartAgree w hw.1 hw.2, hAmpAgree w hw.1 hw.2, hPdAgree w hw.1 hw.2]
    · have hnmem : w ∉ {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := hw
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hnmem]
  rw [hEq]
  have hGcV : Measurable (fun w : ℝ × Point n × Point n => Gc (w.2.2, w.2.1)) :=
    hGcMeas.comp ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hG : Measurable (fun w : ℝ × Point n × Point n => gaussDdim w.1 (Gc (w.2.2, w.2.1))) :=
    QIQTH.InnerKernelJointMeas.gaussDdim_uncurry_measurable.comp (measurable_fst.prodMk hGcV)
  have hSum : Measurable (fun w : ℝ × Point n × Point n =>
      ∑ jj, Gc (w.2.2, w.2.1) jj * Pfield w.2.2 w.2.1 jj) := by
    refine Finset.measurable_sum Finset.univ (fun jj _ => ?_)
    exact ((measurable_pi_apply jj).comp hGcV).mul (hPmeas jj)
  have hSc : Measurable (fun w : ℝ × Point n × Point n =>
      -(∑ jj, Gc (w.2.2, w.2.1) jj * Pfield w.2.2 w.2.1 jj) / (2 * w.1)) :=
    hSum.neg.div (measurable_const.mul measurable_fst)
  exact (((hG.mul hSc).mul hAmpGcMeas).add (hG.mul hAfieldMeas)).indicator hKSmeas

/-! ###############################################################################
    ### §D — the FINAL concrete-gate supplier bundle + the honest shape-mismatch statement.
    ############################################################################### -/

/-- **★★★ `concreteGate_ampPd_Gc_supplier_FINAL` — the `Gc`-route supplier bundle at the concrete gate.**
    A single uniform radius `δ₀ > 0` such that for every `0 < c < δ₀` and the concrete flow-ball gate
    there exist a measurable joint chart representative `Gc` and a measurable amplitude twin `AmpGc`,
    BOTH agreeing on the gate with the raw chart / amplitude, TOGETHER WITH the full gate-set
    measurability (`hKSmeas`).  These are the `k`-INDEPENDENT `Gc`-route inputs that
    `firstFieldPd_prod_measurable_Gc` (§C) consumes IN PLACE of the raw (`.choose`-tied, unprovable)
    chart / amplitude measurability conjuncts.  The remaining §C inputs are all THEOREMS elsewhere:
      • the per-`k` amp-`pd` twin `Afield` + on-gate value = `ampFieldPd_measurable` (§A);
      • the field-jet supplier `Pfield` + `hPmeas` + on-gate `hgate` jet block =
        `FlowDerivMeasurable.flowInverseJet_measurable_component` / `OnGateJets.hcarField_hgate_concrete`;
      • the off-`S` vanishing `hOffS` = `OffSVanishing.concreteGate_carriers_discharged_v2`.

    ── HONEST SHAPE-MISMATCH.  Feeding this bundle + the above banked pieces into
    `firstFieldPd_prod_measurable_Gc` yields the BorelDischargeSurface conjunct (2)
    `Measurable (fun w => witnessFieldDeriv … k …)` CHART-WALL-FREE — the genuine downstream payoff.
    What is NOT done here is re-shaping the ~130-binder v7 capstone: the literal v7 `hcarField`
    existential still demands the RAW `Measurable (fun w => uniformInverseChart …)` and RAW
    `Measurable (fun w => pd (chartFieldAmp …) …)` verbatim inside its ∃-body, which are
    `.choose`-unprovable AS SHAPED.  The honest eliminable target is the `Gc`-swapped consumer §C, NOT
    the raw existential; threading §C into `tripleHEmeas_concrete` is a forbidden kernel-freeze capstone
    edit and is deliberately NOT done here.  NOT `a₁ = R/6`. -/
theorem concreteGate_ampPd_Gc_supplier_FINAL (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
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
  obtain ⟨ρ, hρ, Gc, hGmeas, hWG⟩ :=
    QIQTH.ImageSupportDischarge.hWG_gate_concrete g gi hC hK
  obtain ⟨AG, hAGmeas, ρ', hρ', hAGagree⟩ :=
    exists_measurable_ampGc g gi hC hK a b hg hgi hgpos
  obtain ⟨δm, hδm, hKSm⟩ :=
    QIQTH.ConcreteGateInstantiation.hKSmeas_concrete g gi hC hK
  refine ⟨min (min ρ ρ') δm, lt_min (lt_min hρ hρ') hδm, ?_⟩
  intro c hc0 hcδ S hSeq
  have hcρ : c ≤ ρ := le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hcρ' : c ≤ ρ' := le_of_lt (lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hcδm : c < δm := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2} := by
    have hset : {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
        = {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧
            w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c} := by
      simp only [hSeq]
    rw [hset]; exact hKSm c hc0 hcδm
  refine ⟨Gc, AG, hKSmeas, hGmeas, hAGmeas, ?_, ?_⟩
  · intro w hqK hpS
    have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
      rwa [hSq] at hpS
    exact hWG c hcρ (w.1, w.2.1, w.2.2) hqK hpImg
  · intro w hqK hpS
    have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
      rwa [hSq] at hpS
    exact hAGagree c hcρ' w.1 w.2.2 w.2.1 hqK hpImg

end QIQTH.AmpPdComposition

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AmpPdComposition
#print axioms exists_measurable_ampGc
#print axioms measurable_dq_witness
#print axioms ampFieldPd_measurable
#print axioms ampFieldSecondPd_measurable
#print axioms firstFieldPd_prod_measurable_Gc
#print axioms concreteGate_ampPd_Gc_supplier_FINAL
end AxiomChecks
