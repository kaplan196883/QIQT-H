/-
  FlowDerivMeasurable — J4-239: the measurable JOINT FIELD-DERIVATIVE of the flow inverse.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It discharges
  the LAST v7 supplier obligation isolated by `ChartRepFinal` (J4-238) as residue class (3): the joint
  `(base, field)`-measurability of the chart FIELD-JETS — the Fréchet-derivative columns of the flow
  inverse `W q := uniformInverseChart g gi hC hK q`.  No `sorry` (prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypotheses.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RESIDUE (`ChartRepFinal` class (3)).  A merely-measurable joint chart representative `Gc`
  (Lusin–Souslin, VALUE-only) exposes NO field derivative, so the value-side `Gc`-swap does NOT reach
  the jets `Pfield q p j := fderiv ℝ (W q) p (eₖ) j`.  The route is the DIFFERENCE-QUOTIENT LIMIT: on
  the OPEN flow-ball gate `S q = φ_q '' ball 0 c` the chart is `C²` (banked
  `chartField_contDiffAt_reachable_uniform`), so the first jet is a POINTWISE limit of the measurable
  `Gc`-difference-quotients — hence measurable by `measurable_of_tendsto_metrizable`.

  ── THE CONSTRUCTION.  For a fixed direction `k` and the null sequence `hₘ = 1/(m+1)`:
    • `DQw m w  := hₘ⁻¹ • (Gc (q, p + hₘ·eₖ) − Gc (q, p))`     (globally measurable, `Gc` from
       `hWG_gate_concrete`, a THEOREM);
    • `seqW m   := gateSet.indicator (DQw m)`                    (measurable: measurable set + fn);
    • `Fw       := gateSet.indicator (fun w => fderiv ℝ (W q) p (eₖ))`  (the INDICATOR-EXTENDED jet).
  On the gate, `Gc = W` (value swap) and `hₘ⁻¹ • (W q (p+hₘ·eₖ) − W q p) = slope`, whose limit is the
  `C²` derivative `HasDerivAt`; off the gate the indicator makes `seqW m = 0 → 0 = Fw`.  So
  `seqW m → Fw` EVERYWHERE ⟹ `Measurable Fw`, and the CHOSEN witness `Pfield` (the `(q,p)`-indicator
  of the true jet) satisfies BOTH the measurability conjunct AND, on the gate, the exact
  on-gate value `Pfield q p j = fderiv ℝ (W q) p (eₖ) j` (so the `hgate` `HasDerivAt` is preserved).

  ── WHAT LANDS.
    §A — `flowInverseJet_measurable`      — ★ item 1: the FIRST-jet joint measurability + on-gate value.
    §B — `flowInverseSecondJet_measurable` — ★ item 2: the SECOND jet, one difference-quotient up.
    §C — the payoff wiring of the field-jet measurability conjuncts (§D notes).

  Radii carried HONESTLY: `0 < c < δ₀`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OnGateJets
import QIQTH.ImageSupportDischarge
import QIQTH.ConcreteGateInstantiation
import QIQTH.ChartFieldC2General
import QIQTH.Field2NbhdReshape

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open scoped Topology BigOperators ContDiff

namespace QIQTH.FlowDerivMeasurable

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- The coordinate-line update equals the additive shift along `eₖ`:
    `Function.update p k (p k + s) = p + s • Pi.single k 1`. -/
theorem update_eq_add_smul_single (p : Point n) (k : Fin n) (s : ℝ) :
    Function.update p k (p k + s) = p + s • Pi.single k (1 : ℝ) := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

/-! ###############################################################################
    ### §A — the FIRST-jet joint measurability via the difference-quotient limit.
    ############################################################################### -/

/-- **★★ `flowInverseJet_measurable` — item 1: the measurable JOINT FIELD-DERIVATIVE of the flow
    inverse (first jet).**  A single uniform radius `δ₀ > 0` such that for every `0 < c < δ₀` and the
    concrete flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, for every direction
    `k` there is a GLOBALLY MEASURABLE field-jet witness `Pfield` with:
      • `∀ j, Measurable (fun w => Pfield w.2.2 w.2.1 j)`  (the residue-(3) measurability conjunct);
      • on the gate (`q ∈ K`, `p ∈ S q`), `Pfield q p j = fderiv ℝ (W q) p (eₖ) j`  (so the on-gate
        `hgate` `HasDerivAt` is preserved — the witness AGREES with the true jet there).
    Route: difference-quotient limit of the banked measurable `Gc` (`hWG_gate_concrete`), the pointwise
    limit taken by `measurable_of_tendsto_metrizable`; on-gate convergence from chart-`C²`
    (`chartField_contDiffAt_reachable_uniform`) + `Gc = W` value swap + open-gate eventual shift.
    NOT `a₁ = R/6`. -/
theorem flowInverseJet_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              ∀ j, Pfield w.2.2 w.2.1 j
                = fderiv ℝ (uniformInverseChart g gi hC hK w.2.2) w.2.1 (Pi.single k (1 : ℝ)) j) := by
  classical
  obtain ⟨ρ, hρ, Gc, hGmeas, hagree⟩ :=
    QIQTH.ImageSupportDischarge.hWG_gate_concrete g gi hC hK
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
  -- Abbreviations.
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set φ : Point n → Point n → Point n := uniformFlowExp g gi hC hK with hφdef
  -- the gate as a set in `w`-space (explicit flow image, matching the banked measurability).
  set gateSet : Set (ℝ × Point n × Point n) :=
    {w | w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c} with hgateSetDef
  have hgateSet_meas : MeasurableSet gateSet := hKSm c hc0 hcδm
  -- the null sequence.
  set hm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hmdef
  have hm_pos : ∀ m, 0 < hm m := fun m => by
    have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    simpa [hmdef] using one_div_pos.mpr this
  have hm_tendsto : Tendsto hm atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the difference quotient of `Gc` (globally measurable).
  set DQw : ℕ → (ℝ × Point n × Point n) → Point n :=
    fun m w => (hm m)⁻¹ • (Gc (w.2.2, w.2.1 + hm m • Pi.single k (1 : ℝ)) - Gc (w.2.2, w.2.1))
    with hDQwdef
  have hsnd2 : Measurable (fun w : ℝ × Point n × Point n => w.2.2) :=
    measurable_snd.comp measurable_snd
  have hfst2 : Measurable (fun w : ℝ × Point n × Point n => w.2.1) :=
    measurable_fst.comp measurable_snd
  have hDQw_meas : ∀ m, Measurable (DQw m) := by
    intro m
    simp only [hDQwdef]
    have hshift : Measurable
        (fun w : ℝ × Point n × Point n => (w.2.2, w.2.1 + hm m • Pi.single k (1 : ℝ))) :=
      hsnd2.prodMk (hfst2.add_const _)
    have hbase : Measurable (fun w : ℝ × Point n × Point n => (w.2.2, w.2.1)) :=
      hsnd2.prodMk hfst2
    exact ((hGmeas.comp hshift).sub (hGmeas.comp hbase)).const_smul ((hm m)⁻¹)
  -- the indicator sequence and the target.
  set seqW : ℕ → (ℝ × Point n × Point n) → Point n :=
    fun m => gateSet.indicator (DQw m) with hseqWdef
  set trueJetV : (ℝ × Point n × Point n) → Point n :=
    fun w => fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ)) with htrueJetVdef
  set Fw : (ℝ × Point n × Point n) → Point n := gateSet.indicator trueJetV with hFwdef
  have hseqW_meas : ∀ m, Measurable (seqW m) := fun m =>
    (hDQw_meas m).indicator hgateSet_meas
  -- POINTWISE CONVERGENCE `seqW m → Fw` at every `w`.
  have hconv : ∀ w, Tendsto (fun m => seqW m w) atTop (𝓝 (Fw w)) := by
    intro w
    by_cases hw : w ∈ gateSet
    · -- on the gate: difference-quotient limit is the `C²` derivative.
      have hqK : w.2.2 ∈ K := hw.1
      have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw.2
      obtain ⟨v, hv, hvp⟩ := id hpImg
      have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
      have hCp : ContDiffAt ℝ 2 (W w.2.2) w.2.1 := by
        rw [hWdef, ← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
      -- vector HasDerivAt of the coordinate line.
      have hWdiff : DifferentiableAt ℝ (W w.2.2) w.2.1 := hCp.differentiableAt (by norm_num)
      have hWfd' : HasFDerivAt (W w.2.2) (fderiv ℝ (W w.2.2) w.2.1)
          (Function.update w.2.1 k (w.2.1 k)) := by
        rw [Function.update_eq_self]; exact hWdiff.hasFDerivAt
      have hcompV : HasDerivAt (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s))
          (fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ))) (w.2.1 k) := by
        have h := hWfd'.comp_hasDerivAt (w.2.1 k) (hasDerivAt_update w.2.1 k (w.2.1 k))
        simpa using h
      -- the slope tendsto.
      have hslope : Tendsto
          (slope (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s)) (w.2.1 k))
          (𝓝[≠] (w.2.1 k)) (𝓝 (fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ)))) :=
        hasDerivAt_iff_tendsto_slope.mp hcompV
      -- the null sequence into `𝓝[≠] (p k)`.
      have hxm_tendsto : Tendsto (fun m => w.2.1 k + hm m) atTop (𝓝[≠] (w.2.1 k)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun m => w.2.1 k + hm m) atTop (𝓝 (w.2.1 k + 0)) :=
            tendsto_const_nhds.add hm_tendsto
          simpa using this
        · exact Eventually.of_forall (fun m =>
            (Set.mem_compl_singleton_iff).mpr (lt_add_of_pos_right _ (hm_pos m)).ne')
      have hslope_seq : Tendsto
          (fun m => slope (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s)) (w.2.1 k)
              (w.2.1 k + hm m))
          atTop (𝓝 (fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ)))) :=
        hslope.comp hxm_tendsto
      -- open gate ⟹ shift eventually inside ⟹ `Gc = W` on the shift.
      have hOpenSet : IsOpen (φ w.2.2 '' Metric.ball (0 : Point n) c) :=
        ((hopen w.2.2 hqK).2 c hc0 hcδo).1
      have hp_mem : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hpImg
      have hshift_tendsto :
          Tendsto (fun m => w.2.1 + hm m • Pi.single k (1 : ℝ)) atTop (𝓝 w.2.1) := by
        have h0 : Tendsto (fun m => hm m • Pi.single k (1 : ℝ)) atTop (𝓝 (0 : Point n)) := by
          simpa using (hm_tendsto.smul_const (Pi.single k (1 : ℝ)))
        have h1 : Tendsto (fun m => w.2.1 + hm m • Pi.single k (1 : ℝ)) atTop
            (𝓝 (w.2.1 + (0 : Point n))) := (tendsto_const_nhds (x := w.2.1)).add h0
        simpa using h1
      have hev_in : ∀ᶠ m in atTop, (w.2.1 + hm m • Pi.single k (1 : ℝ))
          ∈ φ w.2.2 '' Metric.ball (0 : Point n) c :=
        hshift_tendsto.eventually_mem (hOpenSet.mem_nhds hp_mem)
      -- `Gc = W` at `p` and (eventually) at the shift.
      have hGcp : Gc (w.2.2, w.2.1) = W w.2.2 w.2.1 :=
        (hagree c hcρ (w.1, w.2.1, w.2.2) hqK hp_mem).symm
      -- the slope equals `DQw` eventually.
      have hev_eq : ∀ᶠ m in atTop,
          slope (fun s : ℝ => W w.2.2 (Function.update w.2.1 k s)) (w.2.1 k) (w.2.1 k + hm m)
            = DQw m w := by
        filter_upwards [hev_in] with m hm_in
        have hGcshift : Gc (w.2.2, w.2.1 + hm m • Pi.single k (1 : ℝ))
            = W w.2.2 (w.2.1 + hm m • Pi.single k (1 : ℝ)) :=
          (hagree c hcρ (w.1, w.2.1 + hm m • Pi.single k (1 : ℝ), w.2.2) hqK hm_in).symm
        have hupd1 : Function.update w.2.1 k (w.2.1 k + hm m) = w.2.1 + hm m • Pi.single k (1 : ℝ) :=
          update_eq_add_smul_single w.2.1 k (hm m)
        have hupd0 : Function.update w.2.1 k (w.2.1 k) = w.2.1 := Function.update_eq_self k w.2.1
        have hsc : (w.2.1 k + hm m) - w.2.1 k = hm m := by ring
        rw [slope_def_module]
        simp only [hDQwdef]
        rw [hsc, hupd1, hupd0, hGcshift, hGcp]
      -- assemble.
      have hDQw_conv : Tendsto (fun m => DQw m w) atTop
          (𝓝 (fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ)))) :=
        hslope_seq.congr' hev_eq
      rw [hseqWdef, hFwdef]
      simp only [Set.indicator_of_mem hw]
      rw [htrueJetVdef]
      exact hDQw_conv
    · -- off the gate: everything is `0`.
      rw [hseqWdef, hFwdef]
      simp only [Set.indicator_of_notMem hw]
      exact tendsto_const_nhds
  -- MEASURABILITY of the indicator-extended jet.
  have hFw_meas : Measurable Fw :=
    measurable_of_tendsto_metrizable hseqW_meas (tendsto_pi_nhds.mpr hconv)
  -- the chosen witness (an `(q,p)`-function equal to the indicator-extended jet).
  refine ⟨fun q p j =>
    (if (q ∈ K ∧ p ∈ φ q '' Metric.ball (0 : Point n) c)
      then fderiv ℝ (W q) p (Pi.single k (1 : ℝ)) else (0 : Point n)) j, ?_, ?_⟩
  · -- measurability: the witness composite equals `Fw`.
    intro j
    have hrw : (fun w : ℝ × Point n × Point n =>
        (if (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c)
          then fderiv ℝ (W w.2.2) w.2.1 (Pi.single k (1 : ℝ)) else (0 : Point n)) j)
        = (fun w => Fw w j) := by
      funext w
      by_cases hw : w ∈ gateSet
      · have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw
        simp only [if_pos hcond, hFwdef, Set.indicator_of_mem hw, htrueJetVdef]
      · have hcond : ¬ (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c) := hw
        simp only [if_neg hcond, hFwdef, Set.indicator_of_notMem hw, Pi.zero_apply]
    rw [hrw]
    exact (measurable_pi_apply j).comp hFw_meas
  · -- on-gate value.
    intro w hqK hpS j
    have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = φ w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
      rwa [hSq] at hpS
    have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := ⟨hqK, hpImg⟩
    simp only [if_pos hcond]

/-! ###############################################################################
    ### §B — the SECOND-jet joint measurability (one difference-quotient up).
    ############################################################################### -/

/-- **★★ `flowInverseSecondJet_measurable` — item 2: the measurable JOINT MIXED SECOND FIELD-JET of
    the flow inverse.**  For every index pair `(i, j)` a single uniform radius `δ₀ > 0` such that for
    every `0 < c < δ₀` and the concrete flow-ball gate there is a GLOBALLY MEASURABLE mixed second-jet
    witness `Qfield` with:
      • `∀ k, Measurable (fun w => Qfield w.2.2 w.2.1 k)`;
      • on the gate, `Qfield q p k = fderiv ℝ (fun y => fderiv ℝ (W q) y (eⱼ)) p (eᵢ) k`.
    Route: difference-quotient (in direction `i`) of the measurable FIRST-jet witness of
    `flowInverseJet_measurable` (direction `j`); on-gate convergence from `chartFieldSecondJet_hasDerivAt`
    (`C² ⟹ D W ∈ C¹`) + the first-jet on-gate value swap + open-gate eventual shift.  NOT `a₁ = R/6`. -/
theorem flowInverseSecondJet_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Qfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → w.2.1 ∈ S w.2.2 →
              ∀ k, Qfield w.2.2 w.2.1 k
                = fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK w.2.2) y
                    (Pi.single j (1 : ℝ))) w.2.1 (Pi.single i (1 : ℝ)) k) := by
  classical
  obtain ⟨δ₁, hδ₁, hspec1⟩ := flowInverseJet_measurable g gi hC hK j
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
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set φ : Point n → Point n → Point n := uniformFlowExp g gi hC hK with hφdef
  -- the FIRST-jet witness (direction `j`) and its properties.
  obtain ⟨Pj, hPjmeas, hPjval⟩ := hspec1 c hc0 hcδ₁ S hSeq
  set gateSet : Set (ℝ × Point n × Point n) :=
    {w | w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c} with hgateSetDef
  have hgateSet_meas : MeasurableSet gateSet := hKSm c hc0 hcδm
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
  -- measurability of the `i`-shifted first-jet witness.
  have hshiftMeas : ∀ (t : ℝ) (k : Fin n),
      Measurable (fun w : ℝ × Point n × Point n => Pj w.2.2 (w.2.1 + t • Pi.single i (1 : ℝ)) k) := by
    intro t k
    have hσ : Measurable (fun w : ℝ × Point n × Point n =>
        ((w.1, w.2.1 + t • Pi.single i (1 : ℝ), w.2.2) : ℝ × Point n × Point n)) :=
      measurable_fst.prodMk ((hfst2.add_const _).prodMk hsnd2)
    exact (hPjmeas k).comp hσ
  -- the per-`k` construction.
  refine ⟨fun q p k =>
    (if (q ∈ K ∧ p ∈ φ q '' Metric.ball (0 : Point n) c)
      then fderiv ℝ (fun y => fderiv ℝ (W q) y (Pi.single j (1 : ℝ))) p (Pi.single i (1 : ℝ)) k
      else (0 : ℝ)), ?_, ?_⟩
  · -- MEASURABILITY: per `k`, via the difference-quotient limit.
    intro k
    set DQw : ℕ → (ℝ × Point n × Point n) → ℝ :=
      fun m w => (Pj w.2.2 (w.2.1 + hm m • Pi.single i (1 : ℝ)) k - Pj w.2.2 w.2.1 k) / hm m
      with hDQwdef
    have hDQw_meas : ∀ m, Measurable (DQw m) := fun m => by
      simp only [hDQwdef]
      exact ((hshiftMeas (hm m) k).sub (hPjmeas k)).div_const _
    set trueJet2 : (ℝ × Point n × Point n) → ℝ :=
      fun w => fderiv ℝ (fun y => fderiv ℝ (W w.2.2) y (Pi.single j (1 : ℝ))) w.2.1
        (Pi.single i (1 : ℝ)) k with htrueJet2def
    set seqW : ℕ → (ℝ × Point n × Point n) → ℝ :=
      fun m => gateSet.indicator (DQw m) with hseqWdef
    set Fw : (ℝ × Point n × Point n) → ℝ := gateSet.indicator trueJet2 with hFwdef
    have hseqW_meas : ∀ m, Measurable (seqW m) := fun m =>
      (hDQw_meas m).indicator hgateSet_meas
    have hconv : ∀ w, Tendsto (fun m => seqW m w) atTop (𝓝 (Fw w)) := by
      intro w
      by_cases hw : w ∈ gateSet
      · have hqK : w.2.2 ∈ K := hw.1
        have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw.2
        obtain ⟨v, hv, hvp⟩ := id hpImg
        have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
        have hCp : ContDiffAt ℝ 2 (W w.2.2) w.2.1 := by
          rw [hWdef, ← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
        have hcompS : HasDerivAt
            (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s) (Pi.single j (1 : ℝ)) k)
            (trueJet2 w) (w.2.1 i) := by
          rw [htrueJet2def]
          exact QIQTH.Field2NbhdReshape.chartFieldSecondJet_hasDerivAt g gi hC hK w.2.2 w.2.1 i j hCp k
        have hslope : Tendsto
            (slope (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s)
                (Pi.single j (1 : ℝ)) k) (w.2.1 i))
            (𝓝[≠] (w.2.1 i)) (𝓝 (trueJet2 w)) :=
          hasDerivAt_iff_tendsto_slope.mp hcompS
        have hxm_tendsto : Tendsto (fun m => w.2.1 i + hm m) atTop (𝓝[≠] (w.2.1 i)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have : Tendsto (fun m => w.2.1 i + hm m) atTop (𝓝 (w.2.1 i + 0)) :=
              tendsto_const_nhds.add hm_tendsto
            simpa using this
          · exact Eventually.of_forall (fun m =>
              (Set.mem_compl_singleton_iff).mpr (lt_add_of_pos_right _ (hm_pos m)).ne')
        have hslope_seq : Tendsto
            (fun m => slope (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s)
                (Pi.single j (1 : ℝ)) k) (w.2.1 i) (w.2.1 i + hm m))
            atTop (𝓝 (trueJet2 w)) :=
          hslope.comp hxm_tendsto
        have hOpenSet : IsOpen (φ w.2.2 '' Metric.ball (0 : Point n) c) :=
          ((hopen w.2.2 hqK).2 c hc0 hcδo).1
        have hshift_tendsto :
            Tendsto (fun m => w.2.1 + hm m • Pi.single i (1 : ℝ)) atTop (𝓝 w.2.1) := by
          have h0 : Tendsto (fun m => hm m • Pi.single i (1 : ℝ)) atTop (𝓝 (0 : Point n)) := by
            simpa using (hm_tendsto.smul_const (Pi.single i (1 : ℝ)))
          have h1 : Tendsto (fun m => w.2.1 + hm m • Pi.single i (1 : ℝ)) atTop
              (𝓝 (w.2.1 + (0 : Point n))) := (tendsto_const_nhds (x := w.2.1)).add h0
          simpa using h1
        have hev_in : ∀ᶠ m in atTop, (w.2.1 + hm m • Pi.single i (1 : ℝ))
            ∈ φ w.2.2 '' Metric.ball (0 : Point n) c :=
          hshift_tendsto.eventually_mem (hOpenSet.mem_nhds hpImg)
        -- first-jet value swap at `p` (item-1 agreement).
        have hval_p : fderiv ℝ (W w.2.2) w.2.1 (Pi.single j (1 : ℝ)) k = Pj w.2.2 w.2.1 k :=
          (hPjval (w.1, w.2.1, w.2.2) hqK (by rw [hSeq]; exact hpImg) k).symm
        have hev_eq : ∀ᶠ m in atTop,
            slope (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s)
                (Pi.single j (1 : ℝ)) k) (w.2.1 i) (w.2.1 i + hm m) = DQw m w := by
          filter_upwards [hev_in] with m hm_in
          have hval_shift : fderiv ℝ (W w.2.2) (w.2.1 + hm m • Pi.single i (1 : ℝ))
              (Pi.single j (1 : ℝ)) k
              = Pj w.2.2 (w.2.1 + hm m • Pi.single i (1 : ℝ)) k :=
            (hPjval (w.1, w.2.1 + hm m • Pi.single i (1 : ℝ), w.2.2) hqK
              (by rw [hSeq]; exact hm_in) k).symm
          have hupd1 : Function.update w.2.1 i (w.2.1 i + hm m)
              = w.2.1 + hm m • Pi.single i (1 : ℝ) := update_eq_add_smul_single w.2.1 i (hm m)
          have hupd0 : Function.update w.2.1 i (w.2.1 i) = w.2.1 := Function.update_eq_self i w.2.1
          have hsc : (w.2.1 i + hm m) - w.2.1 i = hm m := by ring
          rw [slope_def_field]
          simp only [hDQwdef]
          rw [hsc, hupd1, hupd0, hval_shift, hval_p]
        have hDQw_conv : Tendsto (fun m => DQw m w) atTop (𝓝 (trueJet2 w)) :=
          hslope_seq.congr' hev_eq
        rw [hseqWdef, hFwdef]
        simp only [Set.indicator_of_mem hw]
        exact hDQw_conv
      · rw [hseqWdef, hFwdef]
        simp only [Set.indicator_of_notMem hw]
        exact tendsto_const_nhds
    have hFw_meas : Measurable Fw :=
      measurable_of_tendsto_metrizable hseqW_meas (tendsto_pi_nhds.mpr hconv)
    have hrw : (fun w : ℝ × Point n × Point n =>
        (if (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c)
          then fderiv ℝ (fun y => fderiv ℝ (W w.2.2) y (Pi.single j (1 : ℝ))) w.2.1
              (Pi.single i (1 : ℝ)) k
          else (0 : ℝ)))
        = Fw := by
      funext w
      by_cases hw : w ∈ gateSet
      · have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := hw
        simp only [if_pos hcond, hFwdef, Set.indicator_of_mem hw, htrueJet2def]
      · have hcond : ¬ (w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c) := hw
        simp only [if_neg hcond, hFwdef, Set.indicator_of_notMem hw]
    rw [hrw]; exact hFw_meas
  · -- on-gate value.
    intro w hqK hpS k
    have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := by
      have hSq : S w.2.2 = φ w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
      rwa [hSq] at hpS
    have hcond : w.2.2 ∈ K ∧ w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := ⟨hqK, hpImg⟩
    simp only [if_pos hcond]

/-! ###############################################################################
    ### §C — the SECOND-jet on-gate `hgate` conjuncts for the MEASURABLE witnesses.
    ############################################################################### -/

/-- **★★ `flowInverseSecondJet_measurable_component` — the measurable second-jet witnesses satisfy the
    `hcarField2` `hgate` derivative conjuncts.**  For every `(i, j)` a uniform radius `δ₀ > 0` such that
    on the concrete flow-ball gate there are GLOBALLY MEASURABLE witnesses `Pjfield` (first jet,
    direction `j`) and `Qfield` (mixed second jet) with:
      • `∀ k, Measurable (fun w => Pjfield w.2.2 w.2.1 k)` and `∀ k, Measurable (fun w => Qfield …)`;
      • on the full gate (`q ∈ K`, `0 < τ`, `p ∈ S q`):
          `IsOpen (S q)`,
          `∀ y ∈ S q, ∀ k, HasDerivAt (fun s => W q (update y j s) k) (Pjfield q y k) (y j)`,
          `∀ k, HasDerivAt (fun s => Pjfield q (update p i s) k) (Qfield q p k) (p i)`.
    This is EXACTLY the first-jet-family + mixed-second-jet block of `hcarField2`'s `hgate`, now with
    the measurability conjuncts ATTACHED — the honest object a v6 `hcarField2` reshape consumes.  The
    second `HasDerivAt` is transferred from `chartFieldSecondJet_hasDerivAt` by
    `HasDerivAt.congr_of_eventuallyEq` (the indicator-extended `Pjfield` agrees with the true jet in a
    neighbourhood of the interior gate point).  NOT `a₁ = R/6`. -/
theorem flowInverseSecondJet_measurable_component (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i j : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pjfield Qfield : Point n → Point n → Fin n → ℝ,
          (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
          ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              IsOpen (S w.2.2) ∧
              (∀ y ∈ S w.2.2, ∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update y j s) k)
                (Pjfield w.2.2 y k) (y j)) ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
                (Qfield w.2.2 w.2.1 k) (w.2.1 i))) := by
  classical
  obtain ⟨δ₁, hδ₁, hspec1⟩ := flowInverseJet_measurable g gi hC hK j
  obtain ⟨δ₂, hδ₂, hspec2⟩ := flowInverseSecondJet_measurable g gi hC hK i j
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨δo, hδo, hopen⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨min (min δ₁ δ₂) (min δr δo), lt_min (lt_min hδ₁ hδ₂) (lt_min hδr hδo), ?_⟩
  intro c hc0 hcδ S hSeq
  have hcδ₁ : c < δ₁ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hcδ₂ : c < δ₂ := lt_of_lt_of_le hcδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hcδr : c < δr := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcδo : c < δo := lt_of_lt_of_le hcδ (le_trans (min_le_right _ _) (min_le_right _ _))
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set φ : Point n → Point n → Point n := uniformFlowExp g gi hC hK with hφdef
  obtain ⟨Pj, hPjmeas, hPjval⟩ := hspec1 c hc0 hcδ₁ S hSeq
  obtain ⟨Q, hQmeas, hQval⟩ := hspec2 c hc0 hcδ₂ S hSeq
  refine ⟨Pj, Q, hPjmeas, hQmeas, ?_⟩
  intro w hqK hτ hpS
  have hSq : S w.2.2 = φ w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
  have hpImg : w.2.1 ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := by rwa [hSq] at hpS
  have hOpenSet : IsOpen (φ w.2.2 '' Metric.ball (0 : Point n) c) :=
    ((hopen w.2.2 hqK).2 c hc0 hcδo).1
  refine ⟨by rw [hSq]; exact hOpenSet, ?_, ?_⟩
  · -- first-jet HasDerivAt at every reachable `y`.
    intro y hyS k
    have hyImg : y ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := by rwa [hSq] at hyS
    obtain ⟨vy, hvy, hvyp⟩ := id hyImg
    have hvyc : ‖vy‖ < c := by rwa [mem_ball_zero_iff] at hvy
    have hCy : ContDiffAt ℝ 2 (W w.2.2) y := by
      rw [hWdef, ← hvyp]; exact hreach w.2.2 hqK vy (lt_trans hvyc hcδr)
    rw [hPjval (w.1, y, w.2.2) hqK (by rw [hSeq]; exact hyImg) k]
    exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 y j k hCy
  · -- mixed second-jet HasDerivAt at `p`, via congr with the true first-jet field.
    intro k
    obtain ⟨v, hv, hvp⟩ := id hpImg
    have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
    have hCp : ContDiffAt ℝ 2 (W w.2.2) w.2.1 := by
      rw [hWdef, ← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
    have hcompS : HasDerivAt
        (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s) (Pi.single j (1 : ℝ)) k)
        (fderiv ℝ (fun y => fderiv ℝ (W w.2.2) y (Pi.single j (1 : ℝ))) w.2.1
          (Pi.single i (1 : ℝ)) k) (w.2.1 i) :=
      QIQTH.Field2NbhdReshape.chartFieldSecondJet_hasDerivAt g gi hC hK w.2.2 w.2.1 i j hCp k
    -- eventual (in `s`) equality of the `Pj`-line with the true first-jet line.
    have hcont : ContinuousAt (fun s : ℝ => Function.update w.2.1 i s) (w.2.1 i) :=
      ((hasDerivAt_update w.2.1 i (w.2.1 i)).differentiableAt).continuousAt
    have hupd0 : Function.update w.2.1 i (w.2.1 i) = w.2.1 := Function.update_eq_self i w.2.1
    have hev_in : ∀ᶠ s in 𝓝 (w.2.1 i),
        Function.update w.2.1 i s ∈ φ w.2.2 '' Metric.ball (0 : Point n) c := by
      have hmem : φ w.2.2 '' Metric.ball (0 : Point n) c ∈ 𝓝 (Function.update w.2.1 i (w.2.1 i)) := by
        rw [hupd0]; exact hOpenSet.mem_nhds hpImg
      exact hcont.eventually_mem hmem
    have hEqEv :
        (fun s : ℝ => Pj w.2.2 (Function.update w.2.1 i s) k)
          =ᶠ[𝓝 (w.2.1 i)]
        (fun s : ℝ => fderiv ℝ (W w.2.2) (Function.update w.2.1 i s) (Pi.single j (1 : ℝ)) k) := by
      filter_upwards [hev_in] with s hs
      exact hPjval (w.1, Function.update w.2.1 i s, w.2.2) hqK (by rw [hSeq]; exact hs) k
    have hHD : HasDerivAt (fun s : ℝ => Pj w.2.2 (Function.update w.2.1 i s) k)
        (fderiv ℝ (fun y => fderiv ℝ (W w.2.2) y (Pi.single j (1 : ℝ))) w.2.1
          (Pi.single i (1 : ℝ)) k) (w.2.1 i) :=
      hcompS.congr_of_eventuallyEq hEqEv
    rw [hQval w hqK hpS k]
    exact hHD

/-! ###############################################################################
    ### §E — the FIRST-jet on-gate `hgate` conjunct for the measurable witness.
    ############################################################################### -/

/-- **★ `flowInverseJet_measurable_component` — the per-`(k,j)` measurability, extracted.**  A direct
    restatement isolating, for the CHOSEN indicator-extended witness of `flowInverseJet_measurable`,
    the single measurability conjunct `Measurable (fun w => Pfield w.2.2 w.2.1 j)` together with the
    on-gate value — the exact shape consumed by the v5 `hcar` field-jet measurability slot.  NOT
    `a₁ = R/6`. -/
theorem flowInverseJet_measurable_component (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (k : Fin n) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ (S : Point n → Set (Point n)),
        S = (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
          (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
          ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
              ∀ j, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK w.2.2 (Function.update w.2.1 k s) j)
                (Pfield w.2.2 w.2.1 j) (w.2.1 k)) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := flowInverseJet_measurable g gi hC hK k
  obtain ⟨δr, hδr, hreach⟩ :=
    QIQTH.ChartFieldC2General.chartField_contDiffAt_reachable_uniform g gi hC hK
  refine ⟨min δ₀ δr, lt_min hδ₀ hδr, ?_⟩
  intro c hc0 hcδ S hSeq
  have hcδ₀ : c < δ₀ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcδr : c < δr := lt_of_lt_of_le hcδ (min_le_right _ _)
  obtain ⟨Pfield, hmeas, hval⟩ := hspec c hc0 hcδ₀ S hSeq
  refine ⟨Pfield, hmeas, ?_⟩
  intro w hqK hτ hpS j
  -- reachable ⟹ `C²` ⟹ on-gate `HasDerivAt` with value = true jet = witness value.
  have hpImg : w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by
    have : S w.2.2 = uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c := by rw [hSeq]
    rwa [this] at hpS
  obtain ⟨v, hv, hvp⟩ := hpImg
  have hvc : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hv
  have hCp : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK w.2.2) w.2.1 := by
    rw [← hvp]; exact hreach w.2.2 hqK v (lt_trans hvc hcδr)
  rw [hval w hqK hpS j]
  exact QIQTH.OnGateJets.chartFieldFirstJet_hasDerivAt g gi hC hK w.2.2 w.2.1 k j hCp

/-! ###############################################################################
    ### §D — RESIDUE MAP (honest post-brick surface).

    DISCHARGED here (the `ChartRepFinal` residue class (3) = the measurable joint FIELD-DERIVATIVE of
    the flow inverse), all `std-3`, no `sorry` / no new axioms:
      • `flowInverseJet_measurable`               — first field-jet, measurable + on-gate value;
      • `flowInverseJet_measurable_component`      — + the on-gate `hgate` `HasDerivAt` (v5 `hcarField`);
      • `flowInverseSecondJet_measurable`          — mixed second field-jet, measurable + on-gate value;
      • `flowInverseSecondJet_measurable_component`— + the on-gate `Pjfield`/`Qfield` `hgate`
        `HasDerivAt` conjuncts (v6 `hcarField2`).

    STILL CARRIED (NOT this file's residue, honestly named):
      • CLASS (1) — the GLOBAL raw chart-VALUE measurability `Measurable (fun w => W w.2.2 w.2.1)` that
        the v5/v7 supplier existentials still demand verbatim.  Per `ChartRepFinal`, this is `.choose`-
        tied and UNPROVABLE as shaped; it is eliminable only by a v6 assembly whose representative is the
        `Gc`-substituted chart (`Measurable Gc`, banked `hWG_gate_concrete`).  Building that v6 reshape
        is a CAPSTONE restatement (kernel-freeze) and is deliberately NOT done here.
      • CLASS (2)/(3) AMPLITUDE FIELD-`pd`s — `Measurable (fun w => pd (chartFieldAmp …) k w.2.1)` and
        the mixed `pd_i pd_j`.  These are closed forms in `(Gc-value, first jet)` × derivatives of the
        banked smooth factors (`radialCutoff`, `vanVleck^{-1/2}`, transport coeffs); measurable by
        composition of `Measurable Gc` + `flowInverseJet_measurable` once the chain-rule closed form is
        expanded.  The jet inputs are now supplied; the composition is the remaining follow-on.

    CONSEQUENCE.  Every FIELD-JET measurability conjunct of the v7 `hcarField` / `hcarField2` suppliers
    (the precisely-named residue (3)) is now a THEOREM at the concrete flow-ball gate, with witnesses
    that simultaneously satisfy the on-gate `hgate` `HasDerivAt` blocks.  The remaining walls to the FULL
    payoff are the class-(1) chart-VALUE `Gc`-reshape (a forbidden capstone edit) and the class-(2)/(3)
    amplitude-`pd` composition — both orthogonal to the field-derivative measurability wall broken here.
    NOT `a₁ = R/6`.
    ############################################################################### -/

end QIQTH.FlowDerivMeasurable

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FlowDerivMeasurable
#print axioms update_eq_add_smul_single
#print axioms flowInverseJet_measurable
#print axioms flowInverseJet_measurable_component
#print axioms flowInverseSecondJet_measurable
#print axioms flowInverseSecondJet_measurable_component
end AxiomChecks
