/-
  B2MeasurabilityDissolution — J4-320: dissolving the **B2 chart/gate measurability wall cluster**
  (4 of the 9 hCConv walls) of the `CConvChartGateData` bundle, following the gpt-5.6-sol consult.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It dissolves
  interface artefacts and delivers per-wall discharges for the four B2 chart/gate-measurability fields
  (`hSmeasSet`, `hVmapMeas`, `hChartB`, `hSliceData`) of `QIQTH.CConvFacade.CConvChartGateData`.  No
  `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to the conclusion, no existing file edited, nothing committed.  Every carried
  hypothesis is SATISFIABLE (discharged from a banked builder or an honest smallness/geometry carry).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (M0) RECON — the three verdicts driving the dissolution.

  ── WALL 1 (`hSmeasSet : ∀ x₀∈u,∀ i,∀ᶠ x,∀ w, MeasurableSet {z | update x i w ∈ S z}`) — GRAPH-SHAPE
     VERDICT.  The banked graph measurability (`ConcreteGateInstantiation.hKSmeas_concrete`) proves the
     `K`-RESTRICTED joint graph `{w : ℝ×Point×Point | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` is `MeasurableSet`
     (Lusin–Souslin on the compact `K`).  Its `z`-slice at a FIXED field point `p := update x i w` is the
     preimage of that graph under the measurable section `z ↦ (0, p, z)`, so the K-restricted slice
     `{z | z ∈ K ∧ p ∈ S z}` is `MeasurableSet` (`hSmeasSet_Krestricted`).  The field's RAW set
     `{z | p ∈ S z}` (no `K`-guard) is NOT derivable: off `K` the Lusin–Souslin embedding (which needs
     compactness) supplies nothing, and `{z ∉ K | p ∈ φ_z '' ball 0 c}` is a projection of an analytic —
     not provably Borel — set.  HONEST RESIDUE: the K-restricted slice is the largest provable piece; the
     raw off-`K` slice is documented as an open gap (it is the same off-`K` chart-junk wall as `hVmapMeas`).

  ── WALLS 2/3 (`hVmapMeas`, `hChartB` — z-measurability of the off-image inverse chart) — W-PARAMETER
     VERDICT.  `structure CConvChartGateData g gi hC hK S a b t u` HARDWIRES the chart to
     `uniformInverseChart g gi hC hK` (it is NOT a bundle parameter).  The raw `.choose`-built
     `uniformInverseChart z p` is garbage off the flow-image and its AEMeasurability is UNPROVABLE (the
     off-image set is not null).  We therefore deliver the discharges at the PIECEWISE-CHART representative
        `Wg Γ G z p := if (z,p) ∈ Γ then G (z,p) else 0`,
     `Γ = {(z,p) | z ∈ K ∧ p ∈ S z}` the banked graph and `G` the banked jointly-measurable regional
     flow-inverse (`ChartRepConstruction.flowInverse_jointMeasurable_regional`).  `Wg` is jointly
     measurable (`Measurable.ite`), so walls 2 and 3 close AT `Wg` by composition with measurable sections;
     and on the on-gate set `Wg z` agrees with `uniformInverseChart z` on a NEIGHBOURHOOD (regional
     agreement + `S z` open), so the `hCover` field's on-gate `C²` transfers to `Wg`
     (`wg_contDiffAt_onGate`).  HONEST VERDICT: because the facade hardwires `uniformInverseChart`, these
     `Wg` discharges do NOT plug into the CURRENT bundle as-is; they show the fix is a facade REFACTOR
     (take the chart as a parameter, instantiate with `Wg`) that changes ONLY the chart field — the
     witness `vanVleckGatedWitness` is unaffected (it multiplies by the gate indicator, not by `Wg`).

  ── WALL 4 (`hSliceData` — off-gate `radialCutoff`-vanishing + inner-field continuity) — SUPPORT-MARGIN
     INVENTORY.  The strict margin `b < c` (`ConstRadiusGateExport`: the cutoff radius `b` sits strictly
     inside the gate radius `c = (b+ρc)/2`) yields the FRONTIER-COLLAR vanishing: for `q` on the gate
     frontier (`q ∈ closure (S z) \ S z`), the germ inverse forces `‖W z q‖ = c > b`, so
     `radialCutoff a b (W z q) = 0` (`radialCutoff_zero_on_frontier_collar`, = the banked `LEG-3`
     computation).  HONEST RESIDUE: the FULL leg (a) `∀ q ∉ S z` also demands vanishing on the FAR region
     (`q ∉ closure (S z)`), where the raw chart is unconstrained junk — NOT provable.  Leg (b) (inner-field
     `w`-continuity along `update x i ·`) is left as an honest residue: it needs continuity of the chart
     along a line crossing the gate boundary, which fails off-image for the raw chart.

  ## WHAT THIS FILE LANDS
    • `gateGraph2_measurableSet`         — the 2-var `(z,p)` graph from the banked 3-var graph (helper).
    • `hSmeasSet_Krestricted`            — (M1) WALL 1, K-restricted z-slice measurability.
    • `hSmeasSet_field_Krestricted`      — (M1) WALL 1 in the field's `∀ᶠ x, ∀ w` shape, at the flow gate.
    • `Wg` + `wg_zslice_measurable`      — (M2) WALL 2 (`hVmapMeas` core) at `Wg`.
    • `wg_vmap_aemeasurable`             — (M2) WALL 2 (`hVmapMeas`) exact AEMeasurable shape at `Wg`.
    • `wg_chartB_measurable`             — (M2) WALL 3 (`hChartB`) at `Wg`.
    • `wg_eventuallyEq_chart_onGate`     — (M2) `Wg z =ᶠ uniformInverseChart z` near on-gate points.
    • `wg_contDiffAt_onGate`             — (M2) the on-gate `C²` transfer `Wg` inherits from the chart.
    • `wg_walls23_from_banked`           — (M2) satisfiability: `Wg`'s data all sourced from banked builders.
    • `radialCutoff_zero_on_frontier_collar` — (M3) WALL 4 leg (a), frontier-collar cutoff vanishing.

  ## UPDATED hCConv WALL COUNT.  Of the 9 hCConv walls, the B2 cluster (4 walls) is addressed:
    • `hSmeasSet` (WALL 1): FELL to a proved K-restricted discharge (raw off-`K` residue documented).
    • `hVmapMeas`, `hChartB` (WALLS 2/3): DISSOLVED as interface artefacts — the discharges hold at the
      piecewise chart `Wg`; the residue is the honest facade-refactor verdict (chart must be a parameter).
    • `hSliceData` (WALL 4): PARTIAL — frontier-collar leg (a) proved; far-region + leg (b) residues honest.
  Remaining hCConv W-surface: `hFbd`, `hlin`, `hDrep`, `hGateData`, `hGateData'` (unchanged), plus the two
  documented B2 residues (raw off-`K` slice / off-image chart continuity) that are the SAME off-image
  chart-junk wall.  ⚠  STILL NOT `a₁ = R/6`; every carried hypothesis is an honest satisfiable input.
-/
import QIQTH.ChartRepConstruction
import QIQTH.ConcreteGateInstantiation
import QIQTH.ConcreteGateAssembly
import QIQTH.ZeroCollarLocalZero

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.ChartRepConstruction QIQTH.ConcreteGateInstantiation QIQTH.ConcreteGateAssembly
open QIQTH.ZeroCollarLocalZero
open scoped Topology

namespace QIQTH.B2MeasurabilityDissolution

open Classical

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (M1) — WALL 1 (`hSmeasSet`): the K-restricted z-slice measurability.
    ############################################################################### -/

/-- **★ `gateGraph2_measurableSet` — the 2-variable `(z,p)` gate graph.**  From the banked 3-variable
    joint graph `{w : ℝ×Point×Point | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}` (Lusin–Souslin,
    `ConcreteGateInstantiation.hKSmeas_concrete`), the `(z,p)`-graph `{(z,p) | z ∈ K ∧ p ∈ S z}` is
    `MeasurableSet`: it is the preimage of the 3-var graph under the measurable section
    `q ↦ (0, q.2, q.1)`.  NOT `a₁ = R/6`. -/
theorem gateGraph2_measurableSet {K : Set (Point n)} {S : Point n → Set (Point n)}
    (hGraph : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}) :
    MeasurableSet {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1} := by
  have hsec : Measurable (fun q : Point n × Point n => ((0 : ℝ), q.2, q.1)) :=
    measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
  simpa only [Set.preimage_setOf_eq] using hGraph.preimage hsec

/-- **★ (M1) WALL 1 — `hSmeasSet_Krestricted`.**  The `z`-slice of the banked joint gate graph at a FIXED
    field point `p`.  Given the graph measurability `{w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`, the K-restricted
    slice `{z | z ∈ K ∧ p ∈ S z}` is `MeasurableSet` — it is the preimage of the graph under the
    measurable section `z ↦ (0, p, z)`.  This is the largest provable piece of the `hSmeasSet` field
    (the raw off-`K` slice `{z | p ∈ S z}` is the documented off-image residue).  NOT `a₁ = R/6`. -/
theorem hSmeasSet_Krestricted {K : Set (Point n)} {S : Point n → Set (Point n)}
    (hGraph : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (p : Point n) :
    MeasurableSet {z : Point n | z ∈ K ∧ p ∈ S z} := by
  have hsec : Measurable (fun z : Point n => ((0 : ℝ), p, z)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  simpa only [Set.preimage_setOf_eq] using hGraph.preimage hsec

/-- **★★ (M1) WALL 1 field shape — `hSmeasSet_field_Krestricted`.**  The `CConvChartGateData.hSmeasSet`
    field at the CONSTANT-RADIUS flow-ball gate `S z = uniformFlowExp g gi hC hK z '' ball 0 c`, in its
    exact `∀ x₀∈u, ∀ i, ∀ᶠ x, ∀ w` shape but with the honest `K`-guard prepended to the slice set: there
    is a uniform reach `δ₀ > 0` such that for every `0 < c < δ₀`, on all `x` and all `w`, the K-restricted
    slice `{z | z ∈ K ∧ update x i w ∈ φ_z '' ball 0 c}` is `MeasurableSet`.  The reach/graph come from
    `hKSmeas_concrete`; the `∀ᶠ x` holds for ALL `x`.  The `K`-guard is the honest residue vs the raw
    field (off-`K` chart junk).  NOT `a₁ = R/6`. -/
theorem hSmeasSet_field_Krestricted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (u : Set (Point n)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | z ∈ K ∧
          (Function.update x i w) ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c} := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := hKSmeas_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ x₀ _hx₀ i
  refine Filter.Eventually.of_forall (fun x => ?_)
  intro w
  exact hSmeasSet_Krestricted (hspec c hc0 hcδ) (Function.update x i w)

/-! ###############################################################################
    ### (M2) — WALLS 2/3 (`hVmapMeas`, `hChartB`): the piecewise-chart `Wg`.
    ############################################################################### -/

/-- **The piecewise-chart representative `Wg`.**  On the gate graph `Γ` it is the banked jointly-measurable
    regional flow-inverse `G`; off `Γ` it is `0`.  This is the interface fix for the off-image chart-junk
    walls: `Wg` is jointly measurable (unlike the raw `.choose`-built `uniformInverseChart`), and it agrees
    with the chart on-gate (where `G` = the true inverse).  Parametrised by `Γ` and `G` so it carries no
    `.choose`.  NOT `a₁ = R/6`. -/
noncomputable def Wg (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (z p : Point n) : Point n :=
  if (z, p) ∈ Γ then G (z, p) else 0

/-- **★★ (M2) WALL 2 core — `wg_zslice_measurable`.**  For fixed field point `p₀`, the `z`-slice
    `z ↦ Wg Γ G z p₀` is `Measurable` (given the graph `Γ` measurable and `G` measurable): it is the
    `ite` over the measurable set `{z | (z,p₀) ∈ Γ}` of the measurable `z ↦ G (z,p₀)` and the constant
    `0`.  NOT `a₁ = R/6`. -/
theorem wg_zslice_measurable (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hΓ : MeasurableSet Γ) (hG : Measurable G) (p₀ : Point n) :
    Measurable (fun z : Point n => Wg Γ G z p₀) := by
  have hsec : Measurable (fun z : Point n => (z, p₀)) := measurable_id.prodMk measurable_const
  have hset : MeasurableSet {z : Point n | (z, p₀) ∈ Γ} := hΓ.preimage hsec
  have hf : Measurable (fun z : Point n => G (z, p₀)) := hG.comp hsec
  have hrw : (fun z : Point n => Wg Γ G z p₀)
      = (fun z : Point n => if (z, p₀) ∈ Γ then G (z, p₀) else 0) := by
    funext z; simp only [Wg]
  rw [hrw]
  exact Measurable.ite hset hf measurable_const

/-- **★★ (M2) WALL 2 — `wg_vmap_aemeasurable`.**  The exact `hVmapMeas` shape at `Wg`: for fixed field
    point `p₀`, `z ↦ Wg Γ G z p₀` is `AEMeasurable` for `volume`, from `wg_zslice_measurable`.  NOT
    `a₁ = R/6`. -/
theorem wg_vmap_aemeasurable (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hΓ : MeasurableSet Γ) (hG : Measurable G) (p₀ : Point n) :
    AEMeasurable (fun z : Point n => Wg Γ G z p₀) (volume : Measure (Point n)) :=
  (wg_zslice_measurable Γ G hΓ hG p₀).aemeasurable

/-- **★★ (M2) WALL 3 — `wg_chartB_measurable`.**  For fixed field point `p₀`, the map
    `p ↦ Wg Γ G p.2 p₀` on `ℝ × Point` is `Measurable`: the `ite` over the measurable set
    `{p | (p.2,p₀) ∈ Γ}` of the measurable `p ↦ G (p.2,p₀)` and the constant `0`.  This is the
    `Measurable` (not merely `AEMeasurable`) strengthening the `hChartB` field asks for, at `Wg`.  NOT
    `a₁ = R/6`. -/
theorem wg_chartB_measurable (Γ : Set (Point n × Point n)) (G : Point n × Point n → Point n)
    (hΓ : MeasurableSet Γ) (hG : Measurable G) (p₀ : Point n) :
    Measurable (fun p : ℝ × Point n => Wg Γ G p.2 p₀) := by
  have hsec : Measurable (fun p : ℝ × Point n => (p.2, p₀)) :=
    measurable_snd.prodMk measurable_const
  have hset : MeasurableSet {p : ℝ × Point n | (p.2, p₀) ∈ Γ} := hΓ.preimage hsec
  have hf : Measurable (fun p : ℝ × Point n => G (p.2, p₀)) := hG.comp hsec
  have hrw : (fun p : ℝ × Point n => Wg Γ G p.2 p₀)
      = (fun p : ℝ × Point n => if (p.2, p₀) ∈ Γ then G (p.2, p₀) else 0) := by
    funext p; simp only [Wg]
  rw [hrw]
  exact Measurable.ite hset hf measurable_const

/-- **★★ (M2) `wg_eventuallyEq_chart_onGate` — `Wg` agrees with the chart near on-gate points.**  At the
    constant-radius flow-ball gate `S z = φ_z '' ball 0 c` (with `c ≤ ρ`, `ρ` the regional-agreement
    radius), for `z ∈ K` and a gate point `x ∈ S z` with `S z` OPEN, the section `Wg Γ G z` equals the
    inverse chart `uniformInverseChart g gi hC hK z` on a NEIGHBOURHOOD of `x`.  Reason: on `S z` (open,
    hence eventually), every `x' = φ_z v` with `‖v‖ < c ≤ ρ` satisfies `(z,x') ∈ Γ`, so
    `Wg Γ G z x' = G (z,x')`, and the regional agreement gives `uniformInverseChart z x' = G (z,x')` too.
    NOT `a₁ = R/6`. -/
theorem wg_eventuallyEq_chart_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {S : Point n → Set (Point n)}
    {Γ : Set (Point n × Point n)} (hΓeq : Γ = {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1})
    (G : Point n × Point n → Point n)
    (z : Point n) (hzK : z ∈ K) (c ρ : ℝ) (hcρ : c ≤ ρ)
    (hSz : S z = uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hSzopen : IsOpen (S z))
    (hagree : ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v)
          = G (z, uniformFlowExp g gi hC hK z v))
    {x : Point n} (hxSz : x ∈ S z) :
    (fun p : Point n => Wg Γ G z p) =ᶠ[nhds x] (uniformInverseChart g gi hC hK z) := by
  filter_upwards [hSzopen.mem_nhds hxSz] with x' hx'
  have hx'img : x' ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c := by
    rwa [hSz] at hx'
  obtain ⟨v, hv, hvx⟩ := hx'img
  rw [mem_ball_zero_iff] at hv
  have hvρ : ‖v‖ ≤ ρ := le_trans (le_of_lt hv) hcρ
  have hxΓ : (z, x') ∈ Γ := by
    rw [hΓeq]
    exact ⟨hzK, hx'⟩
  have hWg : Wg Γ G z x' = G (z, x') := by simp only [Wg, if_pos hxΓ]
  have hchart : uniformInverseChart g gi hC hK z x' = G (z, x') := by
    rw [← hvx]; exact hagree v hvρ
  rw [hWg, hchart]

/-- **★★ (M2) `wg_contDiffAt_onGate` — the on-gate `C²` transfer.**  Under the hypotheses of
    `wg_eventuallyEq_chart_onGate`, the `hCover` field's on-gate `C²` regularity of the inverse chart
    transfers to `Wg`: if `uniformInverseChart g gi hC hK z` is `C²` at the gate point `x`, so is
    `Wg Γ G z` (via `ContDiffAt.congr_of_eventuallyEq`).  This is what lets a facade instantiated with
    `Wg` still satisfy the `hCover` field.  NOT `a₁ = R/6`. -/
theorem wg_contDiffAt_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {S : Point n → Set (Point n)}
    {Γ : Set (Point n × Point n)} (hΓeq : Γ = {q : Point n × Point n | q.1 ∈ K ∧ q.2 ∈ S q.1})
    (G : Point n × Point n → Point n)
    (z : Point n) (hzK : z ∈ K) (c ρ : ℝ) (hcρ : c ≤ ρ)
    (hSz : S z = uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
    (hSzopen : IsOpen (S z))
    (hagree : ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v)
          = G (z, uniformFlowExp g gi hC hK z v))
    {x : Point n} (hxSz : x ∈ S z)
    (hWc2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x) :
    ContDiffAt ℝ 2 (fun p : Point n => Wg Γ G z p) x :=
  hWc2.congr_of_eventuallyEq
    (wg_eventuallyEq_chart_onGate g gi hC hK hΓeq G z hzK c ρ hcρ hSz hSzopen hagree hxSz)

/-- **★★★ (M2) `wg_walls23_from_banked` — SATISFIABILITY: `Wg`'s data sourced from banked builders.**  At
    the constant-radius flow-ball gate `S z = φ_z '' ball 0 c`, the joint-measurability data feeding the
    `Wg` discharges are ALL banked: there is a regional-agreement radius `ρ > 0` and a globally measurable
    `G` (`ChartRepConstruction.flowInverse_jointMeasurable_regional`) and a reach `δ₀ > 0` such that for
    every `0 < c < δ₀` the graph `Γ = {(z,p) | z ∈ K ∧ p ∈ S z}` is measurable
    (`ConcreteGateInstantiation.hKSmeas_concrete` + `gateGraph2_measurableSet`); consequently WALLS 2 and 3
    hold at `Wg Γ G` for every fixed field point `p₀` — `z ↦ Wg Γ G z p₀` is measurable (hence
    `AEMeasurable`) and `p ↦ Wg Γ G p.2 p₀` is measurable.  This certifies the `Wg` hypotheses (`Γ`
    measurable, `G` measurable, `hagree`) are satisfiable, not vacuous.  NOT `a₁ = R/6`. -/
theorem wg_walls23_from_banked (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ G : Point n × Point n → Point n, Measurable G ∧
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)
          = G (q, uniformFlowExp g gi hC hK q v)) ∧
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
        MeasurableSet {q : Point n × Point n | q.1 ∈ K ∧
            q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c}
        ∧ (∀ p₀ : Point n,
            Measurable (fun z : Point n =>
              Wg {q : Point n × Point n | q.1 ∈ K ∧
                    q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c} G z p₀)
            ∧ AEMeasurable (fun z : Point n =>
                Wg {q : Point n × Point n | q.1 ∈ K ∧
                      q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c} G z p₀)
                (volume : Measure (Point n))
            ∧ Measurable (fun p : ℝ × Point n =>
                Wg {q : Point n × Point n | q.1 ∈ K ∧
                      q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c} G p.2 p₀)) := by
  obtain ⟨ρ, hρ, G, hGmeas, hagree⟩ := flowInverse_jointMeasurable_regional g gi hC hK
  obtain ⟨δ₀, hδ₀, hspec⟩ := hKSmeas_concrete g gi hC hK
  refine ⟨ρ, hρ, G, hGmeas, hagree, δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ
  have hΓ : MeasurableSet {q : Point n × Point n | q.1 ∈ K ∧
      q.2 ∈ uniformFlowExp g gi hC hK q.1 '' Metric.ball (0 : Point n) c} :=
    gateGraph2_measurableSet
      (S := fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
      (hspec c hc0 hcδ)
  refine ⟨hΓ, fun p₀ => ⟨?_, ?_, ?_⟩⟩
  · exact wg_zslice_measurable _ G hΓ hGmeas p₀
  · exact wg_vmap_aemeasurable _ G hΓ hGmeas p₀
  · exact wg_chartB_measurable _ G hΓ hGmeas p₀

/-! ###############################################################################
    ### (M3) — WALL 4 (`hSliceData`): the frontier-collar cutoff vanishing (leg a).
    ############################################################################### -/

/-- **★★ (M3) WALL 4 leg (a) — `radialCutoff_zero_on_frontier_collar`.**  The strict support margin
    `b < c` gives cutoff vanishing on the gate FRONTIER.  For `z ∈ K` and the constant-radius gate
    `S z = φ_z '' ball 0 c`, given the germ left-inverse on the closed ball (`hgerm`) and the closure
    collar `closure (S z) ⊆ φ_z '' closedBall 0 c` (`hclos`, both banked in
    `ConstRadiusGateExport`), any frontier point `q ∈ closure (S z)` with `q ∉ S z` has chart image at
    radius exactly `c > b`, so `radialCutoff a b (uniformInverseChart g gi hC hK z q) = 0`.  This is the
    LEG-3 computation banked in `GateOpennessExport`, extracted as the off-gate cutoff-vanishing leg of
    `hSliceData` on the frontier collar.  HONEST RESIDUE: the far region `q ∉ closure (S z)` is NOT
    covered (raw chart junk).  NOT `a₁ = R/6`. -/
theorem radialCutoff_zero_on_frontier_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {a b c : ℝ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (z : Point n)
    (hgerm : ∀ v : Point n, ‖v‖ ≤ c →
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hclos : closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
        ⊆ uniformFlowExp g gi hC hK z '' Metric.closedBall (0 : Point n) c)
    {q : Point n}
    (hqcl : q ∈ closure (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c))
    (hqS : q ∉ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) :
    radialCutoff a b (uniformInverseChart g gi hC hK z q) = 0 := by
  have hb0 : 0 < b := lt_trans ha hab
  obtain ⟨w', hw', hw'q⟩ := hclos hqcl
  rw [mem_closedBall_zero_iff] at hw'
  have hnormeq : ‖w'‖ = c := by
    rcases lt_or_eq_of_le hw' with hlt | heq
    · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'q⟩ :
        q ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) hqS
    · exact heq
  have hWq : uniformInverseChart g gi hC hK z q = w' := by
    rw [← hw'q]; exact hgerm w' hw'
  have hb2 : b ^ 2 ≤ rncRadialSq (uniformInverseChart g gi hC hK z q) := by
    rw [hWq]
    have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
      have hle := norm_le_rncRadial w'
      have hsq := rncRadial_sq w'
      nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, hsq]
    nlinarith [h1, hnormeq, hb0, hbc]
  exact radialCutoff_eq_zero ha hab hb2

end QIQTH.B2MeasurabilityDissolution

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.B2MeasurabilityDissolution
#print axioms gateGraph2_measurableSet
#print axioms hSmeasSet_Krestricted
#print axioms hSmeasSet_field_Krestricted
#print axioms wg_zslice_measurable
#print axioms wg_vmap_aemeasurable
#print axioms wg_chartB_measurable
#print axioms wg_eventuallyEq_chart_onGate
#print axioms wg_contDiffAt_onGate
#print axioms wg_walls23_from_banked
#print axioms radialCutoff_zero_on_frontier_collar
end AxiomChecks
