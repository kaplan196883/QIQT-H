/-
# `QIQTH.ChartRepConstruction` — the jointly-measurable flow-inverse representative (J4-227)

## What this file delivers, and the precisely-named wall it does NOT cross.

`ChartJointBorel.a1_R6_assembled_v5` (J4-226) carries a single shared supplier obligation

  `hChartRep : ∃ F, Measurable F ∧ ∀ w, w.2.2 ∈ K →
                 uniformInverseChart g gi hC hK w.2.2 w.2.1 = F w`

i.e. a globally measurable joint representative `F` AGREEING with the uniform inverse chart on the
gate `{w.2.2 ∈ K}` — the residue the `.choose`-built `uniformInverseChart` forgot.  Recall
(`UniformChartRadius.lean`) that, on the gate, `uniformInverseChart g gi hC hK q = choose_q :=
((uniformChart_exists …).choose_spec.2 q hq).choose`, whose ONLY exposed property is the germ

  `(fun z => choose_q (uniformFlowExp g gi hC hK q z)) =ᶠ[nhds v] id`   for `‖v‖ < δ₀`,

i.e. `choose_q` is a `C²` LEFT INVERSE of the forward flow `φ_q = uniformFlowExp … q` **on the flow
image** `φ_q '' ball 0 δ₀`.  Off that image `choose_q` is the partial-homeomorph's `symm` on junk:
totally unconstrained by any banked fact.

### The Lusin–Souslin construction (what LANDS here — bankable, `std-3`, NOT `a₁ = R/6`)
The forward-flow graph map
    `Θ : (q, v) ↦ (q, uniformFlowExp g gi hC hK q v)`
is JOINTLY CONTINUOUS on `K ×ˢ ball 0 ρ_K` (`FlowJointContinuity.uniformFlowExp_joint_continuousOn`)
and INJECTIVE there (the germ left-inverse pins `v` from `(q, φ_q v)`).  On the Polish space
`Point n × Point n = (Fin n → ℝ)²`, Mathlib's Lusin–Souslin theorem
(`ContinuousOn.measurableEmbedding`) makes `Θ` restricted to the compact Borel set
`D = K ×ˢ closedBall 0 ρ` a MEASURABLE EMBEDDING.  Its measurable partial inverse
(`MeasurableEmbedding.exists_measurable_extend`) is a GLOBALLY measurable `G : Point² → Point` with
    `G (q, φ_q v) = v`   for all `q ∈ K`, `‖v‖ ≤ ρ`,
and, since `choose_q (φ_q v) = v` too, `G` AGREES with the chart on the flow-image points:
    `uniformInverseChart g gi hC hK q (φ_q v) = G (q, φ_q v)`.
`flowInverse_jointMeasurable_regional` is exactly this — the geometrically-true "measurable
flow-inverse on `K`" content that `ChartJointBorel`'s commentary named as the honest residue.

### HONEST FIREWALL — why this is REGIONAL, not the full `hChartRep`.
The `hChartRep` agreement is `∀ w` (ALL field points `p = w.2.1`), whereas the construction pins the
chart only at `p = φ_q v` (points IN the flow image `φ_q '' closedBall 0 ρ`).  For `p` OFF the image,
`choose_q p` is the partial-homeomorph `symm` on junk — unconstrained by any banked fact and carrying
NO measurable-in-`q` structure — so `choose_q p = G (q, p)` is UNPROVABLE, and hence the GLOBAL chart
measurability that `chartJoint_measurable_of_rep` / `tripleHEmeas_concrete` demand does NOT follow.
This is the same definitional wall `ChartJointBorel.lean`'s header states ("`q ↦ Classical.choose (h q)`
carries NO measurable-in-`q` structure … NOT provably measurable").  This file therefore delivers the
embedding/inverse-measurability LAYER and the on-image (regional) agreement — the largest honest
piece — but does NOT construct `hChartRep`, and does NOT thread `a1_R6_assembled_v6`.

No `sorry`, no new axioms, no `:= True`, no vacuous hypotheses.  Both `hΘcont`/`hΘinj` (continuity and
injectivity of the graph) and `hchart` (the germ) are load-bearing.  NOT `a₁ = R/6`.
-/
import QIQTH.FlowJointContinuity
import QIQTH.UniformChartRadius

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.FlowJointContinuity
open scoped Topology

namespace QIQTH.ChartRepConstruction

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-227 — `flowInverse_jointMeasurable_regional`: the jointly-measurable flow-inverse
    representative on `K`, via Lusin–Souslin.**  There is a uniform radius `ρ > 0` and a GLOBALLY
    measurable `G : Point² → Point` that agrees with the uniform inverse chart on every flow-image
    point over `K`:
        `∀ q ∈ K, ∀ v, ‖v‖ ≤ ρ → uniformInverseChart g gi hC hK q (φ_q v) = G (q, φ_q v)`,
    where `φ_q = uniformFlowExp g gi hC hK q`.  Construction: the graph map `Θ (q,v) = (q, φ_q v)` is
    jointly continuous (B2) and injective (germ left-inverse) on the compact Borel set
    `D = K ×ˢ closedBall 0 ρ`; Mathlib's `ContinuousOn.measurableEmbedding` makes `D.restrict Θ` a
    measurable embedding, and `MeasurableEmbedding.exists_measurable_extend` supplies the measurable
    inverse `G`.  This is the geometrically-true measurable flow-inverse content; it is REGIONAL
    (on-image) agreement — NOT the full `hChartRep` (see header firewall).  NOT `a₁ = R/6`. -/
theorem flowInverse_jointMeasurable_regional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ), ∃ G : Point n × Point n → Point n, Measurable G ∧
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ ρ →
        uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v)
          = G (q, uniformFlowExp g gi hC hK q v) := by
  classical
  -- germ radius `δg` (the left-inverse of `φ_q`) and the joint-continuity radius `R`.
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  set R : ℝ := uniformFlowRadius g gi hC hK with hRdef
  set ρ : ℝ := (min δg R) / 2 with hρdef
  have hminpos : 0 < min δg R := lt_min hδg hRpos
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρ_g : ρ < δg := by
    have hml : min δg R ≤ δg := min_le_left _ _
    rw [hρdef]; linarith
  have hρ_R : ρ < R := by
    have hmr : min δg R ≤ R := min_le_right _ _
    rw [hρdef]; linarith
  -- the germ, cleaned to a pointwise left inverse.
  have hLeftInv : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < δg →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
    intro q hq v hv
    have hgerm := ((hchart q hq).1 v hv).1
    simpa using hgerm.eq_of_nhds
  -- the forward-flow graph map `Θ` and its compact Borel domain `D`.
  set Θ : Point n × Point n → Point n × Point n :=
    fun p => (p.1, uniformFlowExp g gi hC hK p.1 p.2) with hΘ
  set D : Set (Point n × Point n) := K ×ˢ Metric.closedBall (0 : Point n) ρ with hD
  have hDmeas : MeasurableSet D := by
    rw [hD]; exact hK.isClosed.measurableSet.prod measurableSet_closedBall
  -- `D ⊆ K ×ˢ ball 0 R`, so joint continuity B2 restricts to `D`.
  have hDsub : D ⊆ K ×ˢ Metric.ball (0 : Point n) R := by
    rw [hD]; exact Set.prod_mono (Set.Subset.refl K) (Metric.closedBall_subset_ball hρ_R)
  have hsnd : ContinuousOn (fun p : Point n × Point n =>
      uniformFlowExp g gi hC hK p.1 p.2) D :=
    (uniformFlowExp_joint_continuousOn g gi hC hK).mono hDsub
  have hΘcont : ContinuousOn Θ D := by
    rw [hΘ]; exact (continuous_fst.continuousOn).prodMk hsnd
  -- injectivity of `Θ` on `D` via the germ left inverse at the (shared) base.
  have hΘinj : Set.InjOn Θ D := by
    intro x hx y hy hxy
    rw [hD, Set.mem_prod] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hx2n : ‖x.2‖ ≤ ρ := mem_closedBall_zero_iff.mp hx2
    have hy2n : ‖y.2‖ ≤ ρ := mem_closedBall_zero_iff.mp hy2
    rw [hΘ] at hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hx2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 x.2) = x.2 :=
      hLeftInv x.1 hx1 x.2 (lt_of_le_of_lt hx2n hρ_g)
    have hy2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 y.2) = y.2 :=
      hLeftInv x.1 hx1 y.2 (lt_of_le_of_lt hy2n hρ_g)
    have hval : uniformFlowExp g gi hC hK x.1 x.2 = uniformFlowExp g gi hC hK x.1 y.2 := by
      rw [h2, ← h1]
    have hxy2 : x.2 = y.2 := by rw [← hx2', hval, hy2']
    exact Prod.ext_iff.mpr ⟨h1, hxy2⟩
  -- Lusin–Souslin: `D.restrict Θ` is a measurable embedding.
  have hemb : MeasurableEmbedding (D.restrict Θ) :=
    ContinuousOn.measurableEmbedding hDmeas hΘcont hΘinj
  -- the measurable inverse `G` (extended off the image by the `0`-default).
  have hg_meas : Measurable (fun a : D => ((a : Point n × Point n).2)) :=
    measurable_snd.comp measurable_subtype_coe
  obtain ⟨G, hGmeas, hGcomp⟩ :=
    hemb.exists_measurable_extend hg_meas (fun _ => ⟨(0 : Point n)⟩)
  refine ⟨ρ, hρpos, G, hGmeas, ?_⟩
  intro q hq v hv
  have hmem : (q, v) ∈ D := by
    rw [hD]; exact Set.mem_prod.mpr ⟨hq, mem_closedBall_zero_iff.mpr hv⟩
  -- `G (Θ (q,v)) = v` from the extend identity `G ∘ (D.restrict Θ) = snd`.
  have hGval : G (Θ (q, v)) = v := by
    have hcf := congrFun hGcomp ⟨(q, v), hmem⟩
    simpa [Set.restrict_apply] using hcf
  -- rewrite the LHS by the germ, then close by `hGval`.
  rw [hLeftInv q hq v (lt_of_le_of_lt hv hρ_g)]
  have hΘqv : (q, uniformFlowExp g gi hC hK q v) = Θ (q, v) := by simp only [hΘ]
  rw [hΘqv]; exact hGval.symm

end QIQTH.ChartRepConstruction

/-! ## Axiom check — the public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ChartRepConstruction
#print axioms flowInverse_jointMeasurable_regional
end AxiomChecks
