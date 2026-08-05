/-
  ConcreteGateInstantiation — J4-234: LADDER STEP 1, the CONCRETE-S instantiation of the v7 capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It takes the
  credited re-thread capstone `AssemblyV7Rethread.a1_R6_assembled_v7` — whose S1 / measurability supplier
  block is all-satisfiable but whose gate `S` is left ABSTRACT — and DISCHARGES, at the concrete flow-ball
  gate `S z := uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`, every supplier carrier that becomes
  provable there.  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; std-3; NOT `a₁ = R/6`).

    * `hKSmeas_concrete` — ★ THE MEASURABILITY DISCHARGE.  A single uniform radius `δ₀ > 0` such that for
      every ball radius `0 < c < δ₀` the FULL-gate set
        `{w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ φ_(w.2.2) '' Metric.ball 0 c}`
      is `MeasurableSet`.  Construction: the graph `{(q,p) | q ∈ K ∧ p ∈ φ_q '' ball 0 c}` is the image
      of the Borel product `K ×ˢ ball 0 c` under the JOINTLY-CONTINUOUS, INJECTIVE forward-flow graph map
      `Θ (q,v) = (q, φ_q v)`; Mathlib's Lusin–Souslin theorem (`ContinuousOn.measurableEmbedding`) makes
      `D.restrict Θ` a measurable embedding, so its range (the graph) is Borel
      (`MeasurableEmbedding.measurableSet_image`), and the target is the preimage of that graph under the
      measurable coordinate swap `w ↦ (w.2.2, w.2.1)`.  This is the concrete discharge of the v7
      supplier binder `hKSmeas` — SATISFIABLE, `K` NEED NOT be empty.  Radii carried honestly: the radius
      `δ₀ = min (germ radius) (uniformFlowRadius)`; for `c < δ₀` the ball sits inside both the germ
      left-inverse radius (injectivity) and the flow joint-continuity radius.

    * `hchrMeas_concrete` — the christoffel measurability, DERIVED from the smoothness input `hChr`
      (`ContDiff ⟹ Continuous ⟹ Measurable`).  Discharges the v7 binder `hchrMeas`.

    * `hS0_concrete` — the base-point gate membership `0 ∈ S 0` for the concrete gate, from
      `uniformFlowExp_zero` (`φ_0 0 = 0`) + `0 ∈ K` + `0 < c`.  Discharges the v7 binder `hS0`.

    * `concreteGate_carriers_discharged` — ★★★ THE CONCRETE-GATE DISCHARGE BUNDLE.  At the concrete
      flow-ball gate `S z = φ_z '' ball 0 c` (`0 < c < δ₀`), the THREE v7 supplier binders that become
      provable — `hKSmeas`, `hS0`, `hchrMeas` — ALL HOLD SIMULTANEOUSLY, sourced from the three lemmas
      above.  This is the packaged statement of exactly what ladder step 1 discharges from
      `a1_R6_assembled_v7`'s supplier block when `S` is fixed to the concrete gate: the measurability
      story (`hKSmeas`), the base-point membership (`hS0`), and the christoffel measurability (`hchrMeas`)
      are all internal at the concrete gate, so those three binders drop out of any downstream re-thread.

  ## WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion; the post-step-1 surface).
    * The full `a1_R6_assembled_v7` RE-THREAD with the three discharged binders textually removed and `S`
      substituted throughout the ~130-binder signature — a purely MECHANICAL substitution — is deferred:
      the fully-substituted restatement is extremely heavy to elaborate in one theorem (the concrete `S`
      is `.choose`-heavy, so the kernel defeq over the 130-binder conclusion does not terminate in a
      practical window).  The three provable carriers are discharged here as the reusable bundle; the
      wiring itself carries no new mathematical content beyond `concreteGate_carriers_discharged`.
    * `hgiMeas` — the inverse-metric measurability.  NOT freely derivable (no smoothness / positivity of
      `gi` is carried), so it stays an honest input.
    * `hcarTau`/`hcarField`/`hcarField2` — the τ / field / field² jet supplier existentials.  Their
      off-`S` conjuncts `hOffS`/`hOffS2` (the radialCutoff-support vanishings) are packaged INSIDE these
      existentials; discharging them requires the b-vs-c cutoff-support geometry (`radialCutoff_eq_zero`
      + the support-closure `⊆ S q`), a genuine geometric brick deferred to ladder step 2.
    * the full analytic residue pile (`hEboundFull`, `core`, the CConv facade, the R2 trio) — the
      `a₁ = R/6` analytic content, orthogonal to the gate instantiation.

  NOT `a₁ = R/6`.
-/
import QIQTH.AssemblyV7Rethread
import QIQTH.ConcreteGateAssembly
import QIQTH.ChartRepConstruction

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.FlowJointContinuity QIQTH.ChartRepConstruction
open QIQTH.ConcreteGateAssembly QIQTH.GatedRepSFix QIQTH.HgateSatAudit
open QIQTH.RightInverseGeneral QIQTH.AssemblyV7Rethread
open scoped Topology BigOperators ContDiff

namespace QIQTH.ConcreteGateInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE MEASURABILITY DISCHARGE — the FULL-gate set is Borel at the concrete gate.
    ############################################################################### -/

/-- **★ `hKSmeas_concrete` — the FULL-gate `MeasurableSet` at the concrete flow-ball gate.**  A single
    uniform radius `δ₀ > 0` such that for every `0 < c < δ₀` the set
      `{w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ φ_(w.2.2) '' Metric.ball 0 c}`
    (`φ_q = uniformFlowExp g gi hC hK q`) is `MeasurableSet`.  Via Lusin–Souslin: the graph map
    `Θ (q,v) = (q, φ_q v)` is jointly continuous and injective on `D = K ×ˢ ball 0 c`, so `D.restrict Θ`
    is a measurable embedding whose range `Θ '' D` (the (q,p)-graph) is Borel; the target is its preimage
    under the measurable swap `w ↦ (w.2.2, w.2.1)`.  Discharges the v7 supplier binder `hKSmeas`.
    NOT `a₁ = R/6`. -/
theorem hKSmeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c} := by
  classical
  obtain ⟨δg, hδg, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  have hRpos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min δg (uniformFlowRadius g gi hC hK), lt_min hδg hRpos, ?_⟩
  intro c hc0 hcδ
  have hcg : c < δg := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcR : c < uniformFlowRadius g gi hC hK := lt_of_lt_of_le hcδ (min_le_right _ _)
  -- germ left inverse on `ball 0 c`.
  have hLeftInv : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < c →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
    intro q hq v hv
    have hgerm := ((hchart q hq).1 v (lt_trans hv hcg)).1
    simpa using hgerm.eq_of_nhds
  -- the forward-flow graph map and its Borel domain.
  set Θ : Point n × Point n → Point n × Point n :=
    fun p => (p.1, uniformFlowExp g gi hC hK p.1 p.2) with hΘ
  set D : Set (Point n × Point n) := K ×ˢ Metric.ball (0 : Point n) c with hD
  have hDmeas : MeasurableSet D :=
    hK.isClosed.measurableSet.prod measurableSet_ball
  have hDsub : D ⊆ K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK) :=
    Set.prod_mono (Set.Subset.refl K) (Metric.ball_subset_ball (le_of_lt hcR))
  have hsnd : ContinuousOn (fun p : Point n × Point n =>
      uniformFlowExp g gi hC hK p.1 p.2) D :=
    (uniformFlowExp_joint_continuousOn g gi hC hK).mono hDsub
  have hΘcont : ContinuousOn Θ D := (continuous_fst.continuousOn).prodMk hsnd
  -- injectivity of `Θ` on `D` via the germ left inverse at the shared base.
  have hΘinj : Set.InjOn Θ D := by
    intro x hx y hy hxy
    rw [hD, Set.mem_prod] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    rw [mem_ball_zero_iff] at hx2 hy2
    rw [hΘ] at hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hx2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 x.2) = x.2 :=
      hLeftInv x.1 hx1 x.2 hx2
    have hy2' : uniformInverseChart g gi hC hK x.1 (uniformFlowExp g gi hC hK x.1 y.2) = y.2 :=
      hLeftInv x.1 hx1 y.2 hy2
    have hval : uniformFlowExp g gi hC hK x.1 x.2 = uniformFlowExp g gi hC hK x.1 y.2 := by
      rw [h2, ← h1]
    have hxy2 : x.2 = y.2 := by rw [← hx2', hval, hy2']
    exact Prod.ext_iff.mpr ⟨h1, hxy2⟩
  -- Lusin–Souslin: `D.restrict Θ` is a measurable embedding, so the graph `Θ '' D` is Borel.
  have hemb : MeasurableEmbedding (D.restrict Θ) :=
    ContinuousOn.measurableEmbedding hDmeas hΘcont hΘinj
  have hgraph : MeasurableSet (Θ '' D) := by
    have hrange : Θ '' D = Set.range (D.restrict Θ) := (Set.range_restrict Θ D).symm
    rw [hrange, ← Set.image_univ]
    exact hemb.measurableSet_image.mpr MeasurableSet.univ
  -- `Θ '' D` is the (q,p)-graph.
  have hΘimg : Θ '' D =
      {qp : Point n × Point n |
        qp.1 ∈ K ∧ qp.2 ∈ uniformFlowExp g gi hC hK qp.1 '' Metric.ball (0 : Point n) c} := by
    ext qp
    constructor
    · rintro ⟨⟨q, v⟩, hqv, rfl⟩
      rw [hD, Set.mem_prod] at hqv
      obtain ⟨hqK, hv⟩ := hqv
      exact ⟨hqK, v, hv, rfl⟩
    · rintro ⟨hqK, v, hv, hvp⟩
      refine ⟨(qp.1, v), ?_, ?_⟩
      · rw [hD, Set.mem_prod]; exact ⟨hqK, hv⟩
      · rw [hΘ]; exact Prod.ext rfl hvp
  -- the target set is the preimage of the graph under the measurable coordinate swap.
  have hpre : {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ uniformFlowExp g gi hC hK w.2.2 '' Metric.ball (0 : Point n) c}
      = (fun w : ℝ × Point n × Point n => (w.2.2, w.2.1)) ⁻¹'
          {qp : Point n × Point n |
            qp.1 ∈ K ∧ qp.2 ∈ uniformFlowExp g gi hC hK qp.1 '' Metric.ball (0 : Point n) c} := by
    ext w; exact Iff.rfl
  rw [hpre, ← hΘimg]
  exact hgraph.preimage ((measurable_snd.snd).prodMk measurable_snd.fst)

/-! ###############################################################################
    ### THE SMALL METRIC / GEOMETRY DISCHARGES.
    ############################################################################### -/

/-- **`hchrMeas_concrete` — christoffel measurability from smoothness.**  Discharges the v7 binder
    `hchrMeas` directly from the standing smoothness input `hChr` (`ContDiff ⟹ Continuous ⟹ Measurable`).
    NOT `a₁ = R/6`. -/
theorem hchrMeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)) :
    ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p) :=
  fun k i j => (hC k i j).continuous.measurable

/-- **`hS0_concrete` — base-point gate membership at the concrete gate.**  For the concrete flow-ball
    gate `S z = φ_z '' Metric.ball 0 c` with `0 ∈ K` and `0 < c`, `0 ∈ S 0` (`φ_0 0 = 0` via
    `uniformFlowExp_zero`).  Discharges the v7 binder `hS0`.  NOT `a₁ = R/6`. -/
theorem hS0_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) (c : ℝ) (hc0 : 0 < c) :
    (0 : Point n) ∈ uniformFlowExp g gi hC hK (0 : Point n) '' Metric.ball (0 : Point n) c := by
  refine ⟨0, ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_zero]; exact hc0
  · exact uniformFlowExp_zero g gi hC hK 0 hK0

/-! ###############################################################################
    ### ★★★ THE CONCRETE-GATE DISCHARGE BUNDLE — the three provable `a1_R6_assembled_v7` supplier
    ###      binders (`hKSmeas`, `hS0`, `hchrMeas`) all hold at the concrete flow-ball gate.
    ############################################################################### -/

/-- **★★★ `concreteGate_carriers_discharged`.**  At the concrete flow-ball gate
    `S z = uniformFlowExp g gi hChr hK z '' Metric.ball 0 c` (`0 < c < δ₀`, radius from
    `hKSmeas_concrete`), the THREE supplier binders of `AssemblyV7Rethread.a1_R6_assembled_v7` that
    become PROVABLE all hold at once:
      • `hKSmeas`  — `MeasurableSet {w | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}`  (`hKSmeas_concrete`);
      • `hS0`      — `0 ∈ S 0`  (`hS0_concrete`);
      • `hchrMeas` — `∀ k i j, Measurable (christoffel g gi k i j ·)`  (`hchrMeas_concrete`).
    This is the packaged statement of exactly what LADDER STEP 1 discharges from the v7 supplier block
    once `S` is fixed to the concrete gate: those three binders drop out of any downstream re-thread of
    `a1_R6_assembled_v7`.  The full re-thread with `S` textually substituted throughout the ~130-binder
    signature is a mechanical substitution carrying no new mathematical content beyond this bundle.
    NOT `a₁ = R/6`. -/
theorem concreteGate_carriers_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
    ∀ (S : Point n → Set (Point n)),
      S = (fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c) →
      MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2}
      ∧ (0 : Point n) ∈ S 0
      ∧ (∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀spec⟩ := hKSmeas_concrete g gi hChr hK
  refine ⟨δ₀, hδ₀pos, fun c hc0 hcδ S hSeq => ⟨?_, ?_, hchrMeas_concrete g gi hChr⟩⟩
  · rw [hSeq]; exact hδ₀spec c hc0 hcδ
  · rw [hSeq]; exact hS0_concrete g gi hChr hK hK0 c hc0

end QIQTH.ConcreteGateInstantiation

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ConcreteGateInstantiation
#print axioms hKSmeas_concrete
#print axioms hchrMeas_concrete
#print axioms hS0_concrete
#print axioms concreteGate_carriers_discharged
end AxiomChecks
