/-
  FlowJointContinuity — J4-213 (hEmeas-ladder brick B2): JOINT continuity of the `.choose` geodesic
  flow endpoint map `(q, w) ↦ uniformFlowExp g gi hC hK q w`.  ONE brick of the a₁=R/6 campaign;
  **NOT a₁=R/6 itself** and proves NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  Pure regularity brick.  No `sorry`, no new axioms, no `:= True`, no vacuous or
  unsatisfiable hypotheses, none of the results is a conclusion-in-disguise.

  ── THE WELD (B2).  `FlowJointRegularity.lean` §3 records that the `.choose`-built tower exposes NO
     joint-in-`(q,w)` regularity of the point-value flow — only the VELOCITY slot at a FIXED base
     (`contDiffAt2_uniformFlowExp`) and, separately, a BASE-slot Lipschitz modulus uniform in the
     velocity (the two-solution Grönwall W3 `uniformFlowExp_base_diff_bound`).  This file welds those
     two banked single-slot facts into JOINT (within-set) continuity on the honest product region
     `K ×ˢ ball 0 ρ_K` (base in the compact `K`, velocity strictly inside the uniform flow radius),
     via the standard triangle anchored at `q₀`:
        ‖φ(q,w) − φ(q₀,w₀)‖ ≤ ‖φ(q,w) − φ(q₀,w)‖ + ‖φ(q₀,w) − φ(q₀,w₀)‖.
     • Term 1 → 0 by the base Lipschitz modulus W3 (`‖φ_q w − φ_{q₀} w‖ ≤ exp L·‖q − q₀‖`, UNIFORM
       over `‖w‖ ≤ ρ_K` — so it survives `w → w₀`), squeezed to `0`.
     • Term 2 → 0 by the velocity-slot continuity at the FIXED base `q₀`
       (`contDiffAt2_uniformFlowExp … q₀ hq₀ w₀ hw₀ |>.continuousAt`).  No local uniformity of the
       velocity slot in `q` is needed — the triangle is anchored at `q₀`.
     The base bound needs `‖w‖ ≤ ρ_K` and the velocity slot needs `‖w₀‖ < ρ_K`; on the OPEN velocity
     ball both hold, which fixes the product region (and the `ContinuousWithinAt`, not full
     `ContinuousAt`, shape: `K` is not assumed a neighbourhood of `q₀`, so `q` is confined to `K`).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁=R/6).

    * `uniformFlowExp_joint_continuousWithinAt` — **★ B2 (the item-1 deliverable).**  Joint
      `ContinuousWithinAt` of `(q,w) ↦ uniformFlowExp g gi hC hK q w` on `K ×ˢ ball 0 ρ_K` at any
      `(q₀,w₀)` with `q₀ ∈ K`, `‖w₀‖ < ρ_K`.  Fed by exactly the two banked lemmas
      (`GeodesicGronwall.uniformFlowExp_base_diff_bound` W3 + `contDiffAt2_uniformFlowExp` velocity
      slot); carries precisely their side-conditions, no more.

    * `uniformFlowExp_joint_continuousOn` — the `ContinuousOn` packaging of the above on the whole
      product region `K ×ˢ ball 0 ρ_K`.

    * `uniformFlowExp_smoothFactor_continuousOn` — **the item-2 (OBL-2) partial progress, B4 seed.**
      Post-composing the joint flow continuity with ANY continuous spatial factor field
      `H : Point n → ℝ` gives joint on-set continuity of `(q,w) ↦ H (uniformFlowExp … q w)` — the
      composition-through-a-smooth-factor step of the `hKcont` (OBL-2) assembly.

  ── OBL-2 (`hKcont`) — HONEST GAP STATEMENT.  OBL-2 (`HEmeasRecon.HEmeasObligation_kernelJointCont`)
     asks for FULL `Continuous (fun w : ℝ × Point n × Point n => G w.1 w.2.1 w.2.2)` of the concrete
     space-time witness kernel `G`.  Beyond B2 (item 1) it additionally requires, and this file does
     NOT close (no faking): (i) the base point `q` enters `G` through the INVERSE chart
     `uniformInverseChart` (its base-slot continuity at a general field point is the SEPARATE banked
     brick `ChartGeneralPContinuity.chartP_continuousOn`, itself on a set under carried right-inverse
     side-conditions, not a global `Continuous`); (ii) the `τ` and field-`p` slots and the smooth
     coefficient fields must be wired in (E3a–E3e of `GatedWitnessEmeas`); (iii) B2 supplies on-set
     (`K ×ˢ ball`) joint continuity, whereas OBL-2 asks for continuity on the whole space — the
     reach/side-condition bookkeeping (`hChartP`-style disjunction) is the honest residue.  Each of
     these is a genuine further brick, not a `Continuous.comp` away; `uniformFlowExp_smoothFactor_*`
     is the one sub-step that DOES compose, provided here as honest partial progress.

  ── B3 (inverse-chart base continuity) — ALREADY BANKED.  The stretch B3
     (`inverseChart_base_continuousOn`) is NOT re-proved here: it is the already-banked
     `ChartGeneralPContinuity.chartP_continuousOn` (general field point `p`, via the transfer lemma
     `chart_joint_velocity_modulus` + W3 + the right-inverse identity `φ_z(W z p) = p`), which does
     not even route through B2.  Re-exposing it would add nothing.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GeodesicGronwall
import QIQTH.PullbackNaturalityLocal

open Filter
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology

namespace QIQTH.FlowJointContinuity

variable {n : ℕ}

/-! ###############################################################################
    ## ITEM 1 (B2) — joint continuity of the forward geodesic-flow endpoint map.
    ############################################################################### -/

/-- **★ B2 / item 1 — `uniformFlowExp_joint_continuousWithinAt`.**  The `.choose`-built forward
    geodesic-flow endpoint map is JOINTLY continuous in `(q, w)` on the product region
    `K ×ˢ ball 0 ρ_K` (base in the compact `K`, velocity strictly inside the uniform flow radius),
    at any point `(q₀, w₀)` with `q₀ ∈ K` and `‖w₀‖ < ρ_K`.  Welds the two banked single-slot facts:
    the base Lipschitz modulus W3 (`GeodesicGronwall.uniformFlowExp_base_diff_bound`, UNIFORM in the
    velocity) for the base slot, and `contDiffAt2_uniformFlowExp` (velocity slot at the FIXED `q₀`)
    for the velocity slot, through the `q₀`-anchored triangle.  NOT `a₁ = R/6`. -/
theorem uniformFlowExp_joint_continuousWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (q₀ : Point n) (hq₀ : q₀ ∈ K) (w₀ : Point n)
    (hw₀ : ‖w₀‖ < uniformFlowRadius g gi hC hK) :
    ContinuousWithinAt (fun p : Point n × Point n => uniformFlowExp g gi hC hK p.1 p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) (q₀, w₀) := by
  classical
  obtain ⟨L, _hL0, hbase⟩ := QIQTH.GeodesicGronwall.uniformFlowExp_base_diff_bound g gi hC hK
  -- velocity-slot continuity at the FIXED base `q₀`.
  have hvel : ContinuousAt (fun w : Point n => uniformFlowExp g gi hC hK q₀ w) w₀ :=
    (QIQTH.HeatResidualBound.contDiffAt2_uniformFlowExp g gi hC hK q₀ hq₀ w₀ hw₀).continuousAt
  -- projections restricted to the within-set filter (explicit type pins the `nhdsWithin` set).
  have hfst : Tendsto (fun p : Point n × Point n => p.1)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 q₀) :=
    (continuous_fst.tendsto (q₀, w₀)).mono_left nhdsWithin_le_nhds
  have hsndp : Tendsto (fun p : Point n × Point n => p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 w₀) :=
    (continuous_snd.tendsto (q₀, w₀)).mono_left nhdsWithin_le_nhds
  -- TERM 2 → φ q₀ w₀ by velocity-slot continuity ∘ snd.
  have hsnd : Tendsto (fun p : Point n × Point n => uniformFlowExp g gi hC hK q₀ p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀))
      (𝓝 (uniformFlowExp g gi hC hK q₀ w₀)) :=
    hvel.tendsto.comp hsndp
  -- TERM 1 → 0, squeezed by the base Lipschitz modulus W3 (uniform in `w`).
  have htend : Tendsto (fun p : Point n × Point n => Real.exp L * ‖p.1 - q₀‖)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 0) := by
    have hc : Continuous (fun x : Point n => Real.exp L * ‖x - q₀‖) := by fun_prop
    have h := (hc.tendsto q₀).comp hfst
    simpa using h
  have hdiff : Tendsto (fun p : Point n × Point n =>
        uniformFlowExp g gi hC hK p.1 p.2 - uniformFlowExp g gi hC hK q₀ p.2)
      (𝓝[K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)] (q₀, w₀)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ htend
    filter_upwards [self_mem_nhdsWithin] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp2' : ‖p.2‖ ≤ uniformFlowRadius g gi hC hK :=
      le_of_lt (by rwa [mem_ball_zero_iff] at hp2)
    exact hbase p.1 hp1 q₀ hq₀ p.2 hp2'
  -- combine: (term1) + (term2) = φ, limit 0 + φ q₀ w₀ = φ q₀ w₀.
  have hcomb := hdiff.add hsnd
  simp only [zero_add] at hcomb
  exact Filter.Tendsto.congr (fun p => by abel) hcomb

/-- **`uniformFlowExp_joint_continuousOn`.**  The `ContinuousOn` packaging of B2: joint continuity of
    `(q, w) ↦ uniformFlowExp g gi hC hK q w` on the whole product region `K ×ˢ ball 0 ρ_K`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_joint_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ContinuousOn (fun p : Point n × Point n => uniformFlowExp g gi hC hK p.1 p.2)
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  exact uniformFlowExp_joint_continuousWithinAt g gi hC hK p.1 hp1 p.2
    (by rwa [mem_ball_zero_iff] at hp2)

/-! ###############################################################################
    ## ITEM 2 (OBL-2 partial / B4 seed) — smooth-factor composition.
    ############################################################################### -/

/-- **Item 2 (OBL-2 partial progress, B4 seed) — `uniformFlowExp_smoothFactor_continuousOn`.**
    Post-composing the joint flow continuity B2 with ANY continuous spatial factor field
    `H : Point n → ℝ` yields joint on-set continuity of `(q, w) ↦ H (uniformFlowExp … q w)` on
    `K ×ˢ ball 0 ρ_K`.  This is the one `hKcont`-family (OBL-2) sub-step that genuinely composes; the
    remaining OBL-2 gap (τ/field-`p` slots, the inverse-chart substitution `ChartGeneralPContinuity`,
    the on-set→whole-space reach bookkeeping) is documented in the header and NOT closed here.
    NOT `a₁ = R/6`. -/
theorem uniformFlowExp_smoothFactor_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (H : Point n → ℝ) (hH : Continuous H) :
    ContinuousOn (fun p : Point n × Point n => H (uniformFlowExp g gi hC hK p.1 p.2))
      (K ×ˢ Metric.ball (0 : Point n) (uniformFlowRadius g gi hC hK)) :=
  hH.comp_continuousOn (uniformFlowExp_joint_continuousOn g gi hC hK)

end QIQTH.FlowJointContinuity

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.FlowJointContinuity
#print axioms uniformFlowExp_joint_continuousWithinAt
#print axioms uniformFlowExp_joint_continuousOn
#print axioms uniformFlowExp_smoothFactor_continuousOn
end AxiomChecks
