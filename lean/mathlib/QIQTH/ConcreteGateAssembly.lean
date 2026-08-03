/-
  ConcreteGateAssembly — J4-172: instantiating the ABSTRACT field-gate `S` with the CONCRETE
  flow-ball gate `S z = φ_z '' Metric.ball 0 c` and discharging the reachable-gate geometry, then
  assembling the most-closed `hKmeas` / `hC2fam` witness slots on that concrete gate.  ONE brick of
  the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  gate-instantiation / regularity-plumbing brick.  It takes the J4-171 reachable-gate reduction
  (`ChartFieldC2General.hGateDiff_hC2fam_from_reachableGate`) and the J4-169 flow-ball measurability
  discharge (`GateSetMeasurability.hKmeas_concrete_v5` / `flowBallGate_hSmK_of_geom`) and INSTANTIATES
  both on the definite gate `S z = φ_z '' Metric.ball 0 c`.  Never a conclusion; no vacuous or
  unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    * `reachableGate_concrete` — ★ THE CONCRETE-GATE DISCHARGE.  A single uniform radius `δ₀ > 0`
      (from `uniformInverseChart_huniformChart`) such that for every ball radius `0 < c < δ₀`, base
      `z ∈ K`, the flow-ball gate `S z = φ_z '' ball 0 c` is OPEN, the chart is a LEFT inverse on the
      ball (`W z (φ_z v) = v` for `v ∈ ball 0 c`), and every gate point `x ∈ S z` is REACHABLE
      (`∃ v, ‖v‖ < δ₀ ∧ x = φ_z v`) with the field-chart `C²` at `x`.  Pure unfolding of `mem_image`
      plus the banked germ / openness clauses at a single radius.

    * `flowBallGate_hRI_onGate` — the RIGHT-inverse `φ_z (W z p) = p` DERIVED on the gate: for a gate
      point `p ∈ S z`, `p = φ_z v` with `v ∈ ball 0 c`, so `W z p = W z (φ_z v) = v` by the left
      inverse and `φ_z (W z p) = φ_z v = p`.  Shows the on-gate right inverse is NOT a separate carry.

    * `hGateDiff_hC2fam_concrete` — ★★ the reachable-gate pipeline INSTANTIATED on the concrete gate:
      BOTH witness slots (`hGateDiff`, `hC2fam`) for `S z = φ_z '' ball 0 c`, produced from the pure
      COVERAGE geometry (per relevant `(x₀, z)`: `x₀ ∈ S z`) plus `hg`/`hgpos`/`hu`.  The reachability
      / openness / field-`C²` are all supplied by `reachableGate_concrete`, so the standing geometry
      collapses to bare gate MEMBERSHIP.

    * `hKmeas_concrete_v6` — ★★ the most-closed `hKmeas` slot on the concrete gate.  Threads the
      concrete `hGateDiff` (via the coverage geometry) through `hKmeas_concrete_v5`, with the `hSmK`
      measurability discharged by `flowBallGate_hSmK_of_geom` and `hChartP` reconstructed — BOTH from
      ONE unified per-`p` chart-`P` geometry carry `{hball, hnorm, hRI}` (the left inverse `hLI` needed
      by the measurability lever is DERIVED from the banked germ via `reachableGate_concrete`, not
      carried).  Final carries {unified `{hball,hnorm,hRI}` on `K`, coverage geometry, `hg`, `hgpos`,
      `hu`}.

    * `hC2fam_concrete_final` — ★★ the most-closed `hC2fam` slot (the `g2_bundle_assembled` input) on
      the concrete gate, from the point-coverage geometry + `hg`/`hgpos`/`hu`.

    * `l1_residue_status` — the machine-checked reduction statement for the census: from the residue
      (unified chart-`P` geometry + coverage geometry + metric smoothness) BOTH the concrete `hKmeas`
      and `hC2fam` slots follow.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    * The COVERAGE geometry — per relevant `(x₀, z)` with `z ∈ K`, the field point lies in the gate
      `x₀ ∈ φ_z '' ball 0 c`.  This is exactly the design intent of the gate (it is BUILT to cover the
      reach); satisfiable, not the witness.
    * The chart-`P` geometry `{hball, hnorm, hRI}` for the GENERAL field point `p` on all of `K` — the
      genuine chart right-inverse / velocity-bound data driving the `z`-continuity of `z ↦ W z p`.
      The on-gate instance of `hRI` is DERIVED (`flowBallGate_hRI_onGate`); the full-`K`, all-`p`
      instance is the honest chart-geometry carry.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartFieldC2General
import QIQTH.GateSetMeasurability
import QIQTH.WitnessDerivMeasurability

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.ExpMap
open QIQTH.ChartFieldC2General QIQTH.GateSetMeasurability QIQTH.ChartGeneralPContinuity
open scoped BigOperators Topology Interval

namespace QIQTH.ConcreteGateAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE CONCRETE-GATE DISCHARGE — one uniform radius, openness + left inverse +
    ###    reachability + field `C²`, for the flow-ball gate `S z = φ_z '' ball 0 c`.
    ############################################################################### -/

/-- **★ `reachableGate_concrete` — the concrete flow-ball gate discharge.**  A single uniform radius
    `δ₀ > 0` (the `uniformInverseChart_huniformChart` radius) such that for every ball radius
    `0 < c < δ₀` and base `z ∈ K`, the flow-ball gate `S z = φ_z '' Metric.ball 0 c`
    (`φ_z := uniformFlowExp g gi hC hK z`) satisfies:
      • it is OPEN;
      • the inverse chart is a LEFT inverse on the ball (`W z (φ_z v) = v` for `v ∈ ball 0 c`);
      • every gate point `x ∈ S z` is REACHABLE (`∃ v, ‖v‖ < δ₀ ∧ x = φ_z v`) AND the field chart is
        `ContDiffAt ℝ 2` at `x`.
    All four facts read off the banked germ / `C²` / open clauses of `uniformInverseChart_huniformChart`
    at the single radius; the reachability inequality is `mem_ball` plus `c < δ₀`.  NOT `a₁ = R/6`. -/
theorem reachableGate_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ z ∈ K,
      IsOpen (uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
      ∧ (∀ v ∈ Metric.ball (0 : Point n) c,
          uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
      ∧ (∀ x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c,
          (∃ v : Point n, ‖v‖ < δ₀ ∧ x = uniformFlowExp g gi hC hK z v)
          ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ z hz
  obtain ⟨hgermC2, hOC⟩ := hspec z hz
  refine ⟨(hOC c hc0 hcδ).1, ?_, ?_⟩
  · intro v hv
    rw [Metric.mem_ball, dist_zero_right] at hv
    exact (hgermC2 v (lt_trans hv hcδ)).1.eq_of_nhds
  · rintro x ⟨v, hv, hφv⟩
    rw [Metric.mem_ball, dist_zero_right] at hv
    have hvδ : ‖v‖ < δ₀ := lt_trans hv hcδ
    refine ⟨⟨v, hvδ, hφv.symm⟩, ?_⟩
    have hC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z)
        (uniformFlowExp g gi hC hK z v) := (hgermC2 v hvδ).2
    rwa [hφv] at hC2

/-- **`flowBallGate_hRI_onGate` — the RIGHT inverse DERIVED on the gate.**  For a gate point
    `p ∈ φ_z '' Metric.ball 0 c` (with `0 < c < δ₀`, `z ∈ K`), the chart right inverse `φ_z (W z p) = p`
    follows from the LEFT inverse alone:  `p = φ_z v` with `v ∈ ball 0 c`, so `W z p = W z (φ_z v) = v`
    and `φ_z (W z p) = φ_z v = p`.  So `hRI` is NOT a separate carry ON gate points.  NOT `a₁ = R/6`. -/
theorem flowBallGate_hRI_onGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) (z p : Point n) (hz : z ∈ K)
    (hLI : ∀ v ∈ Metric.ball (0 : Point n) c,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hp : p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) :
    uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p := by
  obtain ⟨v, hv, hφv⟩ := hp
  have hWp : uniformInverseChart g gi hC hK z p = v := by rw [← hφv]; exact hLI v hv
  rw [hWp, hφv]

/-! ###############################################################################
    ### ★★ THE REACHABLE-GATE PIPELINE, INSTANTIATED ON THE CONCRETE GATE.
    ############################################################################### -/

/-- **★★ `hGateDiff_hC2fam_concrete` — both witness slots on the concrete flow-ball gate.**  For the
    definite gate `S z = φ_z '' Metric.ball 0 c` (`0 < c < δ₀`), BOTH remaining L1 field-slot carries —
    the witness `hGateDiff` slot (`GateSetMeasurability.hKmeas_concrete_v5`) AND the witness `hC2fam`
    slot (`WitnessDerivMeasurability.g2_bundle_assembled`) — are produced from the pure COVERAGE geometry
    (per relevant `(x₀, z)`: whenever `z ∈ K` the field point lies in the gate `x₀ ∈ S z`) together with
    `hg`/`hgpos`/`hu`.  The reachability / openness / field-`C²` are supplied by `reachableGate_concrete`,
    so the standing geometry is bare gate MEMBERSHIP.  Composes `OnGateFieldRegularity.hGateDiff_from_chart`
    / `hC2fam_from_chart`.  NOT `a₁ = R/6`. -/
theorem hGateDiff_hC2fam_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK
              (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
              a b (t - s) x' z) i x)
      ∧ (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            a b (t - s) x' z) x₀) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ hMemNear hMemPt
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  refine ⟨?_, ?_⟩
  · -- hGateDiff via `hGateDiff_from_chart`, converting membership ⟹ (mem ∧ open ∧ C²).
    apply QIQTH.OnGateFieldRegularity.hGateDiff_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀ i
    filter_upwards [hMemNear x₀ hx₀ i] with s hs
    intro hmem
    filter_upwards [hs hmem] with x hx
    filter_upwards [hx] with z hz
    intro hzK
    have hxSz : x ∈ S z := hz hzK
    obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ z hzK
    exact ⟨hxSz, hopen, (hxfacts x hxSz).2⟩
  · -- hC2fam via `hC2fam_from_chart`, converting the dichotomy ⟹ (mem ∧ open ∧ C²).
    apply QIQTH.OnGateFieldRegularity.hC2fam_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀
    filter_upwards [hMemPt x₀ hx₀] with s hs
    intro hmem
    filter_upwards [hs hmem] with z hz
    rcases hz with h | ⟨hzK, hxSz⟩
    · exact Or.inl h
    · obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ z hzK
      exact Or.inr ⟨hzK, hxSz, hopen, (hxfacts x₀ hxSz).2⟩

/-! ###############################################################################
    ### ★★ THE MOST-CLOSED `hKmeas` / `hC2fam` ON THE CONCRETE GATE.
    ############################################################################### -/

/-- **★★ `hKmeas_concrete_v6` — the most-closed `hKmeas` slot on the concrete flow-ball gate.**  For the
    definite gate `S z = φ_z '' Metric.ball 0 c` (`0 < c < δ₀`), the EXACT `hKmeas` slot of
    `g2_bundle_assembled` (for `witnessFieldDeriv`), with:
      • the `hGateDiff` slot produced from the COVERAGE geometry `hMemNear` (via `hGateDiff_hC2fam_concrete`);
      • the `hSmK` measurability discharged by `flowBallGate_hSmK_of_geom`;
      • `hChartP` reconstructed;
    BOTH the last two from ONE unified per-`p` chart-`P` geometry carry `hGeomP = {hball, hnorm, hRI}`.
    The left inverse `hLI` that the measurability lever needs is DERIVED from the banked germ
    (`reachableGate_concrete`), NOT carried.  Final carries {`hGeomP`, `hMemNear`, `hMemPt`, `hg`,
    `hgpos`, `hu`} — each satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v6 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ p : Point n,
          (∀ z ∈ K, uniformInverseChart g gi hC hK z p
              ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
          ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
          ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            a b i (t - s) x z)
          (volume : Measure (Point n)) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ hGeomP hMemNear
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  -- The unified per-`p` chart-`P` geometry decomposed.
  have hball : ∀ p : Point n, ∀ z ∈ K, uniformInverseChart g gi hC hK z p
      ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose :=
    fun p => (hGeomP p).1
  have hnorm : ∀ p : Point n, ∀ z ∈ K,
      ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK :=
    fun p => (hGeomP p).2.1
  have hRI : ∀ p : Point n, ∀ z ∈ K,
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p :=
    fun p => (hGeomP p).2.2
  -- The left inverse on the ball, DERIVED from the banked germ.
  have hLI : ∀ p : Point n, ∀ z ∈ K, ∀ v ∈ Metric.ball (0 : Point n) c,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
    intro p z hz v hv
    exact (hreach c hc0 hcδ z hz).2.1 v hv
  -- The `K`-relative gate measurability, per `p`.
  have hSmK : ∀ p : Point n, MeasurableSet (K ∩ {z : Point n | p ∈ S z}) := by
    intro p
    exact flowBallGate_hSmK_of_geom g gi hC hK p c (hball p) (hnorm p) (hRI p) (hLI p)
  -- The per-`p` geometry-OR-measurability disjunction (left disjunct from `hGeomP`).
  have hChartP : ∀ p : Point n,
      ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
            ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
        ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
        ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
      ∨ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
          ((volume : Measure (Point n)).restrict K) :=
    fun p => Or.inl (hGeomP p)
  -- The `hGateDiff` slot from the coverage geometry.
  have hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∈ K → PdiffAt (fun x' : Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x := by
    apply QIQTH.OnGateFieldRegularity.hGateDiff_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀ i
    filter_upwards [hMemNear x₀ hx₀ i] with s hs
    intro hmem
    filter_upwards [hs hmem] with x hx
    filter_upwards [hx] with z hz
    intro hzK
    have hxSz : x ∈ S z := hz hzK
    obtain ⟨hopen, _hLIz, hxfacts⟩ := hreach c hc0 hcδ z hzK
    exact ⟨hxSz, hopen, (hxfacts x hxSz).2⟩
  exact hKmeas_concrete_v5 g gi hC hK S a b t u hSmK hg hgpos hu hChartP hGateDiff

/-- **★★ `hC2fam_concrete_final` — the most-closed `hC2fam` slot on the concrete flow-ball gate.**  For
    `S z = φ_z '' Metric.ball 0 c` (`0 < c < δ₀`), the EXACT `hC2fam` input to
    `WitnessDerivMeasurability.g2_bundle_assembled`, produced from the point-coverage geometry `hMemPt`
    (via `hGateDiff_hC2fam_concrete`) together with `hg`/`hgpos`/`hu`.  NOT `a₁ = R/6`. -/
theorem hC2fam_concrete_final (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)) →
      ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK
          (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
          a b (t - s) x' z) x₀ := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := reachableGate_concrete g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc0 hcδ hMemPt
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c with hSdef
  apply QIQTH.OnGateFieldRegularity.hC2fam_from_chart g gi hC hK S a b t u hg hgpos hu
  intro x₀ hx₀
  filter_upwards [hMemPt x₀ hx₀] with s hs
  intro hmem
  filter_upwards [hs hmem] with z hz
  rcases hz with h | ⟨hzK, hxSz⟩
  · exact Or.inl h
  · obtain ⟨hopen, _hLI, hxfacts⟩ := hreach c hc0 hcδ z hzK
    exact Or.inr ⟨hzK, hxSz, hopen, (hxfacts x₀ hxSz).2⟩

/-! ###############################################################################
    ### ★ THE CENSUS REDUCTION STATEMENT.
    ############################################################################### -/

/-- **★ `l1_residue_status` — the machine-checked L1 reduction on the concrete gate.**  From the honest
    residue — the unified chart-`P` geometry `hGeomP` on `K`, the two coverage families
    (`hMemNear`, `hMemPt`), and the metric smoothness `hg`/`hgpos`/`hu` — BOTH the concrete `hKmeas`
    slot (`witnessFieldDeriv` `z`-ae-measurability) AND the concrete `hC2fam` slot (field-`C²` of the
    gated witness) hold, at a single uniform radius `δ₀` and every ball radius `0 < c < δ₀`.  This is
    the census statement:  the L1 witness-regularity surface on the concrete flow-ball gate reduces to
    pure chart geometry + gate coverage + metric smoothness.  NOT `a₁ = R/6`. -/
theorem l1_residue_status (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
      (∀ p : Point n,
          (∀ z ∈ K, uniformInverseChart g gi hC hK z p
              ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
          ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
          ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → x ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) →
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable
          (fun z => witnessFieldDeriv g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            a b i (t - s) x z)
          (volume : Measure (Point n)))
      ∧ (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            a b (t - s) x' z) x₀) := by
  obtain ⟨δ₀K, hδ₀K, hKm⟩ := hKmeas_concrete_v6 g gi hC hK a b t u hg hgpos hu
  obtain ⟨δ₀C, hδ₀C, hCm⟩ := hC2fam_concrete_final g gi hC hK a b t u hg hgpos hu
  refine ⟨min δ₀K δ₀C, lt_min hδ₀K hδ₀C, ?_⟩
  intro c hc0 hcδ hGeomP hMemNear hMemPt
  have hcK : c < δ₀K := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcC : c < δ₀C := lt_of_lt_of_le hcδ (min_le_right _ _)
  exact ⟨hKm c hc0 hcK hGeomP hMemNear, hCm c hc0 hcC hMemPt⟩

end QIQTH.ConcreteGateAssembly

section AxiomChecks
open QIQTH.ConcreteGateAssembly
#print axioms reachableGate_concrete
#print axioms flowBallGate_hRI_onGate
#print axioms hGateDiff_hC2fam_concrete
#print axioms hKmeas_concrete_v6
#print axioms hC2fam_concrete_final
#print axioms l1_residue_status
end AxiomChecks
