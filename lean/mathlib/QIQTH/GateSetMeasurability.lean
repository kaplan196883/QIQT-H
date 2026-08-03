/-
  GateSetMeasurability — J4-169: discharging the field-gate preimage measurability carry `hSm` for the
  CONCRETE flow-ball gate `S z = φ_z '' Metric.ball 0 c`, and the honest K-RELATIVE re-threading of the
  `hSm` slot through the entire `hKmeas_concrete` chain.  ONE brick of the a₁=R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  measurability/geometry brick.  The `hKmeas` chain (`GateChartMeasurability` → `FoldedCoeffChartMeas`
  → `ChartGeneralPContinuity`) leaves standing a carry `hSm : ∀ p, MeasurableSet {z | p ∈ S z}` for the
  ABSTRACT field-gate `S`.  This file (i) turns the abstract `hSm` into a GEOMETRIC statement for the
  concrete flow-ball gate via the chart left- and right-inverse identities, and (ii) shows that only the
  `K`-RELATIVE set `K ∩ {z | p ∈ S z}` ever enters (the gated indicator is `(K ∩ {z|p∈S z}).indicator`),
  so the whole chain re-threads through the strictly WEAKER carry `∀ p, MeasurableSet (K ∩ {z|p∈S z})`.
  Never a conclusion; no vacuous/unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    * `mem_flowBall_iff_chart` — **THE EQUIVALENCE LEVER.**  For a base point `z` and field point `p`,
      under the banked chart inverse identities — the left-inverse germ on the ball
      `hLI : ∀ v ∈ ball 0 c, W z (φ_z v) = v` and the right-inverse at `p` `hRI : φ_z (W z p) = p` —
          `p ∈ φ_z '' Metric.ball 0 c  ↔  W z p ∈ Metric.ball 0 c`.
      (→ uses `hLI` at the pre-image velocity; ← uses `hRI`.)  BOTH directions close cleanly.

    * `chartPreimageBall_Krel_measurableSet` — from `ContinuousOn (z ↦ W z p) K` (J4-168's
      `chartP_continuousOn`), the `K`-relative preimage of the open ball is measurable:
          `MeasurableSet (K ∩ (z ↦ W z p) ⁻¹' Metric.ball 0 c)`  (via `continuousOn_iff'`).

    * `flowBallGate_Krel_measurableSet` — composing the two: for the concrete flow-ball gate,
          `MeasurableSet (K ∩ {z | p ∈ φ_z '' Metric.ball 0 c})`,
      from continuity + the per-`z` equivalence on `K`.  **The concrete flow-ball `hSm`, discharged in
      the (only-relevant) `K`-relative form.**

    * `flowBallGate_hSmK_of_geom` — the raw geometric side-conditions (`hball`,`hnorm`,`hRI`,`hLI` on `K`
      at `p`) ⟹ the `K`-relative measurable-set, wiring `chartP_continuousOn` + the equivalence.

    * `gatedKernel_slice_aestronglyMeasurable_of_restricted_Krel`,
      `vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted_Krel`,
      `hWmeas_from_carries_restricted_Krel` — the `K`-relative re-threading of the restricted indicator
      lever chain: each takes `MeasurableSet (K ∩ {z|p∈S z})` in place of the pair {`hKm`,`hSm`}.

    * `hKmeas_concrete_v5` — **★★ CAPSTONE.**  The EXACT `hKmeas` slot, the `hKmeas_concrete_v4`
      statement with the abstract full-set carry `hSm : ∀ p, MeasurableSet {z|p∈S z}` REPLACED by the
      strictly weaker `K`-relative `hSmK : ∀ p, MeasurableSet (K ∩ {z|p∈S z})`.  Final carries
      {`hSmK`, `hg`, `hgpos`, `hu`, `hChartP`, `hGateDiff`} — each satisfiable, non-vacuous, none the
      conclusion; `hSmK` is dischargeable for the concrete flow-ball gate by `flowBallGate_hSmK_of_geom`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartGeneralPContinuity

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge QIQTH.WitnessMeasDeriv
open QIQTH.GateChartMeasurability QIQTH.GeodesicGronwall QIQTH.FoldedCoeffChartMeas
open QIQTH.ChartGeneralPContinuity
open scoped Interval Topology BigOperators NNReal ContDiff

namespace QIQTH.GateSetMeasurability

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Part 1 — the equivalence lever `p ∈ φ_z '' ball ↔ W z p ∈ ball`.
    ############################################################################### -/

/-- **★ `mem_flowBall_iff_chart` — THE EQUIVALENCE LEVER.**  For a base point `z` and field point `p`,
    under the banked chart inverse identities — the left-inverse germ on the ball
    `hLI : ∀ v ∈ ball 0 c, W z (φ_z v) = v` (the `=ᶠ[𝓝] id` germ banked as
    `uniformInverseChart_huniformChart`, read on the ball) and the right-inverse at `p`
    `hRI : φ_z (W z p) = p` — membership of the flow-ball gate is equivalent to the chart velocity
    landing in the ball:
        `p ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c  ↔  uniformInverseChart g gi hC hK z p ∈
          Metric.ball 0 c`.
    (→) `p = φ_z v` with `v ∈ ball`; then `W z p = W z (φ_z v) = v ∈ ball` by `hLI`.
    (←) `W z p ∈ ball`; then `p = φ_z (W z p) ∈ image` by `hRI`.  NOT `a₁ = R/6`. -/
theorem mem_flowBall_iff_chart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z p : Point n) (c : ℝ)
    (hLI : ∀ v ∈ Metric.ball (0 : Point n) c,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hRI : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) :
    p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c
      ↔ uniformInverseChart g gi hC hK z p ∈ Metric.ball (0 : Point n) c := by
  constructor
  · rintro ⟨v, hv, hφv⟩
    have hWv : uniformInverseChart g gi hC hK z p = v := by
      rw [← hφv]; exact hLI v hv
    rw [hWv]; exact hv
  · intro hWp
    exact ⟨uniformInverseChart g gi hC hK z p, hWp, hRI⟩

/-! ###############################################################################
    ### Part 2 — the K-relative measurability of the flow-ball gate preimage.
    ############################################################################### -/

/-- **`chartPreimageBall_Krel_measurableSet`.**  From `ContinuousOn (z ↦ W z p) K` (J4-168's
    `chartP_continuousOn`), the `K`-relative preimage of the OPEN ball `Metric.ball 0 c` is measurable:
        `MeasurableSet (K ∩ (z ↦ W z p) ⁻¹' Metric.ball 0 c)`.
    Route: `continuousOn_iff'` writes the relative preimage `preimage ∩ K = u ∩ K` for an OPEN `u`,
    whence `IsOpen.measurableSet` + `K` measurable (`IsCompact.measurableSet`).  NOT `a₁ = R/6`. -/
theorem chartPreimageBall_Krel_measurableSet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) (c : ℝ)
    (hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) K) :
    MeasurableSet (K ∩ (fun z : Point n => uniformInverseChart g gi hC hK z p) ⁻¹'
      Metric.ball (0 : Point n) c) := by
  obtain ⟨u, hu_open, hu_eq⟩ :=
    continuousOn_iff'.mp hcont (Metric.ball (0 : Point n) c) Metric.isOpen_ball
  have hset : K ∩ (fun z : Point n => uniformInverseChart g gi hC hK z p) ⁻¹'
      Metric.ball (0 : Point n) c = u ∩ K := by
    rw [Set.inter_comm]; exact hu_eq
  rw [hset]
  exact hu_open.measurableSet.inter hK.measurableSet

/-- **★ `flowBallGate_Krel_measurableSet` — the concrete flow-ball `hSm`, `K`-relative form.**  For the
    concrete flow-ball gate `S z = uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, from
    `ContinuousOn (z ↦ W z p) K` and the per-`z`-on-`K` equivalence `hequiv`
    (`mem_flowBall_iff_chart`), the field-gate preimage is `K`-relatively measurable:
        `MeasurableSet (K ∩ {z | p ∈ uniformFlowExp g gi hC hK z '' Metric.ball 0 c})`.
    Route: the equivalence rewrites the `K`-relative gate set to the `K`-relative CHART preimage, then
    `chartPreimageBall_Krel_measurableSet`.  NOT `a₁ = R/6`. -/
theorem flowBallGate_Krel_measurableSet (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) (c : ℝ)
    (hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) K)
    (hequiv : ∀ z ∈ K,
      p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c
        ↔ uniformInverseChart g gi hC hK z p ∈ Metric.ball (0 : Point n) c) :
    MeasurableSet
      (K ∩ {z : Point n | p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c}) := by
  have hset : K ∩ {z : Point n | p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c}
      = K ∩ (fun z : Point n => uniformInverseChart g gi hC hK z p) ⁻¹'
          Metric.ball (0 : Point n) c := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hzK, hz⟩; exact ⟨hzK, (hequiv z hzK).mp hz⟩
    · rintro ⟨hzK, hz⟩; exact ⟨hzK, (hequiv z hzK).mpr hz⟩
  rw [hset]
  exact chartPreimageBall_Krel_measurableSet g gi hC hK p c hcont

/-- **`flowBallGate_hSmK_of_geom` — the raw-geometry discharge of the concrete flow-ball `hSm`.**  From
    the genuine geometric side-conditions at `p` on `K` — `hball`/`hnorm`/`hRI` (which drive
    `chartP_continuousOn`) plus the left-inverse germ `hLI` on the ball (which, with `hRI`, gives the
    equivalence) — the `K`-relative flow-ball gate preimage is measurable.  Each side-condition is a
    genuine chart-geometry input (satisfiable on the chart's uniform reach over `K`), none the
    conclusion.  NOT `a₁ = R/6`. -/
theorem flowBallGate_hSmK_of_geom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) (c : ℝ)
    (hball : ∀ z ∈ K, uniformInverseChart g gi hC hK z p
      ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
    (hnorm : ∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p)
    (hLI : ∀ z ∈ K, ∀ v ∈ Metric.ball (0 : Point n) c,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v) :
    MeasurableSet
      (K ∩ {z : Point n | p ∈ uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c}) := by
  have hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) K :=
    chartP_continuousOn g gi hC hK p (Set.Subset.refl K) hball hnorm hRI
  refine flowBallGate_Krel_measurableSet g gi hC hK p c hcont ?_
  intro z hz
  exact mem_flowBall_iff_chart g gi hC hK z p c (hLI z hz) (hRI z hz)

/-! ###############################################################################
    ### Part 3 — the K-relative re-threading of the restricted indicator lever chain.
    ############################################################################### -/

/-- **★ `gatedKernel_slice_aestronglyMeasurable_of_restricted_Krel` — the `K`-relative restricted
    indicator lever.**  Verbatim `FoldedCoeffChartMeas.gatedKernel_slice_aestronglyMeasurable_of_restricted`
    with the pair {`hKm : MeasurableSet K`, `hSm : MeasurableSet {z|p∈S z}`} REPLACED by the single
    strictly-weaker carry `hKSm : MeasurableSet (K ∩ {z|p∈S z})` — the ONLY set that ever enters (the
    gated slice equals `(K ∩ {z|p∈S z}).indicator (z ↦ H τ p z)`).  NOT `a₁ = R/6`. -/
theorem gatedKernel_slice_aestronglyMeasurable_of_restricted_Krel (K : Set (Point n))
    (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n)
    (hKSm : MeasurableSet (K ∩ {z : Point n | p ∈ S z}))
    (hHmK : AEStronglyMeasurable (fun z => H τ p z) ((volume : Measure (Point n)).restrict K)) :
    AEStronglyMeasurable (fun z => gatedKernel K S H τ p z) (volume : Measure (Point n)) := by
  classical
  have hrw : (fun z => gatedKernel K S H τ p z)
      = (K ∩ {z : Point n | p ∈ S z}).indicator (fun z => H τ p z) := by
    funext z
    rw [Set.indicator_apply]
    by_cases hzK : z ∈ K
    · by_cases hzS : p ∈ S z
      · rw [gatedKernel_apply_of_mem K S H τ hzK hzS,
          if_pos (show z ∈ K ∩ {z : Point n | p ∈ S z} from ⟨hzK, hzS⟩)]
      · rw [gatedKernel_apply_of_notMem K S H τ p z (Or.inr hzS),
          if_neg (show z ∉ K ∩ {z : Point n | p ∈ S z} from fun h => hzS h.2)]
    · rw [gatedKernel_apply_of_notMem K S H τ p z (Or.inl hzK),
        if_neg (show z ∉ K ∩ {z : Point n | p ∈ S z} from fun h => hzK h.1)]
  rw [hrw, aestronglyMeasurable_indicator_iff hKSm]
  exact hHmK.mono_measure (Measure.restrict_mono_set volume Set.inter_subset_left)

/-- **`vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted_Krel`** — the witness base-slice,
    `K`-relative form.  The `K`-relative analogue of
    `FoldedCoeffChartMeas.vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted`, taking the
    combined `K`-relative carry `hKSm`.  NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted_Krel
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p : Point n)
    (hKSm : MeasurableSet (K ∩ {z : Point n | p ∈ S z}))
    (hInK : AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      ((volume : Measure (Point n)).restrict K)) :
    AEStronglyMeasurable
      (fun z => vanVleckGatedWitness g gi hC hK S a b τ p z) (volume : Measure (Point n)) := by
  unfold vanVleckGatedWitness
  exact gatedKernel_slice_aestronglyMeasurable_of_restricted_Krel K S _ τ p hKSm hInK

/-- **`hWmeas_from_carries_restricted_Krel`** — the EXACT `hWmeas` slot of `hKmeas_from_witness`, from
    the RESTRICTED inner carry `hInK` and the `K`-relative gate carry `hSmK`.  The `K`-relative analogue
    of `FoldedCoeffChartMeas.hWmeas_from_carries_restricted`.  NOT `a₁ = R/6`. -/
theorem hWmeas_from_carries_restricted_Krel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hSmK : ∀ p : Point n, MeasurableSet (K ∩ {z : Point n | p ∈ S z}))
    (hInK : ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      ((volume : Measure (Point n)).restrict K)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
        (volume : Measure (Point n)) := by
  intro x₀ _hx₀ i
  refine ae_of_all volume (fun s => ?_)
  intro _hmem
  refine Filter.Eventually.of_forall (fun x => ?_)
  intro w
  exact vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted_Krel g gi hC hK S a b (t - s)
    (Function.update x i w) (hSmK _) (hInK (t - s) (Function.update x i w))

/-! ###############################################################################
    ### Part 4 — capstone `hKmeas_concrete_v5` (hSm ↦ K-relative `hSmK`).
    ############################################################################### -/

/-- **★★ `hKmeas_concrete_v5`.**  The EXACT `hKmeas` slot of `g2_bundle_assembled` for the concrete
    witness first-derivative kernel `witnessFieldDeriv`, the `hKmeas_concrete_v4` statement with the
    abstract full-set field-gate carry `hSm : ∀ p, MeasurableSet {z|p∈S z}` REPLACED by the strictly
    weaker `K`-relative carry `hSmK : ∀ p, MeasurableSet (K ∩ {z|p∈S z})` (the only set that enters the
    gated indicator).  Threaded via `hWmeas_from_carries_restricted_Krel` in place of the full-set
    restricted lever, with `hVmapMeasK` still reconstructed from the per-`p` geometry-OR-measurability
    disjunction `hChartP` (`hVmapMeasK_of_geomOrMeas`).  Final carries {`hSmK`, `hg`, `hgpos`, `hu`,
    `hChartP`, `hGateDiff`} — each satisfiable, non-vacuous, none the conclusion; `hSmK` is
    dischargeable for the concrete flow-ball gate by `flowBallGate_hSmK_of_geom`.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v5 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hSmK : ∀ p : Point n, MeasurableSet (K ∩ {z : Point n | p ∈ S z}))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChartP : ∀ p : Point n,
      ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
            ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
        ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
        ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
      ∨ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
          ((volume : Measure (Point n)).restrict K))
    (hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
        (volume : Measure (Point n)) :=
  hKmeas_from_witness g gi hC hK S a b t u
    (hWmeas_from_carries_restricted_Krel g gi hC hK S a b t u hSmK
      (hInK_concrete_of_chartK_measurable g gi hC hK a b (hw_discharged g gi hg hgpos hu)
        (hVmapMeasK_of_geomOrMeas g gi hC hK hChartP)))
    (hWdiff_from_gateDiff g gi hC hK S a b t u hGateDiff)

end QIQTH.GateSetMeasurability

section AxiomChecks
open QIQTH.GateSetMeasurability
#print axioms mem_flowBall_iff_chart
#print axioms chartPreimageBall_Krel_measurableSet
#print axioms flowBallGate_Krel_measurableSet
#print axioms flowBallGate_hSmK_of_geom
#print axioms gatedKernel_slice_aestronglyMeasurable_of_restricted_Krel
#print axioms vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted_Krel
#print axioms hWmeas_from_carries_restricted_Krel
#print axioms hKmeas_concrete_v5
end AxiomChecks
