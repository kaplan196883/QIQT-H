/-
  FoldedCoeffChartMeas — J4-167: discharge of the `hw` carry and a RESTRICTED (`volume.restrict K`)
  re-threading of the `hVmapMeas` carry that `QIQTH.GateChartMeasurability.hKmeas_concrete_v2`
  (J4-166) leaves standing for the concrete `N = 1` gated van-Vleck witness first-derivative kernel
  `witnessFieldDeriv`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It takes two of the
  four `hKmeas_concrete_v2` carries — `hw` (coefficient smoothness) and `hVmapMeas` (z-ae-measurability
  of the base-chart pullback) — and (A) DISCHARGES the van-Vleck prefactor half of `hw`, reducing `hw`
  to the STANDARD carried transport-coefficient smoothness `hu` (already threaded through the whole
  chain, e.g. `SpatialC2.hCH_discharge`) plus the metric smoothness `hg` and the genuine
  det-positivity `hgpos`; and (B) re-threads the gated-indicator measurability chain through the
  STRICTLY WEAKER `volume.restrict K` measurability of the chart pullback (`hVmapMeasK`), because off
  `K` the gated kernel is `0` regardless — so only the on-`K` slice matters.  Never the conclusion.

  ── PART A — `hw`.  `foldedCoeff Θ u k = fun y ↦ Θ(y)^{−1/2}·u_k(y)`.  With `Θ = vanVleck g`,
     `Θ^{−1/2}` is `C^∞` wherever `det g > 0` (`vanVleck_contDiffAt` at every point via
     `contDiff_iff_contDiffAt`, then `.rpow_const_of_ne` off the zero of the positive `vanVleck g`),
     and `u_k = transportCoeff …` rides the STANDARD carried smoothness `hu`.  Product ⟹ `hw`.  So
     `hw` REDUCES to {`hg`, `hgpos`, `hu`} — the van-Vleck half is discharged, only the (fundamental)
     transport-coefficient smoothness `hu` remains.  Delivered as `hw_discharged`.

  ── PART B — `hVmapMeas` via the GATED / RESTRICTED route.  The full-volume z-ae-measurability
     `hVmapMeas : ∀ p, AEStronglyMeasurable (z ↦ W z p) volume` is globally absent (banked continuity
     is only `ContinuousOn (z ↦ W z 0) S`, `S ⊆ K`: `GeodesicGronwall.chartOrigin_continuousOn`,
     `FlowJointRegularity.hWmeas₀_of_continuousOn`).  BUT the gated kernel is `0` off `K`, so the inner
     slice only matters on `K`.  We prove:

     ● `gatedKernel_slice_aestronglyMeasurable_of_restricted` — ★ THE RESTRICTED INDICATOR LEVER.  The
       gated slice equals `(K ∩ {z|p∈S z}).indicator (z ↦ H τ p z)`, so via
       `aestronglyMeasurable_indicator_iff` it is `AEStronglyMeasurable` on FULL `volume` as soon as
       `z ↦ H τ p z` is `AEStronglyMeasurable` on `volume.restrict K` ALONE (`mono_measure`, since
       `K ∩ … ⊆ K`).  STRICTLY WEAKER inner hypothesis than the full-volume `hIn`.

     ● `hInK_concrete_of_chartK_measurable` — the concrete inner slice, restricted to `K`, from
       {`hw`, `hVmapMeasK`} via the continuous-spatial-function composition (`witnessInner_continuous`).

     ● `hVmapMeasK_zero_of_geom` — the `p = 0` slice of `hVmapMeasK` DISCHARGED from the banked
       origin-chart `ContinuousOn` (`chartOrigin_continuousOn` at `S = K`) via
       `ContinuousOn.aestronglyMeasurable`, under the chart's genuine geometric side-conditions.

     ● `hKmeas_concrete_v3` — CAPSTONE.  The exact `hKmeas` slot, with `hKm` discharged
       (`compactGate_measurableSet`), `hw` discharged (`hw_discharged`), and `hVmapMeas` WEAKENED to
       the `volume.restrict K` carry `hVmapMeasK`.  Final carries {`hSm`, `hg`, `hgpos`, `hu`,
       `hVmapMeasK`, `hGateDiff`}.

  ── GENERAL-`p` VERDICT.  For `p ≠ 0` no z-continuity of `z ↦ W z p` is banked, so `hVmapMeasK` is
     carried for general `p` (STRICTLY WEAKER than the previous `hVmapMeas` — restricted to `K`), with
     the `p = 0` slice discharged.  A genuine geometric regularity carry, never the conclusion.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GateChartMeasurability
import QIQTH.GeodesicGronwall

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge QIQTH.WitnessMeasDeriv
open QIQTH.GateChartMeasurability QIQTH.GeodesicGronwall
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.FoldedCoeffChartMeas

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — `hw` reduced to {`hg`, `hgpos`, `hu`} (van-Vleck prefactor discharged).
    ############################################################################### -/

/-- **★ `foldedCoeff_vanVleck_contDiff` — the concrete folded-coefficient smoothness lever.**  For the
    van-Vleck amplitude `Θ = vanVleck g`, `foldedCoeff Θ u k = fun y ↦ (vanVleck g y)^{−1/2}·u_k(y)`.
    Where the metric is `C^∞` (`hg`, feeding `vanVleck_contDiffAt`) and `det g > 0` everywhere
    (`hgpos`, giving both smoothness and non-vanishing of the positive `vanVleck g`), the prefactor
    `(vanVleck g)^{−1/2}` is `C^∞` (`contDiff_iff_contDiffAt` + `ContDiffAt.rpow_const_of_ne`); the
    product with the smooth coefficient `u_k` (`hu`) is `C^∞`.  NOT `a₁ = R/6`. -/
theorem foldedCoeff_vanVleck_contDiff (g : Point n → Fin n → Fin n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (u k)) :
    ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff (vanVleck g) u k) := by
  intro k
  have hΘ : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => (vanVleck g y) ^ (-(1 : ℝ) / 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    have hvv : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (vanVleck g) v :=
      vanVleck_contDiffAt g hg v (hgpos v)
    exact hvv.rpow_const_of_ne (ne_of_gt (vanVleck_pos g v (hgpos v)))
  have hrw : foldedCoeff (vanVleck g) u k
      = fun y => (vanVleck g y) ^ (-(1 : ℝ) / 2) * u k y := rfl
  rw [hrw]
  exact hΘ.mul (hu k)

/-- **★★ `hw_discharged` — the `hw` carry REDUCED to {`hg`, `hgpos`, `hu`}.**  The exact `hw` slot of
    `hKmeas_concrete_v2` (concrete `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`),
    with the van-Vleck prefactor half DISCHARGED from the metric smoothness `hg` and the det-positivity
    `hgpos`, leaving only the STANDARD carried transport-coefficient smoothness `hu` (the very carry
    threaded through `SpatialC2.hCH_discharge` etc.).  A genuine reduction — strictly lighter than `hw`
    (drops the `Θ^{−1/2}` obligation).  NOT `a₁ = R/6`. -/
theorem hw_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) :=
  foldedCoeff_vanVleck_contDiff g (transportCoeff (transportOp (vanVleck g) g gi)) hg hgpos hu

/-! ###############################################################################
    ### PART B — `hVmapMeas` via the RESTRICTED (`volume.restrict K`) indicator lever.
    ############################################################################### -/

/-- **★ `gatedKernel_slice_aestronglyMeasurable_of_restricted` — THE RESTRICTED INDICATOR LEVER.**
    The full-volume gated slice `z ↦ gatedKernel K S H τ p z` equals
    `(K ∩ {z|p∈S z}).indicator (z ↦ H τ p z)` (same case-split as the unrestricted lever), so via
    `aestronglyMeasurable_indicator_iff` and `mono_measure` (since `K ∩ … ⊆ K`) it is
    `AEStronglyMeasurable` on FULL `volume` as soon as the inner slice `z ↦ H τ p z` is
    `AEStronglyMeasurable` on `volume.restrict K` ALONE — STRICTLY WEAKER than the full-volume inner
    hypothesis of `gatedKernel_slice_aestronglyMeasurable`.  Reusable, parametric in `H`.
    NOT `a₁ = R/6`. -/
theorem gatedKernel_slice_aestronglyMeasurable_of_restricted (K : Set (Point n))
    (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n)
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
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
  rw [hrw, aestronglyMeasurable_indicator_iff (hKm.inter hSm)]
  exact hHmK.mono_measure (Measure.restrict_mono_set volume Set.inter_subset_left)

/-- **`hIn_composed_aestronglyMeasurable_ofMeasure`** — the generic-measure composition lever.  The
    inner order-1 parametrix slice `z ↦ globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z` is
    `AEStronglyMeasurable` w.r.t. ANY measure `μ` from {`hw`, `AEStronglyMeasurable (z ↦ Vmap z p) μ`}
    — the slice is the composition of the continuous spatial function `witnessInner_continuous` with
    the ae-measurable pullback (`Continuous.comp_aestronglyMeasurable`).  Same content as
    `GateChartMeasurability.hIn_composed_aestronglyMeasurable` but for an arbitrary `μ` (needed with
    `μ = volume.restrict K`).  NOT `a₁ = R/6`. -/
theorem hIn_composed_aestronglyMeasurable_ofMeasure (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (Vmap : Point n → Point n → Point n) (τ : ℝ) (p : Point n) (μ : Measure (Point n))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hVmap : AEStronglyMeasurable (fun z => Vmap z p) μ) :
    AEStronglyMeasurable (fun z => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z) μ := by
  have hcont : Continuous (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) :=
    witnessInner_continuous Θ u a b τ hw
  have hrw : (fun z => globalCutoffParametrixWitnessN 1 Θ u a b Vmap τ p z)
      = (fun z => (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) (Vmap z p)) := by
    funext z; rfl
  rw [hrw]
  exact hcont.comp_aestronglyMeasurable hVmap

/-- **`hInK_concrete_of_chartK_measurable`** — the concrete inner order-1 parametrix slice, restricted
    to `volume.restrict K`, from {`hw`, `hVmapMeasK`} (z-ae-measurability of the base-chart pullback
    on `K` only).  Instantiates the generic-measure composition lever at `μ = volume.restrict K`.
    NOT `a₁ = R/6`. -/
theorem hInK_concrete_of_chartK_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (hw : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hVmapMeasK : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart g gi hC hK z p) ((volume : Measure (Point n)).restrict K)) :
    ∀ (τ : ℝ) (p : Point n), AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      ((volume : Measure (Point n)).restrict K) :=
  fun τ p => hIn_composed_aestronglyMeasurable_ofMeasure (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p
    ((volume : Measure (Point n)).restrict K) hw (hVmapMeasK p)

/-- **`vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted`** — the witness base-slice
    `z ↦ H_G τ p z` is `AEStronglyMeasurable` on FULL `volume` from {`K` measurable, field-gate
    preimage measurable, inner slice measurable on `volume.restrict K`}, via the restricted indicator
    lever.  The RESTRICTED analogue of `WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable`.
    NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (p : Point n)
    (hKm : MeasurableSet K) (hSm : MeasurableSet {z : Point n | p ∈ S z})
    (hInK : AEStronglyMeasurable
      (fun z => globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK) τ p z)
      ((volume : Measure (Point n)).restrict K)) :
    AEStronglyMeasurable
      (fun z => vanVleckGatedWitness g gi hC hK S a b τ p z) (volume : Measure (Point n)) := by
  unfold vanVleckGatedWitness
  exact gatedKernel_slice_aestronglyMeasurable_of_restricted K S _ τ p hKm hSm hInK

/-- **`hWmeas_from_carries_restricted`** — the EXACT `hWmeas` slot of `hKmeas_from_witness`, from the
    RESTRICTED inner carry `hInK` (inner slice measurable on `volume.restrict K`), `hKm`, and `hSm`.
    The restricted analogue of `WitnessMeasDeriv.hWmeas_from_carries`.  NOT `a₁ = R/6`. -/
theorem hWmeas_from_carries_restricted (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hKm : MeasurableSet K)
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
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
  exact vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted g gi hC hK S a b (t - s)
    (Function.update x i w) hKm (hSm _) (hInK (t - s) (Function.update x i w))

/-! ###############################################################################
    ### `hVmapMeasK` at `p = 0` — discharged from the banked origin-chart `ContinuousOn`.
    ############################################################################### -/

/-- **★ `hVmapMeasK_zero_of_geom` — the `p = 0` slice of `hVmapMeasK` DISCHARGED.**  Instantiating the
    banked origin-chart Lipschitz/continuity `GeodesicGronwall.chartOrigin_continuousOn` at `S = K`
    (subset-refl) under the chart's genuine geometric side-conditions {`hball`, `hnorm`, `hRI`} gives
    `ContinuousOn (z ↦ W z 0) K`, whence `ContinuousOn.aestronglyMeasurable` (with `K` measurable,
    `IsCompact.measurableSet`) yields `AEStronglyMeasurable (z ↦ W z 0) (volume.restrict K)`.  The
    `p = 0` slice of the general `hVmapMeasK` carry.  NOT `a₁ = R/6`. -/
theorem hVmapMeasK_zero_of_geom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hball : ∀ z ∈ K, uniformInverseChart g gi hC hK z 0
      ∈ Metric.ball (0 : Point n) (chartOrigin_lipschitz_modulus g gi hC hK).choose)
    (hnorm : ∀ z ∈ K, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) :
    AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z 0)
      ((volume : Measure (Point n)).restrict K) := by
  have hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) K :=
    chartOrigin_continuousOn g gi hC hK (Set.Subset.refl K) hball hnorm hRI
  exact hcont.aestronglyMeasurable hK.measurableSet

/-! ###############################################################################
    ### CAPSTONE — `hKmeas_concrete_v3` (hKm + hw discharged, hVmapMeas weakened to `volume.restrict K`).
    ############################################################################### -/

/-- **★★ `hKmeas_concrete_v3`.**  The EXACT `hKmeas` slot of `g2_bundle_assembled` for the concrete
    witness first-derivative kernel `witnessFieldDeriv`, with THREE reductions relative to the raw
    `WitnessMeasDeriv.hKmeas_concrete` carries: `hKm` DISCHARGED (`compactGate_measurableSet hK`), `hw`
    DISCHARGED (`hw_discharged` from `{hg, hgpos, hu}`), and `hVmapMeas` WEAKENED from full-`volume`
    to `volume.restrict K` measurability of the chart pullback (`hVmapMeasK`), via the restricted
    indicator lever.  Final carries {`hSm`, `hg`, `hgpos`, `hu`, `hVmapMeasK`, `hGateDiff`} — each
    satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmapMeasK : ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart g gi hC hK z p) ((volume : Measure (Point n)).restrict K))
    (hGateDiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
        (volume : Measure (Point n)) :=
  hKmeas_from_witness g gi hC hK S a b t u
    (hWmeas_from_carries_restricted g gi hC hK S a b t u
      (compactGate_measurableSet hK) hSm
      (hInK_concrete_of_chartK_measurable g gi hC hK a b (hw_discharged g gi hg hgpos hu) hVmapMeasK))
    (hWdiff_from_gateDiff g gi hC hK S a b t u hGateDiff)

end QIQTH.FoldedCoeffChartMeas

section AxiomChecks
open QIQTH.FoldedCoeffChartMeas
#print axioms foldedCoeff_vanVleck_contDiff
#print axioms hw_discharged
#print axioms gatedKernel_slice_aestronglyMeasurable_of_restricted
#print axioms hIn_composed_aestronglyMeasurable_ofMeasure
#print axioms hInK_concrete_of_chartK_measurable
#print axioms vanVleckGatedWitness_slice_aestronglyMeasurable_ofRestricted
#print axioms hWmeas_from_carries_restricted
#print axioms hVmapMeasK_zero_of_geom
#print axioms hKmeas_concrete_v3
end AxiomChecks
