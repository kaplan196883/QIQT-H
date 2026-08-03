/-
  ChartGeneralPContinuity — J4-168: generalizing the z-continuity / z-ae-measurability of the uniform
  inverse chart `z ↦ uniformInverseChart g gi hC hK z p` from the banked `p = 0` slice
  (`GeodesicGronwall.chartOrigin_continuousOn` / `FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom`) to a
  GENERAL field point `p : Point n`, and the honest re-threading of the `hVmapMeasK` carry of
  `FoldedCoeffChartMeas.hKmeas_concrete_v3` (`hKmeas_concrete_v4`).  ONE brick of the a₁=R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity brick: the two-solution geodesic Grönwall that made `z ↦ W z 0` continuous is shown to be
  p-PARAMETRIC, so the SAME estimate makes `z ↦ W z p` continuous — hence ae-measurable on `K` — for
  any field point `p`, under the p-analogue of the same genuine geometric side-conditions.  Never a
  conclusion; no vacuous/unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ── THE p-DEPENDENCE ANALYSIS (where p enters the chart ODE).  `uniformInverseChart g gi hC hK z p`
     is the inverse of the forward geodesic-flow endpoint map `uniformFlowExp g gi hC hK z` evaluated at
     the point `p`: i.e. the velocity `v = W z p` with `uniformFlowExp z v = p` (the exp⁻¹ velocity
     hitting `p`).  So `p` enters ONLY as the ENDPOINT the inverse chart hits — NOT as ODE coefficient
     data.  The banked W4a modulus (`chartOrigin_lipschitz_modulus`) welds three p-independent engines:
       • the transfer lemma `chart_joint_velocity_modulus` — stated for ARBITRARY velocities
         `w, w' ∈ ball 0 δ₀` (NO `p = 0` baked in): `‖w−w'‖ ≤ C_inv·(‖φ_q w − φ_{q'} w'‖ + ‖φ_{q'} w' −
         φ_q w'‖)`;
       • the base-flow difference W3 `uniformFlowExp_base_diff_bound` — `‖φ_q w − φ_{q'} w‖ ≤ exp L·‖q −
         q'‖` for EVERY `w` with `‖w‖ ≤ ρ_K` (completely p-independent);
       • the right-inverse identity — at `p = 0` it is `φ_z(W z 0) = 0`; the p-general analogue is
         `φ_z(W z p) = p`.
     Instantiating the transfer at `w = W z p`, `w' = W z' p` gives term-1 `‖φ_z(W z p) − φ_{z'}(W z' p)‖
     = ‖p − p‖ = 0` (the right-inverse at `p`, both sides `= p`) and term-2 `= ‖φ_{z'}(W z' p) −
     φ_z(W z' p)‖ = ‖φ_z(W z' p) − φ_{z'}(W z' p)‖ ≤ exp L·‖z − z'‖` (W3 at velocity `W z' p`, needs NO
     `p`).  So the whole argument rides along at general `p` (OPTION (i): the Grönwall generalizes),
     with the ONLY p-specific input the right-inverse `φ_z(W z p) = p` (plus the domain memberships).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    * `chartP_lipschitz_modulus` — **the p-general origin-chart Lipschitz modulus.**  Verbatim mirror of
      `GeodesicGronwall.chartOrigin_lipschitz_modulus` with `0 ↦ p` and `φ_z(W z 0) = 0 ↦ φ_z(W z p) =
      p`: `‖W z p − W z' p‖ ≤ (C_inv·exp L)·‖z − z'‖` on any `S ⊆ K` where {ball, norm ≤ ρ_K,
      right-inverse-at-`p`} hold.

    * `chartP_continuousOn` — **★ Part A.**  The p-general z-continuity `ContinuousOn (z ↦ W z p) S`
      under the three geometric side-conditions at `p` — the direct generalization of the banked
      `chartOrigin_continuousOn`.

    * `hVmapMeasK_at_p_of_geom` — **Part B.**  For a fixed `p`, from the three side-conditions on `K`
      (via `IsCompact.measurableSet` + `ContinuousOn.aestronglyMeasurable`):
      `AEStronglyMeasurable (z ↦ W z p) (volume.restrict K)`.  The p-general analogue of
      `FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom` (which is exactly its `p = 0` instance).

    * `hVmapMeasK_of_geomOrMeas` — the honest `∀ p` discharge.  Carries, PER `p`, a DISJUNCTION:
      EITHER the geometric side-conditions at `p` (⟹ Part B) OR the bare measurability of that slice.
      Delivers `hVmapMeasK : ∀ p, AEStronglyMeasurable (z ↦ W z p) (volume.restrict K)`.

    * `hKmeas_concrete_v4` — **★ Part C (capstone).**  The EXACT `hKmeas` slot of `g2_bundle_assembled`
      for `witnessFieldDeriv`, threaded through `hKmeas_concrete_v3` with `hVmapMeasK` REPLACED by the
      per-`p` geometry-OR-measurability disjunction `hChartP`.  Final carries {`hSm`, `hg`, `hgpos`,
      `hu`, `hChartP`, `hGateDiff`}.

  ── OPTION VERDICT (which of the task's (i)/(ii)/(iii) landed).  OPTION (i) for the ANALYSIS: the
     Grönwall is p-parametric and `chartP_continuousOn` holds for EVERY `p` for which the three genuine
     geometric side-conditions hold (the p-analogues of the banked `p = 0` carries).  Valid p-range =
     any field point in the uniform reach of the chart over `K` (right-inverse `φ_z(W z p) = p` +
     velocity in `ball δ₀ ∩ closedBall ρ_K`); this is NOT provably ALL of `Point n` (for a metric with
     finite injectivity radius over `K` a far `p` is not reachable and `φ_z(W z p) = p` genuinely
     fails), so full `∀ p` unconditional continuity is NOT claimed.  For the `∀ p` CARRY the capstone
     takes OPTION (iii): a per-`p` disjunction — geometry where the chart reaches, bare measurability
     otherwise (each branch satisfiable, the disjunction total, so `hChartP` is honest and never
     unsatisfiable).  NOTE (option (ii)): the cutoff-support vanishing (`radialCutoff a b (W z p) = 0`
     for `‖W z p‖ ≥ b`) concerns the KERNEL `radialCutoff · heatParametrix`, NOT the slice `z ↦ W z p`
     itself (whose measurability `hVmapMeasK` demands), so it does not discharge the far-`p` slice; it
     is left as the honest residue absorbed by the disjunction's measurability branch.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FoldedCoeffChartMeas

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge QIQTH.WitnessMeasDeriv
open QIQTH.GateChartMeasurability QIQTH.GeodesicGronwall QIQTH.FoldedCoeffChartMeas
open scoped Interval Topology BigOperators NNReal ContDiff

namespace QIQTH.ChartGeneralPContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Part A — the p-general origin-chart Lipschitz modulus and z-continuity.
    ############################################################################### -/

/-- **`chartP_lipschitz_modulus` — the p-general origin-chart Lipschitz modulus.**  Verbatim mirror of
    `GeodesicGronwall.chartOrigin_lipschitz_modulus` with the origin `0` replaced by a general field
    point `p` and the right-inverse identity `φ_z(W z 0) = 0` replaced by `φ_z(W z p) = p`.  Welding the
    p-INDEPENDENT base-flow difference W3 (`uniformFlowExp_base_diff_bound`) to the p-GENERIC transfer
    lemma `chart_joint_velocity_modulus` (arbitrary velocities in `ball 0 δ₀`) and the right-inverse
    at `p`, the inverse chart `z ↦ uniformInverseChart g gi hC hK z p` is Lipschitz in the BASE on any
    `S ⊆ K` where the three carried geometric side-conditions at `p` hold:
        `‖W z p − W z' p‖ ≤ (C_inv · exp L) · ‖z − z'‖`.
    (term-1 `‖φ_z(W z p) − φ_{z'}(W z' p)‖ = ‖p − p‖ = 0` by the right-inverse; term-2
    `= ‖φ_{z'}(W z' p) − φ_z(W z' p)‖ = ‖φ_z(W z' p) − φ_{z'}(W z' p)‖ ≤ exp L·‖z − z'‖` = W3 at
    velocity `W z' p`, needing no `p`).  NOT `a₁ = R/6`. -/
theorem chartP_lipschitz_modulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n) :
    ∃ δ₀ > (0 : ℝ), ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ {S : Set (Point n)}, S ⊆ K →
      (∀ z ∈ S, uniformInverseChart g gi hC hK z p ∈ Metric.ball (0 : Point n) δ₀) →
      (∀ z ∈ S, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK) →
      (∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) →
      ∀ z ∈ S, ∀ z' ∈ S,
        ‖uniformInverseChart g gi hC hK z p - uniformInverseChart g gi hC hK z' p‖
          ≤ Λ * ‖z - z'‖ := by
  obtain ⟨δ₀, hδ₀, C_inv, hCinv0, htrans⟩ := chart_joint_velocity_modulus g gi hC hK
  obtain ⟨L, hL0, hbase⟩ := uniformFlowExp_base_diff_bound g gi hC hK
  refine ⟨δ₀, hδ₀, C_inv * Real.exp L, mul_nonneg hCinv0 (le_of_lt (Real.exp_pos _)), ?_⟩
  intro S hSK hball hnorm hRI z hz z' hz'
  set Wz := uniformInverseChart g gi hC hK z p with hWz
  set Wz' := uniformInverseChart g gi hC hK z' p with hWz'
  -- transfer lemma at `q := z`, `q' := z'`, `w := Wz`, `w' := Wz'`.
  have hT := htrans z (hSK hz) z' (hSK hz') Wz (hball z hz) Wz' (hball z' hz')
  -- right-inverse at `p`: `φ_z(Wz) = p`, `φ_{z'}(Wz') = p`.
  have hRIz : uniformFlowExp g gi hC hK z Wz = p := hRI z hz
  have hRIz' : uniformFlowExp g gi hC hK z' Wz' = p := hRI z' hz'
  -- first transfer term vanishes (`p − p`).
  have hterm1 : ‖uniformFlowExp g gi hC hK z Wz - uniformFlowExp g gi hC hK z' Wz'‖ = 0 := by
    rw [hRIz, hRIz', sub_self, norm_zero]
  -- second transfer term = W3 at velocity `Wz'` (p-INDEPENDENT).
  have hb := hbase z (hSK hz) z' (hSK hz') Wz' (hnorm z' hz')
  have hterm2 : ‖uniformFlowExp g gi hC hK z' Wz' - uniformFlowExp g gi hC hK z Wz'‖
      ≤ Real.exp L * ‖z - z'‖ := by
    rw [norm_sub_rev]; exact hb
  -- assemble.
  calc ‖Wz - Wz'‖
      ≤ C_inv * (‖uniformFlowExp g gi hC hK z Wz - uniformFlowExp g gi hC hK z' Wz'‖
          + ‖uniformFlowExp g gi hC hK z' Wz' - uniformFlowExp g gi hC hK z Wz'‖) := hT
    _ ≤ C_inv * (0 + Real.exp L * ‖z - z'‖) := by
        apply mul_le_mul_of_nonneg_left _ hCinv0
        exact add_le_add (le_of_eq hterm1) hterm2
    _ = (C_inv * Real.exp L) * ‖z - z'‖ := by ring

/-- **★ Part A — `chartP_continuousOn`.**  The p-general z-continuity: the Lipschitz modulus above ⟹
    `ContinuousOn (z ↦ uniformInverseChart g gi hC hK z p) S` on `S ⊆ K`, under the three geometric
    side-conditions at `p` (`hball`, `hnorm`, `hRI`).  The direct generalization of the banked
    `GeodesicGronwall.chartOrigin_continuousOn` (which is its `p = 0` instance).  NOT `a₁ = R/6`. -/
theorem chartP_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n)
    {S : Set (Point n)} (hSK : S ⊆ K)
    (hball : ∀ z ∈ S, uniformInverseChart g gi hC hK z p
      ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
    (hnorm : ∀ z ∈ S, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) :
    ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) S := by
  obtain ⟨Λ, hΛ0, hmod⟩ := (chartP_lipschitz_modulus g gi hC hK p).choose_spec.2
  have hlip : LipschitzOnWith Λ.toNNReal
      (fun z : Point n => uniformInverseChart g gi hC hK z p) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz z' hz'
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal Λ hΛ0]
    exact hmod hSK hball hnorm hRI z hz z' hz'
  exact hlip.continuousOn

/-! ###############################################################################
    ### Part B — the p-general `volume.restrict K` ae-measurability of the chart slice.
    ############################################################################### -/

/-- **★ Part B — `hVmapMeasK_at_p_of_geom`.**  For a fixed field point `p`, the three geometric
    side-conditions on `K` (`S = K`, subset-refl) ⟹ `ContinuousOn (z ↦ W z p) K` (Part A), whence
    `ContinuousOn.aestronglyMeasurable` (with `K` measurable via `IsCompact.measurableSet`):
        `AEStronglyMeasurable (z ↦ uniformInverseChart g gi hC hK z p) (volume.restrict K)`.
    The p-general analogue of `FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom` (its `p = 0` instance).
    NOT `a₁ = R/6`. -/
theorem hVmapMeasK_at_p_of_geom (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (p : Point n)
    (hball : ∀ z ∈ K, uniformInverseChart g gi hC hK z p
      ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
    (hnorm : ∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) :
    AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
      ((volume : Measure (Point n)).restrict K) := by
  have hcont : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z p) K :=
    chartP_continuousOn g gi hC hK p (Set.Subset.refl K) hball hnorm hRI
  exact hcont.aestronglyMeasurable hK.measurableSet

/-- **`hVmapMeasK_of_geomOrMeas` — the honest `∀ p` discharge of the `hVmapMeasK` carry.**  Carries,
    PER field point `p`, a DISJUNCTION: EITHER the three geometric side-conditions at `p` on `K` (which
    discharge the slice through Part B) OR the bare `volume.restrict K` ae-measurability of the slice
    (the honest residue for `p` outside the chart's uniform reach over `K`).  Each branch is satisfiable
    and the disjunction is total, so the carry is never unsatisfiable.  Delivers the full
    `hVmapMeasK : ∀ p, AEStronglyMeasurable (z ↦ W z p) (volume.restrict K)` needed by
    `hKmeas_concrete_v3`.  NOT `a₁ = R/6`. -/
theorem hVmapMeasK_of_geomOrMeas (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hChartP : ∀ p : Point n,
      ( (∀ z ∈ K, uniformInverseChart g gi hC hK z p
            ∈ Metric.ball (0 : Point n) (chartP_lipschitz_modulus g gi hC hK p).choose)
        ∧ (∀ z ∈ K, ‖uniformInverseChart g gi hC hK z p‖ ≤ uniformFlowRadius g gi hC hK)
        ∧ (∀ z ∈ K, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z p) = p) )
      ∨ AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z p)
          ((volume : Measure (Point n)).restrict K)) :
    ∀ p : Point n, AEStronglyMeasurable
      (fun z => uniformInverseChart g gi hC hK z p) ((volume : Measure (Point n)).restrict K) := by
  intro p
  rcases hChartP p with ⟨hball, hnorm, hRI⟩ | hmeas
  · exact hVmapMeasK_at_p_of_geom g gi hC hK p hball hnorm hRI
  · exact hmeas

/-! ###############################################################################
    ### Part C — capstone `hKmeas_concrete_v4` (hVmapMeasK ↦ per-p geometry-OR-measurability).
    ############################################################################### -/

/-- **★★ Part C — `hKmeas_concrete_v4`.**  The EXACT `hKmeas` slot of `g2_bundle_assembled` for the
    concrete witness first-derivative kernel `witnessFieldDeriv`, threaded through
    `FoldedCoeffChartMeas.hKmeas_concrete_v3` with the opaque chart-pullback measurability carry
    `hVmapMeasK : ∀ p, AEStronglyMeasurable (z ↦ W z p) (volume.restrict K)` REPLACED by the per-`p`
    geometry-OR-measurability disjunction `hChartP` (from which `hVmapMeasK` is reconstructed by
    `hVmapMeasK_of_geomOrMeas`: geometry ⟹ Part B where the chart reaches, bare measurability
    otherwise).  Final carries {`hSm`, `hg`, `hgpos`, `hu`, `hChartP`, `hGateDiff`} — each satisfiable,
    non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem hKmeas_concrete_v4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hSm : ∀ p : Point n, MeasurableSet {z : Point n | p ∈ S z})
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
  hKmeas_concrete_v3 g gi hC hK S a b t u hSm hg hgpos hu
    (hVmapMeasK_of_geomOrMeas g gi hC hK hChartP) hGateDiff

end QIQTH.ChartGeneralPContinuity

section AxiomChecks
open QIQTH.ChartGeneralPContinuity
#print axioms chartP_lipschitz_modulus
#print axioms chartP_continuousOn
#print axioms hVmapMeasK_at_p_of_geom
#print axioms hVmapMeasK_of_geomOrMeas
#print axioms hKmeas_concrete_v4
end AxiomChecks
