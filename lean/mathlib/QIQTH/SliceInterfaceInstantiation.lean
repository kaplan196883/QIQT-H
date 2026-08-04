/-
  SliceInterfaceInstantiation — J4-181: instantiating the Part-B slice / interface carries of
  J4-180's `GateDiffWiringMeasSet.hjoint_fully_geometric` — the `w`-slice CONTINUITY `hSliceCont`,
  the joint witness measurabilities at the rational field samples `hWq` and at the base point `hWa`.
  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity / measurability plumbing brick.  It replaces three of the honest Part-B slice/interface
  carries of J4-180's `hjoint_fully_geometric` (`hSliceCont`, `hWq`, `hWa`) by strictly lighter,
  satisfiable, non-vacuous inputs: the GATE-DESIGN cutoff-support condition (the gate strictly
  contains the cutoff support, so the indicator jump lands where the inner kernel already vanishes),
  the inner-kernel `w`-slice continuity, and a Borel-measurable inverse-chart family.  Never a
  conclusion; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── THE SUPPORT-CONDITION IDENTITY (killing the gate-boundary jump).

    The gated witness `H_G = gatedKernel K S (globalCutoffParametrixWitnessN 1 …)` carries, as a
    function of the field slot, a HARD indicator `if q ∈ S z …`.  As `q` moves along a line the
    indicator would jump at `∂(S z)`, breaking continuity — UNLESS the inner kernel already vanishes
    there.  The inner kernel starts with the factor `radialCutoff a b (W z q)`, which is `0` once
    `‖W z q‖ ≥ b` (the cutoff outer radius).  The flow-ball gate `S z = φ_z '' ball 0 c` has chart
    radius `c`; the DESIGN keeps the cutoff support inside the gate (`b < c`), so a field point off
    the gate has `‖W z q‖ ≥ c > b`, the cutoff is `0`, and the inner kernel vanishes.  We take this
    as the honest, satisfiable SUPPORT CONDITION `hsupp : ∀ q ∉ S z, radialCutoff a b (W z q) = 0`,
    under which the gated witness EQUALS the ungated inner kernel in the WHOLE field slot — no jump.

    • `innerKernelField_eq_zero_of_cutoff_zero` — the cutoff-vanishing ⟹ inner-kernel-vanishing leg.
    • `gatedWitness_fieldSlot_eq_inner_of_support` — ★ the field-slot identity `H_G = innerKernel`.
    • `gatedWitness_slice_continuous_of_support` — ★ `w`-slice continuity ON the gate (`z ∈ K`), from
        the identity + the inner-kernel `w`-slice continuity.  NOT `a₁ = R/6`.
    • `gatedWitness_slice_zero_of_notMemK` — the `z ∉ K` slice is `≡ 0`, continuous.
    • `hSliceCont_of_data` — ★★ the EXACT `hSliceCont` slot of J4-180, from the per-`p` dichotomy
        carry `hSliceData` (`z ∉ K`, OR `z ∈ K` with open gate + support + inner slice continuity).

  ── THE JOINT WITNESS MEASURABILITIES `hWq` / `hWa` (Borel indicator glue).

    • `gatedFieldpoint_measurable_of_inner` — ★ the Borel (NOT merely a.e.) mirror of J4-177's
        `witness_joint_aestronglyMeasurable`: the gate is the indicator of the `s`-independent product
        set `snd ⁻¹' (K ∩ {z | q₀ ∈ S z})`, so `Measurable.indicator` upgrades a Borel inner-kernel
        measurability to the Borel gated measurability.
    • `gcpw_fieldpoint_measurable_of_chartBorel` — ★ the ungated order-1 witness Borel measurability
        at a fixed field point, from `witnessInner_measurable_uncurry` (Borel outer) composed with a
        BOREL inverse-chart carry `hChart` (the Borel analogue of J4-178's a.e. `hVmapMeas`).
    • `hWq_of_chartBorel` / `hWa_of_chartBorel` — ★★ the EXACT `hWq` / `hWa` slots of J4-180, reduced
        to `{hKmeasSet, hSmeasSet, hΘc, hΘne, huc, hChartB}`.  NOT `a₁ = R/6`.

  ── CAPSTONE.
    • `hjoint_instantiated` — ★★★ the full `hjoint` capstone with J4-180's `hSliceCont`, `hWq`, `hWa`
        discharged to the lighter slice/interface carries; `hDmeas` (the DERIVATIVE joint
        measurability — the genuine `pd`-content) stays honestly carried, together with the geometric
        gate/coverage/source data.  NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hDmeas` — the joint measurability of the FIELD DERIVATIVE kernel.  Genuinely the derivative
      content (`witnessFieldDeriv = pd`), never faked here.  The `measurable_deriv_with_param` route
      needs JOINT continuity of the `(s,z,w)`-slice, which fails across `∂K` (and across the gate
      before the support identity is applied); the raw slope-limsup equals the derivative only where
      the slice is differentiable.  So `hDmeas` stays the honest carry.
    • `hSliceData` — the per-`p` gate/support/inner-continuity dichotomy (pure chart geometry).
    • `hChartB` — the Borel inverse-chart family (Borel analogue of `hVmapMeas`; satisfiable for a
      chart continuous on the reach with a measurable off-reach default).
    • `{hg, hgi, hgpos, hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hCover, hΘc, hΘne, huc}` — the
      genuine geometric / gate / source / coefficient data (each satisfiable, none the conclusion).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GateDiffWiringMeasSet
import QIQTH.InnerKernelJointMeas
import QIQTH.EngineInstantiation

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity
open QIQTH.InnerKernelJointMeas QIQTH.GateDiffWiringMeasSet
open scoped Interval Topology BigOperators

namespace QIQTH.SliceInterfaceInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART 1 — the SUPPORT-CONDITION field-slot identity (killing the gate jump).
    ############################################################################### -/

/-- **`innerKernelField_eq_zero_of_cutoff_zero`.**  Since the inner kernel starts with the factor
    `radialCutoff a b (W z q)`, once the cutoff vanishes at `q` the whole inner kernel vanishes there.
    NOT `a₁ = R/6`. -/
theorem innerKernelField_eq_zero_of_cutoff_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z q : Point n)
    (hcut : radialCutoff a b (uniformInverseChart g gi hC hK z q) = 0) :
    innerKernelField g gi hC hK a b τ z q = 0 := by
  simp only [innerKernelField, hcut, zero_mul]

/-- **★ `gatedWitness_fieldSlot_eq_inner_of_support` — THE FIELD-SLOT IDENTITY.**  For `z ∈ K` with
    the OPEN gate `S z` and the gate-design SUPPORT CONDITION (`hsupp`: off the gate the cutoff
    vanishes, so the inner kernel vanishes), the gated witness equals the ungated inner kernel in the
    WHOLE field slot: `(fun q ↦ H_G τ q z) = innerKernelField … τ z`.  On the gate they coincide by
    `vanVleckGatedWitness_gate_apply`; off the gate the gated kernel is `0` and so is the inner kernel
    (`hsupp`).  This is the fact that KILLS the gate-boundary indicator jump.  NOT `a₁ = R/6`. -/
theorem gatedWitness_fieldSlot_eq_inner_of_support (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z : Point n) (hzK : z ∈ K)
    (hsupp : ∀ q, q ∉ S z → radialCutoff a b (uniformInverseChart g gi hC hK z q) = 0) :
    (fun q => vanVleckGatedWitness g gi hC hK S a b τ q z)
      = innerKernelField g gi hC hK a b τ z := by
  funext q
  by_cases hq : q ∈ S z
  · rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hzK hq]; rfl
  · have h0 : vanVleckGatedWitness g gi hC hK S a b τ q z = 0 := by
      simp only [vanVleckGatedWitness]
      exact gatedKernel_apply_of_notMem K S _ τ q z (Or.inr hq)
    rw [h0]
    exact (innerKernelField_eq_zero_of_cutoff_zero g gi hC hK a b τ z q (hsupp q hq)).symm

/-- **★ `gatedWitness_slice_continuous_of_support`.**  On the gate (`z ∈ K`, `S z` open, support), the
    `w`-slice of the gated witness is CONTINUOUS, transferred from the inner-kernel `w`-slice
    continuity by the field-slot identity — the gate-boundary jump has been removed.  NOT `a₁ = R/6`. -/
theorem gatedWitness_slice_continuous_of_support (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) (hzK : z ∈ K)
    (hsupp : ∀ q, q ∉ S z → radialCutoff a b (uniformInverseChart g gi hC hK z q) = 0)
    (hinnerCont : Continuous
      (fun w : ℝ => innerKernelField g gi hC hK a b τ z (Function.update x i w))) :
    Continuous (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z) := by
  have hid := gatedWitness_fieldSlot_eq_inner_of_support g gi hC hK S a b τ z hzK hsupp
  have heq : (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z)
      = (fun w : ℝ => innerKernelField g gi hC hK a b τ z (Function.update x i w)) := by
    funext w
    have := congrFun hid (Function.update x i w)
    simpa using this
  rw [heq]; exact hinnerCont

/-- **`gatedWitness_slice_zero_of_notMemK`.**  Off `K` (`z ∉ K`) the gated witness `w`-slice is
    identically `0`, hence continuous.  NOT `a₁ = R/6`. -/
theorem gatedWitness_slice_zero_of_notMemK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (x z : Point n) (hzK : z ∉ K) :
    Continuous (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z) := by
  have heq : (fun w : ℝ => vanVleckGatedWitness g gi hC hK S a b τ (Function.update x i w) z)
      = (fun _ : ℝ => (0 : ℝ)) := by
    funext w
    simp only [vanVleckGatedWitness]
    exact gatedKernel_apply_of_notMem K S _ τ _ z (Or.inl hzK)
  rw [heq]; exact continuous_const

/-- **★★ `hSliceCont_of_data` — THE EXACT `hSliceCont` SLOT of J4-180.**  Produced from the per-`p`
    gate/support/inner-continuity dichotomy carry `hSliceData` (per `p`: either `z ∉ K`, or `z ∈ K`
    with the gate open, the cutoff-support condition, and the inner-kernel `w`-slice continuity).  The
    `z ∉ K` branch gives the `≡ 0` slice; the `z ∈ K` branch runs the support-identity transfer.
    NOT `a₁ = R/6`. -/
theorem hSliceCont_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u₀ : Set (Point n))
    (hSliceData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 →
                radialCutoff a b (uniformInverseChart g gi hC hK p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w)))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ p : ℝ × Point n, Continuous
        (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSliceData x₀ hx₀ i] with x hx
  intro p
  rcases hx p with hnK | ⟨hzK, hsupp, hinnerCont⟩
  · exact gatedWitness_slice_zero_of_notMemK g gi hC hK S a b i (t - p.1) x p.2 hnK
  · exact gatedWitness_slice_continuous_of_support g gi hC hK S a b i (t - p.1) x p.2 hzK
      hsupp hinnerCont

/-! ###############################################################################
    ### PART 2 — the BOREL joint witness measurabilities `hWq` / `hWa`.
    ############################################################################### -/

/-- **★ `gatedFieldpoint_measurable_of_inner` — the Borel indicator glue.**  The Borel mirror of
    J4-177's a.e. `witness_joint_aestronglyMeasurable`: the gate `gatedKernel K S H (τ p.1) q₀ p.2`
    is the indicator of the `s`-independent measurable product set `snd ⁻¹' (K ∩ {z | q₀ ∈ S z})`
    applied to the inner kernel, so `Measurable.indicator` upgrades a Borel inner measurability to a
    Borel gated measurability.  NOT `a₁ = R/6`. -/
theorem gatedFieldpoint_measurable_of_inner {α : Type*} [MeasurableSpace α]
    (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (q₀ : Point n) (τf : α → ℝ)
    (hKmeas : MeasurableSet K)
    (hSmeas : MeasurableSet {z : Point n | q₀ ∈ S z})
    (hinner : Measurable (fun p : α × Point n => H (τf p.1) q₀ p.2)) :
    Measurable (fun p : α × Point n => gatedKernel K S H (τf p.1) q₀ p.2) := by
  classical
  set G : Set (Point n) := K ∩ {z : Point n | q₀ ∈ S z} with hG
  have hGmeas : MeasurableSet G := hKmeas.inter hSmeas
  have hSetMeas : MeasurableSet (Prod.snd ⁻¹' G : Set (α × Point n)) := measurable_snd hGmeas
  have hgate : (fun p : α × Point n => gatedKernel K S H (τf p.1) q₀ p.2)
      = (Prod.snd ⁻¹' G).indicator (fun p : α × Point n => H (τf p.1) q₀ p.2) := by
    funext p
    rw [Set.indicator_apply]
    by_cases hz : p.2 ∈ G
    · have hzK : p.2 ∈ K := hz.1
      have hzS : q₀ ∈ S p.2 := hz.2
      rw [if_pos (by exact hz : p ∈ Prod.snd ⁻¹' G)]
      simp only [gatedKernel, if_pos hzK, if_pos hzS]
    · rw [if_neg (by exact hz : ¬ p ∈ Prod.snd ⁻¹' G)]
      have hnand : ¬ (p.2 ∈ K ∧ q₀ ∈ S p.2) := hz
      rcases not_and_or.mp hnand with hzK | hzS
      · simp only [gatedKernel, if_neg hzK]
      · by_cases hzK : p.2 ∈ K
        · simp only [gatedKernel, if_pos hzK, if_neg hzS]
        · simp only [gatedKernel, if_neg hzK]
  rw [hgate]
  exact hinner.indicator hSetMeas

/-- **★ `gcpw_fieldpoint_measurable_of_chartBorel`.**  The ungated order-1 global-cutoff witness is
    Borel-measurable in `(s,z)` at a fixed field point `q₀`, from the globally Borel outer kernel
    (`witnessInner_measurable_uncurry`) composed with the affine time map and a BOREL inverse-chart
    carry `hChart` — the Borel analogue of J4-178's a.e. `hVmapMeas`.  NOT `a₁ = R/6`. -/
theorem gcpw_fieldpoint_measurable_of_chartBorel {α : Type*} [MeasurableSpace α]
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (q₀ : Point n) (τf : α → ℝ)
    (hτf : Measurable τf)
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChart : Measurable
      (fun p : α × Point n => uniformInverseChart g gi hC hK p.2 q₀)) :
    Measurable (fun p : α × Point n =>
      globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK) (τf p.1) q₀ p.2) := by
  have houter := witnessInner_measurable_uncurry (n := n)
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b hΘc hΘne huc
  have hpair : Measurable
      (fun p : α × Point n => (τf p.1, uniformInverseChart g gi hC hK p.2 q₀)) :=
    (hτf.comp measurable_fst).prodMk hChart
  simpa only [globalCutoffParametrixWitnessN, Function.comp_def] using houter.comp hpair

/-- **★★ `hWq_of_chartBorel` — THE EXACT `hWq` SLOT of J4-180.**  The joint `(s,z)`-Borel
    measurability of the gated witness at the RATIONAL field samples `Function.update x i (x i + q)`,
    reduced to the gate-set data (`hKmeasSet`, `hSmeasSet`), the coefficient data (`hΘc`, `hΘne`,
    `huc`) and the Borel inverse-chart family (`hChartB`).  Via the Borel inner measurability
    (`gcpw_fieldpoint_measurable_of_chartBorel`) + the Borel gate glue
    (`gatedFieldpoint_measurable_of_inner`).  NOT `a₁ = R/6`. -/
theorem hWq_of_chartBorel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChartB : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n =>
          uniformInverseChart g gi hC hK p.2 (Function.update x i w))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
      Measurable (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (t - p.1)
          (Function.update x i (x i + (q : ℝ))) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSmeasSet x₀ hx₀ i, hChartB x₀ hx₀ i] with x hSm hCh
  intro q
  have hinner := gcpw_fieldpoint_measurable_of_chartBorel (α := ℝ) g gi hC hK a b
    (Function.update x i (x i + (q : ℝ))) (fun s => t - s)
    (measurable_const.sub measurable_id) hΘc hΘne huc (hCh (x i + (q : ℝ)))
  have hgate := gatedFieldpoint_measurable_of_inner (α := ℝ) K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))
    (Function.update x i (x i + (q : ℝ))) (fun s => t - s)
    hKmeasSet (hSm (x i + (q : ℝ))) hinner
  exact hgate

/-- **★★ `hWa_of_chartBorel` — THE EXACT `hWa` SLOT of J4-180.**  The joint `(s,z)`-Borel
    measurability of the gated witness at the BASE point `Function.update x i (x i)`, reduced to the
    same lighter carries as `hWq_of_chartBorel` (specialised to the base shift).  NOT `a₁ = R/6`. -/
theorem hWa_of_chartBorel (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChartB : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n =>
          uniformInverseChart g gi hC hK p.2 (Function.update x i w))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      Measurable (fun p : ℝ × Point n =>
        vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSmeasSet x₀ hx₀ i, hChartB x₀ hx₀ i] with x hSm hCh
  have hinner := gcpw_fieldpoint_measurable_of_chartBorel (α := ℝ) g gi hC hK a b
    (Function.update x i (x i)) (fun s => t - s)
    (measurable_const.sub measurable_id) hΘc hΘne huc (hCh (x i))
  have hgate := gatedFieldpoint_measurable_of_inner (α := ℝ) K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))
    (Function.update x i (x i)) (fun s => t - s)
    hKmeasSet (hSm (x i)) hinner
  exact hgate

/-! ###############################################################################
    ### ★★★ CAPSTONE — `hjoint` with `hSliceCont` / `hWq` / `hWa` instantiated.
    ############################################################################### -/

/-- **★★★ `hjoint_instantiated` — the full `hjoint`, Part-B slice/interface carries instantiated.**
    The exact `hjoint` slot of `g2_bundle_assembled` for `dH := witnessFieldDeriv`, with J4-180's
    `hSliceCont`, `hWq`, `hWa` discharged to the lighter slice/interface carries (`hSliceData`,
    `hChartB`, `hΘc`, `hΘne`, `huc`).  `hDmeas` — the joint measurability of the FIELD DERIVATIVE
    kernel (the genuine `pd`-content) — stays honestly carried, together with the geometric gate /
    coverage / source data.  NONE of the carries is the conclusion.  NOT `a₁ = R/6`. -/
theorem hjoint_instantiated (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hFjoint : AEStronglyMeasurable (fun p : ℝ × Point n => F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν))
    (hVmapMeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEMeasurable (fun z : Point n => uniformInverseChart g gi hC hK z (Function.update x i w)) ν)
    (hCover : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂ν,
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x))
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChartB : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n =>
          uniformInverseChart g gi hC hK p.2 (Function.update x i w)))
    (hSliceData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 →
                radialCutoff a b (uniformInverseChart g gi hC hK p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelField g gi hC hK a b (t - p.1) p.2 (Function.update x i w))))
    (hDmeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
  hjoint_fully_geometric g gi hC hK S a b t F ν u₀ hg hgi hgpos hKmeasSet hSmeasSet hFjoint
    hVmapMeas hCover
    (hSliceCont_of_data g gi hC hK S a b t u₀ hSliceData)
    (hWq_of_chartBorel g gi hC hK S a b t u₀ hKmeasSet hSmeasSet hΘc hΘne huc hChartB)
    (hWa_of_chartBorel g gi hC hK S a b t u₀ hKmeasSet hSmeasSet hΘc hΘne huc hChartB)
    hDmeas

end QIQTH.SliceInterfaceInstantiation

section AxiomChecks
open QIQTH.SliceInterfaceInstantiation
#print axioms innerKernelField_eq_zero_of_cutoff_zero
#print axioms gatedWitness_fieldSlot_eq_inner_of_support
#print axioms gatedWitness_slice_continuous_of_support
#print axioms gatedWitness_slice_zero_of_notMemK
#print axioms hSliceCont_of_data
#print axioms gatedFieldpoint_measurable_of_inner
#print axioms gcpw_fieldpoint_measurable_of_chartBorel
#print axioms hWq_of_chartBorel
#print axioms hWa_of_chartBorel
#print axioms hjoint_instantiated
end AxiomChecks
