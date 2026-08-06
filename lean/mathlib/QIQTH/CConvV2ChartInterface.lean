/-
  CConvV2ChartInterface — J4-327 (facade-v2 bricks 3+4 of 14): the CHART-PARAMETRIC copies of the
  slice-interface machinery that currently hardwires `uniformInverseChart`.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign (SOL CONSULT #9, docs/qg_roadmap/JET4_TOWER_PLAN.md).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It re-derives
  the witness-side slice/measurability interface ONCE with the chart taken as an OPAQUE parameter
  `Vmap : Point n → Point n → Point n`, to be instantiated later (bricks 11/14) at BOTH the raw
  `uniformInverseChart g gi hC hK` (recovered definitionally) AND the piecewise chart `Wg` of
  `B2MeasurabilityDissolution`.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO
  vacuous / unsatisfiable hypothesis in this file's OWN theorems, no existing file edited, nothing
  committed.  The opaque chart parameter is kept OPAQUE throughout — no `.choose`, no heavy-tactic
  defeq; the compiled statement shapes of `SliceInterfaceInstantiation` are copied with
  `uniformInverseChart` → `Vmap` local edits and the packaged `SliceChartData.hWjoint` measurability.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (T0) THE CHART-THEOREM CENSUS (what brick 14 needs; verdict + `SliceChartData` field consumed).

  The v2 facade consumer chain is
      `CConvFacade.hCConv_discharged_from_data  ∘  SpatialC2.hCConv_reduction`.
  Grepping the chain for a SWAPPABLE standalone chart `uniformInverseChart g gi hC hK ·` :

  ── `SliceInterfaceInstantiation.hjoint_instantiated` — **copy-with-edits (this file, T1).**  Its
     internal provers `hWq_of_chartBorel` / `hWa_of_chartBorel` (via `gcpw_fieldpoint_measurable_of_
     chartBorel`) and `hSliceCont_of_data` mention `uniformInverseChart` in statements AND proofs.  The
     chart there enters ONLY through the witness inner kernel `globalCutoffParametrixWitnessN 1 Θ u a b
     Vmap` (which is ALREADY chart-parametric in its `Vmap` slot) and the support condition
     `radialCutoff a b (Vmap · ·) = 0`.  RE-DERIVED here for the generic gated witness `gatedWitnessW`
     from `SliceChartData.hWjoint` (the `Measurable (fun p ↦ Vmap p.2 (update x i w))` field).  ⚠ The
     WITNESS-SIDE legs only (`hSliceCont`/`hWq`/`hWa`); the FULL `hjoint_fully_geometric` capstone ALSO
     consumes `uniformInverseChart`'s OWN `hVmapMeas` (global a.e.-measurability) + `hCover` (on-gate
     `C²`) — those are the DERIVATIVE-measurability core inputs, intrinsic to the chart, NOT witness
     legs; they are the documented off-image residue handled at `Wg` by `B2MeasurabilityDissolution` /
     `ChartParamFacadeVariant` (bricks 11/14).  So brick 3 delivers the three witness legs at an opaque
     chart; the capstone reassembly is bricks 11/14.

  ── `WitnessDerivMeasurability` (`g2_bundle_assembled` + `hzmeas`/`hsmeas`/`hsbound`/`hBint`) —
     **already-chart-opaque (no parametric copy needed).**  VERIFIED: this file has ZERO
     `uniformInverseChart` occurrences.  Every slot is stated purely in terms of the FIXED derivative
     object `witnessFieldDeriv g gi hC hK S a b …` (which BAKES the chart internally); the v2 facade
     concludes about that SAME fixed object, so these slots are consumed verbatim.  The genuine
     chart-parametric "measurability of the witness maps at the opaque chart" (T2) IS the Borel
     `hWqW`/`hWaW`/`gcpwW` of T1 (the witness-map, not the derivative-map); the DERIVATIVE joint
     measurability `hDmeas` stays the honest carry, at the fixed OR generic witness alike.  SliceChartData
     field consumed: none (chart-free).

  ── `HenvUInstantiation` — **split: DEAD old-plumbing skip + one WIDE neighbourhood leg (T3).**
     `henvU_assembled` / `henv_assembled` / `hdomS_assembled` / `hzbound_assembled` ride on the
     ADJUDICATED-FALSE `hGateData`/`hGateData'` dichotomy (the constant-`Bs` log-gradient) — DEAD,
     REPLACED by the banked wide legs `CConvV2WitnessStar.hdomS_v2Wide` / `CConvV2EnvelopeFromStar.
     {hdomS_v2,henv_v2}`; SKIP.  The reusable chart-FREE `pd`-vanishing levers
     `pd_eq_zero_of_line_eventuallyEq_zero` / `pd_eq_zero_of_eventuallyEq_zero` are already banked
     (no copy).  What brick 14 STILL needs on the `henvU`-side and is NOT yet banked: the `∀ᵐ s → ∀ᶠ x`
     ORDER of the WIDE dominator (the banked `hdomS_v2Wide` is only the `∀ᶠ x → ∀ᵐ s` order).  Delivered
     here as `henv_v2Wide` (T3), typed against the wide dominator `C·((t−s)^{−1/2}·gaussDdim(4(t−s))z·
     |F s z|)`.  SliceChartData field consumed: none (envelope-side).

  MISSING-FIELD VERDICT on `SliceChartData`.  The T1 witness legs need ONLY `hWjoint`; the slice
  CONTINUITY leg needs an inner-kernel `w`-slice continuity + off-gate cutoff-support carry that
  `SliceChartData` does NOT package (it is the SAME honest `hSliceData` carry the fixed
  `hjoint_instantiated` already took — chart-geometry, satisfiable, never the conclusion).  No new
  `SliceChartData` field is required for brick 3; `SliceChartDataExt` was NOT needed.

  ## WHAT THIS FILE LANDS.
    • `gatedWitnessW` / `innerKernelFieldW`  — the generic Vmap witness + its ungated inner field slot;
      `gatedWitnessW_uniformInverseChart` — the `Vmap := uniformInverseChart` recovery (`rfl`).
    • (T1) `gcpwWField_eq_zero_of_cutoff_zero`, `gatedWitnessW_fieldSlot_eq_inner_of_support`,
      `gatedWitnessW_slice_continuous_of_support`, `gatedWitnessW_slice_zero_of_notMemK`,
      `hSliceContW_of_data` — the parametric SUPPORT-IDENTITY + slice-continuity interface.
    • (T1/T2) `gcpwWField_measurable`, `hWqW_of_chartBorel`, `hWaW_of_chartBorel` — the parametric Borel
      witness-map measurabilities (from `SliceChartData.hWjoint`).
    • (T1) `sliceInterfaceW_of_data` — the three witness legs (`hSliceCont ∧ hWq ∧ hWa`) at the opaque
      chart, packaged from `SliceChartData`.
    • (T3) `henv_v2Wide` — the WIDE `∀ᵐ s → ∀ᶠ x` domination order (sibling of `hdomS_v2Wide`).

  NOT `a₁ = R/6`.
-/
import QIQTH.SliceInterfaceInstantiation
import QIQTH.CConvV2Contracts
import QIQTH.CConvV2WitnessStar

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity
open QIQTH.InnerKernelJointMeas QIQTH.GateDiffWiringMeasSet
open QIQTH.SliceInterfaceInstantiation QIQTH.CConvV2Contracts
open scoped Interval Topology BigOperators

namespace QIQTH.CConvV2ChartInterface

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §0 — the GENERIC (opaque-chart) witness `gatedWitnessW` and its inner field slot.
    ############################################################################### -/

/-- **`gatedWitnessW`.**  The generic gated van-Vleck witness at an OPAQUE chart
    `Vmap : Point n → Point n → Point n` — the chart-parametric abstraction of `vanVleckGatedWitness`
    (whose chart is the fixed `uniformInverseChart g gi hC hK`).  It is `gatedKernel K S` of the
    order-1 global-cutoff parametrix witness `globalCutoffParametrixWitnessN 1 Θ u a b Vmap` (already
    chart-parametric in its `Vmap` slot), with `Θ = vanVleck g`, `u = transportCoeff (transportOp …)`.
    ⚠ NOT `a₁ = R/6`. -/
noncomputable def gatedWitnessW (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n))
    (Vmap : Point n → Point n → Point n) : ℝ → Point n → Point n → ℝ :=
  gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap)

/-- **`innerKernelFieldW`.**  The generic UNGATED inner-kernel field slot `x' ↦ (witness inner)(τ) x' z`
    at the opaque chart `Vmap` — the chart-parametric abstraction of `innerKernelField`.  ⚠ NOT
    `a₁ = R/6`. -/
noncomputable def innerKernelFieldW (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) (τ : ℝ) (z : Point n) : Point n → ℝ :=
  fun x' => globalCutoffParametrixWitnessN 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap τ x' z

/-- **`gatedWitnessW_uniformInverseChart` — the `Vmap := uniformInverseChart` recovery (`rfl`).**  At the
    raw inverse chart the generic witness IS the concrete `vanVleckGatedWitness` (definitional).  This is
    the bridge bricks 11/14 use to instantiate the parametric legs at the fixed witness and feed
    `hjoint_fully_geometric`.  ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessW_uniformInverseChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    gatedWitnessW g gi a b K S (uniformInverseChart g gi hC hK)
      = vanVleckGatedWitness g gi hC hK S a b := rfl

/-! ###############################################################################
    ### §1 (T1, brick 3) — the SUPPORT-CONDITION field-slot identity (opaque chart).
    ############################################################################### -/

/-- **`gcpwWField_eq_zero_of_cutoff_zero`.**  The chart-parametric copy of
    `SliceInterfaceInstantiation.innerKernelField_eq_zero_of_cutoff_zero`: the inner kernel starts with
    the factor `radialCutoff a b (Vmap z q)`, so once the cutoff vanishes at `q` the inner field slot
    vanishes there.  ⚠ NOT `a₁ = R/6`. -/
theorem gcpwWField_eq_zero_of_cutoff_zero (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (Vmap : Point n → Point n → Point n) (τ : ℝ) (z q : Point n)
    (hcut : radialCutoff a b (Vmap z q) = 0) :
    innerKernelFieldW g gi a b Vmap τ z q = 0 := by
  simp only [innerKernelFieldW, globalCutoffParametrixWitnessN, hcut, zero_mul]

/-- **★ `gatedWitnessW_fieldSlot_eq_inner_of_support` — THE FIELD-SLOT IDENTITY (opaque chart).**  For
    `z ∈ K` with the gate-design SUPPORT CONDITION (`hsupp`: off the gate the cutoff of `Vmap z ·`
    vanishes), the generic gated witness equals the ungated inner field slot in the WHOLE field slot.
    Chart-parametric copy of `SliceInterfaceInstantiation.gatedWitness_fieldSlot_eq_inner_of_support`.
    ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessW_fieldSlot_eq_inner_of_support (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n))
    (Vmap : Point n → Point n → Point n) (τ : ℝ) (z : Point n) (hzK : z ∈ K)
    (hsupp : ∀ q, q ∉ S z → radialCutoff a b (Vmap z q) = 0) :
    (fun q => gatedWitnessW g gi a b K S Vmap τ q z) = innerKernelFieldW g gi a b Vmap τ z := by
  funext q
  simp only [gatedWitnessW]
  by_cases hq : q ∈ S z
  · rw [gatedKernel_apply_of_mem K S _ τ hzK hq]; rfl
  · rw [gatedKernel_apply_of_notMem K S _ τ q z (Or.inr hq)]
    exact (gcpwWField_eq_zero_of_cutoff_zero g gi a b Vmap τ z q (hsupp q hq)).symm

/-- **★ `gatedWitnessW_slice_continuous_of_support`.**  On the gate (`z ∈ K`, support), the `w`-slice of
    the generic gated witness is CONTINUOUS, transferred from the inner-kernel `w`-slice continuity by
    the field-slot identity.  Chart-parametric copy of
    `SliceInterfaceInstantiation.gatedWitness_slice_continuous_of_support`.  ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessW_slice_continuous_of_support (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (i : Fin n) (τ : ℝ) (x z : Point n) (hzK : z ∈ K)
    (hsupp : ∀ q, q ∉ S z → radialCutoff a b (Vmap z q) = 0)
    (hinnerCont : Continuous
      (fun w : ℝ => innerKernelFieldW g gi a b Vmap τ z (Function.update x i w))) :
    Continuous (fun w : ℝ => gatedWitnessW g gi a b K S Vmap τ (Function.update x i w) z) := by
  have hid := gatedWitnessW_fieldSlot_eq_inner_of_support g gi a b S Vmap τ z hzK hsupp
  have heq : (fun w : ℝ => gatedWitnessW g gi a b K S Vmap τ (Function.update x i w) z)
      = (fun w : ℝ => innerKernelFieldW g gi a b Vmap τ z (Function.update x i w)) := by
    funext w
    have := congrFun hid (Function.update x i w)
    simpa using this
  rw [heq]; exact hinnerCont

/-- **`gatedWitnessW_slice_zero_of_notMemK`.**  Off `K` (`z ∉ K`) the generic gated witness `w`-slice is
    identically `0`, hence continuous.  Chart-parametric copy of
    `SliceInterfaceInstantiation.gatedWitness_slice_zero_of_notMemK`.  ⚠ NOT `a₁ = R/6`. -/
theorem gatedWitnessW_slice_zero_of_notMemK (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (i : Fin n) (τ : ℝ) (x z : Point n) (hzK : z ∉ K) :
    Continuous (fun w : ℝ => gatedWitnessW g gi a b K S Vmap τ (Function.update x i w) z) := by
  have heq : (fun w : ℝ => gatedWitnessW g gi a b K S Vmap τ (Function.update x i w) z)
      = (fun _ : ℝ => (0 : ℝ)) := by
    funext w
    simp only [gatedWitnessW]
    exact gatedKernel_apply_of_notMem K S _ τ _ z (Or.inl hzK)
  rw [heq]; exact continuous_const

/-- **★★ `hSliceContW_of_data` — THE `hSliceCont` SLOT at the opaque chart.**  Chart-parametric copy of
    `SliceInterfaceInstantiation.hSliceCont_of_data`, from the per-`p` gate/support/inner-continuity
    dichotomy carry `hSliceData` (per `p`: either `z ∉ K`, or `z ∈ K` with the cutoff-support condition
    on `Vmap` and the generic inner-kernel `w`-slice continuity).  Instantiated at
    `Vmap := uniformInverseChart` this is the EXACT `hSliceCont` slot of `hjoint_fully_geometric` (by
    `gatedWitnessW_uniformInverseChart`).  ⚠ NOT `a₁ = R/6`. -/
theorem hSliceContW_of_data (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (t : ℝ) (u₀ : Set (Point n))
    (hSliceData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (Vmap p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelFieldW g gi a b Vmap (t - p.1) p.2 (Function.update x i w)))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ p : ℝ × Point n, Continuous
        (fun w => gatedWitnessW g gi a b K S Vmap (t - p.1) (Function.update x i w) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSliceData x₀ hx₀ i] with x hx
  intro p
  rcases hx p with hnK | ⟨hzK, hsupp, hinnerCont⟩
  · exact gatedWitnessW_slice_zero_of_notMemK g gi a b S Vmap i (t - p.1) x p.2 hnK
  · exact gatedWitnessW_slice_continuous_of_support g gi a b S Vmap i (t - p.1) x p.2 hzK
      hsupp hinnerCont

/-! ###############################################################################
    ### §2 (T1/T2, brick 3) — the BOREL witness-map measurabilities (opaque chart).
    ############################################################################### -/

/-- **★ `gcpwWField_measurable`.**  Chart-parametric copy of
    `SliceInterfaceInstantiation.gcpw_fieldpoint_measurable_of_chartBorel`: the ungated order-1 witness
    inner kernel is Borel-measurable in `(s,z)` at a fixed field point `q₀`, from the globally Borel
    outer kernel (`witnessInner_measurable_uncurry`) composed with the affine time map and the BOREL
    chart-slice carry `hChart` (the `Vmap`-analogue of the a.e. `hVmapMeas`).  ⚠ NOT `a₁ = R/6`. -/
theorem gcpwWField_measurable {α : Type*} [MeasurableSpace α]
    (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ) (q₀ : Point n) (τf : α → ℝ)
    (Vmap : Point n → Point n → Point n)
    (hτf : Measurable τf)
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hChart : Measurable (fun p : α × Point n => Vmap p.2 q₀)) :
    Measurable (fun p : α × Point n =>
      globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap (τf p.1) q₀ p.2) := by
  have houter := witnessInner_measurable_uncurry (n := n)
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b hΘc hΘne huc
  have hpair : Measurable
      (fun p : α × Point n => (τf p.1, Vmap p.2 q₀)) :=
    (hτf.comp measurable_fst).prodMk hChart
  simpa only [globalCutoffParametrixWitnessN, Function.comp_def] using houter.comp hpair

/-- **★★ `hWqW_of_chartBorel` — THE `hWq` SLOT at the opaque chart.**  Chart-parametric copy of
    `SliceInterfaceInstantiation.hWq_of_chartBorel`: the joint `(s,z)`-Borel measurability of the generic
    gated witness at the RATIONAL field samples `update x i (x i + q)`, reduced to the gate-set data
    (`hKmeasSet`, `hSmeasSet`), the coefficient data (`hΘc`, `hΘne`, `huc`) and the packaged
    `SliceChartData.hWjoint` chart-slice measurability.  Via `gcpwWField_measurable` +
    `gatedFieldpoint_measurable_of_inner` (the generic Borel gate glue).  ⚠ NOT `a₁ = R/6`. -/
theorem hWqW_of_chartBorel (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (t : ℝ) (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWjoint : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n => Vmap p.2 (Function.update x i w))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
      Measurable (fun p : ℝ × Point n =>
        gatedWitnessW g gi a b K S Vmap (t - p.1)
          (Function.update x i (x i + (q : ℝ))) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSmeasSet x₀ hx₀ i, hWjoint x₀ hx₀ i] with x hSm hW
  intro q
  have hinner := gcpwWField_measurable (α := ℝ) g gi a b
    (Function.update x i (x i + (q : ℝ))) (fun s => t - s) Vmap
    (measurable_const.sub measurable_id) hΘc hΘne huc (hW (x i + (q : ℝ)))
  have hgate := gatedFieldpoint_measurable_of_inner (α := ℝ) K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap)
    (Function.update x i (x i + (q : ℝ))) (fun s => t - s)
    hKmeasSet (hSm (x i + (q : ℝ))) hinner
  simpa only [gatedWitnessW] using hgate

/-- **★★ `hWaW_of_chartBorel` — THE `hWa` SLOT at the opaque chart.**  Chart-parametric copy of
    `SliceInterfaceInstantiation.hWa_of_chartBorel` (the base-point specialisation of
    `hWqW_of_chartBorel`).  ⚠ NOT `a₁ = R/6`. -/
theorem hWaW_of_chartBorel (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (t : ℝ) (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWjoint : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        Measurable (fun p : ℝ × Point n => Vmap p.2 (Function.update x i w))) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      Measurable (fun p : ℝ × Point n =>
        gatedWitnessW g gi a b K S Vmap (t - p.1) (Function.update x i (x i)) p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hSmeasSet x₀ hx₀ i, hWjoint x₀ hx₀ i] with x hSm hW
  have hinner := gcpwWField_measurable (α := ℝ) g gi a b
    (Function.update x i (x i)) (fun s => t - s) Vmap
    (measurable_const.sub measurable_id) hΘc hΘne huc (hW (x i))
  have hgate := gatedFieldpoint_measurable_of_inner (α := ℝ) K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap)
    (Function.update x i (x i)) (fun s => t - s)
    hKmeasSet (hSm (x i)) hinner
  simpa only [gatedWitnessW] using hgate

/-! ###############################################################################
    ### §3 (T1, brick 3) — the assembled three-leg WITNESS INTERFACE at the opaque chart.
    ############################################################################### -/

/-- **★★★ `sliceInterfaceW_of_data` — the three witness legs at the opaque chart.**  Packages the
    `hSliceCont` / `hWq` / `hWa` legs (the exact `hSliceCont`/`hWq`/`hWa` slots of `hjoint_fully_geometric`,
    at the generic witness `gatedWitnessW`) from: the gate-set data (`hKmeasSet`, `hSmeasSet`), the
    coefficient data (`hΘc`, `hΘne`, `huc`), the packaged `SliceChartData` (its `hWjoint` field feeds
    `hWq`/`hWa`), and the honest per-`p` slice-continuity dichotomy `hSliceData` (the SAME chart-geometry
    carry the fixed `hjoint_instantiated` took — no new `SliceChartData` field needed).  Instantiating
    `Vmap := uniformInverseChart` (via `gatedWitnessW_uniformInverseChart`) reproduces the fixed slots;
    the remaining `hVmapMeas`/`hCover` inputs of the FULL `hjoint_fully_geometric` capstone are the
    chart-intrinsic residue handled at `Wg` by bricks 11/14.  ⚠ NOT `a₁ = R/6`. -/
theorem sliceInterfaceW_of_data (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    {K : Set (Point n)} (S : Point n → Set (Point n)) (Vmap : Point n → Point n → Point n)
    (t : ℝ) (u₀ : Set (Point n)) {Amp : ℝ → Point n → Point n → ℝ}
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (chart : SliceChartData K S u₀ Vmap Amp)
    (hSliceData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ p : ℝ × Point n,
        (p.2 ∉ K)
        ∨ (p.2 ∈ K
            ∧ (∀ q, q ∉ S p.2 → radialCutoff a b (Vmap p.2 q) = 0)
            ∧ Continuous
                (fun w : ℝ =>
                  innerKernelFieldW g gi a b Vmap (t - p.1) p.2 (Function.update x i w)))) :
    (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => gatedWitnessW g gi a b K S Vmap (t - p.1) (Function.update x i w) p.2))
    ∧ (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          gatedWitnessW g gi a b K S Vmap (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    ∧ (∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          gatedWitnessW g gi a b K S Vmap (t - p.1) (Function.update x i (x i)) p.2)) :=
  ⟨hSliceContW_of_data g gi a b S Vmap t u₀ hSliceData,
   hWqW_of_chartBorel g gi a b S Vmap t u₀ hKmeasSet hSmeasSet hΘc hΘne huc chart.hWjoint,
   hWaW_of_chartBorel g gi a b S Vmap t u₀ hKmeasSet hSmeasSet hΘc hΘne huc chart.hWjoint⟩

/-! ###############################################################################
    ### §4 (T3, brick 4) — the WIDE `henvU`-side domination order `∀ᵐ s → ∀ᶠ x → ∀ᵐ z`.
    ############################################################################### -/

/-- **★ (T3) `henv_v2Wide`.**  The WIDE-dominator sibling of the banked `CConvV2WitnessStar.hdomS_v2Wide`
    — the `∀ᵐ s → ∀ᶠ x → ∀ᵐ z` ORDER (genuinely distinct from `hdomS_v2Wide`'s `∀ᶠ x → ∀ᵐ s`), typed
    against the SAME wide dominator `C·((t−s)^{−1/2}·gaussDdim(4(t−s))z·|F s z|)`.  This is the
    `henvU`-side plumbing brick 14's g2-v2 assembly consumes (the `hzbound`-order envelope), sourced
    from the `(⋆)`-WIDE per-point witness bound `hStarW` over the interior window `Ioo 0 t` and the
    neighbourhood carry `hu` (satisfiable for `u` open — `hStarW` is `u`-uniform).  The single endpoint
    `s = t` is `volume`-null (`{t}`), so a.e. `s ∈ uIoc ⟹ s ∈ Ioo`.  ⚠ NOT `a₁ = R/6`. -/
theorem henv_v2Wide (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (ht : 0 ≤ t) (u : Set (Point n)) (F : ℝ → Point n → ℝ) (C : ℝ) (_hC0 : 0 ≤ C)
    (hu : ∀ x₀ ∈ u, u ∈ 𝓝 x₀)
    (hStarW : ∀ x ∈ u, ∀ i : Fin n, ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ z : Point n,
      |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
        ≤ C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n,
      ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
            ≤ C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by
  intro x₀ hx₀ i
  have hvol_t : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact measure_singleton t
  filter_upwards [hvol_t] with s hsne hmem
  rw [Set.uIoc_of_le ht] at hmem
  have hsIoo : s ∈ Set.Ioo (0 : ℝ) t := ⟨hmem.1, lt_of_le_of_ne hmem.2 hsne⟩
  filter_upwards [hu x₀ hx₀] with x hxu
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C * (t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z) * |F s z| :=
        mul_le_mul_of_nonneg_right (hStarW x hxu i s hsIoo z) (abs_nonneg _)
    _ = C * ((t - s) ^ (-(1 : ℝ) / 2) * gaussDdim (4 * (t - s)) z * |F s z|) := by ring

end QIQTH.CConvV2ChartInterface

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvV2ChartInterface
#print axioms gatedWitnessW_uniformInverseChart
#print axioms gcpwWField_eq_zero_of_cutoff_zero
#print axioms gatedWitnessW_fieldSlot_eq_inner_of_support
#print axioms gatedWitnessW_slice_continuous_of_support
#print axioms gatedWitnessW_slice_zero_of_notMemK
#print axioms hSliceContW_of_data
#print axioms gcpwWField_measurable
#print axioms hWqW_of_chartBorel
#print axioms hWaW_of_chartBorel
#print axioms sliceInterfaceW_of_data
#print axioms henv_v2Wide
end AxiomChecks
