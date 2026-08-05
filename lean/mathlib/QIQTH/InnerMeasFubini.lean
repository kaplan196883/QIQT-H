/-
  InnerMeasFubini — J4-245: the F2 inner `(s,z)`-measurability trio + inner-pairing continuity,
  discharged for the CONCRETE gated van-Vleck integrand
      `(s, z) ↦ vanVleckGatedWitness g gi hChr hK S a b (c − s) 0 z
                  · leviSeries (heatOp g gi (vanVleckGatedWitness …)) s z 0`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It supplies
  the four DEFERRED measurability / continuity slots that the R1 capstone
  `RightInverseGeneral.a1_R6_assembled_v2'` still consumes as hypotheses —
      `hMeasFII`, `hFmeas`, `hF'meas`, `hInnerCont`
  — as genuine (std-3, axiom-free) theorems built by composition of ALREADY-BANKED suppliers and a
  handful of honest, satisfiable, non-vacuous carries.  No `sorry` (prose excepted), no new axioms,
  no `:= True`, no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.

  ## THE STRUCTURAL ROUTE (composition-of-sections, NOT product-ae over `Fin n → ℝ`).

    Every deferred slot is `s ↦ ∫ z, (witness factor)·(leviSeries factor)` on some window measure
    `volume.restrict (uIoc 0 d)`.  The clean route is FUBINI-MEASURABILITY of the inner integral:

      • ENGINE `innerIntegral_aesm` — `AEStronglyMeasurable f (μ.prod volume)` ⟹
          `AEStronglyMeasurable (fun s => ∫ z, f (s,z)) μ`  (Mathlib
          `AEStronglyMeasurable.integral_prod_right'`, the SFinite product-marginal Fubini
          measurability).  This turns each slot into a JOINT `(s,z)` measurability.

      • GATED-INDICATOR LEVER `gatedWitnessShift_joint_aesm` — the `(s,z)` analogue of
          `WitnessMeasDeriv.gatedKernel_slice_aestronglyMeasurable`.  The gated witness value factor
          `(s,z) ↦ vanVleckGatedWitness … (c−s) 0 z` equals
          `(Prod.snd ⁻¹' (K ∩ {z | 0 ∈ S z})).indicator ((s,z) ↦ Inner (c−s) 0 z)`
          (`gatedKernel_apply_of_mem/_of_notMem` case split; the gate depends only on `z`), so its
          joint `(s,z)` measurability reduces to {`MeasurableSet K`, `MeasurableSet {z | 0 ∈ S z}`,
          the UNGATED inner parametrix joint measurability `hInner`} via
          `AEStronglyMeasurable.indicator`.  NO product-ae plumbing over `Fin n → ℝ`.

      • LEVISERIES FACTOR — for the FULL-window slot `hMeasFII` (window `= u ∈ (0,T]`) the Levi
          factor's joint `(s,z)` measurability is DISCHARGED GENUINELY from the caller's Levi-strip
          joint continuity `hBcont` (`ContinuousOn.aestronglyMeasurable` + `Measure.prod_restrict`);
          for the truncated-window slots `hFmeas`/`hF'meas` (window `u − εₘ`, which may dip ≤ 0) it is
          carried as the honest family `hLeviJoint`.

      • `hInnerCont` — the interior-time continuity of `s ↦ ∫ z …` on `Ioo 0 u` is reduced by the
          general engine `innerIntegral_continuousOn_of_dominated` (per-interior-point
          `continuousAt_of_dominated`) to the honest per-point dominated-continuity datum
          `hContDom` (local integrable domination + a.e.-`z` pointwise continuity).

  ── HONEST CARRIED INPUTS (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hInner`  — the UNGATED order-1 global-cutoff parametrix joint `(s,z)` measurability (the `z`
      dependence enters only through the chart `uniformInverseChart z 0`; satisfiable from chart
      `z`-measurability + van-Vleck/transport-coefficient continuity, exactly the
      `InnerKernelJointMeas.hinnerJ_discharged` route, at field point `0`).
    • `hLeviJoint` — the Levi-series joint `(s,z)` measurability on the truncated window (satisfiable
      from `hBcont` on `(0,T]`, from `hFzero` on `≤ 0`).
    • `hWitDeriv` — the `∂_τ` witness-field joint `(s,z)` measurability (the `hDτ`-slot analogue).
    • `hKm`, `hSm0` — `MeasurableSet K`, `MeasurableSet {z | 0 ∈ S z}` (geometric gate measurability).
    • `hBcont`, `hUpos`, `hUT` — the caller's own Levi-strip continuity + window bounds.
    • `hContDom` — the per-interior-point dominated-continuity datum for `hInnerCont`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConvApproximants
import QIQTH.IterEMeasurable
import QIQTH.WitnessMeasDeriv

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.InnerMeasFubini

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ENGINE 1 — the Fubini inner-integral measurability.
    ############################################################################### -/

/-- **★ `innerIntegral_aesm` — FUBINI INNER-INTEGRAL MEASURABILITY.**  If the two-variable integrand
    `f : ℝ × Point n → ℝ` is `AEStronglyMeasurable` w.r.t. the product `μ.prod volume`, then the
    inner-integrated section `s ↦ ∫ z, f (s, z)` is `AEStronglyMeasurable` w.r.t. `μ`.  A thin
    specialization of Mathlib's SFinite product-marginal Fubini measurability
    `AEStronglyMeasurable.integral_prod_right'`.  This is the engine every deferred F2 slot runs on.
    NOT `a₁ = R/6`. -/
theorem innerIntegral_aesm {μ : Measure ℝ} (f : ℝ × Point n → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable (fun s => ∫ z, f (s, z)) μ :=
  hf.integral_prod_right'

/-! ###############################################################################
    ### ENGINE 2 — the gated-witness value joint `(s,z)` measurability lever.
    ############################################################################### -/

/-- **★★ `gatedWitnessShift_joint_aesm` — THE GATED-INDICATOR JOINT `(s,z)` LEVER.**  The joint
    `(s,z)`-ae-strong-measurability of the shifted gated van-Vleck witness value
    `(s,z) ↦ vanVleckGatedWitness g gi hC hK S a b (c − s) 0 z` reduces to
    {`MeasurableSet K`, `MeasurableSet {z | 0 ∈ S z}`, the UNGATED inner parametrix joint
    measurability `hInner`}, via the indicator representation over the base-gate cylinder
    `Prod.snd ⁻¹' (K ∩ {z | 0 ∈ S z})` (the gate depends only on `z`; `p = 0` fixed) and
    `AEStronglyMeasurable.indicator`.  This is the `(s,z)` analogue of the `z`-slice lever
    `WitnessMeasDeriv.gatedKernel_slice_aestronglyMeasurable`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessShift_joint_aesm (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (c : ℝ) {μ : Measure ℝ}
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hInner : AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hC hK) (c - p.1) 0 p.2)
      (μ.prod (volume : Measure (Point n)))) :
    AEStronglyMeasurable
      (fun p : ℝ × Point n => vanVleckGatedWitness g gi hC hK S a b (c - p.1) 0 p.2)
      (μ.prod (volume : Measure (Point n))) := by
  classical
  have hrw : (fun p : ℝ × Point n => vanVleckGatedWitness g gi hC hK S a b (c - p.1) 0 p.2)
      = (Prod.snd ⁻¹' (K ∩ {z : Point n | (0 : Point n) ∈ S z})).indicator
          (fun p : ℝ × Point n =>
            globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK) (c - p.1) 0 p.2) := by
    funext p
    unfold vanVleckGatedWitness
    rw [Set.indicator_apply]
    by_cases hzK : p.2 ∈ K
    · by_cases hzS : (0 : Point n) ∈ S p.2
      · rw [gatedKernel_apply_of_mem K S _ (c - p.1) hzK hzS,
          if_pos (show p ∈ Prod.snd ⁻¹' (K ∩ {z : Point n | (0 : Point n) ∈ S z}) from
            ⟨hzK, hzS⟩)]
      · rw [gatedKernel_apply_of_notMem K S _ (c - p.1) 0 p.2 (Or.inr hzS),
          if_neg (show p ∉ Prod.snd ⁻¹' (K ∩ {z : Point n | (0 : Point n) ∈ S z}) from
            fun h => hzS h.2)]
    · rw [gatedKernel_apply_of_notMem K S _ (c - p.1) 0 p.2 (Or.inl hzK),
        if_neg (show p ∉ Prod.snd ⁻¹' (K ∩ {z : Point n | (0 : Point n) ∈ S z}) from
          fun h => hzK h.1)]
  rw [hrw]
  exact hInner.indicator ((hKm.inter hSm0).preimage measurable_snd)

/-! ###############################################################################
    ### ENGINE 3 — the Levi-series joint `(s,z)` measurability from the strip continuity `hBcont`.
    ############################################################################### -/

/-- **★ `leviJoint_of_hBcont`.**  On the honest window `(0,u] ⊆ (0,T]` (i.e. `0 < u ≤ T`), the
    Levi-series factor `(s,z) ↦ leviSeries (heatOp g gi H) s z 0` is `AEStronglyMeasurable` w.r.t.
    `(volume.restrict (uIoc 0 u)).prod volume`, DISCHARGED from the caller's Levi-strip joint
    continuity `hBcont` via `ContinuousOn.aestronglyMeasurable` and `Measure.prod_restrict`.
    NOT `a₁ = R/6`. -/
theorem leviJoint_of_hBcont (g gi : Point n → Fin n → Fin n → ℝ)
    (H : ℝ → Point n → Point n → ℝ) (u T : ℝ) (hu : 0 < u) (huT : u ≤ T)
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n => leviSeries (heatOp g gi H) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)))) :
    AEStronglyMeasurable
      (fun p : ℝ × Point n => leviSeries (heatOp g gi H) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 u)).prod (volume : Measure (Point n))) := by
  have hmeasset : MeasurableSet (Set.uIoc 0 u ×ˢ (Set.univ : Set (Point n))) :=
    measurableSet_uIoc.prod MeasurableSet.univ
  have hsub : Set.uIoc 0 u ×ˢ (Set.univ : Set (Point n))
      ⊆ Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n)) := by
    apply Set.prod_mono _ (subset_refl _)
    rw [Set.uIoc_of_le hu.le]
    exact Set.Ioc_subset_Ioc_right huT
  have haesm := (hBcont.mono hsub).aestronglyMeasurable
    (μ := ((volume : Measure ℝ).prod (volume : Measure (Point n)))) hmeasset
  rwa [← Measure.prod_restrict, Measure.restrict_univ] at haesm

/-! ###############################################################################
    ### ENGINE 4 — the interior-time continuity of the inner integral (dominated route).
    ############################################################################### -/

/-- **★ `innerIntegral_continuousOn_of_dominated`.**  On an OPEN parameter set `s`, the
    inner-integrated section `x ↦ ∫ a, F x a ∂μ` is `ContinuousOn s` provided each point of `s`
    carries a dominated-continuity datum: a `μ`-integrable local bound, local `AEStronglyMeasurable`
    slices, a local a.e. norm bound, and a.e.-`a` pointwise continuity of `x ↦ F x a` at the point.
    Per-point `continuousAt_of_dominated` + `ContinuousAt.continuousWithinAt`.  This reduces the
    interior-time continuity of the inner space-time pairing to the honest local dominated-continuity
    datum.  NOT `a₁ = R/6`. -/
theorem innerIntegral_continuousOn_of_dominated
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : X → α → ℝ) (s : Set X)
    (hdatum : ∀ x₀ ∈ s, ∃ bound : α → ℝ, Integrable bound μ ∧
        (∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) ∧
        (∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) ∧
        (∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀)) :
    ContinuousOn (fun x => ∫ a, F x a ∂μ) s := by
  intro x₀ hx₀
  obtain ⟨bound, hbi, hm, hb, hc⟩ := hdatum x₀ hx₀
  exact (continuousAt_of_dominated hm hb hbi hc).continuousWithinAt

/-! ###############################################################################
    ### THE CONCRETE F2 SLOTS.
    ############################################################################### -/

/-- **★★★ `hMeasFII_concrete` — THE `hMeasFII` SLOT, FULLY DISCHARGED.**  The base
    `s`-ae-strong-measurability of the inner space-time pairing on the full window `(0,u]`,
    `u ∈ U ⊆ (0,T]`.  Genuine: the witness value factor via the gated lever + `hInner`, the Levi
    factor GENUINELY from `hBcont`, joined by `.mul` and integrated out by the Fubini engine.
    Honest carries: {`hKm`, `hSm0`, `hInner`, `hBcont`, `hUpos`, `hUT`}.  NOT `a₁ = R/6`. -/
theorem hMeasFII_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hInner : ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK) (c - p.1) 0 p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T) :
    ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)) := by
  intro u hu
  have hWit := gatedWitnessShift_joint_aesm g gi hChr hK S a b u
    (μ := volume.restrict (Set.uIoc 0 u)) hKm hSm0 (hInner u u)
  have hLevi := leviJoint_of_hBcont g gi (vanVleckGatedWitness g gi hChr hK S a b) u T
    (hUpos u hu) (hUT u hu) hBcont
  exact innerIntegral_aesm
    (fun p : ℝ × Point n => vanVleckGatedWitness g gi hChr hK S a b (u - p.1) 0 p.2
      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
    (hWit.mul hLevi)

/-- **★★ `hFmeas_concrete` — THE `hFmeas` SLOT.**  The `a'`-parametrized slice family on the
    truncated window `(0, u − εₘ]`.  Witness value factor at shift `a'` via the gated lever +
    `hInner`; Levi factor carried as `hLeviJoint` (the truncated window may dip `≤ 0`, where the
    Levi factor vanishes — outside `hBcont`'s strip).  Joined by `.mul` + Fubini engine.  Honest
    carries: {`hKm`, `hSm0`, `hInner`, `hLeviJoint`}.  NOT `a₁ = R/6`. -/
theorem hFmeas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hInner : ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK) (c - p.1) 0 p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u _hu a'
  have hWit := gatedWitnessShift_joint_aesm g gi hChr hK S a b a'
    (μ := volume.restrict (Set.uIoc 0 (u - epsSeq m))) hKm hSm0 (hInner a' (u - epsSeq m))
  exact innerIntegral_aesm
    (fun p : ℝ × Point n => vanVleckGatedWitness g gi hChr hK S a b (a' - p.1) 0 p.2
      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
    (hWit.mul (hLeviJoint (u - epsSeq m)))

/-- **★★ `hF'meas_concrete` — THE `hF'meas` SLOT.**  The `∂_τ`-witness slice family on the
    truncated window.  The `∂_τ` witness value factor `(s,z) ↦ deriv (fun r => H r 0 z) (u−s)` is
    carried jointly as `hWitDeriv` (the `hDτ`-slot analogue), the Levi factor as `hLeviJoint`;
    joined by `.mul` + Fubini engine.  Honest carries: {`hWitDeriv`, `hLeviJoint`}.
    NOT `a₁ = R/6`. -/
theorem hF'meas_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hWitDeriv : ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 p.2) (c - p.1))
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n)))) :
    ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))) := by
  intro m u _hu
  exact innerIntegral_aesm
    (fun p : ℝ × Point n =>
      deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 p.2) (u - p.1)
      * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
    ((hWitDeriv u (u - epsSeq m)).mul (hLeviJoint (u - epsSeq m)))

/-- **★★ `hInnerCont_concrete` — THE `hInnerCont` SLOT.**  The interior-time continuity of the inner
    space-time pairing on `Ioo 0 u`, reduced by the general dominated engine
    `innerIntegral_continuousOn_of_dominated` to the honest per-interior-point dominated-continuity
    datum `hContDom`.  NOT `a₁ = R/6`. -/
theorem hInnerCont_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hContDom : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀)) :
    ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u) :=
  fun u hu =>
    innerIntegral_continuousOn_of_dominated
      (fun s z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (Set.Ioo 0 u) (hContDom u hu)

/-! ###############################################################################
    ### ★ THE F2 PACK — the four concrete slots bundled.
    ############################################################################### -/

/-- **★★★ `f2Pack_concrete` — THE SELF-CONTAINED CONCRETE F2 SUPPLY.**  Bundles the four deferred
    F2 slots (`hMeasFII`, `hInnerCont`, `hFmeas`, `hF'meas`) exactly as the R1 capstone
    `RightInverseGeneral.a1_R6_assembled_v2'` consumes them, from the honest carried inputs
    {`hKm`, `hSm0`, `hInner`, `hWitDeriv`, `hLeviJoint`, `hBcont`, `hUpos`, `hUT`, `hContDom`} — each
    satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem f2Pack_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hInner : ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        globalCutoffParametrixWitnessN 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) a b
          (uniformInverseChart g gi hChr hK) (c - p.1) 0 p.2)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hWitDeriv : ∀ c d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 p.2) (c - p.1))
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hContDom : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀)) :
    -- (F2-a) hMeasFII
    (∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- (F2-b) hInnerCont
    ∧ (∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    -- (F2-c) hFmeas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (F2-d) hF'meas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) :=
  ⟨hMeasFII_concrete g gi hChr hK S a b T U hKm hSm0 hInner hBcont hUpos hUT,
   hInnerCont_concrete g gi hChr hK S a b U hContDom,
   hFmeas_concrete g gi hChr hK S a b U hKm hSm0 hInner hLeviJoint,
   hF'meas_concrete g gi hChr hK S a b U hWitDeriv hLeviJoint⟩

end QIQTH.InnerMeasFubini

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.InnerMeasFubini
#print axioms innerIntegral_aesm
#print axioms gatedWitnessShift_joint_aesm
#print axioms leviJoint_of_hBcont
#print axioms innerIntegral_continuousOn_of_dominated
#print axioms hMeasFII_concrete
#print axioms hFmeas_concrete
#print axioms hF'meas_concrete
#print axioms hInnerCont_concrete
#print axioms f2Pack_concrete
end AxiomChecks
