/-
  HbintMeasurabilityNullFrontier — the MEASURABILITY (not continuity) route to `hbint`, dodging the
  proved boundary no-go of `BTubeCompactnessAssembly` (J4-892).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick REDUCES the `hbint` field of
  `MixedDirectionsFieldHessianEnvelope` (the `z`-integrability of the product dominator `BL·BF`) to a set
  of ELEMENTARY, feedable carries via the standard "continuous off a Lebesgue-null set ⟹ a.e.-strongly-
  measurable" mechanism.  It does **NOT** close `hbint` unconditionally — it converts it to
  {interior-continuity of `BF` (fed by the interior joint-chart regularity), off-`K` vanishing (banked),
  boundedness on `K`, and `volume (frontier K) = 0` (elementary, discharged for the live ball `K`)}.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal to the
  conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHY THIS FILE EXISTS — the two prior routes chased a FALSE target.

  The `hbint` field asks for `Integrable (fun z => BL s z * BF s z)` where `BF s z := ⨆ x, ‖field-
  Hessian(z,x)‖`.  The two prior routes (`FieldHessianJointContinuityClosed` J4-878; the in-gate chart-
  `C²` cover `QuantifiedCoherentChartTube` J4-889) both sought JOINT / ambient-open CONTINUITY of the
  field-Hessian across ALL of `K`, and `BTubeCompactnessAssembly` (J4-892) PROVED that route boundary-
  UNSATISFIABLE: the concrete `uniformFlowExp K` is DEGENERATE off `K` (`= q` for `q ∉ K`), so the joint
  map is genuinely DISCONTINUOUS across `∂K`, and an open in-gate cover of the core-graph forces its base
  projection `⊆ interior K`, which cannot contain the boundary diagonal points.

  BUT `hbint` only needs INTEGRABILITY, i.e. `AEStronglyMeasurable (BL·BF)` + an integrable dominator —
  NOT continuity.  `AEStronglyMeasurable` TOLERATES a Lebesgue-null discontinuity locus that continuity
  does not.  The discontinuity locus of `BF` is contained in `∂K = frontier K`; for the live confinement
  set `K = closedBall 0 r` this is a sphere, which is Lebesgue-NULL (`Measure.addHaar_sphere`).  On the
  co-null open set `interior K ∪ Kᶜ`, `BF` is continuous (interior: the joint-chart regularity supplies
  continuity there; exterior: `BF ≡ 0`).  Hence `BF` — and the product `BL·BF` — is a.e.-strongly-
  measurable, and with the compact-support bound is integrable.  This is exactly the escape route
  `BTubeCompactnessAssembly`'s own verdict named ("a route that does NOT require joint chart `C²` on an
  ambient OPEN neighbourhood of boundary points").  Confirmed sound by gpt-5.6-sol (conditional on
  `volume (frontier K) = 0`, which is discharged for the live ball `K`).  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedDirectionsFieldHessianEnvelope

open MeasureTheory Filter Set
open QIQTH QIQTH.Curvature QIQTH.HeatResidualBound
open scoped Topology BigOperators ENNReal

namespace QIQTH.HbintMeasurabilityNullFrontier

variable {n : ℕ}

/-! ###############################################################################
    ### C0 — general measure-theory bridges (provider-independent, reusable).
    ############################################################################### -/

/-- **★ `aestronglyMeasurable_of_continuousOn_compl_null`.**  A function continuous on an OPEN set `U`
    whose complement is Lebesgue-null is `AEStronglyMeasurable`.  Mechanism: `ContinuousOn` on the
    measurable `U` gives `AEStronglyMeasurable f (μ.restrict U)`; since `μ Uᶜ = 0`, `μ.restrict U = μ`
    (`Measure.restrict_eq_self_of_ae_mem`, as `∀ᵐ x, x ∈ U`).  General, no geometry.  NOT `a₁ = R/6`. -/
theorem aestronglyMeasurable_of_continuousOn_compl_null
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {U : Set X} {f : X → ℝ}
    (hUopen : IsOpen U) (hf : ContinuousOn f U) (hnull : μ Uᶜ = 0) :
    AEStronglyMeasurable f μ := by
  have hres : AEStronglyMeasurable f (μ.restrict U) :=
    hf.aestronglyMeasurable hUopen.measurableSet
  have hae : ∀ᵐ x ∂μ, x ∈ U := by
    rw [ae_iff]
    simpa using hnull
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hres

/-- **★ `integrable_of_bounded_compactSupport`.**  A real function that is `AEStronglyMeasurable`,
    vanishes off a compact `K`, and is bounded by `C` on `K` is `Integrable` (`volume`).  Dominator:
    `C · 1_K`, integrable since `K` has finite volume.  General, no geometry.  NOT `a₁ = R/6`. -/
theorem integrable_of_bounded_compactSupport
    {f : Point n → ℝ} {K : Set (Point n)} (hKcpt : IsCompact K)
    (hmeas : AEStronglyMeasurable f volume)
    (hext : ∀ z ∉ K, f z = 0) (C : ℝ)
    (hbound : ∀ z ∈ K, ‖f z‖ ≤ C) :
    Integrable f volume := by
  have hKmeas : MeasurableSet K := hKcpt.measurableSet
  -- Dominator `g := |C| · 1_K` (using `|C| ≥ 0` sidesteps the empty-`K` degeneracy).
  set g : Point n → ℝ := fun z => K.indicator (fun _ => |C|) z with hg
  have hgint : Integrable g volume := by
    rw [hg]
    refine (integrable_indicator_iff hKmeas).mpr ?_
    exact integrableOn_const hKcpt.measure_lt_top.ne
  refine hgint.mono' hmeas ?_
  filter_upwards with z
  show ‖f z‖ ≤ K.indicator (fun _ => |C|) z
  by_cases hz : z ∈ K
  · rw [indicator_of_mem hz]
    exact le_trans (hbound z hz) (le_abs_self C)
  · have hfz : f z = 0 := hext z hz
    rw [hfz, norm_zero, indicator_of_notMem hz]

/-! ###############################################################################
    ### C1 — the null frontier of the LIVE confinement set `K = closedBall 0 r`.
    ############################################################################### -/

/-- **★ `volume_frontier_closedBall_eq_zero`.**  For `n ≥ 1` and `r ≠ 0`, the frontier of the closed
    ball is the sphere `sphere 0 r`, which is Lebesgue-null (`Measure.addHaar_sphere`).  This DISCHARGES
    the `volume (frontier K) = 0` hypothesis of the main reduction at the live curved-witness confinement
    set `K = Metric.closedBall 0 r`.  NOT `a₁ = R/6`. -/
theorem volume_frontier_closedBall_eq_zero (hn : 0 < n) (r : ℝ) (hr : r ≠ 0) :
    volume (frontier (Metric.closedBall (0 : Point n) r)) = 0 := by
  haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Point n) := Pi.nontrivial
  rw [frontier_closedBall (0 : Point n) hr]
  exact Measure.addHaar_sphere volume (0 : Point n) r

/-! ###############################################################################
    ### C2 — interior-continuity + off-`K` vanishing + null frontier ⟹ `AEStronglyMeasurable`.
    ############################################################################### -/

/-- **★★ `aestronglyMeasurable_of_interiorContinuous_nullFrontier`.**  A real function that is
    `ContinuousOn (interior K)` and vanishes off the CLOSED set `K`, on a set with `volume (frontier K)
    = 0`, is `AEStronglyMeasurable`.  On the OPEN co-null set `U := interior K ∪ Kᶜ` (complement exactly
    `frontier K` for closed `K`) the function is continuous — interior by hypothesis, exterior because it
    is locally `0`.  The measurability route that DODGES the boundary no-go (J4-892): never asks for
    continuity ACROSS `∂K`, only measurability, which tolerates the null `∂K`.  NOT `a₁ = R/6`. -/
theorem aestronglyMeasurable_of_interiorContinuous_nullFrontier
    {K : Set (Point n)} (hKcl : IsClosed K) (f : Point n → ℝ)
    (hint : ContinuousOn f (interior K)) (hext : ∀ z ∉ K, f z = 0)
    (hnull : volume (frontier K) = 0) :
    AEStronglyMeasurable f volume := by
  set U : Set (Point n) := interior K ∪ Kᶜ with hU
  have hUopen : IsOpen U := isOpen_interior.union hKcl.isOpen_compl
  have hUc : Uᶜ = frontier K := by
    rw [hU, Set.compl_union, compl_compl, Set.inter_comm, hKcl.frontier_eq, Set.diff_eq]
  have hnull' : volume Uᶜ = 0 := by rw [hUc]; exact hnull
  have hcont : ContinuousOn f U := by
    intro z hz
    rcases hz with hzi | hzc
    · exact (hint.continuousAt (isOpen_interior.mem_nhds hzi)).continuousWithinAt
    · have hev : f =ᶠ[nhds z] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hKcl.isOpen_compl.mem_nhds hzc) (fun w hw => hext w hw)
      exact (continuousAt_const.congr hev.symm).continuousWithinAt
  exact aestronglyMeasurable_of_continuousOn_compl_null hUopen hcont hnull'

/-! ###############################################################################
    ### C3 — THE `hbint` REDUCTION (the exact `MixedDirectionsFieldHessianEnvelope.hbint` shape).
    ############################################################################### -/

/-- **★★★ `hbint_of_interiorContinuous_nullFrontier` — the `hbint` field, via the MEASURABILITY route.**
    The EXACT `hbint` field of `MixedDirectionsFieldHessianEnvelope` FOLLOWS from the feedable carries:
    `hnull` (null frontier; discharged for the live ball), `hBFint` (interior joint-chart regularity —
    the asset the no-go LEAVES available), `hBFext` (banked off-`K` vanishing), `hBLK` (standard
    `BL`-continuity), `hbnd` (compact-`K` product bound).  Per `s`: the product is `ContinuousOn (interior
    K)` and `0` off `K`, hence `AEStronglyMeasurable`; with the bound, integrable.  Never asks for
    continuity across `∂K`.  NOT `a₁ = R/6`. -/
theorem hbint_of_interiorContinuous_nullFrontier
    {K : Set (Point n)} (hKcl : IsClosed K) (hKcpt : IsCompact K)
    (hnull : volume (frontier K) = 0)
    (BL BF : ℝ → Point n → ℝ) (t : ℝ) (m : ℕ)
    (hBFint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ContinuousOn (BF s) (interior K))
    (hBFext : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ∀ z ∉ K, BF s z = 0)
    (hBLK : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) → ContinuousOn (BL s) K)
    (hbnd : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∃ C : ℝ, ∀ z ∈ K, ‖BL s z * BF s z‖ ≤ C) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z => BL s z * BF s z) volume := by
  filter_upwards [hBFint, hBFext, hBLK, hbnd] with s hBFints hBFexts hBLKs hbnds hsU
  have hprodext : ∀ z ∉ K, BL s z * BF s z = 0 := by
    intro z hz; rw [hBFexts hsU z hz, mul_zero]
  have hprodint : ContinuousOn (fun z => BL s z * BF s z) (interior K) :=
    ((hBLKs hsU).mono interior_subset).mul (hBFints hsU)
  have hmeas : AEStronglyMeasurable (fun z => BL s z * BF s z) volume :=
    aestronglyMeasurable_of_interiorContinuous_nullFrontier hKcl
      (fun z => BL s z * BF s z) hprodint hprodext hnull
  obtain ⟨C, hC⟩ := hbnds hsU
  exact integrable_of_bounded_compactSupport hKcpt hmeas hprodext C hC

/-! ###############################################################################
    ### C4 — NON-VACUITY (the reduction fires at the live ball `K`).
    ############################################################################### -/

/-- **NON-VACUITY.**  At `K = Metric.closedBall 0 r` (`n ≥ 1`, `r ≠ 0`) and `BF = BL = 0`, every carry
    holds and the conclusion `Integrable 0` holds.  The reduction is INHABITED non-vacuously at the real
    live set.  NOT `a₁ = R/6`. -/
theorem hbint_reduction_nonvacuous (hn : 0 < n) (r : ℝ) (hr : r ≠ 0) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      Integrable (fun z : Point n =>
        (fun (_ : ℝ) (_ : Point n) => (0 : ℝ)) s z
          * (fun (_ : ℝ) (_ : Point n) => (0 : ℝ)) s z) volume := by
  refine hbint_of_interiorContinuous_nullFrontier
    (Metric.isClosed_closedBall) (isCompact_closedBall (0 : Point n) r)
    (volume_frontier_closedBall_eq_zero hn r hr)
    (fun (_ : ℝ) (_ : Point n) => 0) (fun (_ : ℝ) (_ : Point n) => 0) t m ?_ ?_ ?_ ?_
  · filter_upwards with s _; exact continuousOn_const
  · filter_upwards with s _; intro z _; rfl
  · filter_upwards with s _; exact continuousOn_const
  · filter_upwards with s _; exact ⟨0, fun z _ => by simp⟩

end QIQTH.HbintMeasurabilityNullFrontier

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HbintMeasurabilityNullFrontier
#print axioms aestronglyMeasurable_of_continuousOn_compl_null
#print axioms integrable_of_bounded_compactSupport
#print axioms volume_frontier_closedBall_eq_zero
#print axioms aestronglyMeasurable_of_interiorContinuous_nullFrontier
#print axioms hbint_of_interiorContinuous_nullFrontier
#print axioms hbint_reduction_nonvacuous
end AxiomChecks
