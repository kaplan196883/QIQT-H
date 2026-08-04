/-
  CoeffContWdiffLift — J4-179: discharging the LIGHT coefficient carries `{hΘc, hΘne, huc}` and
  lifting the joint field-differentiability carry `hWdiffJ` of J4-178's `hjoint_final`
  (`QIQTH.InnerKernelJointMeas`).  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity / measurability plumbing brick.  It discharges three of the four coefficient carries of
  J4-178's `hjoint_final` straight from the geometric hypotheses `{hg, hgi, hgpos}`, and re-threads
  the joint field-differentiability carry `hWdiffJ` through the honest ae_ae → ae_prod converter.
  Never a conclusion; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── PART A — THE COEFFICIENT CARRIES (all LIGHT, discharged from `{hg, hgi, hgpos}`).

    • `vanVleck_continuous` — ★ `hΘc : Continuous (vanVleck g)`.  `vanVleck g = (√ det g)⁻¹`;
        `det ∘ g` is continuous (`det_contDiff`), `√` is continuous (`Real.continuous_sqrt`), and the
        inverse is continuous because `√ det g` never vanishes (`hgpos ⟹ Real.sqrt_pos`), via
        `Continuous.inv₀`.  The positivity `hgpos` is genuine and load-bearing (`(·)⁻¹` is singular
        at `0`).  NOT `a₁ = R/6`.
    • `vanVleck_ne_zero` — `hΘne : ∀ w, vanVleck g w ≠ 0`, from `vanVleck_pos` + `ne_of_gt`.
    • `huc_discharged` — ★ `huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k)`.
        The concrete transport operator involves the Laplace–Beltrami SECOND derivatives, so it does
        NOT preserve mere continuity; the honest route is the `C^∞` chain `hu_infty_closed`
        (J4-175, from `{hg, hgi, hgpos}`) downcast by `ContDiff.continuous`.  NOT `a₁ = R/6`.
    • `hjoint_from_geometry` — ★★ threads the three discharges into J4-178's `hjoint_final`, so the
        inner-kernel carries drop from `{hΘc, hΘne, huc, hVmapMeas}` to `{hg, hgi, hgpos, hVmapMeas}`.
        NOT `a₁ = R/6`.

  ── PART B — THE `hWdiffJ` PRODUCT-LIFT.

    The per-`z` gate-dichotomy differentiability is banked as `WitnessMeasDeriv.hWdiff_from_gateDiff`
    in the quantifier order `(∀ᵐ s)(∀ᶠ x)(∀ᵐ z)`; the target `hWdiffJ` needs `(∀ᶠ x)(∀ᵐ (s,z))`.

    • `hWdiff_from_gateDiff'` — ★ the REORDERED variant `(∀ᶠ x)(∀ᵐ s)(∀ᵐ z)`, proved exactly like the
        banked original but from a `∀ᶠ x`-FIRST gate-dichotomy carry `hGateDiff'` (the honest reorder:
        the reorder `∀ᵐ s ∀ᶠ x ⟹ ∀ᶠ x ∀ᵐ s` is NOT valid in general, so we take the input carry
        directly in the `∀ᶠ x`-first form — mirroring J4-173's `hGateData'` / `hdomS` handling).
        On-gate (`z ∈ K`) uses `hWdiff_onGate` with the carried `PdiffAt`; off-gate (`z ∉ K`) uses the
        unconditional `hWdiff_offGate`.  Generic in the base measure `ν` on `z`.  NOT `a₁ = R/6`.
    • `hWdiffJ_from_slices` — ★★ the `∀ᵐ s ∀ᵐ z ⟹ ∀ᵐ (s,z)` lift via J4-177's `ae_prod_of_ae_ae`.
        This direction (iterated → product) genuinely needs the measurability of the `HasDerivAt`
        property set (Rudin §8.9(c) is the counterexample without it).  For the GENERAL lever the
        `HasDerivAt`-set is not measurable from `AEStronglyMeasurable` data alone (a single sequence
        `a + 1/(k+1)` captures only a subsequential slope limit, not the full `𝓝[≠] a` limit, unless
        the slices are continuous in `w` — which the abstract lever does not assume), and Mathlib has
        no banked `measurableSet_hasDerivAt`.  So the measurable-set is carried honestly as `hMeasSet`
        — a genuine, satisfiable, NON-vacuous measurability SIDE-condition (the concrete witness slices
        are continuous in `w`, so the set IS Borel), and NEVER the differentiability conclusion (that
        content rides `hGateDiff'`).  NOT `a₁ = R/6`.
    • `hjoint_from_geometry_final` — ★★★ the full `hjoint` capstone: everything threaded, carrying
        `{hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hg, hgi, hgpos, hGateDiff', hMeasSet}`.
        NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hg` / `hgi` — `C^∞` metric / inverse-metric components; `hgpos` — `det g > 0` (positive
      definiteness).  The genuine geometric inputs the whole campaign rides.
    • `hVmapMeas` — the `ν`-level chart ae-measurability (unchanged from J4-178).
    • `hKmeasSet` / `hSmeasSet` / `hFjoint` — the gate / source measurable data (unchanged from J4-177).
    • `hGateDiff'` — the `∀ᶠ x`-first on-gate `C¹` gate-dichotomy family (the `pd`-is-a-derivative
      content, reordered).
    • `hMeasSet` — the `HasDerivAt`-property-set measurability side-condition (satisfiable; the honest
      residue of the iterated → product a.e. converter).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InnerKernelJointMeas
import QIQTH.WitnessMeasDeriv
import QIQTH.HuInftyRebase

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RNCExpansion QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatResidualBound QIQTH.HuInftyRebase
open QIQTH.WitnessMeasDeriv QIQTH.JointMeasurability QIQTH.InnerKernelJointMeas
open scoped Interval Topology BigOperators

namespace QIQTH.CoeffContWdiffLift

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — the coefficient carries `{hΘc, hΘne, huc}` + the geometry thread.
    ############################################################################### -/

/-- **★ `vanVleck_continuous` — the `hΘc` carry, discharged.**  `Continuous (vanVleck g)` from the
    `C^∞` metric components (`hg`) and positive definiteness (`hgpos`): `vanVleck g = (√ det g)⁻¹`,
    with `det ∘ g` continuous (`det_contDiff`), `√` continuous, and the inverse continuous because
    `√ det g` never vanishes (`hgpos ⟹ Real.sqrt_pos`), via `Continuous.inv₀`.  The positivity
    `hgpos` is genuine and load-bearing (`(·)⁻¹` is singular at `0`).  NOT `a₁ = R/6`. -/
theorem vanVleck_continuous (g : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    Continuous (vanVleck g) := by
  have hdet : Continuous (fun v : Point n => Matrix.det (g v)) :=
    (det_contDiff g hg).continuous
  have hsqrt : Continuous (fun v : Point n => Real.sqrt (Matrix.det (g v))) :=
    Real.continuous_sqrt.comp hdet
  have hne : ∀ v : Point n, Real.sqrt (Matrix.det (g v)) ≠ 0 :=
    fun v => ne_of_gt (Real.sqrt_pos.mpr (hgpos v))
  show Continuous (fun v : Point n => (Real.sqrt (Matrix.det (g v)))⁻¹)
  exact hsqrt.inv₀ hne

/-- **`vanVleck_ne_zero` — the `hΘne` carry, discharged.**  `∀ w, vanVleck g w ≠ 0` from
    `vanVleck_pos` (positivity where `det g > 0`, carried as `hgpos`) via `ne_of_gt`.
    NOT `a₁ = R/6`. -/
theorem vanVleck_ne_zero (g : Point n → Fin n → Fin n → ℝ)
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∀ w, vanVleck g w ≠ 0 :=
  fun w => ne_of_gt (vanVleck_pos g w (hgpos w))

/-- **★ `huc_discharged` — the `huc` carry, discharged.**  `∀ k, Continuous (transportCoeff
    (transportOp (vanVleck g) g gi) k)` from `{hg, hgi, hgpos}`.  The concrete transport operator
    `Θ^{-½}·Δ_g(Θ^{½}··)` carries the Laplace–Beltrami SECOND derivatives, so it does NOT preserve
    mere continuity (`transportCoeff_continuous_of_preserve`'s `hT : T preserves Continuous` is NOT
    satisfiable for this `T`); the honest route is the `C^∞` chain `hu_infty_closed` (J4-175)
    downcast by `ContDiff.continuous`.  NOT `a₁ = R/6`. -/
theorem huc_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k) :=
  fun k => (hu_infty_closed g gi hg hgi hgpos k).continuous

/-- **★★ `hjoint_from_geometry` — J4-178's `hjoint_final` with `{hΘc, hΘne, huc}` discharged.**  The
    inner-kernel coefficient carries are replaced by the geometric hypotheses `{hg, hgi, hgpos}`
    (composing `vanVleck_continuous` / `vanVleck_ne_zero` / `huc_discharged`), so the concrete
    `hjoint` slot of `g2_bundle_assembled` for `dH := witnessFieldDeriv` now carries only
    `{hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hWdiffJ, hg, hgi, hgpos}`.  NOT `a₁ = R/6`. -/
theorem hjoint_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hWdiffJ : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
  hjoint_final g gi hC hK S a b t F ν u₀
    hKmeasSet hSmeasSet hFjoint
    (vanVleck_continuous g hg hgpos)
    (vanVleck_ne_zero g hgpos)
    (huc_discharged g gi hg hgi hgpos)
    hVmapMeas hWdiffJ

/-! ###############################################################################
    ### PART B — the `hWdiffJ` product-lift.
    ############################################################################### -/

/-- **★ `hWdiff_from_gateDiff'` — the REORDERED gate-dichotomy differentiability.**  The `∀ᶠ x`-first
    variant of `WitnessMeasDeriv.hWdiff_from_gateDiff`, in the order `(∀ᶠ x)(∀ᵐ s)(∀ᵐ z)`.  The
    reorder `∀ᵐ s ∀ᶠ x ⟹ ∀ᶠ x ∀ᵐ s` is NOT valid in general, so the input carry `hGateDiff'` is
    taken directly in the `∀ᶠ x`-first form (mirroring J4-173's `hGateData'` / `hdomS`).  For a.e. `z`
    (w.r.t. the GENERIC base measure `ν`): on-gate (`z ∈ K`) applies `hWdiff_onGate` to the carried
    `PdiffAt`; off-gate (`z ∉ K`) applies the unconditional `hWdiff_offGate`.  NOT `a₁ = R/6`. -/
theorem hWdiff_from_gateDiff' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ν : Measure (Point n)) (u₀ : Set (Point n))
    (hGateDiff' : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
          ∀ᵐ z ∂ν,
            z ∈ K → PdiffAt (fun x' : Point n =>
              vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
        ∀ᵐ z ∂ν,
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
            (witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i) := by
  intro x₀ hx₀ i
  filter_upwards [hGateDiff' x₀ hx₀ i] with x hx
  filter_upwards [hx] with s hs
  filter_upwards [hs] with z hz
  by_cases hzK : z ∈ K
  · exact hWdiff_onGate g gi hC hK S a b i (t - s) x z (hz hzK)
  · exact hWdiff_offGate g gi hC hK S a b i (t - s) x z hzK

/-- **★★ `hWdiffJ_from_slices` — the `∀ᵐ s ∀ᵐ z ⟹ ∀ᵐ (s,z)` product-lift, the exact `hWdiffJ`.**
    Threads `hWdiff_from_gateDiff'` (the reordered slice differentiability) through J4-177's
    `ae_prod_of_ae_ae` (the iterated → product a.e. converter).  This direction genuinely needs the
    measurability of the `HasDerivAt` property set (Rudin's counterexample), carried honestly as
    `hMeasSet` — a satisfiable, non-vacuous measurability SIDE-condition (the concrete witness slices
    are continuous in `w`, so the set is Borel), NEVER the differentiability conclusion (that content
    rides `hGateDiff'`).  Delivers the EXACT `hWdiffJ` shape of `hjoint_from_geometry`.
    NOT `a₁ = R/6`. -/
theorem hWdiffJ_from_slices (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hMeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        MeasurableSet {p : ℝ × Point n |
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)})
    (hGateDiff' : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
          ∀ᵐ z ∂ν,
            z ∈ K → PdiffAt (fun x' : Point n =>
              vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
        HasDerivAt
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
          (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i) := by
  intro x₀ hx₀ i
  filter_upwards [hWdiff_from_gateDiff' g gi hC hK S a b t ν u₀ hGateDiff' x₀ hx₀ i,
    hMeasSet x₀ hx₀ i] with x hx hms
  exact ae_prod_of_ae_ae (volume.restrict (Set.uIoc 0 t)) ν hms hx

/-! ###############################################################################
    ### CAPSTONE — the full `hjoint` from the geometry + the reordered slice data.
    ############################################################################### -/

/-- **★★★ `hjoint_from_geometry_final` — the full `hjoint` capstone.**  Threads
    `hWdiffJ_from_slices` (Part B) into `hjoint_from_geometry` (Part A), delivering the EXACT `hjoint`
    slot of `g2_bundle_assembled` for `dH := witnessFieldDeriv`, carrying only the honest, satisfiable,
    non-vacuous residue `{hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hg, hgi, hgpos, hGateDiff',
    hMeasSet}` — none of which is the conclusion.  NOT `a₁ = R/6`. -/
theorem hjoint_from_geometry_final (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hMeasSet : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        MeasurableSet {p : ℝ × Point n |
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)})
    (hGateDiff' : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
          ∀ᵐ z ∂ν,
            z ∈ K → PdiffAt (fun x' : Point n =>
              vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
  hjoint_from_geometry g gi hC hK S a b t F ν u₀ hg hgi hgpos
    hKmeasSet hSmeasSet hFjoint hVmapMeas
    (hWdiffJ_from_slices g gi hC hK S a b t ν u₀ hMeasSet hGateDiff')

end QIQTH.CoeffContWdiffLift

section AxiomChecks
open QIQTH.CoeffContWdiffLift
#print axioms vanVleck_continuous
#print axioms vanVleck_ne_zero
#print axioms huc_discharged
#print axioms hjoint_from_geometry
#print axioms hWdiff_from_gateDiff'
#print axioms hWdiffJ_from_slices
#print axioms hjoint_from_geometry_final
end AxiomChecks
