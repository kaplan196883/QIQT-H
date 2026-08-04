/-
  GateDiffWiringMeasSet — J4-180: discharging the two last honest carries of J4-179's
  `CoeffContWdiffLift.hjoint_from_geometry_final` — the `∀ᶠ x`-first gate-dichotomy differentiability
  family `hGateDiff'` (PURE geometry-only wiring, Part A) and the `HasDerivAt`-property-set
  measurability `hMeasSet` (a genuine measurability lemma, Part B).  ONE brick of the a₁ = R/6
  heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity / measurability plumbing brick.  It replaces two of the honest residue carries of
  J4-179's `hjoint_from_geometry_final` by the pure gate/chart GEOMETRY (the reachable-gate coverage
  family) and a genuine, satisfiable measurability side-condition.  Never a conclusion; no vacuous /
  unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── PART A — `hGateDiff'` from the s-INDEPENDENT reachable-gate COVERAGE family (geometry-only).

    The gate/chart geometry (`x ∈ S z`, `IsOpen (S z)`, the field-chart `C²`) is τ-INDEPENDENT: the
    width `τ = t − s` enters `vanVleckGatedWitness` ONLY through the inner Gaussian·van-Vleck·transport
    factors, never through the gate `S z` or the chart `V_z`.  So the on-gate `PdiffAt` is produced for
    EVERY `s` from the SAME s-independent coverage carry.  The `∀ᵐ s` slot is then discharged by
    `ae_of_all` (the statement holds for all `s`).

    • `innerKernel_contDiffAt_field_infty` / `gatedWitness_contDiffAt_field_infty` /
        `gatedWitness_pdiffAt_field_infty` — the `∞`-order MIRRORS of J4-170's
        `OnGateFieldRegularity.{innerKernel_contDiffAt_field, gatedWitness_contDiffAt_field,
        gatedWitness_pdiffAt_field}`, proved by the SAME factor-wise `ContDiffAt.comp` tower but taking
        `hu` at `∞` (NOT `ω`), downcast to `C²` by `.of_le (2 ≤ ∞)`.  This makes the whole chain
        GEOMETRY-ONLY: `hu` is discharged at `∞` from `{hg, hgi, hgpos}` by `hu_infty_closed` (the `ω`
        analytic-solve wall is never touched).  NOT `a₁ = R/6`.
    • `hGateDiff'_from_coverage` — ★★ the EXACT `hGateDiff'` slot of J4-179, produced from `{hg, hgi,
        hgpos}` + the `∀ᶠ x`-first, ν-generic, s-INDEPENDENT reachable-gate coverage family `hCover`.
        NOT `a₁ = R/6`.

  ── PART B — `hMeasSet` for w-CONTINUOUS slices (the genuine measurability lever).

    For a base point `a` and a family of slices `F p : ℝ → ℝ` CONTINUOUS in `w`, `HasDerivAt (F p) L a`
    is characterised by countably many RATIONAL ε-δ conditions (Rudin §5; the `⟸` needs continuity):
        `HasDerivAt f L a ↔ ∀ ε∈ℚ⁺, ∃ δ∈ℚ⁺, ∀ h∈ℚ, |h|<δ → |f(a+h)−f a−L·h| ≤ ε·|h|`.
    Each inner condition is a measurable set in `p` when the slice values and the derivative are jointly
    measurable, and the countable ⋂⋃⋂ over ℚ stays measurable.  Hence the `HasDerivAt`-property set is
    Borel whenever the slices are w-continuous and the data are measurable.

    • `le_mul_abs_of_rat_dense` — the density-extension core: a `≤ ε|h|` bound on all RATIONAL `h` in a
        ball extends (via continuity + `Rat.denseRange_cast`) to all REAL `h` in the ball.
    • `hasDerivAt_iff_rat_of_continuous` — ★ the RATIONAL characterisation of `HasDerivAt` at `a` for a
        continuous `f`.  NOT `a₁ = R/6`.
    • `measurableSet_hasDerivAt_of_continuous_slices` — ★★ the GENERAL measurability lever: for a
        measurable family of w-continuous slices with measurable derivative, `{p | HasDerivAt (F p)
        (d p) a}` is a `MeasurableSet`.  NOT `a₁ = R/6`.
    • `hMeasSet_of_sliceCont` — ★★ the `hMeasSet` slot of J4-179, REDUCED to the honest w-continuity /
        measurability slice carries (satisfiable off the gate-boundary null set; NEVER the derivative).
    • `hjoint_fully_geometric` — ★★★ the full `hjoint` capstone with `hGateDiff'` replaced by the
        reachable-gate coverage (Part A) and `hMeasSet` reduced to the slice carries (Part B).
        NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `{hg, hgi, hgpos}` — the `C^∞` metric / inverse-metric components and `det g > 0` (the campaign's
      genuine geometric inputs).
    • `hCover` — the `∀ᶠ x`-first reachable-gate coverage geometry (pure chart geometry, τ-independent).
    • the Part-B slice measurability / w-continuity carries (`hMeasSet` residue) — satisfiable for the
      concrete w-continuous witness slices; NEVER the derivative content (that rides `hGateDiff'`).

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OnGateFieldRegularity
import QIQTH.HuInftyRebase
import QIQTH.CoeffContWdiffLift

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HuInftyRebase
open QIQTH.OnGateFieldRegularity
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.GateDiffWiringMeasSet

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A — the `∞`-order MIRRORS of the J4-170 field-slot regularity core.
    ############################################################################### -/

/-- **`innerKernel_contDiffAt_field_infty` — the `∞` MIRROR of J4-170's `innerKernel_contDiffAt_field`.**
    Same factor-wise `ContDiffAt.comp` tower, but taking `hu` at `∞` (NOT `ω = ⊤`), downcast to `C²`
    by `.of_le (2 ≤ ∞)`.  Lets the whole chain run GEOMETRY-ONLY (`hu` from `hu_infty_closed`).
    NOT `a₁ = R/6`. -/
theorem innerKernel_contDiffAt_field_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z x₀ : Point n)
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (innerKernelField g gi hC hK a b τ z) x₀ := by
  unfold innerKernelField
  set W := uniformInverseChart g gi hC hK z with hWdef
  have h2inf : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    simpa using h
  have hcut : ContDiffAt ℝ 2 (fun p => radialCutoff a b (W p)) x₀ :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp x₀ hWC2
  have hgauss : ContDiffAt ℝ 2 (fun p => gaussDdim τ (W p)) x₀ :=
    ((gaussDdim_contDiff τ).contDiffAt.of_le le_top).comp x₀ hWC2
  have hdetW : 0 < Matrix.det (g (W x₀)) := hgpos (W x₀)
  have hvv : ContDiffAt ℝ 2 (fun p => vanVleck g (W p)) x₀ :=
    (vanVleck_contDiffAt g hg (W x₀) hdetW (k := 2)).comp x₀ hWC2
  have hne : (fun p => vanVleck g (W p)) x₀ ≠ 0 :=
    ne_of_gt (vanVleck_pos g (W x₀) hdetW)
  have hrpow : ContDiffAt ℝ 2 (fun p => vanVleck g (W p) ^ (-(1 : ℝ) / 2)) x₀ :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)) x₀ :=
    (((hu 0).contDiffAt).of_le h2inf).comp x₀ hWC2
  have hu1 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1 (W p)) x₀ :=
    (((hu 1).contDiffAt).of_le h2inf).comp x₀ hWC2
  have hsum : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * τ) x₀ :=
    hu0.add (hu1.mul contDiffAt_const)
  exact hcut.mul ((hgauss.mul hrpow).mul hsum)

/-- **`gatedWitness_contDiffAt_field_infty` — the `∞` MIRROR of J4-170's `gatedWitness_contDiffAt_field`.**
    On-gate field-slot `C²` of the witness, from the `∞`-order inner kernel + the local-coincidence
    lever (reused verbatim).  NOT `a₁ = R/6`. -/
theorem gatedWitness_contDiffAt_field_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z x₀ : Point n) (hzK : z ∈ K) (hx₀ : x₀ ∈ S z) (hSopen : IsOpen (S z))
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x₀ := by
  have hinner := innerKernel_contDiffAt_field_infty g gi hC hK a b τ z x₀ hWC2 hg hgpos hu
  exact hinner.congr_of_eventuallyEq
    (gatedWitness_eventuallyEq_inner g gi hC hK S a b τ z x₀ hzK hx₀ hSopen)

/-- **`gatedWitness_pdiffAt_field_infty` — the `∞` MIRROR of J4-170's `gatedWitness_pdiffAt_field`.**
    On-gate field-slot `PdiffAt` along `i`, `ContDiffAt ℝ 2 ⟹ DifferentiableAt ⟹ PdiffAt`.
    NOT `a₁ = R/6`. -/
theorem gatedWitness_pdiffAt_field_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (i : Fin n) (z x : Point n) (hzK : z ∈ K) (hxSz : x ∈ S z) (hSopen : IsOpen (S z))
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    PdiffAt (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x := by
  have hcd := gatedWitness_contDiffAt_field_infty g gi hC hK S a b τ z x hzK hxSz hSopen hWC2
    hg hgpos hu
  exact pdiffAt_of_differentiableAt _ i x (hcd.differentiableAt (by norm_num))

/-! ###############################################################################
    ### PART A ★★ — the EXACT `hGateDiff'` slot, geometry-only from the coverage family.
    ############################################################################### -/

/-- **★★ `hGateDiff'_from_coverage` — the EXACT `hGateDiff'` slot of J4-179, geometry-only.**  From the
    `C^∞` metric data `{hg, hgi, hgpos}` (which discharge `hu` at `∞` via `hu_infty_closed`) and the
    `∀ᶠ x`-first, ν-generic, s-INDEPENDENT reachable-gate coverage family `hCover` (for `x` near `x₀`,
    a.e. `z`, whenever `z ∈ K` the field point `x` is in the OPEN gate `S z` and the field-chart is
    `C²` at `x`), produces the `∀ᶠ x`-first gate-dichotomy differentiability family.  The `∀ᵐ s` slot
    is discharged by `ae_of_all`: the on-gate `PdiffAt` holds for EVERY `s` because the gate/chart
    geometry is τ-independent.  NOT `a₁ = R/6`. -/
theorem hGateDiff'_from_coverage (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ν : Measure (Point n)) (u₀ : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hCover : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂ν,
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
        ∀ᵐ z ∂ν,
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x := by
  have hu := hu_infty_closed g gi hg hgi hgpos
  intro x₀ hx₀ i
  filter_upwards [hCover x₀ hx₀ i] with x hx
  refine ae_of_all _ (fun s => ?_)
  filter_upwards [hx] with z hz
  intro hzK
  obtain ⟨hxSz, hSopen, hWC2⟩ := hz hzK
  exact gatedWitness_pdiffAt_field_infty g gi hC hK S a b (t - s) i z x hzK hxSz hSopen hWC2
    hg hgpos hu

/-! ###############################################################################
    ### PART B — the RATIONAL characterisation of `HasDerivAt` for continuous slices.
    ############################################################################### -/

/-- **`le_mul_abs_of_rat_dense` — the density-extension core.**  A `≤ ε·|h|` bound holding on all
    RATIONAL `h` in a ball extends to all REAL `h` in the ball, using continuity of `G` and the density
    of `ℚ` in `ℝ` (`Rat.denseRange_cast`): approximate the real `h₀` by rationals `qₖ → h₀`, eventually
    inside the ball, and pass the bound to the limit.  NOT `a₁ = R/6`. -/
theorem le_mul_abs_of_rat_dense {G : ℝ → ℝ} (hG : Continuous G) {ε δ : ℝ}
    (hrat : ∀ q : ℚ, |(q : ℝ)| < δ → |G (q : ℝ)| ≤ ε * |(q : ℝ)|)
    {h₀ : ℝ} (hh₀ : |h₀| < δ) : |G h₀| ≤ ε * |h₀| := by
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp (Rat.denseRange_cast h₀)
  choose q hq using hu_mem
  have hqeq : (fun k => ((q k : ℝ))) = u := funext hq
  have hqtend : Tendsto (fun k => ((q k : ℝ))) atTop (𝓝 h₀) := by rw [hqeq]; exact hu_tend
  have habs_tend : Tendsto (fun k => |(q k : ℝ)|) atTop (𝓝 |h₀|) :=
    (continuous_abs.tendsto h₀).comp hqtend
  have hev : ∀ᶠ k in atTop, |(q k : ℝ)| < δ :=
    habs_tend.eventually (eventually_lt_nhds hh₀)
  have hL : Tendsto (fun k => |G (q k : ℝ)|) atTop (𝓝 |G h₀|) :=
    ((continuous_abs.comp hG).tendsto h₀).comp hqtend
  have hR : Tendsto (fun k => ε * |(q k : ℝ)|) atTop (𝓝 (ε * |h₀|)) :=
    tendsto_const_nhds.mul habs_tend
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [hev] with k hk
  exact hrat (q k) hk

/-- **★ `hasDerivAt_iff_rat_of_continuous` — the RATIONAL characterisation of `HasDerivAt`.**  For a
    CONTINUOUS `f : ℝ → ℝ`, `HasDerivAt f L a` is equivalent to countably many rational ε-δ conditions.
    `⟹` reads off the little-o bound and rationalises `δ`; `⟸` builds the little-o bound from the
    rational conditions, extending each `≤ ε|h|` inequality from rational to real `h` by continuity
    (`le_mul_abs_of_rat_dense`) and letting `ε ↓` through the rationals.  NOT `a₁ = R/6`. -/
theorem hasDerivAt_iff_rat_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (L a : ℝ) :
    HasDerivAt f L a ↔
      ∀ ε : ℚ, 0 < ε → ∃ δ : ℚ, 0 < δ ∧ ∀ h : ℚ, |(h : ℝ)| < (δ : ℝ) →
        |f (a + (h : ℝ)) - f a - L * (h : ℝ)| ≤ (ε : ℝ) * |(h : ℝ)| := by
  constructor
  · -- `⟹` : from the little-o characterisation.
    intro hderiv ε hε
    have hlo := hasDerivAt_iff_isLittleO.mp hderiv
    rw [Asymptotics.isLittleO_iff] at hlo
    have hc : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hev := hlo hc
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δr, hδr, hb⟩ := hev
    obtain ⟨δ, h0δ, hδδr⟩ := exists_rat_btwn hδr
    refine ⟨δ, by exact_mod_cast h0δ, ?_⟩
    intro h hh
    have hxmem : dist (a + (h : ℝ)) a < δr := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_trans hh hδδr
    have hbnd := hb hxmem
    simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at hbnd
    have hcomm : |f (a + (h : ℝ)) - f a - L * (h : ℝ)|
        = |f (a + (h : ℝ)) - f a - (h : ℝ) * L| := by rw [mul_comm L (h : ℝ)]
    rw [hcomm]; exact hbnd
  · -- `⟸` : build the little-o from the rational conditions.
    intro hcond
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨ε, hε0, hεc⟩ := exists_rat_btwn hc
    obtain ⟨δ, hδ0, hδspec⟩ := hcond ε (by exact_mod_cast hε0)
    rw [Metric.eventually_nhds_iff]
    refine ⟨(δ : ℝ), by exact_mod_cast hδ0, ?_⟩
    intro x' hx'
    have hGcont : Continuous (fun h : ℝ => f (a + h) - f a - L * h) :=
      ((hf.comp (continuous_const.add continuous_id)).sub continuous_const).sub
        (continuous_const.mul continuous_id)
    have hh0lt : |x' - a| < (δ : ℝ) := by rw [← Real.dist_eq]; exact hx'
    have hbnd := le_mul_abs_of_rat_dense (G := fun h : ℝ => f (a + h) - f a - L * h)
      hGcont (fun q hq => hδspec q hq) hh0lt
    have hax : a + (x' - a) = x' := by ring
    simp only [hax] at hbnd
    -- hbnd : |f x' - f a - L * (x' - a)| ≤ ε * |x' - a|
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hcomm : f x' - f a - (x' - a) • L = f x' - f a - L * (x' - a) := by
      rw [smul_eq_mul, mul_comm]
    rw [hcomm]
    calc |f x' - f a - L * (x' - a)| ≤ (ε : ℝ) * |x' - a| := hbnd
      _ ≤ c * |x' - a| := mul_le_mul_of_nonneg_right hεc.le (abs_nonneg _)

/-! ###############################################################################
    ### PART B ★★ — the GENERAL `HasDerivAt`-set measurability lever for continuous slices.
    ############################################################################### -/

/-- **★★ `measurableSet_hasDerivAt_of_continuous_slices` — the GENERAL measurability lever.**  For a
    family of slices `F p : ℝ → ℝ` CONTINUOUS in `w` (`hcont`), with the slice values at the RATIONAL
    sample points `a + q` (`hFmeas`) and at `a` (`hFa`), and the derivative `d` (`hd`) all measurable
    in the parameter `p`, the `HasDerivAt`-property set `{p | HasDerivAt (F p) (d p) a}` is a
    `MeasurableSet`.  Proof: rewrite via the rational characterisation into the countable
    `⋂ε ⋃δ ⋂h`-family of measurable ε-δ conditions over `ℚ`, then close by countable measurable
    operations.  This is the exact tool the iterated → product a.e. converter (J4-177) needs — with
    the honest `w`-continuity content supplied, NOT a differentiability conclusion.  NOT `a₁ = R/6`. -/
theorem measurableSet_hasDerivAt_of_continuous_slices
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → ℝ → ℝ) (d : Ω → ℝ) (a : ℝ)
    (hcont : ∀ p, Continuous (F p))
    (hFmeas : ∀ q : ℚ, Measurable (fun p => F p (a + (q : ℝ))))
    (hFa : Measurable (fun p => F p a))
    (hd : Measurable d) :
    MeasurableSet {p : Ω | HasDerivAt (F p) (d p) a} := by
  classical
  have hbase : ∀ (ε h : ℚ), MeasurableSet
      {p : Ω | |F p (a + (h : ℝ)) - F p a - d p * (h : ℝ)| ≤ (ε : ℝ) * |(h : ℝ)|} := by
    intro ε h
    have hmeas : Measurable
        (fun p => |F p (a + (h : ℝ)) - F p a - d p * (h : ℝ)|) :=
      (((hFmeas h).sub hFa).sub (hd.mul measurable_const)).abs
    exact measurableSet_le hmeas measurable_const
  have hset : {p : Ω | HasDerivAt (F p) (d p) a} =
      ⋂ (ε : ℚ), ⋂ (_ : 0 < ε), ⋃ (δ : ℚ), ⋃ (_ : 0 < δ),
        ⋂ (h : ℚ), ⋂ (_ : |(h : ℝ)| < (δ : ℝ)),
          {p : Ω | |F p (a + (h : ℝ)) - F p a - d p * (h : ℝ)| ≤ (ε : ℝ) * |(h : ℝ)|} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact hasDerivAt_iff_rat_of_continuous (hcont p) (d p) a
  rw [hset]
  refine MeasurableSet.iInter (fun ε => MeasurableSet.iInter (fun _ => ?_))
  refine MeasurableSet.iUnion (fun δ => MeasurableSet.iUnion (fun _ => ?_))
  refine MeasurableSet.iInter (fun h => MeasurableSet.iInter (fun _ => ?_))
  exact hbase ε h

/-! ###############################################################################
    ### PART B ★★ — the `hMeasSet` slot, reduced to the honest slice carries.
    ############################################################################### -/

/-- **★★ `hMeasSet_of_sliceCont` — the EXACT `hMeasSet` slot of J4-179, reduced to the honest slice
    carries.**  The `HasDerivAt`-property-set measurability side-condition, produced from: the `w`-slice
    CONTINUITY of the witness (`hSliceCont` — the honest boundary residue; on-gate `C²`, off-gate `0`,
    satisfiable off the gate-boundary null set), together with the joint `(s,z)`-measurability of the
    witness at the rational field samples (`hWq`), at the base point (`hWa`), and of the field
    derivative (`hDmeas`) — exactly the J4-178 joint-measurability interface.  NONE is the derivative
    content (that rides `hGateDiff'`).  Via `measurableSet_hasDerivAt_of_continuous_slices` at the
    base point `x i`.  NOT `a₁ = R/6`. -/
theorem hMeasSet_of_sliceCont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ν : Measure (Point n)) (u₀ : Set (Point n))
    (hSliceCont : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    (hWq : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    (hWa : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2))
    (hDmeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      MeasurableSet {p : ℝ × Point n |
        HasDerivAt
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
          (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)} := by
  intro x₀ hx₀ i
  filter_upwards [hSliceCont x₀ hx₀ i, hWq x₀ hx₀ i, hWa x₀ hx₀ i, hDmeas x₀ hx₀ i]
    with x hcont hwq hwa hdm
  exact measurableSet_hasDerivAt_of_continuous_slices
    (fun (p : ℝ × Point n) w =>
      vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
    (fun (p : ℝ × Point n) => witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)
    (x i) hcont (fun q => hwq q) hwa hdm

/-! ###############################################################################
    ### ★★★ CAPSTONE — the full `hjoint`, geometry + slice carries only.
    ############################################################################### -/

/-- **★★★ `hjoint_fully_geometric` — the full `hjoint` capstone, geometry + slice carries only.**  The
    exact `hjoint` slot of `g2_bundle_assembled` for `dH := witnessFieldDeriv`, with J4-179's two honest
    residues discharged: `hGateDiff'` is replaced by the s-INDEPENDENT reachable-gate coverage
    `hCover` (Part A, geometry-only via `hGateDiff'_from_coverage`), and `hMeasSet` is reduced to the
    honest slice `w`-continuity / joint-measurability carries (Part B, via `hMeasSet_of_sliceCont`).
    The remaining carries `{hg, hgi, hgpos, hKmeasSet, hSmeasSet, hFjoint, hVmapMeas}` are the genuine
    geometric / gate / source data, each satisfiable and non-vacuous, none the conclusion.
    NOT `a₁ = R/6`. -/
theorem hjoint_fully_geometric (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hSliceCont : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    (hWq : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    (hWa : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2))
    (hDmeas : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) :=
  QIQTH.CoeffContWdiffLift.hjoint_from_geometry_final g gi hC hK S a b t F ν u₀ hg hgi hgpos
    hKmeasSet hSmeasSet hFjoint hVmapMeas
    (hMeasSet_of_sliceCont g gi hC hK S a b t ν u₀ hSliceCont hWq hWa hDmeas)
    (hGateDiff'_from_coverage g gi hC hK S a b t ν u₀ hg hgi hgpos hCover)

end QIQTH.GateDiffWiringMeasSet

section AxiomChecks
open QIQTH.GateDiffWiringMeasSet
#print axioms innerKernel_contDiffAt_field_infty
#print axioms gatedWitness_contDiffAt_field_infty
#print axioms gatedWitness_pdiffAt_field_infty
#print axioms hGateDiff'_from_coverage
#print axioms le_mul_abs_of_rat_dense
#print axioms hasDerivAt_iff_rat_of_continuous
#print axioms measurableSet_hasDerivAt_of_continuous_slices
#print axioms hMeasSet_of_sliceCont
#print axioms hjoint_fully_geometric
end AxiomChecks
