/-
  OnGateFieldRegularity — J4-170: the SHARED field-slot regularity core of the two remaining L1
  carries (`hGateDiff` and `hC2fam`) of the gated `N = 1` van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the a₁ = R/6 heat-kernel campaign.  It isolates the COMMON regularity core of the two field-slot
  carries that the concrete-witness continuity/measurability chains still carry:

    • `hC2fam`   (consumed by `WitnessDerivMeasurability.g2_bundle_assembled` via `hzcont_witness`):
        a.e.-`z`  `ContDiffAt ℝ 2 (fun x' ↦ vanVleckGatedWitness … (t−s) x' z) x₀`  for `x₀ ∈ u`.
    • `hGateDiff` (consumed by `GateSetMeasurability.hKmeas_concrete_v5` via
        `WitnessMeasDeriv.hWdiff_from_gateDiff`):  a.e.-`z` on-gate
        `PdiffAt (fun x' ↦ vanVleckGatedWitness … (t−s) x' z) i x` for `x` near `x₀ ∈ u`.

  BOTH rest on the SAME fact:  near a FIELD point inside the OPEN gate `S z` (base `z ∈ K`), the gated
  witness COINCIDES locally with its ungated INNER kernel (no indicator jump), and that inner kernel is
  `C²` in the FIELD slot — because the field point enters ONLY through the inverse chart
  `V_z := uniformInverseChart g gi hC hK z`, composed with the smooth cutoff · Gaussian · van-Vleck ·
  transport-coefficient factors (exactly the `SpatialC2.hCH_discharge` factorisation, lifted from the
  centre `0` to a GENERAL field point).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    • `innerKernelField`                      — the ungated inner kernel as a function of the field slot
        (the on-gate value of `vanVleckGatedWitness_gate_apply`).
    • `gatedWitness_eventuallyEq_inner`       — ★ THE LOCAL-COINCIDENCE LEVER.  For `z ∈ K` and
        `x₀ ∈ S z` OPEN, `(fun x' ↦ witness … x' z) =ᶠ[𝓝 x₀] innerKernelField`.
    • `innerKernel_contDiffAt_field`          — ★ the inner kernel's field-slot `C²` at a general field
        point `x₀`, from the field-chart `C²` carry `ContDiffAt ℝ 2 (V_z) x₀` + `hg`/`hgpos`/`hu`
        (factor-wise `ContDiffAt.comp`, the `hCH_discharge` tower away from the centre; `det g > 0`
        gives both van-Vleck smoothness and the nonzero `−1/2` rpow base).
    • `gatedWitness_contDiffAt_field`         — ★★ combines the two: on-gate field-slot `C²` of the
        witness.
    • `gatedWitness_contDiffAt_field_offK`    — off the base gate (`z ∉ K`) the witness is the constant
        `0` in the field slot, hence trivially `C²`.
    • `gatedWitness_pdiffAt_field`            — the `hGateDiff` atom:  on-gate field-slot `PdiffAt`
        (`ContDiffAt ℝ 2 ⟹ DifferentiableAt ⟹ PdiffAt` via the coordinate-line chain).
    • `hC2fam_from_chart`                     — ★★ the EXACT `hC2fam` slot, REDUCED to the gate/chart
        dichotomy carry (per a.e. `z`: `z ∉ K`, OR `z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z) ∧ V_z C² at x₀`).
    • `hGateDiff_from_chart`                  — ★★ the EXACT `hGateDiff` slot, REDUCED to the near-`x₀`
        gate/chart carry (∀ᶠ `x`, a.e. `z`, `z ∈ K → x ∈ S z ∧ IsOpen (S z) ∧ V_z C² at x`).
    • `hGateDiff_hC2fam_shared_core`          — ★★★ the SHARED-CORE capstone: BOTH carries, produced
        from the two chart/gate families, resting on the SAME `gatedWitness_contDiffAt_field` core.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • The FIELD-SLOT chart `C²` at GENERAL field points, `ContDiffAt ℝ 2 (V_z) x`.  Banked in-repo ONLY
      at the field CENTRE `0` (`ChartJetBounds.chartField_contDiffAt_center`,
      `AmplitudeFamilyDischarge.chartField_contDiffAt_center_general`).  Satisfiable at general field
      points by the inverse-function theorem on the smooth flow exponential `φ_z` (a local diffeo, so
      its local inverse `V_z` is `C²` throughout its domain, not only at the centre); carried here.
    • The GATE geometry `x ∈ S z` on the OPEN flow-ball gate — pure chart geometry, satisfiable for
      field points in the chart's reach over `K`, NOT the witness or its derivative.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.GeneralBaseJets
import QIQTH.GateSetMeasurability

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound
open scoped BigOperators Topology Interval

namespace QIQTH.OnGateFieldRegularity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The ungated inner kernel as a function of the field slot.
    ############################################################################### -/

/-- **`innerKernelField`.**  The ungated inner kernel of the gated `N = 1` van-Vleck witness, viewed
    as a function of the FIELD slot `x'` (base `z` fixed).  This is exactly the RHS of the on-gate
    value `vanVleckGatedWitness_gate_apply` (with `p = x'`, `q = z`): the field point enters ONLY
    through the inverse chart `V_z x' = uniformInverseChart g gi hC hK z x'`.  NOT `a₁ = R/6`. -/
noncomputable def innerKernelField (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z : Point n) : Point n → ℝ :=
  fun x' =>
    radialCutoff a b (uniformInverseChart g gi hC hK z x')
      * (gaussDdim τ (uniformInverseChart g gi hC hK z x')
          * vanVleck g (uniformInverseChart g gi hC hK z x') ^ (-(1 : ℝ) / 2)
          * (transportCoeff (transportOp (vanVleck g) g gi) 0
                (uniformInverseChart g gi hC hK z x')
            + transportCoeff (transportOp (vanVleck g) g gi) 1
                (uniformInverseChart g gi hC hK z x') * τ))

/-! ###############################################################################
    ### ★ THE LOCAL-COINCIDENCE LEVER.
    ############################################################################### -/

/-- **★ `gatedWitness_eventuallyEq_inner` — THE LOCAL-COINCIDENCE LEVER.**  For a base point `z ∈ K`
    and a field point `x₀` in the OPEN gate `S z`, the gated witness (as a function of the field slot)
    coincides with the ungated `innerKernelField` on a whole neighbourhood of `x₀` — the indicator is
    locally constant `1`, so there is no gate jump:
        `(fun x' ↦ vanVleckGatedWitness … τ x' z) =ᶠ[𝓝 x₀] innerKernelField … τ z`.
    From `vanVleckGatedWitness_gate_apply` on the OPEN `S z`.  NOT `a₁ = R/6`. -/
theorem gatedWitness_eventuallyEq_inner (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z x₀ : Point n) (hzK : z ∈ K) (hx₀ : x₀ ∈ S z) (hSopen : IsOpen (S z)) :
    (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      =ᶠ[𝓝 x₀] innerKernelField g gi hC hK a b τ z := by
  refine eventually_nhds_iff.mpr ⟨S z, ?_, hSopen, hx₀⟩
  intro x' hx'
  show vanVleckGatedWitness g gi hC hK S a b τ x' z = innerKernelField g gi hC hK a b τ z x'
  rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hzK hx']
  rfl

/-! ###############################################################################
    ### ★ THE INNER KERNEL'S FIELD-SLOT `C²` AT A GENERAL FIELD POINT.
    ############################################################################### -/

/-- **★ `innerKernel_contDiffAt_field`.**  The ungated inner kernel is `ContDiffAt ℝ 2` in the FIELD
    slot at a GENERAL field point `x₀`, from the honest field-chart `C²` carry
    `hWC2 : ContDiffAt ℝ 2 (V_z) x₀` plus `hg` (metric smoothness), `hgpos` (`det g > 0` everywhere)
    and `hu` (transport-coefficient smoothness).  This is the `SpatialC2.hCH_discharge` factor-wise
    `ContDiffAt.comp` tower, lifted from the field centre `0` to `x₀`: `det g (V_z x₀) > 0` supplies
    BOTH the van-Vleck smoothness and the nonzero base of the `−1/2` rpow branch.  NOT `a₁ = R/6`. -/
theorem innerKernel_contDiffAt_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (τ : ℝ) (z x₀ : Point n)
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (innerKernelField g gi hC hK a b τ z) x₀ := by
  unfold innerKernelField
  set W := uniformInverseChart g gi hC hK z with hWdef
  -- cutoff and Gaussian through the chart.
  have hcut : ContDiffAt ℝ 2 (fun p => radialCutoff a b (W p)) x₀ :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp x₀ hWC2
  have hgauss : ContDiffAt ℝ 2 (fun p => gaussDdim τ (W p)) x₀ :=
    ((gaussDdim_contDiff τ).contDiffAt.of_le le_top).comp x₀ hWC2
  -- van-Vleck smoothness and nonzero-ness at `W x₀` from `det g (W x₀) > 0`.
  have hdetW : 0 < Matrix.det (g (W x₀)) := hgpos (W x₀)
  have hvv : ContDiffAt ℝ 2 (fun p => vanVleck g (W p)) x₀ :=
    (vanVleck_contDiffAt g hg (W x₀) hdetW (k := 2)).comp x₀ hWC2
  have hne : (fun p => vanVleck g (W p)) x₀ ≠ 0 :=
    ne_of_gt (vanVleck_pos g (W x₀) hdetW)
  have hrpow : ContDiffAt ℝ 2 (fun p => vanVleck g (W p) ^ (-(1 : ℝ) / 2)) x₀ :=
    hvv.rpow_const_of_ne hne
  -- the two transport coefficients through the chart.
  have hu0 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)) x₀ :=
    (((hu 0).contDiffAt).of_le le_top).comp x₀ hWC2
  have hu1 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1 (W p)) x₀ :=
    (((hu 1).contDiffAt).of_le le_top).comp x₀ hWC2
  have hsum : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * τ) x₀ :=
    hu0.add (hu1.mul contDiffAt_const)
  exact hcut.mul ((hgauss.mul hrpow).mul hsum)

/-! ###############################################################################
    ### ★★ ON-GATE / OFF-GATE FIELD-SLOT `C²` OF THE WITNESS.
    ############################################################################### -/

/-- **★★ `gatedWitness_contDiffAt_field`.**  On the gate (`z ∈ K`, `x₀ ∈ S z` OPEN), the gated witness
    is `ContDiffAt ℝ 2` in the FIELD slot at `x₀`.  Combines the local-coincidence lever with the
    inner-kernel field-slot `C²`, transferred by `ContDiffAt.congr_of_eventuallyEq`.  NOT `a₁ = R/6`. -/
theorem gatedWitness_contDiffAt_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z x₀ : Point n) (hzK : z ∈ K) (hx₀ : x₀ ∈ S z) (hSopen : IsOpen (S z))
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x₀ := by
  have hinner := innerKernel_contDiffAt_field g gi hC hK a b τ z x₀ hWC2 hg hgpos hu
  exact hinner.congr_of_eventuallyEq
    (gatedWitness_eventuallyEq_inner g gi hC hK S a b τ z x₀ hzK hx₀ hSopen)

/-- **`gatedWitness_contDiffAt_field_offK`.**  Off the base gate (`z ∉ K`), the gated witness is the
    constant `0` in the FIELD slot (`gatedKernel_apply_of_notMem`), hence trivially `ContDiffAt ℝ 2`.
    NOT `a₁ = R/6`. -/
theorem gatedWitness_contDiffAt_field_offK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z x₀ : Point n) (hz : z ∉ K) :
    ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x₀ := by
  have hzero : (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) = fun _ => (0 : ℝ) := by
    funext x'
    unfold vanVleckGatedWitness
    exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  rw [hzero]; exact contDiffAt_const

/-! ###############################################################################
    ### The `PdiffAt` atom (for `hGateDiff`).
    ############################################################################### -/

/-- **`pdiffAt_of_differentiableAt`.**  Full differentiability at `x` gives partial differentiability
    along any coordinate `i`: the coordinate-slice `s ↦ f (update x i s)` is `f ∘ (line)` with the
    line `s ↦ update x i s` differentiable (`hasDerivAt_update_line`) and `f` differentiable at
    `update x i (x i) = x`.  NOT `a₁ = R/6`. -/
theorem pdiffAt_of_differentiableAt (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : DifferentiableAt ℝ f x) : PdiffAt f i x := by
  have hf' : DifferentiableAt ℝ f (Function.update x i (x i)) := by
    rw [Function.update_eq_self]; exact hf
  have hline : DifferentiableAt ℝ (fun s : ℝ => Function.update x i s) (x i) :=
    (hasDerivAt_update_line x i).differentiableAt
  show DifferentiableAt ℝ (fun s : ℝ => f (Function.update x i s)) (x i)
  exact hf'.comp (x i) hline

/-- **`gatedWitness_pdiffAt_field` — the `hGateDiff` atom.**  On the gate (`z ∈ K`, `x ∈ S z` OPEN),
    the gated witness is `PdiffAt` along coordinate `i` at the field point `x`.
    `ContDiffAt ℝ 2 ⟹ DifferentiableAt ⟹ PdiffAt`.  NOT `a₁ = R/6`. -/
theorem gatedWitness_pdiffAt_field (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (i : Fin n) (z x : Point n) (hzK : z ∈ K) (hxSz : x ∈ S z) (hSopen : IsOpen (S z))
    (hWC2 : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    PdiffAt (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x := by
  have hcd := gatedWitness_contDiffAt_field g gi hC hK S a b τ z x hzK hxSz hSopen hWC2 hg hgpos hu
  exact pdiffAt_of_differentiableAt _ i x (hcd.differentiableAt (by norm_num))

/-! ###############################################################################
    ### ★★ THE TWO CARRY REDUCTIONS.
    ############################################################################### -/

/-- **★★ `hC2fam_from_chart`.**  The EXACT `hC2fam` slot of `WitnessDerivMeasurability.g2_bundle_assembled`
    (`hzcont_witness`), REDUCED to the gate/chart DICHOTOMY carry `hFieldReg2` (per a.e. `z`: either
    `z ∉ K`, or `z ∈ K` with `x₀` in the OPEN gate `S z` and the field-chart `C²` at `x₀`) together
    with `hg`/`hgpos`/`hu`.  `z ∉ K` ⟹ the off-gate constant-`0` branch; the on-gate branch is the
    shared `gatedWitness_contDiffAt_field` core.  NOT `a₁ = R/6`. -/
theorem hC2fam_from_chart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hFieldReg2 : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)) :
    ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀ := by
  intro x₀ hx₀
  filter_upwards [hFieldReg2 x₀ hx₀] with s hs
  intro hmem
  filter_upwards [hs hmem] with z hz
  rcases hz with hzK | ⟨hzK, hxSz, hSopen, hWC2⟩
  · exact gatedWitness_contDiffAt_field_offK g gi hC hK S a b (t - s) z x₀ hzK
  · exact gatedWitness_contDiffAt_field g gi hC hK S a b (t - s) z x₀ hzK hxSz hSopen hWC2
      hg hgpos hu

/-- **★★ `hGateDiff_from_chart`.**  The EXACT `hGateDiff` slot of `GateSetMeasurability.hKmeas_concrete_v5`
    (`hWdiff_from_gateDiff`), REDUCED to the near-`x₀` gate/chart carry `hFieldReg` (∀ᶠ `x` near `x₀`,
    for a.e. `z`, whenever `z ∈ K` the field point `x` is in the OPEN gate `S z` and the field-chart is
    `C²` at `x`) together with `hg`/`hgpos`/`hu`.  The on-gate `PdiffAt` is the shared
    `gatedWitness_pdiffAt_field` core.  The conclusion is guarded by `z ∈ K`, so no off-gate branch is
    needed.  NOT `a₁ = R/6`. -/
theorem hGateDiff_from_chart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hFieldReg : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x := by
  intro x₀ hx₀ i
  filter_upwards [hFieldReg x₀ hx₀ i] with s hs
  intro hmem
  filter_upwards [hs hmem] with x hx
  filter_upwards [hx] with z hz
  intro hzK
  obtain ⟨hxSz, hSopen, hWC2⟩ := hz hzK
  exact gatedWitness_pdiffAt_field g gi hC hK S a b (t - s) i z x hzK hxSz hSopen hWC2
    hg hgpos hu

/-! ###############################################################################
    ### ★★★ THE SHARED-CORE CAPSTONE.
    ############################################################################### -/

/-- **★★★ `hGateDiff_hC2fam_shared_core`.**  BOTH remaining L1 field-slot carries — the `hGateDiff`
    slot (`GateSetMeasurability.hKmeas_concrete_v5`) AND the `hC2fam` slot
    (`WitnessDerivMeasurability.g2_bundle_assembled`) — produced SIMULTANEOUSLY from the two chart/gate
    families and the common `hg`/`hgpos`/`hu`.  Both rest on the SAME `gatedWitness_contDiffAt_field`
    field-slot regularity core (`hGateDiff` via `PdiffAt`-of-`C¹`, `hC2fam` directly), demonstrating
    that the two carries share one geometric root: on-gate coincidence with the inner kernel plus
    field-chart `C²`.  NOT `a₁ = R/6`. -/
theorem hGateDiff_hC2fam_shared_core (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hFieldReg : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x))
    (hFieldReg2 : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)) :
    (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x)
    ∧ (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀) :=
  ⟨hGateDiff_from_chart g gi hC hK S a b t u hg hgpos hu hFieldReg,
   hC2fam_from_chart g gi hC hK S a b t u hg hgpos hu hFieldReg2⟩

end QIQTH.OnGateFieldRegularity

section AxiomChecks
open QIQTH.OnGateFieldRegularity
#print axioms gatedWitness_eventuallyEq_inner
#print axioms innerKernel_contDiffAt_field
#print axioms gatedWitness_contDiffAt_field
#print axioms gatedWitness_contDiffAt_field_offK
#print axioms pdiffAt_of_differentiableAt
#print axioms gatedWitness_pdiffAt_field
#print axioms hC2fam_from_chart
#print axioms hGateDiff_from_chart
#print axioms hGateDiff_hC2fam_shared_core
end AxiomChecks
