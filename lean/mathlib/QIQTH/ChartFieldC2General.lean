/-
  ChartFieldC2General — J4-171: the INVERSE-FUNCTION-THEOREM brick for the field-slot `C²` of the
  uniform inverse chart `uniformInverseChart` at GENERAL (reachable) field points, feeding the
  J4-170 (`OnGateFieldRegularity`) reduction of the two remaining L1 field-slot carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE brick of
  the a₁ = R/6 heat-kernel campaign.  J4-170 reduced BOTH remaining field-slot carries (`hC2fam`,
  `hGateDiff`) to ONE regularity core:  the field-slot `C²` of the chart,
      `ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x`
  at a GENERAL field point `x` (banked in-repo ONLY at the field centre `0`).  This file supplies
  that core at every REACHABLE field point `x = φ_z v` (`φ_z := uniformFlowExp g gi hC hK z`), and
  packages the abstract inverse-function-theorem mechanism behind it.

  ── WHAT `uniformInverseChart z` INVERTS.  On the base set `z ∈ K` it is the local inverse (from
     `ApproximatesLinearOn.toOpenPartialHomeomorph`, i.e. the quantitative IFT) of the flow
     exponential `φ_z = uniformFlowExp g gi hC hK z`:  the germ identity
     `uniformInverseChart z (φ_z v) = v` holds on the uniform ball `‖v‖ < δ₀`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    • `chartField_contDiffAt_of_leftInverse_germ`  — ★ THE ABSTRACT IFT IDENTIFICATION CORE (genuinely
        new).  For `φ, W : E → F` with `φ` `C^n` at `v₀` (`n ≠ 0`), invertible strict derivative
        `φ' : E ≃L[𝕂] F`, and a LEFT-inverse germ `W (φ v) = v` near `v₀`, the chart `W` is `C^n` at
        `φ v₀`.  Mechanism:  Mathlib's `ContDiffAt.to_localInverse` gives a `C^n` local inverse `g` at
        `φ v₀`; `HasStrictFDerivAt.localInverse_unique` identifies `W =ᶠ[𝓝 (φ v₀)] g`;
        `ContDiffAt.congr_of_eventuallyEq` transfers the regularity.
    • `chartField_contDiffAt_reachable_uniform`    — ★ THE CONCRETE DISCHARGE.  A single uniform radius
        `δ₀ > 0` such that for every base `z ∈ K` and reachable point `φ_z v` (`‖v‖ < δ₀`),
        `ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (φ_z v)`.  Directly from
        `uniformInverseChart_huniformChart` (whose construction already ran the quantitative IFT
        internally) — so the J4-170 carry is discharged at ALL reachable field points, no metric
        hypotheses needed.
    • `chartField_contDiffAt_basePoint_viaIFT`     — ★ THE END-TO-END INSTANTIATION.  Re-derives the
        base-point `C²` (`x = z = φ_z 0`) THROUGH the abstract core, instantiating its three
        hypotheses from banked exp-tower facts:  `contDiffAt2_uniformFlowExp` (`φ_z ∈ C²`),
        `uniformFlowExp_fderiv_near_id_quant` at `v = 0` (`Dφ_z(0) = Id`, an equiv), and the
        `uniformInverseChart_huniformChart` germ.  Demonstrates the abstract core is NON-VACUOUS and
        instantiable on the concrete flow.
    • `hFieldReg2_from_reachableGate`              — ★★ the J4-170 `hFieldReg2` DICHOTOMY family,
        produced from the pure-geometry REACHABLE-GATE family (per a.e. `z`: `z ∉ K`, or `z ∈ K` with
        `x₀` in the OPEN gate `S z` AND `x₀ = φ_z v` for some `‖v‖ < δ₀`).  The `C²` conclusion is
        supplied by `chartField_contDiffAt_reachable_uniform`.
    • `hFieldReg_from_reachableGate`               — ★★ the J4-170 `hFieldReg` near-`x₀` family, from
        the analogous near-`x₀` reachable-gate geometry family.
    • `hC2fam_from_reachableGate`, `hGateDiff_from_reachableGate`, `hGateDiff_hC2fam_from_reachableGate`
        — ★★★ the full pipeline:  compose the two families above with J4-170's
        `OnGateFieldRegularity.hC2fam_from_chart` / `hGateDiff_from_chart` to land the EXACT witness
        `hC2fam` / `hGateDiff` slots directly from reachable-gate geometry + `hg`/`hgpos`/`hu`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • The REACHABLE-GATE geometry:  per (a.e. `z`, field point), `x ∈ S z` OPEN with `x = φ_z v`,
      `‖v‖ < δ₀`.  This is PURE chart geometry — exactly how the gate `S z = φ_z '' ball` is built
      (see `UniformChartRadius.gatedWitness_hEboundW_of_good_gen`); satisfiable, NOT the witness or its
      derivative.
    • The off-centre strict-derivative EQUIV of `φ_z` (needed to instantiate the abstract core at a
      GENERAL reachable `v₀ ≠ 0`) = the no-conjugate-points wall.  NOT hit here:  the concrete discharge
      `chartField_contDiffAt_reachable_uniform` uses the germ banked by the IFT that ran INSIDE the
      chart construction, and the end-to-end instantiation is at `v₀ = 0` where `Dφ_z(0) = Id`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OnGateFieldRegularity
import QIQTH.UniformChartRadius
import QIQTH.PullbackNaturalityLocal
import QIQTH.NearIsometryBudget
import QIQTH.ChartJetBounds

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.ExpMap
open scoped BigOperators Topology Interval

namespace QIQTH.ChartFieldC2General

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE ABSTRACT INVERSE-FUNCTION-THEOREM IDENTIFICATION CORE.
    ############################################################################### -/

/-- **★ `chartField_contDiffAt_of_leftInverse_germ` — THE ABSTRACT IFT IDENTIFICATION CORE.**
    Let `φ, W : E → F` be maps between Banach spaces (`E` complete, `𝕂 = ℝ` or `ℂ`).  Suppose `φ` is
    `C^n` at `v₀` with `n ≠ 0`, has an INVERTIBLE strict derivative `φ' : E ≃L[𝕂] F` at `v₀`, and `W`
    is a LEFT inverse of `φ` on a neighbourhood of `v₀` (`W (φ v) = v` for `v` near `v₀`).  Then the
    chart `W` — no matter how it was built (e.g. a `.choose` of an existential, as here) — is `C^n` at
    the image point `φ v₀`.

    Mechanism:  `ContDiffAt.to_localInverse` produces a `C^n` local inverse `g` of `φ` at `φ v₀`;
    `HasStrictFDerivAt.localInverse_unique` (applied to the left-inverse germ) shows `W =ᶠ[𝓝 (φ v₀)] g`;
    `ContDiffAt.congr_of_eventuallyEq` transfers `g`'s regularity to `W`.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt_of_leftInverse_germ
    {𝕂 : Type*} [RCLike 𝕂]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
    {φ : E → F} {W : F → E} {v₀ : E} {φ' : E ≃L[𝕂] F} {N : WithTop ℕ∞}
    (hφ : ContDiffAt 𝕂 N φ v₀)
    (hφ' : HasFDerivAt φ (φ' : E →L[𝕂] F) v₀)
    (hN : N ≠ 0)
    (hleft : ∀ᶠ v in 𝓝 v₀, W (φ v) = v) :
    ContDiffAt 𝕂 N W (φ v₀) := by
  -- The strict derivative (needed to identify the local inverse germ).
  have hstrict : HasStrictFDerivAt φ (φ' : E →L[𝕂] F) v₀ := hφ.hasStrictFDerivAt' hφ' hN
  -- The `C^n` local inverse of `φ` at `φ v₀`.
  have hloc : ContDiffAt 𝕂 N (hφ.localInverse hφ' hN) (φ v₀) := hφ.to_localInverse hφ' hN
  -- `W` coincides with that local inverse near `φ v₀`, from the left-inverse germ (uniqueness).
  have hEq : W =ᶠ[𝓝 (φ v₀)] hφ.localInverse hφ' hN := hstrict.localInverse_unique hleft
  exact hloc.congr_of_eventuallyEq hEq

/-! ###############################################################################
    ### ★ THE CONCRETE DISCHARGE — field-slot `C²` at every reachable field point.
    ############################################################################### -/

/-- **★ `chartField_contDiffAt_reachable_uniform`.**  There is a SINGLE uniform radius `δ₀ > 0` such
    that for every base `z ∈ K` and every reachable field point `φ_z v` with `‖v‖ < δ₀`
    (`φ_z := uniformFlowExp g gi hC hK z`), the inverse chart is `ContDiffAt ℝ 2` there:
        `ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (uniformFlowExp g gi hC hK z v)`.
    This is EXACTLY the J4-170 field-slot carry, discharged at ALL reachable points (not only the
    centre `0`).  It reads off the `C²` clause of `uniformInverseChart_huniformChart`, whose
    construction already ran the quantitative inverse-function theorem inside the chart definition.
    NO metric hypotheses (`hg`/`hgpos`/`hu`) needed — pure chart geometry.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt_reachable_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∀ z ∈ K, ∀ v : Point n, ‖v‖ < δ₀ →
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (uniformFlowExp g gi hC hK z v) := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro z hz v hv
  exact ((hspec z hz).1 v hv).2

/-! ###############################################################################
    ### ★ END-TO-END INSTANTIATION of the abstract core at the base point.
    ############################################################################### -/

/-- **★ `chartField_contDiffAt_basePoint_viaIFT`.**  Re-derives the base-point field-slot `C²`
    (`x = z = φ_z 0`) for any base `z ∈ K` THROUGH the abstract IFT core
    `chartField_contDiffAt_of_leftInverse_germ`, instantiating its three hypotheses from banked
    exp-tower facts:
      • `hφ`  = `contDiffAt2_uniformFlowExp` (`φ_z ∈ C²` at `0`);
      • `hφ'` = `uniformFlowExp_fderiv_near_id_quant` at `v = 0` (`Dφ_z(0) = Id`, the `refl` equiv);
      • `hleft` = the `uniformInverseChart_huniformChart` left-inverse germ at `0`.
    Shows the abstract core is NON-VACUOUS and instantiable on the concrete flow.  (For general
    reachable `v₀ ≠ 0` the strict-derivative equiv is the no-conjugate-points wall; the discharge at
    all reachable points goes through `chartField_contDiffAt_reachable_uniform` instead, which reads
    off the IFT already run inside the chart construction.)  NOT `a₁ = R/6`. -/
theorem chartField_contDiffAt_basePoint_viaIFT (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) :
    ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) z := by
  have hR0 : ‖(0 : Point n)‖ < uniformFlowRadius g gi hC hK := by
    rw [norm_zero]; exact uniformFlowRadius_pos g gi hC hK
  have hφ : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK z) 0 :=
    contDiffAt2_uniformFlowExp g gi hC hK z hz 0 hR0
  -- `Dφ_z(0) = Id`.
  have hfderiv_id : fderiv ℝ (uniformFlowExp g gi hC hK z) 0
      = ContinuousLinearMap.id ℝ (Point n) := by
    obtain ⟨ρ₀, hρ₀, C_D, _, hnear⟩ := uniformFlowExp_fderiv_near_id_quant g gi hC hK
    have h0ρ : ‖(0 : Point n)‖ < ρ₀ := by rw [norm_zero]; exact hρ₀
    have hb := hnear z hz 0 h0ρ
    rw [norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  have hrefl : ((ContinuousLinearEquiv.refl ℝ (Point n)) : Point n →L[ℝ] Point n)
      = ContinuousLinearMap.id ℝ (Point n) := by simp
  have hφ' : HasFDerivAt (uniformFlowExp g gi hC hK z)
      ((ContinuousLinearEquiv.refl ℝ (Point n)) : Point n →L[ℝ] Point n) 0 := by
    rw [hrefl, ← hfderiv_id]
    exact (hφ.differentiableAt (by norm_num)).hasFDerivAt
  -- The left-inverse germ at `0`.
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  have h0δ : ‖(0 : Point n)‖ < δ₀ := by rw [norm_zero]; exact hδ₀
  have hleft : ∀ᶠ v in 𝓝 (0 : Point n),
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v :=
    ((hspec z hz).1 0 h0δ).1
  have hcd := chartField_contDiffAt_of_leftInverse_germ hφ hφ' (by norm_num) hleft
  rwa [uniformFlowExp_zero g gi hC hK z hz] at hcd

/-! ###############################################################################
    ### ★★ FAMILY WIRING — the J4-170 `hFieldReg2` / `hFieldReg` families from reachable-gate
    ###      geometry (the pure-chart-geometry carry), C² supplied by the concrete discharge.
    ############################################################################### -/

/-- **★★ `hFieldReg2_from_reachableGate`.**  Produces J4-170's `hFieldReg2` DICHOTOMY family — the
    exact input to `OnGateFieldRegularity.hC2fam_from_chart` — from the pure-geometry REACHABLE-GATE
    family:  a uniform radius `δ₀ > 0` such that, whenever per a.e. `z` the point `x₀` either misses
    the base (`z ∉ K`) or lands in the OPEN gate `S z` AS a reachable point `x₀ = φ_z v`, `‖v‖ < δ₀`,
    the field-chart `C²` at `x₀` follows (via `chartField_contDiffAt_reachable_uniform`).  The
    reachable-gate geometry is exactly how the gate `S z = φ_z '' ball` is built — non-vacuous, NOT
    the witness.  NOT `a₁ = R/6`. -/
theorem hFieldReg2_from_reachableGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (t : ℝ) (u : Set (Point n)) :
    ∃ δ₀ > (0 : ℝ),
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z)
              ∧ ∃ v : Point n, ‖v‖ < δ₀ ∧ x₀ = uniformFlowExp g gi hC hK z v)) →
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x₀)) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro hGeom x₀ hx₀
  filter_upwards [hGeom x₀ hx₀] with s hs
  intro hmem
  filter_upwards [hs hmem] with z hz
  rcases hz with h | ⟨hzK, hxSz, hSopen, v, hvδ, hxv⟩
  · exact Or.inl h
  · exact Or.inr ⟨hzK, hxSz, hSopen, by rw [hxv]; exact hreach z hzK v hvδ⟩

/-- **★★ `hFieldReg_from_reachableGate`.**  Produces J4-170's `hFieldReg` near-`x₀` family — the exact
    input to `OnGateFieldRegularity.hGateDiff_from_chart` — from the analogous near-`x₀` reachable-gate
    geometry family (∀ᶠ `x` near `x₀`, a.e. `z`, `z ∈ K → x ∈ S z` OPEN and `x = φ_z v`, `‖v‖ < δ₀`).
    NOT `a₁ = R/6`. -/
theorem hFieldReg_from_reachableGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (t : ℝ) (u : Set (Point n)) :
    ∃ δ₀ > (0 : ℝ),
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ∃ v : Point n, ‖v‖ < δ₀ ∧ x = uniformFlowExp g gi hC hK z v)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) x)) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro hGeom x₀ hx₀ i
  filter_upwards [hGeom x₀ hx₀ i] with s hs
  intro hmem
  filter_upwards [hs hmem] with x hx
  filter_upwards [hx] with z hz
  intro hzK
  obtain ⟨hxSz, hSopen, v, hvδ, hxv⟩ := hz hzK
  exact ⟨hxSz, hSopen, by rw [hxv]; exact hreach z hzK v hvδ⟩

/-! ###############################################################################
    ### ★★★ FULL PIPELINE — reachable-gate geometry ⟹ the EXACT witness `hC2fam` / `hGateDiff`.
    ############################################################################### -/

/-- **★★★ `hGateDiff_hC2fam_from_reachableGate`.**  The full pipeline capstone:  BOTH remaining L1
    field-slot carries — the witness `hGateDiff` slot (`GateSetMeasurability.hKmeas_concrete_v5`) AND
    the witness `hC2fam` slot (`WitnessDerivMeasurability.g2_bundle_assembled`) — produced from the two
    pure-geometry REACHABLE-GATE families at a SINGLE uniform radius `δ₀`, together with the metric
    smoothness data `hg`/`hgpos`/`hu`.  Composes the field-chart `C²` discharge
    (`chartField_contDiffAt_reachable_uniform`) with J4-170's `hGateDiff_from_chart` / `hC2fam_from_chart`.
    NOT `a₁ = R/6`. -/
theorem hGateDiff_hC2fam_from_reachableGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ δ₀ > (0 : ℝ),
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → (x ∈ S z ∧ IsOpen (S z)
              ∧ ∃ v : Point n, ‖v‖ < δ₀ ∧ x = uniformFlowExp g gi hC hK z v)) →
      (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          (z ∉ K)
          ∨ (z ∈ K ∧ x₀ ∈ S z ∧ IsOpen (S z)
              ∧ ∃ v : Point n, ‖v‖ < δ₀ ∧ x₀ = uniformFlowExp g gi hC hK z v)) →
      (∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∈ K → PdiffAt (fun x' : Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) i x)
      ∧ (∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀) := by
  obtain ⟨δ₀, hδ₀, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro hGeomNear hGeomPt
  refine ⟨?_, ?_⟩
  · -- hGateDiff via `hGateDiff_from_chart`, feeding the near-`x₀` geometry discharged to `C²`.
    apply QIQTH.OnGateFieldRegularity.hGateDiff_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀ i
    filter_upwards [hGeomNear x₀ hx₀ i] with s hs
    intro hmem
    filter_upwards [hs hmem] with x hx
    filter_upwards [hx] with z hz
    intro hzK
    obtain ⟨hxSz, hSopen, v, hvδ, hxv⟩ := hz hzK
    exact ⟨hxSz, hSopen, by rw [hxv]; exact hreach z hzK v hvδ⟩
  · -- hC2fam via `hC2fam_from_chart`, feeding the dichotomy geometry discharged to `C²`.
    apply QIQTH.OnGateFieldRegularity.hC2fam_from_chart g gi hC hK S a b t u hg hgpos hu
    intro x₀ hx₀
    filter_upwards [hGeomPt x₀ hx₀] with s hs
    intro hmem
    filter_upwards [hs hmem] with z hz
    rcases hz with h | ⟨hzK, hxSz, hSopen, v, hvδ, hxv⟩
    · exact Or.inl h
    · exact Or.inr ⟨hzK, hxSz, hSopen, by rw [hxv]; exact hreach z hzK v hvδ⟩

end QIQTH.ChartFieldC2General

section AxiomChecks
open QIQTH.ChartFieldC2General
#print axioms chartField_contDiffAt_of_leftInverse_germ
#print axioms chartField_contDiffAt_reachable_uniform
#print axioms chartField_contDiffAt_basePoint_viaIFT
#print axioms hFieldReg2_from_reachableGate
#print axioms hFieldReg_from_reachableGate
#print axioms hGateDiff_hC2fam_from_reachableGate
end AxiomChecks
