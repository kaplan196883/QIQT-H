/-
  ChartFieldJacobian — J4-433: the chart FIELD-slot Jacobian base-continuity — the J3-blocker attack.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE OBJECT (J4-432 `BaseSlotAmpDeriv`).  The whole derivative-sup wall of the a₁ = R/6
  sup/constant family reduces to ONE atomic carry:
        `ContinuousOn (fun z => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U`
  — the JOINT-in-base continuity of the chart FIELD-slot Jacobian at the field centre `0`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE J3 DIAGNOSIS.

  ### WHAT `uniformInverseChart` IS.  `W z := uniformInverseChart g gi hC hK z` is a
  `Classical.choose`-built object (`UniformChartRadius.uniformInverseChart` = the `.choose` of the
  per-base partial-homeomorph inverse produced by `uniformChart_exists`).  Structurally it is the
  LOCAL INVERSE of the geodesic-flow endpoint map
        `φ_z := uniformFlowExp g gi hC hK z`,
  which is ITSELF a `.choose` over an EXPOSED geodesic ODE (`uniformFlowTube`, CASE C in the
  FlowJointRegularity taxonomy).  The only access to `W z` is its spec lemma
  `uniformInverseChart_huniformChart`: the LEFT-INVERSE germ `W z (φ_z v) = v` on `‖v‖ < δ₀` and the
  per-base field-centre `C²` (THE `.choose` LESSON — spec lemma only).

  ### WHICH ROUTE.  This is route **(c) IMPLICIT / `.choose` inverse — the inverse-function-theorem
  route**.  `W z` is (locally) the inverse of the jointly-defined forward flow `φ_z`, so the chart
  field-slot Jacobian is IDENTIFIED, at the field centre, by the IFT-Jacobian formula
        `fderiv ℝ (W z) 0 = (fderiv ℝ φ_z (W z 0))⁻¹`      (as a ring element of `Point n →L[ℝ] Point n`)
  (valid because `φ_z (W z 0) = 0` by the right-inverse `chartW0_rightInverse`, and `Dφ_z(W z 0)` is
  invertible in the uniform nondegeneracy ball `uniformFlowExp_common_nondeg_radius`).  This file
  PROVES that identity (`chartFieldJacobian_eq_ringInverse`, via the abstract Mathlib core
  `fderiv_localLeftInverse_eq_ringInverse`) and then REDUCES the J3 base-continuity to the ONE
  geometric ingredient the identity exposes.

  ### THE OUTCOME — REDUCED (route (c) collapses J3 to a single geometry-only forward carry).
  Because `Ring.inverse` is continuous at units (`contDiffAt_ringInverse`) and `z ↦ W z 0` is
  base-continuous (banked: `GeodesicGronwall.chartOrigin_continuousOn`), the base-continuity of the
  chart field-Jacobian follows from the base-continuity of
        `z ↦ fderiv ℝ φ_z (W z 0)`,
  which is exactly the FORWARD-flow first-jet evaluated along the (continuous) origin section — i.e.
  the JOINT-in-`(z,v)` continuity of the forward-flow Jacobian
        `(z, v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v`.
  That IS the recognized J3 base-point-regularity residue (`FlowJointRegularity` audit §3: there is NO
  `ContinuousOn`/`ContDiff` fact about the joint forward flow in the `.choose` tower — only per-fixed-`z`
  velocity `ContDiffAt` and the conditional `δ=0` base Fréchet derivative of `BasepointFDeriv`).  It is
  GEOMETRY-ONLY (a true fact about the geodesic flow), NOT a modular/analytic TODO — the honest missing
  ingredient for Sol #21.

  ── WHAT LANDS.
    • `fderiv_localLeftInverse_eq_ringInverse` — ★ THE ABSTRACT IFT-JACOBIAN IDENTITY (pure Mathlib):
        a local left-inverse germ + invertible forward derivative ⟹ the inverse's Jacobian is the
        ring inverse of the forward Jacobian.
    • `chartFieldJacobian_eq_ringInverse` — ★★ the concrete chart IFT-Jacobian identity at the field
        centre, from banked per-`z` regularity facts (germ / reachable `C²` / forward `C²` / nondeg /
        right-inverse).
    • `chartFieldJacobian_facts_of_small` — the provider: the five per-`z` regularity facts, all
        discharged from banked lemmas under an explicit smallness of `‖W z 0‖` and `‖z‖`.
    • `chartFieldJacobian_continuousOn_of_forwardJointCont` — ★★★ THE REDUCTION (= `jacobian_
        continuity_of_forward`).  The J3 base-continuity of the chart field-Jacobian, REDUCED to the
        forward-flow Jacobian's joint-in-base continuity + the banked origin-section continuity + the
        (identity-supplied) invertibility.

  ── hcont1 / hcont2 STATUS.  Via `BaseSlotAmpDeriv.pd_chartAmp_center_eq`, hcont1 (first field
  derivative sup) reduces to THIS first-order chart field-Jacobian continuity — so hcont1 is now
  reachable from the FIRST-order forward joint continuity.  hcont2 (second field derivative sup) needs
  the SECOND-order analogue: base-continuity of `z ↦ fderiv² (W z) 0`, whose IFT identity involves the
  forward SECOND jet `(z,v) ↦ fderiv² φ_z v` jointly — a strictly higher (second-order) forward-joint
  carry, stated honestly here, NOT discharged.

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.ChartFieldC2General
import QIQTH.GeodesicGronwall
import QIQTH.ResidueThreading
import QIQTH.UniformFlowNondegClose
import QIQTH.NearIsometryBudget

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.GeodesicGronwall
open QIQTH.ChartFieldC2General
open scoped Topology

namespace QIQTH.ChartFieldJacobian

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE ABSTRACT IFT-JACOBIAN IDENTITY (pure Mathlib).
    ############################################################################### -/

/-- **★ `fderiv_localLeftInverse_eq_ringInverse` — the abstract IFT-Jacobian identity.**  Let
    `φ, W : E → E` on a normed `ℝ`-space, `v₀ : E`, with `φ` differentiable at `v₀`, `W` differentiable
    at `φ v₀`, a LEFT-inverse germ `W (φ v) = v` near `v₀`, and an INVERTIBLE forward derivative
    `IsUnit (fderiv ℝ φ v₀)`.  Then the inverse's Jacobian at the image point is the ring inverse of the
    forward Jacobian:
        `fderiv ℝ W (φ v₀) = Ring.inverse (fderiv ℝ φ v₀)`     (in the ring `E →L[ℝ] E`).
    Mechanism: the chain rule + the germ give `(fderiv W (φ v₀)) * (fderiv φ v₀) = 1`, and a left inverse
    of a unit equals its inverse.  NOT `a₁ = R/6`. -/
theorem fderiv_localLeftInverse_eq_ringInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ W : E → E} {v₀ : E}
    (hφd : DifferentiableAt ℝ φ v₀)
    (hWd : DifferentiableAt ℝ W (φ v₀))
    (hgerm : ∀ᶠ v in 𝓝 v₀, W (φ v) = v)
    (hunit : IsUnit (fderiv ℝ φ v₀)) :
    fderiv ℝ W (φ v₀) = Ring.inverse (fderiv ℝ φ v₀) := by
  have hcomp : fderiv ℝ (W ∘ φ) v₀ = (fderiv ℝ W (φ v₀)).comp (fderiv ℝ φ v₀) :=
    fderiv_comp v₀ hWd hφd
  have hEq : (W ∘ φ) =ᶠ[𝓝 v₀] id := by
    filter_upwards [hgerm] with v hv using hv
  have hid : fderiv ℝ (W ∘ φ) v₀ = ContinuousLinearMap.id ℝ E := by
    rw [hEq.fderiv_eq]; simp
  have hmul1 : (fderiv ℝ W (φ v₀)) * (fderiv ℝ φ v₀) = 1 := by
    have hcc : (fderiv ℝ W (φ v₀)).comp (fderiv ℝ φ v₀) = ContinuousLinearMap.id ℝ E := by
      rw [← hcomp, hid]
    rw [ContinuousLinearMap.mul_def, hcc, ContinuousLinearMap.one_def]
  calc fderiv ℝ W (φ v₀)
      = (fderiv ℝ W (φ v₀)) * ((fderiv ℝ φ v₀) * Ring.inverse (fderiv ℝ φ v₀)) := by
        rw [Ring.mul_inverse_cancel _ hunit, mul_one]
    _ = ((fderiv ℝ W (φ v₀)) * (fderiv ℝ φ v₀)) * Ring.inverse (fderiv ℝ φ v₀) := by rw [mul_assoc]
    _ = Ring.inverse (fderiv ℝ φ v₀) := by rw [hmul1, one_mul]

/-! ###############################################################################
    ### ★★ THE CONCRETE CHART IFT-JACOBIAN IDENTITY (at the field centre).
    ############################################################################### -/

/-- **★★ `chartFieldJacobian_eq_ringInverse` — the concrete chart IFT-Jacobian identity.**  For a base
    `z` with the banked per-`z` regularity facts (forward `φ_z` differentiable at `W z 0`, inverse chart
    `W z` differentiable at `0`, the left-inverse germ at `W z 0`, the right-inverse `φ_z (W z 0) = 0`,
    and `Dφ_z(W z 0)` a unit), the chart field-slot Jacobian at the field centre `0` is the ring inverse
    of the forward Jacobian at the origin section:
        `fderiv ℝ (W z) 0 = Ring.inverse (fderiv ℝ φ_z (W z 0))`.
    Immediate from `fderiv_localLeftInverse_eq_ringInverse` at `v₀ = W z 0`, rewriting `φ_z (W z 0) = 0`.
    NOT `a₁ = R/6`. -/
theorem chartFieldJacobian_eq_ringInverse (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hφd : DifferentiableAt ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0))
    (hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0)
    (hgerm : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hRI : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0)
    (hunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0))) :
    fderiv ℝ (uniformInverseChart g gi hC hK z) 0
      = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0)) := by
  have hWd' : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z)
      (uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0)) := by
    rw [hRI]; exact hWd
  have h := fderiv_localLeftInverse_eq_ringInverse (φ := uniformFlowExp g gi hC hK z)
    (W := uniformInverseChart g gi hC hK z) (v₀ := uniformInverseChart g gi hC hK z 0)
    hφd hWd' hgerm hunit
  rwa [hRI] at h

/-- **`chartFieldJacobian_facts_of_small` — the provider of the five per-`z` regularity facts.**  All
    of `hφd`/`hWd`/`hgerm`/`hRI`/`hunit` (the inputs of `chartFieldJacobian_eq_ringInverse`) are
    DISCHARGED from banked lemmas, given `z ∈ K`, a norm bound `‖z‖ < r_RI` (for the right-inverse
    `chartW0_rightInverse`) and a single smallness `‖W z 0‖ < ρm` where `ρm` is the minimum of the
    banked radii: the germ / reachable-`C²` radius (`uniformInverseChart_huniformChart`), the
    forward-flow `C²` radius (`uniformFlowRadius`), and the uniform nondegeneracy radius
    (`uniformFlowExp_common_nondeg_radius`).  Each fact is a genuine geometric statement, none vacuous.
    NOT `a₁ = R/6`. -/
theorem chartFieldJacobian_facts_of_small (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (hz : z ∈ K) :
    ∃ rRI > (0 : ℝ), ∃ ρm > (0 : ℝ),
      ‖z‖ < rRI → ‖uniformInverseChart g gi hC hK z 0‖ < ρm →
        DifferentiableAt ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)
        ∧ DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0
        ∧ (∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
            uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
        ∧ uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0
        ∧ IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)) := by
  obtain ⟨rRI, hrRI, hRIspec⟩ := chartW0_rightInverse g gi hC hK
  obtain ⟨δg, hδg, hgermspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δr, hδr, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨ρnd, hρnd, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  set ρm : ℝ := min (min δg δr) (min (uniformFlowRadius g gi hC hK) ρnd) with hρmdef
  have hρmpos : 0 < ρm := by
    rw [hρmdef]; exact lt_min (lt_min hδg hδr) (lt_min (uniformFlowRadius_pos g gi hC hK) hρnd)
  refine ⟨rRI, hrRI, ρm, hρmpos, fun hzr hsmall => ?_⟩
  set v₀ : Point n := uniformInverseChart g gi hC hK z 0 with hv₀
  have hv₀δg : ‖v₀‖ < δg := lt_of_lt_of_le hsmall (le_trans (min_le_left _ _) (min_le_left _ _))
  have hv₀δr : ‖v₀‖ < δr := lt_of_lt_of_le hsmall (le_trans (min_le_left _ _) (min_le_right _ _))
  have hv₀R : ‖v₀‖ < uniformFlowRadius g gi hC hK :=
    lt_of_lt_of_le hsmall (le_trans (min_le_right _ _) (min_le_left _ _))
  have hv₀nd : ‖v₀‖ < ρnd := lt_of_lt_of_le hsmall (le_trans (min_le_right _ _) (min_le_right _ _))
  -- right inverse
  have hRI : uniformFlowExp g gi hC hK z v₀ = 0 := hRIspec z hz hzr
  -- forward C² ⟹ differentiable at v₀
  have hφd : DifferentiableAt ℝ (uniformFlowExp g gi hC hK z) v₀ :=
    (contDiffAt2_uniformFlowExp g gi hC hK z hz v₀ hv₀R).differentiableAt (by norm_num)
  -- reachable C² of W z at φ_z v₀ = 0 ⟹ differentiable at 0
  have hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0 := by
    have hcd := hreach z hz v₀ hv₀δr
    rw [hRI] at hcd
    exact hcd.differentiableAt (by norm_num)
  -- germ at v₀
  have hgerm : ∀ᶠ v in 𝓝 v₀,
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
    have hg := ((hgermspec z hz).1 v₀ hv₀δg).1
    filter_upwards [hg] with v hv using hv
  -- nondegeneracy at v₀
  have hunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) v₀) := hnondeg z hz v₀ hv₀nd
  exact ⟨hφd, hWd, hgerm, hRI, hunit⟩

/-! ###############################################################################
    ### ★★★ THE REDUCTION — J3 base-continuity ⟸ forward joint continuity.
    ############################################################################### -/

/-- **★★★ `chartFieldJacobian_continuousOn_of_forwardJointCont` — THE J3 REDUCTION**
    (`= jacobian_continuity_of_forward`).  The base-continuity of the chart FIELD-slot Jacobian at the
    field centre `0`,
        `ContinuousOn (fun z => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U`,
    is REDUCED to three inputs on `U`:
      • `hW0`   — base-continuity of the origin section `z ↦ W z 0` (banked:
                  `GeodesicGronwall.chartOrigin_continuousOn` under its geometric side-conditions);
      • `hFwd`  — the JOINT-in-`(z,v)` continuity of the FORWARD-flow first jet
                  `(z, v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v` on `U ×ˢ univ`
                  (the recognized J3 base-point-regularity residue — GEOMETRY-ONLY, the precise missing
                  ingredient for Sol #21);
      • `hunit` — invertibility of `Dφ_z(W z 0)` on `U` (from the uniform nondegeneracy ball);
      • `hIFT`  — the IFT-Jacobian identity on `U` (supplied by `chartFieldJacobian_eq_ringInverse`).
    Mechanism: `hIFT` rewrites the target to `Ring.inverse (fderiv φ_z (W z 0))`; the inner map is
    `hFwd ∘ (z ↦ (z, W z 0))` (continuous via `hW0`), and `Ring.inverse` is continuous at each unit
    value (`contDiffAt_ringInverse`).  NOT `a₁ = R/6`. -/
theorem chartFieldJacobian_continuousOn_of_forwardJointCont (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {U : Set (Point n)}
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) U)
    (hFwd : ContinuousOn
      (fun p : Point n × Point n => fderiv ℝ (uniformFlowExp g gi hC hK p.1) p.2)
      (U ×ˢ Set.univ))
    (hunit : ∀ z ∈ U, IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hIFT : ∀ z ∈ U, fderiv ℝ (uniformInverseChart g gi hC hK z) 0
      = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
          (uniformInverseChart g gi hC hK z 0))) :
    ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U := by
  -- the origin-section pairing `z ↦ (z, W z 0)` is continuous into `U ×ˢ univ`.
  have hpair : ContinuousOn
      (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U :=
    continuousOn_id.prodMk hW0
  have hmaps : Set.MapsTo (fun z : Point n => (z, uniformInverseChart g gi hC hK z 0)) U
      (U ×ˢ Set.univ) := fun z hz => ⟨hz, Set.mem_univ _⟩
  -- the inner forward-Jacobian along the origin section is continuous on `U`.
  have hinner : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0)) U :=
    hFwd.comp hpair hmaps
  -- `Ring.inverse` of the inner map is continuous on `U` (continuity at each unit value).
  have hRinv : ContinuousOn
      (fun z : Point n => Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0))) U := by
    intro z₀ hz₀
    obtain ⟨u₀, hu₀⟩ := hunit z₀ hz₀
    have hca : ContinuousAt Ring.inverse
        (fderiv ℝ (uniformFlowExp g gi hC hK z₀) (uniformInverseChart g gi hC hK z₀ 0)) := by
      rw [← hu₀]; exact (contDiffAt_ringInverse (n := 1) ℝ u₀).continuousAt
    -- compose through `Tendsto.comp` (robust unification: inner determined by `hinner`).
    exact hca.tendsto.comp (hinner z₀ hz₀)
  -- transfer through the IFT identity.
  exact hRinv.congr hIFT

end QIQTH.ChartFieldJacobian

/-! ## THE J3 LEDGER (post J4-433).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  BEFORE (J4-432):  the derivative sups `C₁`/`C₂`/`M₁chart`/`M₂chart` were GROUNDED-CONDITIONAL on │
  │  the OPAQUE joint-base continuity of the `.choose`-built chart field-Jacobian                     │
  │      `ContinuousOn (z ↦ fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U`.                        │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  AFTER (J4-433):  via route (c) (IFT / `.choose` inverse) that carry is REDUCED, by               │
  │  `chartFieldJacobian_continuousOn_of_forwardJointCont`, to the GEOMETRY-ONLY forward carry         │
  │      `hFwd : ContinuousOn ((z,v) ↦ fderiv ℝ (uniformFlowExp g gi hC hK z) v) (U ×ˢ univ)`         │
  │  (plus the BANKED origin-section continuity `chartOrigin_continuousOn` and the identity/nondeg,    │
  │   which `chartFieldJacobian_eq_ringInverse` + `chartFieldJacobian_facts_of_small` discharge).      │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE MISSING INGREDIENT (Sol #21).  `hFwd` = joint-in-base continuity of the FORWARD-flow first    │
  │  jet.  FlowJointRegularity audit §3: the `.choose` tower exposes NO `ContinuousOn`/`ContDiff` fact │
  │  of the joint forward flow — only per-fixed-`z` velocity `ContDiffAt` and `BasepointFDeriv`'s      │
  │  conditional `δ=0` base Fréchet derivative.  `hFwd` is a TRUE geodesic-flow fact (smooth           │
  │  dependence on initial conditions); Mathlib's ODE layer has Grönwall + Picard–Lindelöf existence   │
  │  but NOT the joint-`C¹`/continuous dependence of the flow Jacobian on initial data — so `hFwd`     │
  │  is the honest carry.  Recommended discharge: the nonlinear two-solution Grönwall on the FIRST-    │
  │  VARIATION (Jacobi) equation over the compact confinement region (the `fderiv`-analogue of         │
  │  `chart_joint_velocity_modulus` / `uniformFlowExp_base_diff_bound`).                               │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  hcont1 (first field-derivative sup):  reachable from `hFwd` (FIRST order) via                     │
  │      `BaseSlotAmpDeriv.pd_chartAmp_center_eq` + this reduction.                                    │
  │  hcont2 (second field-derivative sup):  needs the SECOND-order analogue — base-continuity of        │
  │      `z ↦ fderiv² (W z) 0`, whose IFT identity involves the FORWARD SECOND jet                      │
  │      `(z,v) ↦ fderiv² (uniformFlowExp g gi hC hK z) v` jointly — a strictly higher forward-joint   │
  │      carry (not discharged here).                                                                 │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.ChartFieldJacobian
#print axioms fderiv_localLeftInverse_eq_ringInverse
#print axioms chartFieldJacobian_eq_ringInverse
#print axioms chartFieldJacobian_facts_of_small
#print axioms chartFieldJacobian_continuousOn_of_forwardJointCont
end AxiomChecks
