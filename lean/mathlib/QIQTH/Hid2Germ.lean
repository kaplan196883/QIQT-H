/-
  Hid2Germ — J4-489: discharging the 2nd-order IFT residue `hid2` — the RIGHT-inverse germ.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3
  only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  J4-488 (`C2CarrierCollapse.supConstant_phase5`) collapsed SIX of the seven standing
  geometric carriers of the C₂ derivative-sup family to a statement resting on (I1) `hReach` PLUS the
  SINGLE isolated residue `hid2` — the per-`z` SECOND-order IFT identity
      `fderiv ℝ (fun y => fderiv ℝ (W_z) y) 0 = E_z`   (`E_z` the 2nd-order ring-inverse expression),
  which `ChartSecondJet.chartSecondJet_eq_of_forward2` proves from FIVE per-`z` carries.  Four are
  banked (`W_z` diff at `0`; `φ_z` twice-diff at `W_z 0`; `φ_z (W_z 0) = 0`; `Dφ_z(W_z 0)` a unit).
  The FIFTH — the crux — is the FDERIV-germ
      `hgerm : ∀ᶠ y in 𝓝 0, fderiv ℝ W_z y = Ring.inverse (fderiv ℝ φ_z (W_z y))`,
  which in turn needs the RIGHT-inverse germ `φ_z (W_z y) = y` NEAR `0`.  The bank exposes only the
  LEFT germ `W_z (φ_z v) = v` near `W_z 0` and the POINTWISE right inverse `φ_z (W_z 0) = 0`.

  ## THE GATE (the right-germ route).  `W_z = E.symm` is the `.choose` inverse of the
  ApproximatesLinearOn OpenPartialHomeomorph `E` of the nondegenerate forward flow `φ_z`; the banked
  spec HIDES `E`, exposing only the LEFT germ.  So the right germ is recovered by a FRESH strict-IFT
  invocation on the nondegenerate `φ_z`: from `φ_z ∈ C²` at `W_z 0` (`contDiffAt2_uniformFlowExp`) and
  `IsUnit (Dφ_z(W_z 0))` (`uniformFlowExp_common_nondeg_radius`) — BOTH already used by
  `c2_carriers_discharged` — build `HasStrictFDerivAt φ_z (↑fev) (W_z 0)` with the derivative equiv
  `fev`, then Mathlib's `HasStrictFDerivAt.localInverse_unique` shows the banked left inverse `W_z`
  AGREES near `0` with the strict-IFT local inverse `L` (`W_z =ᶠ L`), and
  `HasStrictFDerivAt.eventually_right_inverse` gives `φ_z (L y) = y` near `0`; hence `φ_z (W_z y) = y`
  near `0`.  A local diffeo has BOTH germs — the right germ is a THEOREM OF THE BANK, needing NO input
  beyond it.  So `hid2` is NOT a new physical/geometric input; it FOLDS AWAY, and C₂ rests on (I1)
  `hReach` alone (+ the banked convergence trio / geometric wiring).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `chartRightInverse_germ` — ★ THE RIGHT-INVERSE GERM `φ_z (W_z y) = y` near `0`, from the strict
      IFT (`localInverse_unique` + `eventually_right_inverse`) on the nondegenerate `φ_z`.
    * `chartFDerivInverse_germ` — ★ the FDERIV-germ `fderiv W_z y = Ring.inverse (fderiv φ_z (W_z y))`
      near `0`, from the right germ + the per-neighbourhood first-order IFT algebra
      (`fderiv_localLeftInverse_eq_ringInverse`).
    * `hid2_discharged` — ★★ the per-`z` 2nd-order IFT identity `= E_z` (the `hid2` shape), assembled
      from the fderiv-germ via `chartSecondJet_eq_of_forward2`.
    * `supConstant_phase6` — ★★★ the sup family, phase 6: on a CONCRETE small ball, `C₀`/`C₁`/`C₂` are
      grounded from (I1) `hReach` ALONE — the SIX geometric carriers AND the 2nd-order residue `hid2`
      are all supplied INTERNALLY from the bank.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion): (I1) `hReach` ONLY (at the C₂
    derivative-sup level).  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1), the banked
    convergence trio, and the geometric wiring).
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.C2CarrierCollapse

open Filter Set
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.ChartFieldC2General QIQTH.GeodesicGronwall QIQTH.JacobiCLMExposure
open QIQTH.ChartFieldJacobian QIQTH.ChartSecondJet QIQTH.AmplitudeSecondJet
open QIQTH.SupFamilyFirstOrder QIQTH.SupConstantFamily QIQTH.AmplitudeDataOnCollar
open QIQTH.HrepGermFactorization QIQTH.C2CarrierCollapse
open scoped Topology ContDiff

namespace QIQTH.Hid2Germ

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ THE RIGHT-INVERSE GERM — `φ_z (W_z y) = y` near `0` (the fresh strict IFT).
    ############################################################################### -/

/-- **★ `chartRightInverse_germ` — the RIGHT-inverse germ near the field centre.**  For a base `z`
    with `φ_z := uniformFlowExp … z` of class `C²` at `W_z 0` (`W_z := uniformInverseChart … z`),
    invertible forward derivative `Dφ_z(W_z 0)`, the banked LEFT-inverse germ `W_z (φ_z v) = v` near
    `W_z 0`, and the pointwise right inverse `φ_z (W_z 0) = 0`, the RIGHT inverse holds in a
    NEIGHBOURHOOD of the field centre:
        `∀ᶠ y in 𝓝 0, φ_z (W_z y) = y`.
    Mechanism (the fresh strict-IFT invocation): `HasStrictFDerivAt φ_z (↑fev) (W_z 0)` from the `C²`
    + nondegeneracy (`fev` = the derivative equiv), then `HasStrictFDerivAt.localInverse_unique`
    (`W_z =ᶠ` the strict-IFT local inverse `L` near `0`) composed with
    `HasStrictFDerivAt.eventually_right_inverse` (`φ_z (L y) = y` near `0`).  NOT `a₁ = R/6`. -/
theorem chartRightInverse_germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hφC2 : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0))
    (hunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hleft : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
      uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hRI : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) :
    ∀ᶠ y in 𝓝 (0 : Point n),
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z y) = y := by
  classical
  set φ := uniformFlowExp g gi hC hK z with hφdef
  set W := uniformInverseChart g gi hC hK z with hWdef
  -- the derivative equiv at `W 0` from the unit.
  set fev : Point n ≃L[ℝ] Point n := ContinuousLinearEquiv.ofUnit hunit.unit with hfev
  have hcoev : (fev : Point n →L[ℝ] Point n) = fderiv ℝ φ (W 0) := by
    apply ContinuousLinearMap.ext; intro x
    have h1 : (fev : Point n →L[ℝ] Point n) x = (hunit.unit : Point n →L[ℝ] Point n) x := rfl
    rw [h1, hunit.unit_spec]
  -- the strict Fréchet derivative of `φ` at `W 0`.
  have hStrict0 : HasStrictFDerivAt φ (fderiv ℝ φ (W 0)) (W 0) :=
    hφC2.hasStrictFDerivAt (by norm_num)
  have hStrict : HasStrictFDerivAt φ (fev : Point n →L[ℝ] Point n) (W 0) := by
    rw [hcoev]; exact hStrict0
  -- the banked left inverse AGREES with the strict-IFT local inverse near `φ (W 0)`.
  have hWL := hStrict.localInverse_unique hleft
  -- the strict-IFT right inverse near `φ (W 0)`.
  have hRright := hStrict.eventually_right_inverse
  -- combine into the two-sided germ `φ (W y) = y`.
  have hcomb : ∀ᶠ y in 𝓝 (φ (W 0)), φ (W y) = y := by
    filter_upwards [hWL, hRright] with y h1 h2
    rw [h1]; exact h2
  rw [hRI] at hcomb
  exact hcomb

/-! ###############################################################################
    ### ★ THE FDERIV-GERM — `fderiv W_z y = Ring.inverse (fderiv φ_z (W_z y))` near `0`.
    ############################################################################### -/

/-- **★ `chartFDerivInverse_germ` — the FDERIV-germ near the field centre.**  Given the RIGHT germ and
    the per-neighbourhood regularity carries, the operator-valued first-jet map agrees near `0` with
    the ring-inverse composite:
        `∀ᶠ y in 𝓝 0, fderiv ℝ W_z y = Ring.inverse (fderiv ℝ φ_z (W_z y))`.
    Mechanism: at each `y` near `0`, apply the first-order IFT-Jacobian identity
    `ChartFieldJacobian.fderiv_localLeftInverse_eq_ringInverse` at `v₀ = W_z y` (using
    `hφdGerm`/`hWdGerm`/`hleftGerm`/`hunitGerm`), then rewrite `φ_z (W_z y) = y` (`hRightGerm`).
    NOT `a₁ = R/6`. -/
theorem chartFDerivInverse_germ (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hRightGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z y) = y)
    (hφdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y))
    (hWdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) y)
    (hleftGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z y),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hunitGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y))) :
    ∀ᶠ y in 𝓝 (0 : Point n),
      fderiv ℝ (uniformInverseChart g gi hC hK z) y
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z y)) := by
  set φ := uniformFlowExp g gi hC hK z with hφdef
  set W := uniformInverseChart g gi hC hK z with hWdef
  filter_upwards [hRightGerm, hφdGerm, hWdGerm, hleftGerm, hunitGerm] with y ha hb hc hd he
  have hWd' : DifferentiableAt ℝ W (φ (W y)) := by rw [ha]; exact hc
  have h := fderiv_localLeftInverse_eq_ringInverse (φ := φ) (W := W) (v₀ := W y) hb hWd' hd he
  rw [ha] at h
  exact h

/-! ###############################################################################
    ### ★★ THE `hid2` DISCHARGE — the per-`z` 2nd-order IFT identity from the germ.
    ############################################################################### -/

/-- **★★ `hid2_discharged` — the per-`z` 2nd-order IFT identity (the `hid2` shape).**  Assembles the
    chart SECOND field-jet identity at the field centre from the point-level carries (`hWd`/`hφ2`/`hRI`/
    `hunit`) and the neighbourhood germ carries (which yield the FDERIV-germ via
    `chartFDerivInverse_germ`), through `ChartSecondJet.chartSecondJet_eq_of_forward2`:
        `fderiv ℝ (fun y => fderiv ℝ W_z y) 0 = E_z`,
    with `E_z = (−mulLeftRight I I) ∘L ((fderiv (fderiv φ_z) (W_z 0)) ∘L I)`, `I = Ring.inverse
    (Dφ_z(W_z 0))`.  This IS the `hid2` binder of `supConstant_phase5`.  NOT `a₁ = R/6`. -/
theorem hid2_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n)
    (hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0)
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
      (uniformInverseChart g gi hC hK z 0))
    (hRI : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0)
    (hunit : IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z)
      (uniformInverseChart g gi hC hK z 0)))
    (hRightGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z y) = y)
    (hφdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y))
    (hWdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) y)
    (hleftGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z y),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v)
    (hunitGerm : ∀ᶠ y in 𝓝 (0 : Point n),
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y))) :
    fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
      = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))).comp
        ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
              (uniformInverseChart g gi hC hK z 0)).comp
          (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)))) := by
  have hgerm := chartFDerivInverse_germ g gi hC hK z hRightGerm hφdGerm hWdGerm hleftGerm hunitGerm
  exact chartSecondJet_eq_of_forward2 g gi hC hK z hWd hφ2 hgerm hRI hunit

/-! ###############################################################################
    ### ★★★ THE PACKAGE — the sup family, phase 6 (C₂ on (I1) ALONE).
    ############################################################################### -/

/-- **★★★ `supConstant_phase6` — the sup/constant family, phase 6.**  On a CONCRETE small ball, the
    whole sup family `M₀`/`M₁`/`M₂` (= `C₀`/`C₁`/`C₂`, hence `Sconst`) is grounded from the SINGLE
    carried input (I1) `hReach`.  The SIX geometric carriers of `supConstant_phase4`
    (`hUK`/`hW0`/`horigin`/`hunit`/`hJac`/`hreg`) are discharged from the bank (as in
    `c2_carriers_discharged`), AND the 2nd-order IFT residue `hid2` is now ALSO discharged internally
    via the right-inverse germ (`chartRightInverse_germ` → `chartFDerivInverse_germ` → `hid2_discharged`).
    `C₀` UNCONDITIONAL, `C₁` geometric-closed, `C₂` on (I1) ALONE.  NOT `a₁ = R/6`. -/
theorem supConstant_phase6 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q) :
    ∃ ρ, 0 < ρ ∧
      ((∃ ρ₀ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
          ∀ τ z, collarRegime (K := K) ρ₀ c τ₀ τ z → |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
        ∧ (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
            |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
        ∧ (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
            |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂)) := by
  classical
  -- the banked uniform radii (mirrors `c2_carriers_discharged`).
  obtain ⟨εK, hεK0, hεKsub⟩ := Metric.mem_nhds_iff.mp h0Kmem
  obtain ⟨r₁, hr₁0, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  obtain ⟨rRI, hrRI0, hRIspec⟩ := chartW0_rightInverse g gi hC hK
  obtain ⟨δg, hδg0, hgermspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨δr, hδr0, hreach⟩ := chartField_contDiffAt_reachable_uniform g gi hC hK
  obtain ⟨ρnd, hρnd0, hnondeg⟩ := uniformFlowExp_common_nondeg_radius g gi hC hK
  set δlip : ℝ := (chartOrigin_lipschitz_modulus g gi hC hK).choose with hδlipdef
  have hδlip0 : 0 < δlip := (chartOrigin_lipschitz_modulus g gi hC hK).choose_spec.1
  -- the ceiling for `‖W₀ z‖`.
  set Wbound : ℝ := min (min δg δr) (min (min (uniformFlowRadius g gi hC hK) ρnd) δlip) with hWbdef
  have hWb_δg : Wbound ≤ δg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hWb_δr : Wbound ≤ δr := le_trans (min_le_left _ _) (min_le_right _ _)
  have hWb_uf : Wbound ≤ uniformFlowRadius g gi hC hK :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hWb_ρnd : Wbound ≤ ρnd :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hWb_δlip : Wbound ≤ δlip := le_trans (min_le_right _ _) (min_le_right _ _)
  have hWbpos : 0 < Wbound :=
    lt_min (lt_min hδg0 hδr0) (lt_min (lt_min (uniformFlowRadius_pos g gi hC hK) hρnd0) hδlip0)
  have h1CW : (0 : ℝ) < 1 + C_W := by linarith
  -- the master small radius.
  set base : ℝ := min (min εK r₁) (min rRI (min 1 (Wbound / (1 + C_W)))) with hbasedef
  have hbase0 : 0 < base :=
    lt_min (lt_min hεK0 hr₁0) (lt_min hrRI0 (lt_min one_pos (by positivity)))
  set ρ : ℝ := base / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρbase : ρ < base := by rw [hρdef]; linarith
  have hρ_lt : ∀ x : ℝ, base ≤ x → ρ < x := fun x hx => lt_of_lt_of_le hρbase hx
  have hρεK : ρ < εK := hρ_lt εK (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρr₁ : ρ < r₁ := hρ_lt r₁ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρrRI : ρ < rRI := hρ_lt rRI (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ1 : ρ < 1 := hρ_lt 1 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρWb : ρ < Wbound / (1 + C_W) :=
    hρ_lt _ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- `hUK`.
  have hUK : Metric.closedBall (0 : Point n) ρ ⊆ K := by
    intro x hx
    have hxn : ‖x‖ ≤ ρ := mem_closedBall_zero_iff.mp hx
    exact hεKsub (mem_ball_zero_iff.mpr (lt_of_le_of_lt hxn hρεK))
  -- the per-`z` package on the ball.
  have hzfacts : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      z ∈ K
      ∧ ‖uniformInverseChart g gi hC hK z 0‖ < Wbound
      ∧ uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
    have zK : z ∈ K := hUK hz
    have hzr₁ : ‖z‖ < r₁ := lt_of_le_of_lt hzn hρr₁
    have hzrRI : ‖z‖ < rRI := lt_of_le_of_lt hzn hρrRI
    have hz1 : ‖z‖ ≤ 1 := le_of_lt (lt_of_le_of_lt hzn hρ1)
    have hDisp : ‖uniformInverseChart g gi hC hK z 0 + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hD1 z zK hzr₁
    have hWle : ‖uniformInverseChart g gi hC hK z 0‖ ≤ (1 + C_W) * ‖z‖ := by
      have htri : ‖uniformInverseChart g gi hC hK z 0‖
          ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := by
        calc ‖uniformInverseChart g gi hC hK z 0‖
            = ‖(uniformInverseChart g gi hC hK z 0 + z) - z‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖uniformInverseChart g gi hC hK z 0 + z‖ + ‖z‖ := norm_sub_le _ _
      nlinarith [htri, hDisp, mul_nonneg (mul_nonneg hCW0 (norm_nonneg z)) (sub_nonneg.mpr hz1)]
    have hWlt : ‖uniformInverseChart g gi hC hK z 0‖ < Wbound := by
      have hstep : (1 + C_W) * ‖z‖ ≤ (1 + C_W) * ρ :=
        mul_le_mul_of_nonneg_left hzn (le_of_lt h1CW)
      have hlt : (1 + C_W) * ρ < Wbound := by
        rw [mul_comm]; exact (lt_div_iff₀ h1CW).mp hρWb
      exact lt_of_le_of_lt (le_trans hWle hstep) hlt
    have hRIz : uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 :=
      hRIspec z zK hzrRI
    exact ⟨zK, hWlt, hRIz⟩
  -- `horigin`.
  have horigin : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK :=
    fun z hz => lt_of_lt_of_le (hzfacts z hz).2.1 hWb_uf
  -- `hunit`.
  have hunit : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0)) := by
    intro z hz
    obtain ⟨zK, hWlt, _⟩ := hzfacts z hz
    exact hnondeg z zK (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_ρnd)
  -- `hreg`.
  have hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n) := by
    intro z hz
    obtain ⟨zK, hWlt, hRIz⟩ := hzfacts z hz
    have hcd := hreach z zK (uniformInverseChart g gi hC hK z 0) (lt_of_lt_of_le hWlt hWb_δr)
    rwa [hRIz] at hcd
  -- `hW0`.
  have hball : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      uniformInverseChart g gi hC hK z 0 ∈ Metric.ball (0 : Point n) δlip :=
    fun z hz => mem_ball_zero_iff.mpr (lt_of_lt_of_le (hzfacts z hz).2.1 hWb_δlip)
  have hnorm : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK :=
    fun z hz => le_of_lt (horigin z hz)
  have hRI : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 :=
    fun z hz => (hzfacts z hz).2.2
  have hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ) :=
    chartOrigin_continuousOn g gi hC hK hUK hball hnorm hRI
  -- `hIFT` (per `z`) ⟹ `hJac`.
  have hIFT : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      fderiv ℝ (uniformInverseChart g gi hC hK z) 0
        = Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
            (uniformInverseChart g gi hC hK z 0)) := by
    intro z hz
    obtain ⟨zK, hWlt, hRIz⟩ := hzfacts z hz
    have hφd : DifferentiableAt ℝ (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0) :=
      (contDiffAt2_uniformFlowExp g gi hC hK z zK (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_uf)).differentiableAt (by norm_num)
    have hWd : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0 :=
      (hreg z hz).differentiableAt (by norm_num)
    have hgerm : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
      have hge := ((hgermspec z zK).1 (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_δg)).1
      filter_upwards [hge] with v hv using hv
    exact chartFieldJacobian_eq_ringInverse g gi hC hK z hφd hWd hgerm hRIz (hunit z hz)
  have hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ) :=
    chartFieldJacobian_continuousOn g gi hC hK hUK hW0 horigin hunit hIFT
  -- the NEW discharge: `hid2` on the ball, via the right-inverse germ.
  have hid2 : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))) := by
    intro z hz
    obtain ⟨zK, hWlt, hRIz⟩ := hzfacts z hz
    -- the point-level carries at `v₀ = W_z 0`.
    have hφC2v₀ : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK z)
        (uniformInverseChart g gi hC hK z 0) :=
      contDiffAt2_uniformFlowExp g gi hC hK z zK (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_uf)
    have hleftv₀ : ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z 0),
        uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
      filter_upwards [((hgermspec z zK).1 (uniformInverseChart g gi hC hK z 0)
        (lt_of_lt_of_le hWlt hWb_δg)).1] with v hv using hv
    have hWd0 : DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) 0 :=
      (hreg z hz).differentiableAt (by norm_num)
    have hφ2 : DifferentiableAt ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
        (uniformInverseChart g gi hC hK z 0) :=
      (hφC2v₀.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    -- the RIGHT germ (fresh strict IFT).
    have hRightGerm := chartRightInverse_germ g gi hC hK z hφC2v₀ (hunit z hz) hleftv₀ hRIz
    -- the neighbourhood smallness bound `‖W_z y‖ < m` near `0`.
    set m : ℝ := min (min δg (uniformFlowRadius g gi hC hK)) ρnd with hmdef
    have hmδg : m ≤ δg := le_trans (min_le_left _ _) (min_le_left _ _)
    have hmR : m ≤ uniformFlowRadius g gi hC hK := le_trans (min_le_left _ _) (min_le_right _ _)
    have hmρnd : m ≤ ρnd := min_le_right _ _
    have hv₀m : ‖uniformInverseChart g gi hC hK z 0‖ < m :=
      lt_min (lt_min (lt_of_lt_of_le hWlt hWb_δg) (lt_of_lt_of_le hWlt hWb_uf))
        (lt_of_lt_of_le hWlt hWb_ρnd)
    have hmnhds : Metric.ball (0 : Point n) m ∈ 𝓝 (uniformInverseChart g gi hC hK z 0) :=
      Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv₀m)
    have hEnorm : ∀ᶠ y in 𝓝 (0 : Point n),
        uniformInverseChart g gi hC hK z y ∈ Metric.ball (0 : Point n) m :=
      (hreg z hz).continuousAt.eventually_mem hmnhds
    -- the four neighbourhood germ carries.
    have hφdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
        DifferentiableAt ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y) := by
      filter_upwards [hEnorm] with y hy
      exact (contDiffAt2_uniformFlowExp g gi hC hK z zK (uniformInverseChart g gi hC hK z y)
        (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmR)).differentiableAt (by norm_num)
    have hWdGerm : ∀ᶠ y in 𝓝 (0 : Point n),
        DifferentiableAt ℝ (uniformInverseChart g gi hC hK z) y := by
      filter_upwards [(hreg z hz).eventually (by norm_num)] with y hy
      exact hy.differentiableAt (by norm_num)
    have hleftGerm : ∀ᶠ y in 𝓝 (0 : Point n),
        ∀ᶠ v in 𝓝 (uniformInverseChart g gi hC hK z y),
          uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v := by
      filter_upwards [hEnorm] with y hy
      filter_upwards [((hgermspec z zK).1 (uniformInverseChart g gi hC hK z y)
        (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmδg)).1] with v hv using hv
    have hunitGerm : ∀ᶠ y in 𝓝 (0 : Point n),
        IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z y)) := by
      filter_upwards [hEnorm] with y hy
      exact hnondeg z zK (uniformInverseChart g gi hC hK z y)
        (lt_of_lt_of_le (mem_ball_zero_iff.mp hy) hmρnd)
    exact hid2_discharged g gi hC hK z hWd0 hφ2 hRIz (hunit z hz)
      hRightGerm hφdGerm hWdGerm hleftGerm hunitGerm
  -- assemble via `supConstant_phase4` — C₂ now on (I1) `hReach` ALONE.
  exact ⟨ρ, hρ0,
    supConstant_phase4 g gi hC hK h0Kmem hg hgi hgpos a b c τ₀ i ρ hρ0 hUK hReach
      hW0 horigin hunit hid2 hJac hreg⟩

end QIQTH.Hid2Germ

/-! ## THE GERM LEDGER (post J4-489).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE RESIDUE.  `C2CarrierCollapse.supConstant_phase5` grounded `C₀`/`C₁`/`C₂` on (I1) `hReach` +   │
  │  the ONE isolated 2nd-order IFT residue `hid2` — the per-`z` chart SECOND-jet identity, which       │
  │  `ChartSecondJet.chartSecondJet_eq_of_forward2` proves from FIVE carries, four banked and the FIFTH  │
  │  the FDERIV-germ needing the RIGHT-inverse germ `φ_z (W_z y) = y` near `0`.                          │
  ├───────────────┬───────────────────────────────────────────────────────────────────────────────┤
  │ GERM STEP     │ ROUTE (this brick)                                                                │
  ├───────────────┼───────────────────────────────────────────────────────────────────────────────┤
  │ RIGHT germ    │ FRESH strict-IFT invocation on the nondegenerate `φ_z`: `HasStrictFDerivAt` from    │
  │ `φ_z∘W_z=id`  │ `C²` (`contDiffAt2_uniformFlowExp`) + unit (`uniformFlowExp_common_nondeg_radius`); │
  │               │ `localInverse_unique` (`W_z =ᶠ L`) + `eventually_right_inverse` (`φ_z (L y)=y`).    │
  │               │ Both banked ingredients ALREADY used by `c2_carriers_discharged` — NO new input.    │
  │ FDERIV germ   │ per-`y` first-order IFT algebra `fderiv_localLeftInverse_eq_ringInverse` at         │
  │               │ `v₀ = W_z y`, rewriting the right germ.  Neighbourhood carries from continuity of   │
  │               │ `W_z` at `0` (`ContinuousAt.eventually_mem`) + `ContDiffAt.eventually`.             │
  │ `hid2`        │ `chartSecondJet_eq_of_forward2` fed the fderiv-germ + the four point carries.        │
  ├───────────────┴───────────────────────────────────────────────────────────────────────────────┤
  │  THE OUTCOME.  `supConstant_phase6`: the whole sup family is grounded on a CONCRETE small ball from │
  │  (I1) `hReach` ALONE.  SIX geometric carriers gone (as in J4-488) AND the 2nd-order residue `hid2`  │
  │  discharged.  C₀ UNCONDITIONAL, C₁ geometric-closed, C₂ ON (I1) ALONE.  NEVER `a₁ = R/6`.          │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── THE SUP FAMILY IS CLOSED ON (I1) ALONE.  The last derivative slot (C₂) of the a₁-R/6 sup/constant
     family now rests on the SINGLE geometric input (I1) `hReach` — matching the convergent wall — with
     NO separate second-order germ residue.  The right germ FOLDS INTO the bank (a local diffeo has both
     germs; the fresh strict-IFT re-derivation uses only `contDiffAt2_uniformFlowExp` +
     `uniformFlowExp_common_nondeg_radius`, both already carrier-discharged).

  ── DONT-UNDERCREDIT findings.
    * The abstract 2nd-order IFT algebra (`hasFDerivAt_fderiv_localLeftInverse`) AND the first-order
      IFT-Jacobian identity (`fderiv_localLeftInverse_eq_ringInverse`) were ALREADY banked; this brick
      only supplies the missing GERM (the strict-IFT right inverse) that both consumed.
    * `hid2` was the SOLE geometric carrier flagged as not-collapsing in J4-488; it is NOT a new input —
      it reduces, via a fresh (but bank-only) strict-IFT invocation, to the same nondegeneracy + `C²`
      already used to discharge the other six carriers.  No input beyond (I1) survives at the C₂ level.
    * The right germ genuinely needed a FRESH IFT invocation (the banked spec HIDES the
      OpenPartialHomeomorph and exposes only the LEFT germ) — but that invocation is a THEOREM of the
      bank, not an assumption.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1) `hReach`, the banked convergence trio, and
    the geometric wiring).
-/

section AxiomChecks
open QIQTH.Hid2Germ
#print axioms chartRightInverse_germ
#print axioms chartFDerivInverse_germ
#print axioms hid2_discharged
#print axioms supConstant_phase6
end AxiomChecks
