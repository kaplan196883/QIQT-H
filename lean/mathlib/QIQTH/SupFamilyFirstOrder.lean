/-
  SupFamilyFirstOrder — J4-436: the `hcont1` shape wiring — GROUNDING the first-order sups of the
  a₁ = R/6 sup/constant family UNCONDITIONALLY (modulo the reduced geometric continuity facts).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE CHAIN.  J4-432 (`BaseSlotAmpDeriv`) identified the base-slot first field-derivative at the
  centre EXACTLY (`pd_chartAmp_center_eq`):
        `pd (chartAmp … τ z ·) i 0
           = fderiv ℝ (manifoldAmp … τ) (W z 0)  (fderiv ℝ (W z) 0 (eᵢ))`,  `W z = uniformInverseChart …`,
  and grounded `C₁`/`M₁chart` by compactness CONDITIONAL on `hcont1` = the JOINT-in-`(τ,z)` continuity
  of that identified field on `[0,τ₀] ×ˢ closedBall 0 ρ`.  J4-433 (`ChartFieldJacobian`) reduced the
  chart field-Jacobian's base continuity to the FORWARD jet; J4-435 (`JacobiCLMExposure`) proved
  `chartFieldJacobian_continuousOn` UNCONDITIONAL.  THIS BRICK composes the pieces into the exact
  `hcont1` shape and grounds the first-order sups.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    • `manifoldAmp_fderiv_continuous`  — ★ the manifold-amplitude Fréchet-derivative field
        `(τ, w) ↦ fderiv ℝ (manifoldAmp … τ) w` is JOINTLY CONTINUOUS.  `manifoldAmp` is AFFINE in `τ`,
        `manifoldAmp … τ = c₀ + τ·c₁` with `c₀`/`c₁` the `C²` `w`-factors, so its `w`-Fréchet derivative
        is `fderiv c₀ w + τ·fderiv c₁ w` — continuous in `(τ,w)` since `fderiv c_k` is continuous
        (`ContDiff.continuous_fderiv`).  Geometry-only.
    • `supFamilyFirstOrder_hcont1`     — ★★ THE hcont1 SHAPE, composed.  Given the (reduced, geometric)
        origin-section continuity `hW0`, the chart field-Jacobian continuity `hJac`, and the per-point
        reachable `C²` `hreg` on `closedBall 0 ρ`, the base-slot first field-derivative field
        `(τ,z) ↦ pd (chartAmp … τ z ·) i 0` is `ContinuousOn` on `[0,τ₀] ×ˢ closedBall 0 ρ` — via
        `pd_chartAmp_center_eq` + the joint manifold-amp derivative continuity + the continuous
        `clm_apply`.
    • `baseSlotAmpDeriv1_grounded`     — ★★ `C₁`/`M₁chart` GROUNDED from `hcont1` (no opaque carry).
    • `supConstant_phase3`             — ★★★ the sup family, phase 3: phase-1 amplitude sup
        (UNCONDITIONAL) ∧ the first-derivative sup (grounded from the geometric facts) ∧ the
        second-derivative sup (still carrying the opaque `hcont2` — the honest 2nd-order residue).

  ── DOMAIN RECONCILIATION (honest).  `chartFieldJacobian_continuousOn` (J4-435) runs over `U ⊆ K`
  under the smallness side-conditions `horigin`/`hunit`/`hIFT` (and the reachable `C²` needs
  `‖W z 0‖ < δ₀`); the sup lemma `baseSlotAmpDeriv1_sup_onCollar` runs over the CLOSED ball
  `closedBall 0 ρ`.  These line up ONLY when `ρ` is small enough that `closedBall 0 ρ ⊆ K` and the
  banked smallness radii hold on it.  Rather than fabricate that reconciliation, this brick takes the
  three geometric facts (`hW0`, `hJac`, `hreg`) AS HYPOTHESES on `closedBall 0 ρ` — exactly the
  outputs of `GeodesicGronwall.chartOrigin_continuousOn`, `JacobiCLMExposure.chartFieldJacobian_
  continuousOn`, and `ChartFieldC2General.chartField_contDiffAt_reachable_uniform` on a suitable small
  ball.  This converts the OPAQUE analytic `hcont1` into three NAMED, individually-banked-reducible
  geometric facts — a net honesty gain — and leaves the small-ball domain reconciliation as the stated
  residual (see THE SUP LEDGER v3).

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SupConstantFamily
import QIQTH.BaseSlotAmpDeriv
import QIQTH.JacobiCLMExposure
import QIQTH.GeneralBaseJets
import QIQTH.HuInftyRebase

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.VanVleck QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar QIQTH.SupConstantFamily
open QIQTH.HuInftyRebase QIQTH.BaseSlotAmpDeriv
open scoped Topology ContDiff

namespace QIQTH.SupFamilyFirstOrder

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ The manifold-amplitude Fréchet-derivative field is JOINTLY continuous.
    ############################################################################### -/

/-- **★ `manifoldAmp_fderiv_continuous` — the manifold-amplitude derivative field is jointly
    continuous.**  `(τ, w) ↦ fderiv ℝ (manifoldAmp g gi a b τ) w` is `Continuous` on `ℝ × Point n`.
    Mechanism: `manifoldAmp g gi a b τ` is AFFINE in `τ`,
      `manifoldAmp g gi a b τ = fun w => c₀ w + c₁ w · τ`,
    where `c_k w = radialCutoff a b w · vanVleck g w ^ (−½) · transportCoeff … k w` are `C²` (each
    factor `C²`, `contDiff_iff_contDiffAt`).  Hence its `w`-Fréchet derivative is
    `fderiv ℝ c₀ w + τ • fderiv ℝ c₁ w`, and `w ↦ fderiv ℝ c_k w` is continuous
    (`ContDiff.continuous_fderiv`); the affine `τ`-assembly is jointly continuous.  NOT `a₁ = R/6`. -/
theorem manifoldAmp_fderiv_continuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b : ℝ) :
    Continuous (fun p : ℝ × Point n => fderiv ℝ (manifoldAmp g gi a b p.1) p.2) := by
  -- the `w`-slot base fields `c_k` are `C²` (uniformly in `k`)
  have hcd_raw : ∀ k : ℕ, ContDiff ℝ 2 (fun w : Point n =>
      radialCutoff a b w * (vanVleck g w ^ (-(1 : ℝ) / 2)
        * transportCoeff (transportOp (vanVleck g) g gi) k w)) := by
    intro k
    rw [contDiff_iff_contDiffAt]
    intro w
    have h2inf : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)); simpa using h
    have hu := hu_infty_closed g gi hg hgi hgpos
    have hcut : ContDiffAt ℝ 2 (radialCutoff a b) w :=
      (radialCutoff_contDiff a b).contDiffAt.of_le h2inf
    have hvv : ContDiffAt ℝ 2 (vanVleck g) w := vanVleck_contDiffAt g hg w (hgpos w)
    have hne : vanVleck g w ≠ 0 := ne_of_gt (vanVleck_pos g w (hgpos w))
    have hrpow : ContDiffAt ℝ 2 (fun w => vanVleck g w ^ (-(1 : ℝ) / 2)) w :=
      hvv.rpow_const_of_ne hne
    have huk : ContDiffAt ℝ 2 (transportCoeff (transportOp (vanVleck g) g gi) k) w :=
      (hu k).contDiffAt.of_le h2inf
    exact hcut.mul (hrpow.mul huk)
  set c0 : Point n → ℝ := fun w =>
    radialCutoff a b w * (vanVleck g w ^ (-(1 : ℝ) / 2)
      * transportCoeff (transportOp (vanVleck g) g gi) 0 w) with hc0
  set c1 : Point n → ℝ := fun w =>
    radialCutoff a b w * (vanVleck g w ^ (-(1 : ℝ) / 2)
      * transportCoeff (transportOp (vanVleck g) g gi) 1 w) with hc1
  have hcd0 : ContDiff ℝ 2 c0 := by rw [hc0]; exact hcd_raw 0
  have hcd1 : ContDiff ℝ 2 c1 := by rw [hc1]; exact hcd_raw 1
  have hcF0 : Continuous (fderiv ℝ c0) := hcd0.continuous_fderiv (by norm_num)
  have hcF1 : Continuous (fderiv ℝ c1) := hcd1.continuous_fderiv (by norm_num)
  -- the affine-in-`τ` presentation
  have heq : ∀ τ : ℝ, manifoldAmp g gi a b τ = fun w => c0 w + c1 w * τ := by
    intro τ; funext w
    simp only [hc0, hc1, manifoldAmp]
    ring
  -- the `w`-Fréchet derivative of `manifoldAmp … τ`
  have hid : ∀ (τ : ℝ) (w : Point n),
      fderiv ℝ (manifoldAmp g gi a b τ) w = fderiv ℝ c0 w + τ • fderiv ℝ c1 w := by
    intro τ w
    have hb0 : HasFDerivAt c0 (fderiv ℝ c0 w) w :=
      (hcd0.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hb1 : HasFDerivAt c1 (fderiv ℝ c1 w) w :=
      (hcd1.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hb1c : HasFDerivAt (fun w => c1 w * τ) (τ • fderiv ℝ c1 w) w := hb1.mul_const τ
    have hsum : HasFDerivAt (fun w => c0 w + c1 w * τ)
        (fderiv ℝ c0 w + τ • fderiv ℝ c1 w) w := hb0.add hb1c
    rw [heq τ]
    exact hsum.fderiv
  -- assemble the joint continuity
  have hfun : (fun p : ℝ × Point n => fderiv ℝ (manifoldAmp g gi a b p.1) p.2)
      = (fun p : ℝ × Point n => fderiv ℝ c0 p.2 + p.1 • fderiv ℝ c1 p.2) := by
    funext p; exact hid p.1 p.2
  rw [hfun]
  exact (hcF0.comp continuous_snd).add (continuous_fst.smul (hcF1.comp continuous_snd))

/-! ###############################################################################
    ### ★★ THE hcont1 SHAPE, COMPOSED.
    ############################################################################### -/

/-- **★★ `supFamilyFirstOrder_hcont1` — the exact `hcont1` shape, composed.**  For the base-slot first
    field-derivative field `(τ, z) ↦ pd (chartAmp … τ z ·) i 0` on `[0,τ₀] ×ˢ closedBall 0 ρ`, the
    JOINT continuity is established from three GEOMETRIC facts on `closedBall 0 ρ` (each a reduced,
    banked-reducible input, NOT the opaque analytic carry):
      • `hreg` — the per-point reachable `C²` of the chart field slot `W z` at the centre `0`
                 (`ChartFieldC2General.chartField_contDiffAt_reachable_uniform` on a small ball);
      • `hW0`  — base continuity of the origin section `z ↦ W z 0`
                 (`GeodesicGronwall.chartOrigin_continuousOn`);
      • `hJac` — base continuity of the chart field-slot Jacobian `z ↦ fderiv ℝ (W z) 0`
                 (`JacobiCLMExposure.chartFieldJacobian_continuousOn`, UNCONDITIONAL).
    Mechanism: `pd_chartAmp_center_eq` rewrites the field to
      `fderiv ℝ (manifoldAmp … p.1) (W p.2 0)  (fderiv ℝ (W p.2) 0 eᵢ)`;
    the CLM factor is `manifoldAmp_fderiv_continuous ∘ (p ↦ (p.1, W p.2 0))` (continuous via `hW0`),
    the vector factor is `hJac`-`clm_apply`'d against the constant `eᵢ`, and `ContinuousOn.clm_apply`
    combines them; `ContinuousOn.congr` transfers back through the identification.  NOT `a₁ = R/6`. -/
theorem supFamilyFirstOrder_hcont1 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ₀ : ℝ) (i : Fin n) (ρ : ℝ)
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n))
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ)) :
    ContinuousOn (fun p : ℝ × Point n => pd (chartAmp g gi hC hK a b p.1 p.2) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
  -- `Prod.snd` maps the domain into the base ball.
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => p.2)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)
      (Metric.closedBall (0 : Point n) ρ) := fun p hp => hp.2
  -- origin section on the domain
  have hW0D : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    hW0.comp continuous_snd.continuousOn hmaps
  -- the pair `(τ, W z 0)` on the domain
  have hpair : ContinuousOn
      (fun p : ℝ × Point n => (p.1, uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (continuous_fst.continuousOn).prodMk hW0D
  -- the CLM factor `fderiv (manifoldAmp … τ) (W z 0)`
  have hA : ContinuousOn
      (fun p : ℝ × Point n =>
        fderiv ℝ (manifoldAmp g gi a b p.1) (uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (manifoldAmp_fderiv_continuous g gi hg hgi hgpos a b).comp_continuousOn hpair
  -- the vector factor `fderiv (W z) 0 eᵢ`, first on the ball, then on the domain
  have hJacApply : ContinuousOn
      (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ)))
      (Metric.closedBall (0 : Point n) ρ) :=
    hJac.clm_apply continuousOn_const
  have hx' : ContinuousOn
      (fun p : ℝ × Point n =>
        fderiv ℝ (uniformInverseChart g gi hC hK p.2) 0 (Pi.single i (1 : ℝ)))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    hJacApply.comp continuous_snd.continuousOn hmaps
  -- combine via the continuous `clm_apply`
  have hExplicit : ContinuousOn
      (fun p : ℝ × Point n =>
        (fderiv ℝ (manifoldAmp g gi a b p.1) (uniformInverseChart g gi hC hK p.2 0))
          (fderiv ℝ (uniformInverseChart g gi hC hK p.2) 0 (Pi.single i (1 : ℝ))))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    hA.clm_apply hx'
  -- transfer through the explicit identification `pd_chartAmp_center_eq`
  refine hExplicit.congr ?_
  intro p hp
  exact pd_chartAmp_center_eq g gi hC hK hg hgi hgpos a b p.1 p.2 i (hreg p.2 hp.2)

/-! ###############################################################################
    ### ★★ / ★★★ THE GROUNDED FIRST-ORDER SUP AND THE PACKAGE.
    ############################################################################### -/

/-- **★★ `baseSlotAmpDeriv1_grounded` — `C₁` / `M₁chart` GROUNDED (no opaque carry).**  Feeds the
    composed `hcont1` (`supFamilyFirstOrder_hcont1`) into `BaseSlotAmpDeriv.baseSlotAmpDeriv1_sup_
    onCollar`, delivering the collar-restricted `M₁chart` bound in the EXACT
    `amplitudeDataOn_concrete.hM₁chart` carry shape — now conditional only on the three reduced
    GEOMETRIC facts `hreg`/`hW0`/`hJac`, not the opaque joint-continuity carry.  NOT `a₁ = R/6`. -/
theorem baseSlotAmpDeriv1_grounded (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n))
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ)) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
      |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁ :=
  baseSlotAmpDeriv1_sup_onCollar g gi hC hK a b c τ₀ i ρ hρ
    (supFamilyFirstOrder_hcont1 g gi hC hK hg hgi hgpos a b τ₀ i ρ hreg hW0 hJac)

/-- **★★★ `supConstant_phase3` — the sup/constant family, phase 3.**  Packages the phase-1 amplitude
    center-value sup `M₀chart` (UNCONDITIONAL, `chartAmp_center_sup_onCollar`), the FIRST-derivative sup
    `M₁chart` (= `C₁`; now grounded from the three reduced GEOMETRIC facts `hreg`/`hW0`/`hJac` via
    `supFamilyFirstOrder_hcont1`, no opaque carry), and the SECOND-derivative sup `M₂chart` (= `C₂`;
    still carrying the opaque 2nd-order joint-continuity `hcont2` — the honest 2nd-order residue).  All
    three in the collar carry shapes consumed by `amplitudeDataOn_concrete`.  NOT `a₁ = R/6`. -/
theorem supConstant_phase3 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n))
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hcont2 : ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (chartAmp g gi hC hK a b p.1 p.2) i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)) :
    (∃ ρ₀ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
        ∀ τ z, collarRegime (K := K) ρ₀ c τ₀ τ z → |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
    ∧ (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
    ∧ (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂) :=
  supConstant_phase2 g gi hC hK h0Kmem hg hgi hgpos a b c τ₀ i ρ hρ
    (supFamilyFirstOrder_hcont1 g gi hC hK hg hgi hgpos a b τ₀ i ρ hreg hW0 hJac) hcont2

end QIQTH.SupFamilyFirstOrder

/-! ## THE SUP LEDGER v3 — the honest per-constant table after J4-436.

  ┌──────────┬───────────────────────────────────────────────────────────────────────────────────┐
  │ CONSTANT │ STATUS (post J4-436)                                                                 │
  ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
  │ C_L      │ GROUNDED (banked).  `SupConstantFamily.levi_C_L_grounded`.                           │
  ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
  │ Mqc /    │ GROUNDED, collar-restricted (UNCONDITIONAL).  `SupConstantFamily.chartAmp_center_    │
  │ M₀chart  │ sup_onCollar` (compactness of the continuous base-slot amplitude field).  Re-exported │
  │          │ as `supConstant_phase3` conjunct 1.                                                  │
  ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
  │ C₁ /     │ GROUNDED (this brick).  `baseSlotAmpDeriv1_grounded` / `supConstant_phase3` conjunct  │
  │ M₁chart  │ 2.  The opaque analytic `hcont1` is DISCHARGED (`supFamilyFirstOrder_hcont1`) by       │
  │          │ composing `pd_chartAmp_center_eq` + `manifoldAmp_fderiv_continuous` (joint, proved     │
  │          │ here, unconditional) + the continuous `clm_apply`, over the three REDUCED GEOMETRIC     │
  │          │ facts on `closedBall 0 ρ`:                                                            │
  │          │   `hreg` (reachable `C²`)  · `hW0` (origin section)  · `hJac` (field Jacobian).        │
  │          │ Each is an OUTPUT of a banked lemma (`chartField_contDiffAt_reachable_uniform` /       │
  │          │ `chartOrigin_continuousOn` / `chartFieldJacobian_continuousOn`) on a small ball — see  │
  │          │ DOMAIN RESIDUAL below.  NOT the opaque `.choose` carry.                               │
  ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
  │ M        │ FACTOR grounded (this brick); NOT a bare `s`-uniform constant (honest).               │
  │          │ `M = sup|A1amp·F| = sup|ρ·(−2∂ᵢchartAmp 0)·F|`.  The amplitude-derivative factor       │
  │          │ `−2∂ᵢchartAmp 0` is grounded by `baseSlotAmpDeriv1_grounded`, and `ρ ≤ collarK`        │
  │          │ (`rhoRatio_le_collarK`); but `F` is only `s`-LOCALLY Gaussian-bounded (peak `∝ s^{−d/2}`│
  │          │ blows up as `s→0`), so `M` as a single `s`-uniform sup does NOT compose — it is CARRIED │
  │          │ pointwise into the slot's `hdom` (exactly as recorded in the J4-431 ledger).  The      │
  │          │ standalone amplitude-derivative FACTOR is what this brick grounds.                    │
  ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
  │ C₂ /     │ GROUNDED-CONDITIONAL on `hcont2` (the honest 2nd-order residue).  `supConstant_phase3` │
  │ M₂chart /│ conjunct 3 carries `hcont2` = joint continuity of the SECOND field-derivative field.   │
  │ Sconst   │ SPEC for the next brick (J4-437, the 2nd-order analogue of this brick):               │
  │          │   (i)   the forward SECOND jet joint-in-base continuity                               │
  │          │         `(z,v) ↦ fderiv² (uniformFlowExp … z) v`  (a strictly higher forward-joint     │
  │          │         carry than J4-435's first jet);                                               │
  │          │   (ii)  the 2nd-order IFT identity for `z ↦ fderiv² (W z) 0` (the second-order         │
  │          │         analogue of `chartFieldJacobian_eq_ringInverse`, involving the forward second   │
  │          │         jet and the first-jet ring inverse);                                          │
  │          │   (iii) the pd²-identification `pd (fun y => pd (chartAmp … τ z ·) i y) i 0 = …` in     │
  │          │         terms of `fderiv (manifoldAmp … τ)`, `fderiv² (manifoldAmp … τ)`, `fderiv (W z)`│
  │          │         and `fderiv² (W z)` at the centre (the 2nd-order analogue of                   │
  │          │         `pd_chartAmp_center_eq`); then the joint `manifoldAmp` SECOND-derivative        │
  │          │         continuity (analogue of `manifoldAmp_fderiv_continuous`) closes `hcont2`.       │
  └──────────┴───────────────────────────────────────────────────────────────────────────────────┘

  DOMAIN RESIDUAL (honest, first-order).  `hcont1` is fully discharged from `hreg`/`hW0`/`hJac` on
  `closedBall 0 ρ`.  Those three are the outputs of banked lemmas whose smallness side-conditions
  (`closedBall 0 ρ ⊆ K`; `‖W z 0‖ < min(δ₀, uniformFlowRadius, ρ_nondeg)`; the right-inverse
  `φ_z(W z 0) = 0`) hold on a SUFFICIENTLY SMALL ball.  This brick does NOT fabricate that small-ball
  reconciliation — it carries the three as explicit geometric hypotheses.  Providing them on a concrete
  small ball (via `chartFieldJacobian_facts_of_small` + `chartOrigin_continuousOn` + the reachable
  `C²`, with `ρ` pinned below the banked radii and `closedBall 0 ρ ⊆ K` from `K ∈ 𝓝 0`) is the stated
  first-order residual.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.SupFamilyFirstOrder
#print axioms manifoldAmp_fderiv_continuous
#print axioms supFamilyFirstOrder_hcont1
#print axioms baseSlotAmpDeriv1_grounded
#print axioms supConstant_phase3
end AxiomChecks
