/-
  BaseSlotAmpDeriv — J4-432: the BASE-SLOT field-DERIVATIVE brick, unblocking the shared derivative
  wall of the a₁ = R/6 sup/constant family (J4-431, `SupConstantFamily`).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms; std-3 only.  No existing file is edited.

  ── THE OBSTRUCTED FAMILY (J4-431 `SupConstantFamily`).  `supConstant_phase1` grounded the amplitude
  center-value sup `M₀chart` (via `BaseSlotAmplitude.baseSlotAmp_bound`, genuine compactness of the
  continuous BASE-SLOT amplitude field).  The four DERIVATIVE sups `C₁`/`C₂`/`M₁chart`/`M₂chart` were
  OBSTRUCTED on ONE shared wall: the banked derivative bounds are per-FIXED-base (germ-local field
  jets), so there is no JOINT-in-base continuous DERIVATIVE field to run compactness over.

  ── THE KEY QUESTION (mission step 2): is the base-slot field derivative
        `(τ, z) ↦ pd (chartFieldAmp … τ z ·) i 0`
     given by an EXPLICIT formula?  ANSWER (this file, `pd_chartFieldAmp_center_eq`): YES, up to the
     chart field-Jacobian.  The concrete amplitude factors THROUGH the manifold amplitude field
        `manifoldAmp g gi a b τ w
           = radialCutoff a b w · Θ(w)^{−½} · (u₀(w) + u₁(w)·τ)`,   Θ = vanVleck g,
     namely `chartFieldAmp … τ z = manifoldAmp … τ ∘ (W z)` (DEFEQ, `W z = uniformInverseChart …`).
     The chain rule (`HasFDerivAt.comp_hasDerivAt`, with the field jet from
     `GeneralBaseJets.chartField_firstJet_nhds_of_contDiffAt`) IDENTIFIES the derivative EXACTLY:
        `pd (chartFieldAmp … τ z ·) i 0
           = fderiv ℝ (manifoldAmp … τ) (W z 0)  (fderiv ℝ (W z) 0 (eᵢ))`.
     The FIRST factor `fderiv (manifoldAmp … τ) (W z 0)` is banked-continuous in the base (through
     `W z 0`, the CoV center-value which IS jointly continuous — `BaseSlotAmplitude`).  The SECOND
     factor `fderiv ℝ (W z) 0` is the chart FIELD-slot Jacobian at the field centre, as the base `z`
     varies — and its JOINT-in-base continuity is the recognized J3 base-point-regularity blocker
     (`FlowJointRegularity`/`BasepointFDeriv`: "there is NO `ContinuousOn`/`ContDiff` fact about the
     joint map `(q,v) ↦ uniformFlowExp … q v`").  So the explicit formula is REACHED, and the sole
     residual for the derivative sups is isolated to ONE atomic missing carry.  We do NOT fabricate it
     via `.choose` (THE `.choose` TRAP): every sup below runs over the ACTUAL derivative field UNDER an
     explicit joint-continuity hypothesis, which is exactly the atomic carry that lands the moment the
     J3 field-Jacobian continuity is banked.

  ── WHAT LANDS.
    • `manifoldAmp`                     — the manifold amplitude field (the `w`-slot amplitude through
        which `chartFieldAmp`/`chartAmp` factor).
    • `manifoldAmp_contDiffAt`          — ★ `manifoldAmp … τ` is `ContDiffAt ℝ 2` at every point
        (geometry-only, from `{hg, hgi, hgpos}` via `hu_infty_closed`, `vanVleck_contDiffAt`,
        `radialCutoff_contDiff`).
    • `pd_chartFieldAmp_center_eq`      — ★★ THE EXPLICIT DERIVATIVE IDENTIFICATION (chain rule), the
        answer to the key question.
    • `pd_chartAmp_center_eq`           — the same identification for `chartAmp` (via the field-function
        equality `chartAmp … = chartFieldAmp …`), the shape the collar bundle carries.
    • `baseSlotAmpDeriv1_sup_onCollar`  — ★★ `C₁`/`M₁chart` GROUNDED by compactness, CONDITIONAL on the
        joint continuity of the (identified) first field-derivative field (the atomic J3-blocker carry).
    • `baseSlotAmpDeriv2_sup_onCollar`  — ★★ `C₂`/`M₂chart`, same one derivative order up.
    • `supConstant_phase2`              — ★★★ the package: phase-1 amplitude sup (UNCONDITIONAL) ∧ the
        two conditionally-grounded derivative sups, in the collar carry shapes.

  ── THE EXACT OBSTRUCTION (for Sol #21 — the spec lemma J4-433 must supply).  Both derivative sups
  reduce, via `pd_chartFieldAmp_center_eq`, to the JOINT-in-base continuity of the chart FIELD-slot
  Jacobian at the field centre:
        `ContinuousOn (fun z => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U`
  (equivalently, joint `C¹` of `(z, x') ↦ uniformInverseChart g gi hC hK z x'` near `(·, 0)`).  This
  is the recognized J3 base-point-regularity blocker (`FlowJointRegularity`, `BasepointFDeriv`); the
  CoV bundle (`baseVaryingIFTPackage_unconditional`) supplies ONLY the base-slot derivative of the
  CENTER VALUE `z ↦ W z 0`, a DIFFERENT jet (base slot, not field slot).  With that carry, the
  `hcont`/`hcont1`/`hcont2` hypotheses below discharge by composition, unconditionally grounding
  `C₁`/`C₂`/`M₁chart`/`M₂chart` (and hence `M`/`Sconst`).

  ⚠  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SupConstantFamily
import QIQTH.GeneralBaseJets
import QIQTH.HuInftyRebase

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.VanVleck QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar QIQTH.SupConstantFamily
open QIQTH.HuInftyRebase
open scoped Topology ContDiff

namespace QIQTH.BaseSlotAmpDeriv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The manifold amplitude field (the `w`-slot factor).
    ############################################################################### -/

/-- **`manifoldAmp`** — the manifold (chart-image) amplitude field, a function of the MANIFOLD point
    `w`, through which both `chartFieldAmp` and `chartAmp` factor by composition with the field-slot
    inverse chart `W z = uniformInverseChart g gi hC hK z`:
      `manifoldAmp g gi a b τ w
         = radialCutoff a b w · vanVleck g w ^ (−½) · (u₀ w + u₁ w · τ)`,
    `u_k = transportCoeff (transportOp (vanVleck g) g gi) k`.  Definitionally
    `chartFieldAmp … τ z = fun x' => manifoldAmp … τ (W z x')`.  NOT `a₁ = R/6`. -/
noncomputable def manifoldAmp (g gi : Point n → Fin n → Fin n → ℝ) (a b τ : ℝ) (w : Point n) : ℝ :=
  radialCutoff a b w
    * (vanVleck g w ^ (-(1 : ℝ) / 2)
        * (transportCoeff (transportOp (vanVleck g) g gi) 0 w
          + transportCoeff (transportOp (vanVleck g) g gi) 1 w * τ))

/-- **★ `manifoldAmp_contDiffAt` — the manifold amplitude field is `C²` everywhere.**  Geometry-only:
    each factor — `radialCutoff a b` (`radialCutoff_contDiff`), `vanVleck g ^ (−½)` (`vanVleck_contDiffAt`
    + nonvanishing `vanVleck_pos`), and the two transport coefficients (`hu_infty_closed`) — is
    `ContDiffAt ℝ 2` at `w`; assembled by `ContDiffAt.mul`.  The Riemannian positivity `hgpos` is
    load-bearing (the `−½`-rpow branch).  NOT `a₁ = R/6`. -/
theorem manifoldAmp_contDiffAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ : ℝ) (w : Point n) :
    ContDiffAt ℝ 2 (manifoldAmp g gi a b τ) w := by
  have h2inf : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)); simpa using h
  have hu := hu_infty_closed g gi hg hgi hgpos
  have hcut : ContDiffAt ℝ 2 (radialCutoff a b) w :=
    (radialCutoff_contDiff a b).contDiffAt.of_le h2inf
  have hvv : ContDiffAt ℝ 2 (vanVleck g) w := vanVleck_contDiffAt g hg w (hgpos w)
  have hne : vanVleck g w ≠ 0 := ne_of_gt (vanVleck_pos g w (hgpos w))
  have hrpow : ContDiffAt ℝ 2 (fun w => vanVleck g w ^ (-(1 : ℝ) / 2)) w :=
    hvv.rpow_const_of_ne hne
  have hu0 : ContDiffAt ℝ 2 (transportCoeff (transportOp (vanVleck g) g gi) 0) w :=
    (hu 0).contDiffAt.of_le h2inf
  have hu1 : ContDiffAt ℝ 2 (transportCoeff (transportOp (vanVleck g) g gi) 1) w :=
    (hu 1).contDiffAt.of_le h2inf
  have hsum : ContDiffAt ℝ 2
      (fun w => transportCoeff (transportOp (vanVleck g) g gi) 0 w
        + transportCoeff (transportOp (vanVleck g) g gi) 1 w * τ) w :=
    hu0.add (hu1.mul contDiffAt_const)
  show ContDiffAt ℝ 2 (manifoldAmp g gi a b τ) w
  unfold manifoldAmp
  exact hcut.mul (hrpow.mul hsum)

/-! ###############################################################################
    ### ★★ THE EXPLICIT DERIVATIVE IDENTIFICATION (the key question, answered).
    ############################################################################### -/

/-- **★★ `pd_chartFieldAmp_center_eq` — the explicit base-slot field-derivative formula.**  Via the
    factorisation `chartFieldAmp … τ z = manifoldAmp … τ ∘ (W z)` (DEFEQ) and the chain rule
    (`HasFDerivAt.comp_hasDerivAt`, with the field jet supplied by
    `GeneralBaseJets.chartField_firstJet_nhds_of_contDiffAt`), the first field-slot partial of the
    concrete amplitude at the field centre is IDENTIFIED EXACTLY:
      `pd (chartFieldAmp … τ z ·) i 0
         = fderiv ℝ (manifoldAmp … τ) (W z 0)  (fderiv ℝ (W z) 0 (eᵢ))`,
    `W z = uniformInverseChart g gi hC hK z`, `eᵢ = Pi.single i 1`.  The first factor is banked-
    continuous in the base (through `W z 0`); the second — the chart FIELD-slot Jacobian — is the J3
    base-point-regularity blocker (see header).  Conditional on the honest chart-centre `C²` carry
    `hreg`.  NOT `a₁ = R/6`. -/
theorem pd_chartFieldAmp_center_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n)) :
    pd (chartFieldAmp g gi hC hK a b τ z) i 0
      = fderiv ℝ (manifoldAmp g gi a b τ) (uniformInverseChart g gi hC hK z 0)
          (fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ))) := by
  -- the field jet at `x = 0` (vector form)
  have hjet_ev := chartField_firstJet_nhds_of_contDiffAt g gi hC hK z i hreg
  have hjet0 : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update (0 : Point n) i s) k)
      (fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ)) k) ((0 : Point n) i) :=
    hjet_ev.self_of_nhds
  have hvec : HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update (0 : Point n) i s))
      (fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ))) ((0 : Point n) i) :=
    hasDerivAt_pi.mpr hjet0
  -- the manifold-amplitude Fréchet derivative at `W z 0`
  have hA : HasFDerivAt (manifoldAmp g gi a b τ)
      (fderiv ℝ (manifoldAmp g gi a b τ) (uniformInverseChart g gi hC hK z 0))
      (uniformInverseChart g gi hC hK z 0) :=
    ((manifoldAmp_contDiffAt g gi hg hgi hgpos a b τ (uniformInverseChart g gi hC hK z 0)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hf0 : (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update (0 : Point n) i s))
        ((0 : Point n) i) = uniformInverseChart g gi hC hK z 0 := by
    simp only [Function.update_eq_self]
  have hA0 : HasFDerivAt (manifoldAmp g gi a b τ)
      (fderiv ℝ (manifoldAmp g gi a b τ) (uniformInverseChart g gi hC hK z 0))
      ((fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update (0 : Point n) i s))
        ((0 : Point n) i)) := by
    rw [hf0]; exact hA
  have hcomp := hA0.comp_hasDerivAt ((0 : Point n) i) hvec
  -- pd is the scalar derivative of the composed slice; DEFEQ collapses `chartFieldAmp` to `manifoldAmp ∘ W`.
  exact hcomp.deriv

/-- **`chartAmp_eq_chartFieldAmp_fun`.**  The two concrete amplitude presentations agree as FIELD-slot
    functions (they differ only by the associativity of the triple product): `chartAmp … τ z =
    chartFieldAmp … τ z`.  Hence their field partials coincide.  NOT `a₁ = R/6`. -/
theorem chartAmp_eq_chartFieldAmp_fun (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) :
    chartAmp g gi hC hK a b τ z = chartFieldAmp g gi hC hK a b τ z := by
  funext x'
  simp only [chartAmp, chartFieldAmp]
  ring

/-- **`pd_chartAmp_center_eq` — the identification in the `chartAmp` carry shape.**  Same explicit
    formula as `pd_chartFieldAmp_center_eq`, transported to `chartAmp` (the shape carried by the collar
    bundle's `hM₁chart`).  NOT `a₁ = R/6`. -/
theorem pd_chartAmp_center_eq (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ : ℝ) (z : Point n) (i : Fin n)
    (hreg : ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n)) :
    pd (chartAmp g gi hC hK a b τ z) i 0
      = fderiv ℝ (manifoldAmp g gi a b τ) (uniformInverseChart g gi hC hK z 0)
          (fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ))) := by
  rw [chartAmp_eq_chartFieldAmp_fun g gi hC hK a b τ z]
  exact pd_chartFieldAmp_center_eq g gi hC hK hg hgi hgpos a b τ z i hreg

/-! ###############################################################################
    ### ★★ The derivative sups, GROUNDED by compactness (conditional on the J3 carry).
    ############################################################################### -/

/-- **★★ `baseSlotAmpDeriv1_sup_onCollar` — `C₁` / `M₁chart` GROUNDED.**  Given a base radius `ρ > 0`
    and the JOINT continuity of the first field-derivative field
      `(τ, z) ↦ pd (chartAmp … τ z ·) i 0`   on `[0,τ₀] ×ˢ closedBall 0 ρ`
    (the atomic J3 carry — dischargeable via `pd_chartAmp_center_eq` once the chart field-Jacobian's
    base-continuity is banked), compactness (`IsCompact.exists_bound_of_continuousOn`, NO `.choose`)
    yields the collar-restricted `M₁chart` bound in the EXACT `amplitudeDataOn_concrete.hM₁chart`
    carry shape.  NOT `a₁ = R/6`. -/
theorem baseSlotAmpDeriv1_sup_onCollar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c τ₀ : ℝ) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun p : ℝ × Point n => pd (chartAmp g gi hC hK a b p.1 p.2) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
      |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁ := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨CA, hCA⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨2 * max CA 0, mul_nonneg (by norm_num) (le_max_right _ _), fun τ z hreg => ?_⟩
  obtain ⟨hτpos, hττ₀, _hzK, hzρ, _hzc⟩ := hreg
  have hzball : z ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzρ.le
  have hbd := hCA (τ, z) ⟨⟨hτpos.le, hττ₀⟩, hzball⟩
  rw [Real.norm_eq_abs] at hbd
  calc |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)|
        = 2 * |pd (chartAmp g gi hC hK a b τ z) i 0| := by rw [abs_mul]; norm_num
    _ ≤ 2 * max CA 0 :=
        mul_le_mul_of_nonneg_left (le_trans hbd (le_max_left _ _)) (by norm_num)

/-- **★★ `baseSlotAmpDeriv2_sup_onCollar` — `C₂` / `M₂chart` GROUNDED.**  Same as
    `baseSlotAmpDeriv1_sup_onCollar`, one derivative order up: given the JOINT continuity of the
    SECOND field-derivative field `(τ, z) ↦ pd (fun y => pd (chartAmp … τ z ·) i y) i 0` on
    `[0,τ₀] ×ˢ closedBall 0 ρ`, compactness yields the collar-restricted `M₂chart` bound in the EXACT
    `amplitudeDataOn_concrete.hM₂chart` carry shape.  NOT `a₁ = R/6`. -/
theorem baseSlotAmpDeriv2_sup_onCollar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c τ₀ : ℝ) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hcont : ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (chartAmp g gi hC hK a b p.1 p.2) i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
      |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂ := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨CA, hCA⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max CA 0, le_max_right _ _, fun τ z hreg => ?_⟩
  obtain ⟨hτpos, hττ₀, _hzK, hzρ, _hzc⟩ := hreg
  have hzball : z ∈ Metric.closedBall (0 : Point n) ρ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hzρ.le
  have hbd := hCA (τ, z) ⟨⟨hτpos.le, hττ₀⟩, hzball⟩
  rw [Real.norm_eq_abs] at hbd
  exact le_trans hbd (le_max_left _ _)

/-! ###############################################################################
    ### ★★★ THE PACKAGE.
    ############################################################################### -/

/-- **★★★ `supConstant_phase2` — the sup/constant family, phase 2.**  Packages the J4-431 phase-1
    amplitude center-value sup `M₀chart` (UNCONDITIONAL, `chartAmp_center_sup_onCollar`) together with
    the two derivative sups `M₁chart`/`M₂chart` (= the `C₁`/`C₂` content, and hence — combined with the
    banked `F` Gaussian bound + `rhoRatio_le_collarK` — the `M`/`Sconst` products), each GROUNDED by
    compactness CONDITIONAL on the atomic joint-continuity carry of the (explicitly identified via
    `pd_chartAmp_center_eq`) field-derivative fields.  All three are in the collar carry shapes consumed
    by `amplitudeDataOn_concrete`.  NOT `a₁ = R/6`. -/
theorem supConstant_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hcont1 : ContinuousOn (fun p : ℝ × Point n => pd (chartAmp g gi hC hK a b p.1 p.2) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ))
    (hcont2 : ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (chartAmp g gi hC hK a b p.1 p.2) i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)) :
    (∃ ρ₀ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
        ∀ τ z, collarRegime (K := K) ρ₀ c τ₀ τ z → |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
    ∧ (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
    ∧ (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂) :=
  ⟨chartAmp_center_sup_onCollar g gi hC hK h0Kmem hg hgi hgpos a b c τ₀,
   baseSlotAmpDeriv1_sup_onCollar g gi hC hK a b c τ₀ i ρ hρ hcont1,
   baseSlotAmpDeriv2_sup_onCollar g gi hC hK a b c τ₀ i ρ hρ hcont2⟩

end QIQTH.BaseSlotAmpDeriv

/-! ## THE SUP LEDGER v2 — the honest per-constant table after J4-432.

  Each sup/constant is classified GROUNDED (unconditional) / GROUNDED-CONDITIONAL (on the single named
  atomic carry) / with the exact obstruction named.

    ┌──────────┬───────────────────────────────────────────────────────────────────────────────────┐
    │ CONSTANT │ STATUS (post J4-432)                                                                 │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C_L      │ GROUNDED (banked).  `SupConstantFamily.levi_C_L_grounded`.                           │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ Mqc /    │ GROUNDED (amplitude factor), collar-restricted.  `SupConstantFamily.chartAmp_center_ │
    │ M₀chart /│ sup_onCollar` (compactness of the continuous BASE-SLOT amplitude field; NO `.choose`).│
    │ M₀ (Aamp)│ Re-exported here as `supConstant_phase2` conjunct 1 (UNCONDITIONAL).                  │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C₁ /     │ GROUNDED-CONDITIONAL.  `baseSlotAmpDeriv1_sup_onCollar` grounds `M₁chart` (the        │
    │ M₁chart  │ `-2·∂ᵢchartAmp 0` sup) by compactness, CONDITIONAL on the ONE atomic carry             │
    │          │ `hcont1` = joint continuity of `(τ,z) ↦ pd (chartAmp … τ z ·) i 0`.  The derivative   │
    │          │ is now EXPLICITLY IDENTIFIED (`pd_chartAmp_center_eq`):                              │
    │          │   `= fderiv (manifoldAmp … τ) (W z 0) (fderiv (W z) 0 eᵢ)`.  `hcont1` reduces to the  │
    │          │   joint-base continuity of the chart FIELD-Jacobian `z ↦ fderiv (W z) 0` (the first  │
    │          │   factor is banked-continuous).  ⇒ the wall is now ONE atomic geometric carry.       │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ C₂ /     │ GROUNDED-CONDITIONAL.  `baseSlotAmpDeriv2_sup_onCollar` grounds `M₂chart` by          │
    │ M₂chart  │ compactness, CONDITIONAL on `hcont2` (second field-derivative field continuity), the  │
    │          │ same atomic carry one derivative order up.                                           │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ M        │ GROUNDED-CONDITIONAL (via M₁chart).  `M = sup|A1amp·F| = sup|ρ·(−2∂ᵢchartAmp 0)·F|`;  │
    │          │ `F` is `z`-uniformly Gaussian-bounded, `ρ ≤ collarK` (`rhoRatio_le_collarK`), and the │
    │          │ `−2∂ᵢchartAmp 0` factor is grounded by `baseSlotAmpDeriv1_sup_onCollar` (conjunct 2). │
    ├──────────┼───────────────────────────────────────────────────────────────────────────────────┤
    │ Sconst   │ GROUNDED-CONDITIONAL (via M₂chart).  `Sconst = sup|A2amp·F| = sup|ρ·(∂ᵢ²chartAmp 0)·F|`│
    │          │ — same as M, one derivative order up (via `baseSlotAmpDeriv2_sup_onCollar`).          │
    └──────────┴───────────────────────────────────────────────────────────────────────────────────┘

  THE EXACT OBSTRUCTION (Sol #21 / J4-433).  The atomic carry `hcont1`/`hcont2` reduces — through the
  explicit identification `pd_chartAmp_center_eq` — to the JOINT-in-base continuity of the chart
  FIELD-slot Jacobian at the field centre:
      `ContinuousOn (fun z => fderiv ℝ (uniformInverseChart g gi hC hK z) 0) U`
  (equivalently joint `C¹` of `(z, x') ↦ uniformInverseChart g gi hC hK z x'` near `(·, 0)`).  This is
  the recognized J3 base-point-regularity blocker (`FlowJointRegularity`/`BasepointFDeriv`).  The CoV
  bundle supplies ONLY the base-derivative of the CENTER VALUE `z ↦ W z 0`, a DIFFERENT jet.  THE
  `.choose` TRAP is respected: we NEVER sup a `.choose` germ — the compactness sups run over the ACTUAL
  identified derivative field UNDER the explicit continuity hypothesis.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.BaseSlotAmpDeriv
#print axioms manifoldAmp_contDiffAt
#print axioms pd_chartFieldAmp_center_eq
#print axioms pd_chartAmp_center_eq
#print axioms baseSlotAmpDeriv1_sup_onCollar
#print axioms baseSlotAmpDeriv2_sup_onCollar
#print axioms supConstant_phase2
end AxiomChecks
