/-
  AmplitudeSecondJet — J4-487: the AMPLITUDE 2nd-order chain-rule assembly for `hcont2` / `C₂` — closing
  the C₂ derivative-sup on the (I1) reachability input `hReach`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is ONE
  brick of the convergence-trio campaign.  No `sorry` (header prose excepted), no `:= True`, no new
  axioms, no vacuous / unsatisfiable hypotheses, no result that is a conclusion-in-disguise.  std-3
  only.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  The `C₂` consumer `hcont2` (`SupFamilyFirstOrder.supConstant_phase3`'s last, still
  opaque, joint-continuity slot) is the SECOND field-partial of the concrete chart amplitude
        `(τ, z) ↦ pd (fun y => pd (chartAmp … τ z ·) i y) i 0`,   `chartAmp … τ z = manifoldAmp … τ ∘ W_z`,
  `W_z = uniformInverseChart g gi hC hK z`.  The 2nd-order chain rule
  (`HeatResidualBound.pd_pd_comp_local`) expands it into FOUR jointly-continuous blocks:
      (Hessian) `∑ₐ (∑_b pd²(manifoldAmp)·pd(W·b))·pd(W·a)`  +  (gradient) `∑ₐ pd(manifoldAmp)·pd²(W·a)`.
  Three blocks are pure-Mathlib / banked bookkeeping; the FOURTH — the raw-chart second jet `pd²(W·a)` —
  is the ONLY genuine second-variation analytic wall, and is delivered (gated by the (I1) `hReach`) by
  `OperatorPdBridge.chartSecondJetComponent_continuousOn_of_reach`.

  ## THE TWO GATES (this file).
    (a) `manifoldAmp_fderiv2_continuous` — the manifold-amplitude SECOND-derivative field
        `(τ, w) ↦ fderiv² (manifoldAmp … τ) w` is JOINTLY CONTINUOUS.  The `J4-436` affine-in-`τ` insight
        one order up: `manifoldAmp … τ = c₀ + τ·c₁` (each `c_k` a `C²` `w`-factor), so its `w`-Hessian is
        `fderiv²c₀ + τ·fderiv²c₁`, and `w ↦ fderiv²c_k` is continuous (`c_k` is `C²`).  Geometry-only.
    (b) the `pd_pd_comp_local` assembly of the four blocks — the `J4-478` `SmoothCarrierGrounding`
        4-block route, swapping the raw-chart block for the `J4-486` delivery and the profile blocks for
        the amplitude blocks (`manifoldAmp_fderiv_continuous` / `manifoldAmp_fderiv2_continuous`).

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `pd_pd_scalar_eq`               — the SCALAR coordinate gate `pd ∘ pd f = a coordinate of fderiv² f`
      (the `OperatorPdBridge.pd_pd_component_eq` pattern, scalar codomain — no `proj`).
    * `manifoldAmp_fderiv2_continuous` — ★ THE HESSIAN GATE (a); the affine-in-`τ` joint continuity of the
      manifold-amplitude second-derivative field.
    * `hcont2_of_reach`              — ★★ the `C₂` box: the SECOND field-partial of `chartAmp` is
      `ContinuousOn` on `[0,τ₀] ×ˢ closedBall 0 ρ`, gated by (I1) `hReach` + the standing geometric
      carries — the EXACT `supConstant_phase3` `hcont2` shape.
    * `supConstant_phase4`           — ★★★ the sup family, phase 4: `M₀`/`M₁`/`M₂` all grounded MODULO
      (I1) — the last derivative slot `C₂` now rests on the geometric input, no opaque analytic carry.

  ⚠ CARRIED (labelled, satisfiable, non-vacuous, NEVER a conclusion): the (I1) `hReach`, and the standing
    geometric carries of `chartSecondJet` / the first-order sup (`hW0`/`horigin`/`hunit`/`hid2`/`hJac`/
    `hreg`/`hUK`).  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.SupFamilyFirstOrder
import QIQTH.OperatorPdBridge
import QIQTH.PullbackNaturalityLocal

open Filter Set MeasureTheory
open QIQTH.Curvature QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.RadialDistance
open QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar QIQTH.SupConstantFamily
open QIQTH.BaseSlotAmpDeriv QIQTH.SupFamilyFirstOrder QIQTH.OperatorPdBridge
open QIQTH.HuInftyRebase
open scoped Topology ContDiff

namespace QIQTH.AmplitudeSecondJet

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (A) The SCALAR coordinate gate — `pd ∘ pd f` = a coordinate of `fderiv² f`.
    ############################################################################### -/

/-- **`pd_pd_scalar_eq` — the scalar coordinate gate.**  The scalar analogue of
    `OperatorPdBridge.pd_pd_component_eq` (no output component `c`).  For a scalar field `f : Point n → ℝ`
    differentiable in a NEIGHBOURHOOD of `x` (`hf`) whose derivative field `y ↦ fderiv ℝ f y` is
    differentiable AT `x` (`hf2`),
      `pd (fun w => pd f a' w) b' x
         = fderiv ℝ (fun y => fderiv ℝ f y) x (Pi.single b' 1) (Pi.single a' 1)`.
    Mechanism: the inner `pd f a'` equals — near `x`, via `pd_eq_fderiv` — the scalar evaluation
    `Λ (fderiv ℝ f ·)`, `Λ = apply e_{a'}`; `pd_congr_nhds` transports the outer `pd`, `pd_eq_fderiv` +
    the CLM chain rule (`Λ.hasFDerivAt.comp`) extract the `e_{b'}`-coordinate.  NOT `a₁ = R/6`. -/
theorem pd_pd_scalar_eq (f : Point n → ℝ) (a' b' : Fin n) (x : Point n)
    (hf : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y)
    (hf2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x) :
    pd (fun w => pd f a' w) b' x
      = fderiv ℝ (fun y => fderiv ℝ f y) x (Pi.single b' (1 : ℝ)) (Pi.single a' (1 : ℝ)) := by
  classical
  set Λ : (Point n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single a' (1 : ℝ)) with hΛdef
  have hev : (fun w => pd f a' w) =ᶠ[nhds x] (fun w => Λ (fderiv ℝ f w)) := by
    filter_upwards [hf] with y hy
    have hpc := pd_eq_fderiv f a' y hy
    simp only [hΛdef, ContinuousLinearMap.apply_apply]
    exact hpc
  have hcomp : HasFDerivAt (fun w => Λ (fderiv ℝ f w))
      (Λ.comp (fderiv ℝ (fun y => fderiv ℝ f y) x)) x :=
    Λ.hasFDerivAt.comp x hf2.hasFDerivAt
  rw [QIQTH.PullbackMetric.pd_congr_nhds b' x hev, pd_eq_fderiv _ b' x hcomp.differentiableAt,
    hcomp.fderiv]
  simp only [hΛdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-! ###############################################################################
    ### ★ (B) THE HESSIAN GATE (a) — `manifoldAmp` second-derivative joint continuity.
    ############################################################################### -/

/-- **★ `manifoldAmp_fderiv2_continuous` — the manifold-amplitude SECOND-derivative field is jointly
    continuous.**  `(τ, w) ↦ fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b τ) y) w` is `Continuous`
    on `ℝ × Point n`.  The `J4-436` affine-in-`τ` insight ONE ORDER UP: `manifoldAmp g gi a b τ =
    c₀ + τ·c₁` with `c_k` the `C²` `w`-factors, so `fderiv (manifoldAmp … τ) = fderiv c₀ + τ • fderiv c₁`
    and hence `fderiv² (manifoldAmp … τ) = fderiv (fderiv c₀) + τ • fderiv (fderiv c₁)`; each
    `w ↦ fderiv (fderiv c_k) w` is continuous (`c_k` is `C²` ⟹ `fderiv c_k` is `C¹`,
    `ContDiff.continuous_fderiv`), and the affine-in-`τ` assembly is jointly continuous.  Geometry-only.
    NOT `a₁ = R/6`. -/
theorem manifoldAmp_fderiv2_continuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b : ℝ) :
    Continuous (fun p : ℝ × Point n =>
      fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b p.1) y) p.2) := by
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
  -- `fderiv c_k` is `C¹`, hence `fderiv (fderiv c_k)` is continuous
  have hd0 : ContDiff ℝ 1 (fderiv ℝ c0) := hcd0.fderiv_right (by norm_num)
  have hd1 : ContDiff ℝ 1 (fderiv ℝ c1) := hcd1.fderiv_right (by norm_num)
  have hFF0 : Continuous (fderiv ℝ (fderiv ℝ c0)) := hd0.continuous_fderiv (by norm_num)
  have hFF1 : Continuous (fderiv ℝ (fderiv ℝ c1)) := hd1.continuous_fderiv (by norm_num)
  -- the affine-in-`τ` presentation and its first derivative (the J4-436 stepping stone)
  have heq : ∀ τ : ℝ, manifoldAmp g gi a b τ = fun w => c0 w + c1 w * τ := by
    intro τ; funext w
    simp only [hc0, hc1, manifoldAmp]
    ring
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
  -- the SECOND `w`-Fréchet derivative of `manifoldAmp … τ` (the affine trick one order up)
  have hid2 : ∀ (τ : ℝ) (w : Point n),
      fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b τ) y) w
        = fderiv ℝ (fderiv ℝ c0) w + τ • fderiv ℝ (fderiv ℝ c1) w := by
    intro τ w
    have hfun : (fun y => fderiv ℝ (manifoldAmp g gi a b τ) y)
        = (fun y => fderiv ℝ c0 y + τ • fderiv ℝ c1 y) := by
      funext y; exact hid τ y
    rw [hfun]
    have hb0 : HasFDerivAt (fun y => fderiv ℝ c0 y) (fderiv ℝ (fderiv ℝ c0) w) w :=
      ((hd0.differentiable (by norm_num)).differentiableAt).hasFDerivAt
    have hb1 : HasFDerivAt (fun y => fderiv ℝ c1 y) (fderiv ℝ (fderiv ℝ c1) w) w :=
      ((hd1.differentiable (by norm_num)).differentiableAt).hasFDerivAt
    have hb1c : HasFDerivAt (fun y => τ • fderiv ℝ c1 y) (τ • fderiv ℝ (fderiv ℝ c1) w) w :=
      hb1.const_smul τ
    have hsum : HasFDerivAt (fun y => fderiv ℝ c0 y + τ • fderiv ℝ c1 y)
        (fderiv ℝ (fderiv ℝ c0) w + τ • fderiv ℝ (fderiv ℝ c1) w) w := hb0.add hb1c
    exact hsum.fderiv
  -- assemble the joint continuity
  have hfun : (fun p : ℝ × Point n =>
        fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b p.1) y) p.2)
      = (fun p : ℝ × Point n =>
        fderiv ℝ (fderiv ℝ c0) p.2 + p.1 • fderiv ℝ (fderiv ℝ c1) p.2) := by
    funext p; exact hid2 p.1 p.2
  rw [hfun]
  exact (hFF0.comp continuous_snd).add (continuous_fst.smul (hFF1.comp continuous_snd))

/-! ###############################################################################
    ### ★★ (C) THE C₂ BOX — the 4-block chain-rule assembly, gated by (I1) `hReach`.
    ############################################################################### -/

/-- **`chartAmp_eq_manifoldAmp_comp`.**  The concrete chart amplitude factors THROUGH the manifold
    amplitude by composition with the field-slot inverse chart:
      `chartAmp g gi hC hK a b τ z = fun x' => manifoldAmp g gi a b τ (uniformInverseChart g gi hC hK z x')`.
    (Both unfold to the same triple product up to associativity — `ring`.)  NOT `a₁ = R/6`. -/
theorem chartAmp_eq_manifoldAmp_comp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) :
    chartAmp g gi hC hK a b τ z
      = fun x' => manifoldAmp g gi a b τ (uniformInverseChart g gi hC hK z x') := by
  funext x'
  simp only [chartAmp, manifoldAmp]
  ring

/-- **★★ `hcont2_of_reach` — the `C₂` box, gated by (I1).**  On `[0,τ₀] ×ˢ closedBall 0 ρ`, the SECOND
    field-partial of the concrete chart amplitude
      `(τ, z) ↦ pd (fun y => pd (chartAmp … τ z ·) i y) i 0`
    is `ContinuousOn` — the EXACT `SupFamilyFirstOrder.supConstant_phase3` `hcont2` slot.  Mechanism:
    `chartAmp_eq_manifoldAmp_comp` + `pd_pd_comp_local` expand the pd² into the four blocks, each proved
    jointly `ContinuousOn` on the box:
      • Hessian `pd² (manifoldAmp … τ)` ∘ `W`  — `manifoldAmp_fderiv2_continuous` (gate (a)) via the
        scalar gate `pd_pd_scalar_eq`, contracted by `clm_apply`;
      • gradient `pd (manifoldAmp … τ)` ∘ `W`  — banked `manifoldAmp_fderiv_continuous` via `pd_eq_fderiv`;
      • first jet `pd (W·b)`                    — banked `hJac` (chart field-Jacobian) via `pd_component_eq'`;
      • ★ second jet `pd² (W·a)`               — `OperatorPdBridge.chartSecondJetComponent_continuousOn_of_
        reach`, the ONLY genuine second-variation block, gated by (I1) `hReach`.
    Carries (I1) `hReach` + the standing geometric carries `hUK`/`hW0`/`horigin`/`hunit`/`hid2`/`hJac`/
    `hreg` on `closedBall 0 ρ`.  NOT `a₁ = R/6`. -/
theorem hcont2_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    {K : Set (Point n)} (hK : IsCompact K)
    (a b τ₀ : ℝ) (i : Fin n) (ρ : ℝ)
    (hUK : Metric.closedBall (0 : Point n) ρ ⊆ K)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (horigin : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0)))
    (hid2 : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))))
    (hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n)) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (chartAmp g gi hC hK a b p.1 p.2) i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
  classical
  -- the manifold amplitude is `C²` everywhere (side-conditions for the scalar gate / `pd_eq_fderiv`)
  have hmC2 : ∀ (τ : ℝ) (w : Point n), ContDiffAt ℝ 2 (manifoldAmp g gi a b τ) w :=
    fun τ w => manifoldAmp_contDiffAt g gi hg hgi hgpos a b τ w
  -- `Prod.snd` maps the box into the base ball, the origin section and the pair `(τ, W z 0)`
  have hmaps : Set.MapsTo (fun p : ℝ × Point n => p.2)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ)
      (Metric.closedBall (0 : Point n) ρ) := fun p hp => hp.2
  have hW0D : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    hW0.comp continuous_snd.continuousOn hmaps
  have hpair : ContinuousOn
      (fun p : ℝ × Point n => (p.1, uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (continuous_fst.continuousOn).prodMk hW0D
  -- the manifold first/second Fréchet-derivative fields at `W z 0`
  have hA : ContinuousOn
      (fun p : ℝ × Point n =>
        fderiv ℝ (manifoldAmp g gi a b p.1) (uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (manifoldAmp_fderiv_continuous g gi hg hgi hgpos a b).comp_continuousOn hpair
  have hA2 : ContinuousOn
      (fun p : ℝ × Point n =>
        fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b p.1) y)
          (uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (manifoldAmp_fderiv2_continuous g gi hg hgi hgpos a b).comp_continuousOn hpair
  -- BLOCK (Hessian): `pd² (manifoldAmp … τ)` at `W z 0`, coordinate `(b', a')`
  have Fhess : ∀ a' b' : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun w => pd (manifoldAmp g gi a b p.1) a' w) b' (uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
    intro a' b'
    have hknown : ContinuousOn
        (fun p : ℝ × Point n =>
          fderiv ℝ (fun y => fderiv ℝ (manifoldAmp g gi a b p.1) y)
            (uniformInverseChart g gi hC hK p.2 0) (Pi.single b' (1 : ℝ)) (Pi.single a' (1 : ℝ)))
        (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
      (hA2.clm_apply continuousOn_const).clm_apply continuousOn_const
    refine hknown.congr (fun p _ => ?_)
    refine pd_pd_scalar_eq (manifoldAmp g gi a b p.1) a' b'
      (uniformInverseChart g gi hC hK p.2 0) ?_ ?_
    · exact Filter.Eventually.of_forall (fun y => (hmC2 p.1 y).differentiableAt (by norm_num))
    · exact ((hmC2 p.1 (uniformInverseChart g gi hC hK p.2 0)).fderiv_right (m := 1)
        (by norm_num)).differentiableAt (by norm_num)
  -- BLOCK (gradient): `pd (manifoldAmp … τ)` at `W z 0`, coordinate `a'`
  have Fgrad : ∀ a' : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (manifoldAmp g gi a b p.1) a' (uniformInverseChart g gi hC hK p.2 0))
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
    intro a'
    have hknown : ContinuousOn
        (fun p : ℝ × Point n =>
          fderiv ℝ (manifoldAmp g gi a b p.1) (uniformInverseChart g gi hC hK p.2 0)
            (Pi.single a' (1 : ℝ)))
        (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
      hA.clm_apply continuousOn_const
    refine hknown.congr (fun p _ => ?_)
    exact pd_eq_fderiv (manifoldAmp g gi a b p.1) a' (uniformInverseChart g gi hC hK p.2 0)
      ((hmC2 p.1 (uniformInverseChart g gi hC hK p.2 0)).differentiableAt (by norm_num))
  -- BLOCK (first jet): `pd (W·b')` at `0`, base-varying (banked `hJac`)
  have Fjac : ∀ b' : Fin n, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => uniformInverseChart g gi hC hK p.2 y b') i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
    intro b'
    have hballknown : ContinuousOn
        (fun z : Point n =>
          fderiv ℝ (uniformInverseChart g gi hC hK z) 0 (Pi.single i (1 : ℝ)) b')
        (Metric.closedBall (0 : Point n) ρ) :=
      (continuous_apply b').comp_continuousOn (hJac.clm_apply continuousOn_const)
    have hballpd : ContinuousOn
        (fun z : Point n => pd (fun y => uniformInverseChart g gi hC hK z y b') i 0)
        (Metric.closedBall (0 : Point n) ρ) := by
      refine hballknown.congr (fun z hz => ?_)
      exact pd_component_eq' (uniformInverseChart g gi hC hK z) i b' 0
        ((hreg z hz).differentiableAt (by norm_num))
    exact hballpd.comp continuous_snd.continuousOn hmaps
  -- BLOCK ★ (second jet): `pd² (W·a')` at `0`, base-varying — the (I1)-gated wall
  have Fhess2 : ∀ a' : Fin n, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => uniformInverseChart g gi hC hK p.2 z a') i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) := by
    intro a'
    have hball := chartSecondJetComponent_continuousOn_of_reach g gi hC hK hUK hReach hW0
      horigin hunit hid2 hreg a' i i
    exact hball.comp continuous_snd.continuousOn hmaps
  -- ASSEMBLE the four blocks (the `pd_pd_comp_local` RHS shape)
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        (∑ a', (∑ b', pd (fun w => pd (manifoldAmp g gi a b p.1) a' w) b'
                    (uniformInverseChart g gi hC hK p.2 0)
                  * pd (fun y => uniformInverseChart g gi hC hK p.2 y b') i 0)
              * pd (fun y => uniformInverseChart g gi hC hK p.2 y a') i 0)
        + ∑ a', pd (manifoldAmp g gi a b p.1) a' (uniformInverseChart g gi hC hK p.2 0)
              * pd (fun y => pd (fun z => uniformInverseChart g gi hC hK p.2 z a') i y) i 0)
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) ρ) :=
    (continuousOn_finsetSum _ (fun a' _ =>
        (continuousOn_finsetSum _ (fun b' _ => (Fhess a' b').mul (Fjac b'))).mul (Fjac a'))).add
      (continuousOn_finsetSum _ (fun a' _ => (Fgrad a').mul (Fhess2 a')))
  -- transfer through `chartAmp_eq_manifoldAmp_comp` + `pd_pd_comp_local`
  refine hClosed.congr (fun p hp => ?_)
  rw [chartAmp_eq_manifoldAmp_comp g gi hC hK a b p.1 p.2]
  exact pd_pd_comp_local (manifoldAmp g gi a b p.1) (uniformInverseChart g gi hC hK p.2) i i 0
    (hmC2 p.1 (uniformInverseChart g gi hC hK p.2 0))
    (contDiffAt_pi.mp (hreg p.2 hp.2))

/-! ###############################################################################
    ### ★★★ THE PACKAGE — the sup family, phase 4 (C₂ grounded modulo (I1)).
    ############################################################################### -/

/-- **★★★ `supConstant_phase4` — the sup/constant family, phase 4.**  Feeds `hcont2_of_reach` into
    `SupFamilyFirstOrder.supConstant_phase3`, discharging the last opaque `C₂` joint-continuity slot.
    All three sups — the amplitude center-value `M₀chart` (UNCONDITIONAL), the first-derivative `M₁chart`
    (grounded from the geometric facts), and now the second-derivative `M₂chart` (= `C₂`, and hence the
    `Sconst` content) — are grounded, the LAST resting on the (I1) `hReach` input + bookkeeping, never on
    `a₁ = R/6`.  Carries (I1) `hReach` + the standing geometric carries on `closedBall 0 ρ`.
    NOT `a₁ = R/6`. -/
theorem supConstant_phase4 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b c τ₀ : ℝ) (i : Fin n) (ρ : ℝ) (hρ : 0 < ρ)
    (hUK : Metric.closedBall (0 : Point n) ρ ⊆ K)
    (hReach : ∀ q ∈ K, uniformFlowRadius g gi hC hK ≤ expRho g gi hC q)
    (hW0 : ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0)
      (Metric.closedBall (0 : Point n) ρ))
    (horigin : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ‖uniformInverseChart g gi hC hK z 0‖ < uniformFlowRadius g gi hC hK)
    (hunit : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      IsUnit (fderiv ℝ (uniformFlowExp g gi hC hK z) (uniformInverseChart g gi hC hK z 0)))
    (hid2 : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      fderiv ℝ (fun y => fderiv ℝ (uniformInverseChart g gi hC hK z) y) 0
        = (-ContinuousLinearMap.mulLeftRight ℝ (Point n →L[ℝ] Point n)
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))
              (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
                (uniformInverseChart g gi hC hK z 0)))).comp
          ((fderiv ℝ (fderiv ℝ (uniformFlowExp g gi hC hK z))
                (uniformInverseChart g gi hC hK z 0)).comp
            (Ring.inverse (fderiv ℝ (uniformFlowExp g gi hC hK z)
              (uniformInverseChart g gi hC hK z 0)))))
    (hJac : ContinuousOn (fun z : Point n => fderiv ℝ (uniformInverseChart g gi hC hK z) 0)
      (Metric.closedBall (0 : Point n) ρ))
    (hreg : ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
      ContDiffAt ℝ 2 (uniformInverseChart g gi hC hK z) (0 : Point n)) :
    (∃ ρ₀ > (0 : ℝ), ∃ M₀ : ℝ, 0 ≤ M₀ ∧
        ∀ τ z, collarRegime (K := K) ρ₀ c τ₀ τ z → |chartAmp g gi hC hK a b τ z 0| ≤ M₀)
    ∧ (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |(-2 * pd (chartAmp g gi hC hK a b τ z) i 0)| ≤ M₁)
    ∧ (∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ τ z, collarRegime (K := K) ρ c τ₀ τ z →
        |pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0| ≤ M₂) :=
  supConstant_phase3 g gi hC hK h0Kmem hg hgi hgpos a b c τ₀ i ρ hρ hreg hW0 hJac
    (hcont2_of_reach g gi hC hg hgi hgpos hK a b τ₀ i ρ hUK hReach hW0 horigin hunit hid2 hJac hreg)

end QIQTH.AmplitudeSecondJet

/-! ## THE C2 LEDGER (post J4-487).

  ┌───────────────────────────────────────────────────────────────────────────────────────────────┐
  │  THE C₂ CONSUMER.  `SupFamilyFirstOrder.supConstant_phase3` grounded `M₀`/`M₁` but carried the     │
  │  opaque 2nd-order joint-continuity `hcont2` — the SECOND field-partial of the concrete chart        │
  │  amplitude `(τ,z) ↦ pd (fun y => pd (chartAmp … τ z ·) i y) i 0` — as its last derivative slot.     │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE 2nd-ORDER CHAIN RULE.  `chartAmp … τ z = manifoldAmp … τ ∘ W_z`; `pd_pd_comp_local` expands     │
  │  the pd² into FOUR jointly-continuous blocks:                                                       │
  │    (Hessian)  `pd² (manifoldAmp) ∘ W`  — `manifoldAmp_fderiv2_continuous` (the affine-in-τ Hessian   │
  │               joint continuity, GATE (a)) via the scalar gate `pd_pd_scalar_eq` + `clm_apply`;        │
  │    (gradient) `pd (manifoldAmp) ∘ W`   — banked `manifoldAmp_fderiv_continuous` via `pd_eq_fderiv`;   │
  │    (first jet) `pd (W·b)`              — banked `hJac` via `pd_component_eq'`;                        │
  │    ★ (second jet) `pd² (W·a)`         — the ONLY genuine second-variation block, delivered by        │
  │               `OperatorPdBridge.chartSecondJetComponent_continuousOn_of_reach`, GATED by (I1)         │
  │               `hReach` (through `Hfwd2Weld.chartSecondJet_continuousOn_of_reach`).                    │
  ├───────────────────────────────────────────────────────────────────────────────────────────────┤
  │  THE OUTCOME.  `hcont2_of_reach` produces `hcont2` in the EXACT `supConstant_phase3` shape, gated    │
  │  by (I1) + the standing geometric carries.  `supConstant_phase4` discharges the last `C₂` slot:      │
  │  M₀ (UNCONDITIONAL) ∧ M₁ (geometric facts) ∧ M₂ = C₂ (now on (I1) + bookkeeping).                    │
  └───────────────────────────────────────────────────────────────────────────────────────────────┘

  ── C₂ STATUS.  C₂ / M₂chart / Sconst are GROUNDED MODULO (I1): the sup family's last derivative slot
  now rests on the geometric reachability input `hReach` + banked chain-rule bookkeeping.  The raw-chart
  SECOND-jet block — the sole genuine second-variation analytic wall — is the ONLY block riding on
  `hReach`; the other three blocks (manifold Hessian/gradient joint continuity + chart first-jet) are
  pure-Mathlib / banked.  NEVER `a₁ = R/6`.

  ── DONT-UNDERCREDIT findings.
    * The manifold-amplitude Hessian joint continuity is NOT a new wall: it is the `J4-436`
      `manifoldAmp_fderiv_continuous` affine-in-τ trick ONE ORDER UP (`c₀ + τ·c₁`, each `c_k` `C²`).
    * The scalar coordinate gate `pd_pd_scalar_eq` is NOT a new wall: it is the `OperatorPdBridge.
      pd_pd_component_eq` evaluation-CLM pattern with a scalar codomain (no output `proj`).
    * The raw-chart second-jet block is already delivered by the `J4-486` bridge; this brick only
      ASSEMBLES it with the (banked / gate-(a)) amplitude blocks via `pd_pd_comp_local` — the `J4-478`
      `SmoothCarrierGrounding` 4-block route, re-used verbatim in shape.

  ⚠ NOT `a₁ = R/6`.  a₁ = R/6 remains CONDITIONAL (on (I1) `hReach`, the banked convergence trio, and the
  geometric wiring).
-/

section AxiomChecks
open QIQTH.AmplitudeSecondJet
#print axioms pd_pd_scalar_eq
#print axioms manifoldAmp_fderiv2_continuous
#print axioms hcont2_of_reach
#print axioms supConstant_phase4
end AxiomChecks
