/-
  ChartJetFactsDischarge — J4-288: the CHART-JET FACTS discharge for the boundary-chain
  `E`-continuity capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `QIQTH.ChartComposedHeatOp.heatOpGatedWitness_jointContinuousOn_final` (J4-287) proves
  the joint `(τ,z)`-continuity of the concrete gated van-Vleck witness heat operator on
  `Icc t₁ t₂ ×ˢ closedBall 0 R`, but CARRIES three genuine CHART FACTS about the field-slot base-0
  inverse chart  `W₀ := uniformInverseChart g gi hC hK 0`:

    • `hWc2`      : `∀ z ∈ closedBall 0 R, ∀ c, ContDiffAt ℝ 2 (fun y => W₀ y c) z`,
    • `hWc1cont`  : `∀ c i, ContinuousOn (fun p => pd (fun y => W₀ y c) i p.2)
                          (Icc t₁ t₂ ×ˢ closedBall 0 R)`,
    • `hWc2cont`  : `∀ c i j, ContinuousOn (fun p => pd (fun y => pd (fun z => W₀ z c) j y) i p.2)
                          (Icc t₁ t₂ ×ˢ closedBall 0 R)`.

  This file DISCHARGES those three carries from the CHART BANK
  (`ChartJetBounds.chartField_contDiffAt_center` : `ContDiffAt ℝ 2 W₀ 0`), and composes the result into
  a `heatOpGatedWitness_jointContinuousOn_chartFree` capstone in which the three chart facts are
  INTERNAL — leaving only the honest coefficient/geometry carries.

  ── THE PLAN (J1–J5).
     • (J1) `chartField_contDiffOn_ball` — from the CENTRE `ContDiffAt ℝ 2 W₀ 0` extract an OPEN ball
       `ball 0 ρc` (`ρc > 0`) on which `W₀ ∈ ContDiffOn ℝ 2` (`ContDiffAt.contDiffOn` +
       `Metric.mem_nhds_iff`).  `chartField_contDiffOn_closedBall` records the closed-ball form.
     • (J2) `hWc2_of_contDiffOn_ball` — per-component `ContDiffAt ℝ 2` at every `z ∈ closedBall 0 R`
       with `R < ρc` (interior point of `ball 0 ρc` ⟹ `ContDiffOn.contDiffAt`; component via
       `contDiff_apply`).
     • (J3) `hWc1cont_of_contDiffOn_ball` — the FIRST-jet continuity `pd (W₀·c) i`, from `C²` on the
       ball (`pd = fderiv(·)(eᵢ)`, `fderiv` of a `C²` field is `C¹` hence continuous), restricted to
       `closedBall 0 R` and lifted to the `(τ,z)`-slot (composition with `Prod.snd`).
     • (J4) `hWc2cont_of_contDiffOn_ball` — the SECOND-jet continuity `pd (pd (W₀·c) j) i`, from `C²`
       on the ball ONLY (two coordinate derivatives; `pd∘pd` continuous where the field is `C²`), via
       the germ-local `pd_congr_of_eventuallyEq` + the `fderiv`-of-`fderiv` chain, restricted+lifted.
     • (J5) `heatOpGatedWitness_jointContinuousOn_chartFree` — J4-287's final with the THREE chart
       facts INTERNAL: `∃ ρc > 0, ∀ R, 0 < R → R < ρc → …carries… → ContinuousOn E …`.

  ── MINIMAL HONEST CARRY LIST of J5 (after internalising the chart facts): the g-level COEFFICIENT
     regularity `hw`/`hΘc`/`hΘne`/`huc` (van-Vleck + transport smoothness; satisfiable from `g`-smooth
     + `det g > 0` via the van-Vleck bank, kept as carries to keep the statement `g`-agnostic), the
     per-`R` GEOMETRY continuities `hgi`/`hChr`, the gate data `hSopen`/`hsub`, and the cutoff germ
     `hcut`.  NONE is the conclusion; the chart facts are the only carries this file removes.

  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no `:= True`, no conclusion-as-hypothesis.
     The three discharged chart facts are genuine local regularity of `W₀` on a ball inside its `C²`
     region — DERIVED here, not assumed.  This file only RELOCATES the boundary-chain regularity onto
     the inverse chart; the curvature value is untouched.  **NOT `a₁ = R/6`.**
-/
import Mathlib
import QIQTH.ChartComposedHeatOp
import QIQTH.ChartJetBounds
import QIQTH.JacobianRadial

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.HeatParametrixOrder
open QIQTH.ParametrixPartsContinuity QIQTH.ParametrixSpatialPartials
open QIQTH.GatedWitnessHeatOpBridge
open QIQTH.ChartComposedHeatOp
open scoped Topology ContDiff

namespace QIQTH.ChartJetFactsDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## Generic scalar pd-continuity engines on an OPEN set (C² ⟹ jet continuity).
    ############################################################################### -/

/-- **First-jet continuity on an open set.**  If a scalar field `f` is `ContDiffOn ℝ 2` on an open set
    `s`, then its coordinate partial `∂ᵢf = pd f i` is `ContinuousOn s`.  Route: on `s` the field is
    differentiable so `pd f i = fderiv f (·)(eᵢ)` (`pd_eq_fderiv`), and `fderiv f` is `ContDiffOn ℝ 1`
    on the open `s` (`fderiv_of_isOpen`), hence continuous.  (`C¹` would suffice; we carry `C²`.) -/
theorem pd_continuousOn_open (f : Point n → ℝ) (i : Fin n) {s : Set (Point n)}
    (hs : IsOpen s) (hf : ContDiffOn ℝ 2 f s) :
    ContinuousOn (fun w => pd f i w) s := by
  have hdiffOn : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  have hfd_cd : ContDiffOn ℝ 1 (fun w => fderiv ℝ f w) s := hf.fderiv_of_isOpen hs (by norm_num)
  have hfd_cont : ContinuousOn (fun w => fderiv ℝ f w (Pi.single i (1 : ℝ))) s :=
    hfd_cd.continuousOn.clm_apply continuousOn_const
  refine hfd_cont.congr ?_
  intro w hw
  exact pd_eq_fderiv f i w (hdiffOn.differentiableAt (hs.mem_nhds hw))

/-- **Second-jet continuity on an open set.**  If a scalar field `f` is `ContDiffOn ℝ 2` on an open set
    `s`, then the mixed second coordinate partial `∂ᵢ∂ⱼf = pd (pd f j) i` is `ContinuousOn s`.  `C²` is
    exactly enough (two coordinate derivatives, continuity only).  Route: `Gⱼ := fderiv f (·)(eⱼ)` is
    `ContDiffOn ℝ 1` on `s`; `pd f j = Gⱼ` on `s` (`pd_eq_fderiv`) so `pd (pd f j) i = pd Gⱼ i` on `s`
    (`pd_congr_of_eventuallyEq`, `pd` is germ-local); and `pd Gⱼ i = fderiv Gⱼ (·)(eᵢ)` with `fderiv Gⱼ`
    `ContDiffOn ℝ 0` on `s`, hence continuous. -/
theorem pd_pd_continuousOn_open (f : Point n → ℝ) (i j : Fin n) {s : Set (Point n)}
    (hs : IsOpen s) (hf : ContDiffOn ℝ 2 f s) :
    ContinuousOn (fun w => pd (fun y => pd f j y) i w) s := by
  -- `Gⱼ = fderiv f (·)(eⱼ)` is `C¹` on `s`.
  have hfd_cd : ContDiffOn ℝ 1 (fun w => fderiv ℝ f w) s := hf.fderiv_of_isOpen hs (by norm_num)
  have hGj_cd : ContDiffOn ℝ 1 (fun w => fderiv ℝ f w (Pi.single j (1 : ℝ))) s :=
    hfd_cd.clm_apply contDiffOn_const
  have hGj_diffOn : DifferentiableOn ℝ (fun w => fderiv ℝ f w (Pi.single j (1 : ℝ))) s :=
    hGj_cd.differentiableOn (by norm_num)
  -- `fderiv Gⱼ (·)(eᵢ)` continuous on `s`.
  have hGjfd_cd : ContDiffOn ℝ 0
      (fun w => fderiv ℝ (fun u => fderiv ℝ f u (Pi.single j (1 : ℝ))) w) s :=
    hGj_cd.fderiv_of_isOpen hs (by norm_num)
  have hGjfd_cont : ContinuousOn
      (fun w => fderiv ℝ (fun u => fderiv ℝ f u (Pi.single j (1 : ℝ))) w (Pi.single i (1 : ℝ))) s :=
    hGjfd_cd.continuousOn.clm_apply continuousOn_const
  -- `pd Gⱼ i` continuous on `s`.
  have hpdGj_cont : ContinuousOn
      (fun w => pd (fun y => fderiv ℝ f y (Pi.single j (1 : ℝ))) i w) s := by
    refine hGjfd_cont.congr ?_
    intro w hw
    exact pd_eq_fderiv (fun y => fderiv ℝ f y (Pi.single j (1 : ℝ))) i w
      (hGj_diffOn.differentiableAt (hs.mem_nhds hw))
  -- transfer to `pd (pd f j) i` via the germ-local congruence of the inner first jet.
  have hf_diffOn : DifferentiableOn ℝ f s := hf.differentiableOn (by norm_num)
  refine hpdGj_cont.congr ?_
  intro w hw
  have hInnerEqOn : Set.EqOn (fun y => pd f j y)
      (fun y => fderiv ℝ f y (Pi.single j (1 : ℝ))) s := by
    intro y hy
    exact pd_eq_fderiv f j y (hf_diffOn.differentiableAt (hs.mem_nhds hy))
  exact QIQTH.JacobianRadial.pd_congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hs.mem_nhds hw) hInnerEqOn)

/-- **`(τ,z)`-lift of a `z`-only `ContinuousOn`.**  A field continuous on `closedBall 0 R` lifts to the
    product slab by precomposition with `Prod.snd`. -/
theorem lift_snd {φ : Point n → ℝ} {R : ℝ} (h : ContinuousOn φ (Metric.closedBall 0 R))
    (t₁ t₂ : ℝ) :
    ContinuousOn (fun p : ℝ × Point n => φ p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  h.comp (continuous_snd.continuousOn) (fun _ hp => hp.2)

/-! ###############################################################################
    ## (J1) The base-0 inverse chart is `C²` on a ball.
    ############################################################################### -/

/-- **★ (J1) `chartField_contDiffOn_ball`.**  From the CENTRE `ContDiffAt ℝ 2 W₀ 0`
    (`ChartJetBounds.chartField_contDiffAt_center`, unconditional given `0 ∈ K`) there is an OPEN ball
    `ball 0 ρc` (`ρc > 0`) on which the base-0 inverse chart `W₀ = uniformInverseChart g gi hC hK 0`
    is `ContDiffOn ℝ 2`.  `ContDiffAt.contDiffOn` gives a `𝓝 0`-neighbourhood; `Metric.mem_nhds_iff`
    extracts the ball.  NOT `a₁ = R/6`. -/
theorem chartField_contDiffOn_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ∃ ρc : ℝ, 0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK 0) (Metric.ball 0 ρc) := by
  obtain ⟨u, hu_nhds, hu_cd⟩ :=
    (chartField_contDiffAt_center g gi hC hK h0K).contDiffOn
      (le_refl (2 : WithTop ℕ∞)) (by simp)
  obtain ⟨ρc, hρc, hball⟩ := Metric.mem_nhds_iff.mp hu_nhds
  exact ⟨ρc, hρc, hu_cd.mono hball⟩

/-- **(J1, closed-ball form) `chartField_contDiffOn_closedBall`.**  The same regularity on a definite
    closed ball (half radius), recorded for convenience. -/
theorem chartField_contDiffOn_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    ∃ ρc : ℝ, 0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK 0) (Metric.closedBall 0 ρc) := by
  obtain ⟨ρc, hρc, hball⟩ := chartField_contDiffOn_ball g gi hC hK h0K
  refine ⟨ρc / 2, by positivity, hball.mono ?_⟩
  exact Metric.closedBall_subset_ball (by linarith)

/-! ###############################################################################
    ## (J2)–(J4) The three chart facts from `ContDiffOn ℝ 2` on `ball 0 ρc`.
    ############################################################################### -/

/-- **★ (J2) `hWc2_of_contDiffOn_ball`.**  Per-component `ContDiffAt ℝ 2` of the vector chart `W` at
    every `z ∈ closedBall 0 R` with `R < ρc`: interior of `ball 0 ρc` ⟹ `ContDiffOn.contDiffAt`, then
    the coordinate projection is smooth (`contDiff_apply`).  This is exactly the `hWc2` carry. -/
theorem hWc2_of_contDiffOn_ball (W : Point n → Point n) (ρc R : ℝ) (hR : R < ρc)
    (hW : ContDiffOn ℝ 2 W (Metric.ball 0 ρc)) :
    ∀ z ∈ Metric.closedBall (0 : Point n) R, ∀ c, ContDiffAt ℝ 2 (fun y => W y c) z := by
  intro z hz c
  have hzball : z ∈ Metric.ball (0 : Point n) ρc := Metric.closedBall_subset_ball hR hz
  have hWatz : ContDiffAt ℝ 2 W z := hW.contDiffAt (Metric.isOpen_ball.mem_nhds hzball)
  exact (contDiff_apply ℝ ℝ c).contDiffAt.comp z hWatz

/-- **★ (J3) `hWc1cont_of_contDiffOn_ball`.**  The first coordinate-jet `pd (W·c) i` is jointly
    `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)` for `R < ρc`: component `C²` on the ball
    (`contDiff_apply.comp_contDiffOn`), first jet continuous (`pd_continuousOn_open`), restricted to the
    closed ball and lifted to the `(τ,z)`-slot (`lift_snd`).  This is exactly the `hWc1cont` carry. -/
theorem hWc1cont_of_contDiffOn_ball (W : Point n → Point n) (ρc R t₁ t₂ : ℝ) (hR : R < ρc)
    (hW : ContDiffOn ℝ 2 W (Metric.ball 0 ρc)) :
    ∀ c i, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => W y c) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro c i
  have hcomp : ContDiffOn ℝ 2 (fun y => W y c) (Metric.ball 0 ρc) :=
    (contDiff_apply ℝ ℝ c).comp_contDiffOn hW
  have hz : ContinuousOn (fun w => pd (fun y => W y c) i w) (Metric.ball 0 ρc) :=
    pd_continuousOn_open (fun y => W y c) i Metric.isOpen_ball hcomp
  exact lift_snd (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-- **★ (J4) `hWc2cont_of_contDiffOn_ball`.**  The mixed second coordinate-jet
    `pd (pd (W·c) j) i` is jointly `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)` for `R < ρc`: component
    `C²` on the ball, second jet continuous from `C²` ONLY (`pd_pd_continuousOn_open`), restricted and
    lifted.  This is exactly the `hWc2cont` carry. -/
theorem hWc2cont_of_contDiffOn_ball (W : Point n → Point n) (ρc R t₁ t₂ : ℝ) (hR : R < ρc)
    (hW : ContDiffOn ℝ 2 W (Metric.ball 0 ρc)) :
    ∀ c i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (fun z => W z c) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro c i j
  have hcomp : ContDiffOn ℝ 2 (fun y => W y c) (Metric.ball 0 ρc) :=
    (contDiff_apply ℝ ℝ c).comp_contDiffOn hW
  have hz : ContinuousOn (fun w => pd (fun y => pd (fun z => W z c) j y) i w) (Metric.ball 0 ρc) :=
    pd_pd_continuousOn_open (fun z => W z c) i j Metric.isOpen_ball hcomp
  exact lift_snd (hz.mono (Metric.closedBall_subset_ball hR)) t₁ t₂

/-! ###############################################################################
    ## (J5) The chart-free boundary-chain `E`-continuity capstone.
    ############################################################################### -/

/-- **★★ (J5) `heatOpGatedWitness_jointContinuousOn_chartFree`.**  J4-287's boundary-chain
    `E`-continuity with the THREE chart facts (`hWc2`/`hWc1cont`/`hWc2cont`) made INTERNAL: there is a
    radius `ρc > 0` (the `C²` region of the base-0 inverse chart `W₀`, from J1) such that for EVERY
    `R` with `0 < R < ρc`, given the honest remaining carries — the gate data `hSopen`/`hsub`, the
    cutoff germ `hcut`, the `g`-level coefficient regularity `hw`/`hΘc`/`hΘne`/`huc` (van-Vleck +
    transport smoothness), and the per-`R` geometry continuities `hgi`/`hChr` — the concrete gated
    van-Vleck witness heat operator
      `E := fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0`
    is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`.

    The three chart facts are DISCHARGED (J2–J4) from J1's `ContDiffOn ℝ 2 W₀ (ball 0 ρc)`; none is
    the conclusion.  The kept carries are genuinely about `g`/the gate, not the chart.  **NOT
    `a₁ = R/6`.** -/
theorem heatOpGatedWitness_jointContinuousOn_chartFree (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ : ℝ) (ht₁ : 0 < t₁) (h0K : (0 : Point n) ∈ K)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hΘc : Continuous (vanVleck g)) (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ ρc : ℝ, 0 < ρc ∧ ∀ R : ℝ, 0 < R → R < ρc →
      IsOpen (S 0) →
      Metric.closedBall (0 : Point n) R ⊆ S 0 →
      (∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
        (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK 0 p'))
          =ᶠ[nhds p.2] (fun _ => (1 : ℝ))) →
      (∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) →
      (∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  obtain ⟨ρc, hρc, hball⟩ := chartField_contDiffOn_ball g gi hC hK h0K
  refine ⟨ρc, hρc, fun R hRpos hR hSopen hsub hcut hgi hChr => ?_⟩
  exact heatOpGatedWitness_jointContinuousOn_final g gi hC hK S a b t₁ t₂ R ht₁ h0K hSopen hsub
    hcut hw hΘc hΘne huc hgi hChr
    (hWc2_of_contDiffOn_ball _ ρc R hR hball)
    (hWc1cont_of_contDiffOn_ball _ ρc R t₁ t₂ hR hball)
    (hWc2cont_of_contDiffOn_ball _ ρc R t₁ t₂ hR hball)

end QIQTH.ChartJetFactsDischarge

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ChartJetFactsDischarge
#print axioms pd_continuousOn_open
#print axioms pd_pd_continuousOn_open
#print axioms chartField_contDiffOn_ball
#print axioms hWc2_of_contDiffOn_ball
#print axioms hWc1cont_of_contDiffOn_ball
#print axioms hWc2cont_of_contDiffOn_ball
#print axioms heatOpGatedWitness_jointContinuousOn_chartFree
end AxiomChecks
