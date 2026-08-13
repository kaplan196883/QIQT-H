/-
  WhiteHJetCont — J4-698: THE `hGradCont` / `hHessCont` SUPPLIERS — joint `(τ,z)` continuity of the
  FIRST and SECOND spatial jets of the whitened field, the two chart-jet-continuity residues of
  `white_hLterm_continuousOn_of_jets` (WhiteHLcont.lean, J4-697).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It supplies the
  two joint spatial-jet CONTINUITIES that were the surviving analytic residue of the `Δ_z` reduction.
  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed, nothing wired into
  `QIQTH.lean` / `AxiomAudit`.

  ── THE ENGINE (§A, GENERAL).  For a joint field `H : ℝ × Point n → ℝ` that is `ContDiffAt ℝ 2` at
     every point of a set `s`, the SPATIAL first jet `(τ,z) ↦ ∂_k [H(τ,·)] z` and SPATIAL mixed second
     jet `(τ,z) ↦ ∂_i∂_j [H(τ,·)] z` are `ContinuousOn s`.  Mechanism: `pd` of the `z`-slice equals the
     JOINT Fréchet derivative applied to the block basis vector `(0, e_k)` (`pd_snd_eq_fderiv`, via
     `pd_eq_fderiv` composed with the smooth inclusion `y ↦ (τ,y)`); `fderiv ℝ H` is continuous
     (`ContDiffAt.fderiv_right`), and one order up the field `(τ,z) ↦ fderiv ℝ H (τ,z)(0,e_j)` is again
     `ContDiffAt ℝ 1`, so its own `fderiv` is continuous — the two jets are contractions of these
     continuous derivative fields.  No open-set hypothesis: `ContDiffAt.eventually` supplies the local
     slice-differentiability the second `pd` needs.

  ── THE FLAT GAUSSIAN, JOINTLY (§B).  `(τ,x) ↦ gaussDdim τ x` is `ContDiffAt ℝ ⊤` for `τ > 0` — the
     `√(4πτ)⁻¹·exp(−x²/4τ)` factors are jointly smooth off `τ = 0` (`Real.contDiffAt_sqrt`,
     `ContDiffAt.inv`, `ContDiffAt.div`, `Real.contDiff_exp`), and the `d`-fold product is
     `contDiffAt_prod`.  Flat-space; NOT `a₁ = R/6`.

  ── THE WHITENED CUT KERNEL, JOINTLY (§C).  `H(τ,z) = whiteCutKernel κ … τ z 0
       = radialCutoff a b (V₀ z) · (√det g^κ(0) · gaussDdim τ (V₀ z))`, `V₀ = whiteInvChart κ hκ hKc 0`,
     is `ContDiffAt ℝ 2` at `(τ,z)` whenever `τ > 0` and the chart `V₀` is `ContDiffAt ℝ 2` at `z` (the
     flow-ball germ) — the cutoff / Gaussian factors are jointly smooth (§B), the whitening is a CLM.

  ── THE SUPPLIERS (§D).  On the in-window in-gate positive-time box the gated witness EQUALS the cut
     kernel on a neighbourhood, so their `pd`/`pd∘pd` agree (`pd_congr_nhds`); the engine (§A) at the
     cut-kernel `C²` (§C) then lands `hGradCont` / `hHessCont`, and the capstone feeds them into
     `whiteDefectKernel_jointContinuousOn_modulo_jets` — the `Δ_z` side of the whitened `hbase` fully
     discharged from the flow-ball chart germ.

  ⚠  STILL NOT `a₁ = R/6`.  The jets are a STRICTLY lower-level, DIFFERENT function's continuity.
-/
import Mathlib
import QIQTH.WhiteHLcont
import QIQTH.WhiteS1P2

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp QIQTH.ExpMap
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteS1
open QIQTH.WhiteHBaseReduction QIQTH.WhiteHRepCont QIQTH.WhiteHVcont QIQTH.WhiteHLcont
open QIQTH.HeatParametrixOrder QIQTH.HeatKernelA1
open QIQTH.WhiteS1P1 QIQTH.WhiteS1P2
open scoped Topology BigOperators

namespace QIQTH.WhiteHJetCont

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — THE GENERAL SPATIAL-JET CONTINUITY ENGINE.
    ############################################################################### -/

/-- **`pd_snd_eq_fderiv` — the spatial `pd` as a joint directional Fréchet derivative.**  For a joint
    field `H : ℝ × Point n → ℝ` differentiable at `(τ, z)`, the partial derivative of the `z`-slice
    `y ↦ H(τ,y)` along coordinate `k` equals `DH(τ,z)[(0, e_k)]`. -/
theorem pd_snd_eq_fderiv (H : ℝ × Point n → ℝ) (τ : ℝ) (z : Point n) (k : Fin n)
    (hH : DifferentiableAt ℝ H (τ, z)) :
    pd (fun y => H (τ, y)) k z
      = fderiv ℝ H (τ, z) ((0 : ℝ), (Pi.single k (1 : ℝ) : Point n)) := by
  have hincl : HasFDerivAt (fun y : Point n => (τ, y))
      ((0 : Point n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Point n))) z :=
    (hasFDerivAt_const τ z).prodMk (hasFDerivAt_id z)
  have hcomp : HasFDerivAt (fun y : Point n => H (τ, y))
      ((fderiv ℝ H (τ, z)).comp
        ((0 : Point n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Point n)))) z :=
    hH.hasFDerivAt.comp z hincl
  rw [pd_eq_fderiv (fun y => H (τ, y)) k z hcomp.differentiableAt, hcomp.fderiv]
  simp

/-- **`fderiv_continuousOn_of_contDiffAt`.**  `fderiv ℝ H` is `ContinuousOn s` when `H` is
    `ContDiffAt ℝ 2` on `s` (`ContDiffAt.fderiv_right` at `m = 1`). -/
theorem fderiv_continuousOn_of_contDiffAt (H : ℝ × Point n → ℝ) {s : Set (ℝ × Point n)}
    (hH : ∀ p ∈ s, ContDiffAt ℝ 2 H p) :
    ContinuousOn (fun p => fderiv ℝ H p) s := fun p hp =>
  (((hH p hp).fderiv_right (m := 1) (by norm_num)).continuousAt).continuousWithinAt

/-- **★ `pd_snd_jointContinuousOn` — the FIRST spatial jet, jointly continuous.**  For `H`
    `ContDiffAt ℝ 2` on `s`, the spatial first jet `(τ,z) ↦ ∂_k [H(τ,·)] z` is `ContinuousOn s`. -/
theorem pd_snd_jointContinuousOn (H : ℝ × Point n → ℝ) {s : Set (ℝ × Point n)}
    (hH : ∀ p ∈ s, ContDiffAt ℝ 2 H p) (k : Fin n) :
    ContinuousOn (fun p : ℝ × Point n => pd (fun y => H (p.1, y)) k p.2) s := by
  have hfd : ContinuousOn (fun p => fderiv ℝ H p) s := fderiv_continuousOn_of_contDiffAt H hH
  have hknown : ContinuousOn
      (fun p : ℝ × Point n => fderiv ℝ H p ((0 : ℝ), (Pi.single k (1 : ℝ) : Point n))) s :=
    hfd.clm_apply continuousOn_const
  refine hknown.congr (fun p hp => ?_)
  exact pd_snd_eq_fderiv H p.1 p.2 k ((hH p hp).differentiableAt (by norm_num))

/-- **★★ `pd_pd_snd_jointContinuousOn` — the SECOND spatial jet, jointly continuous.**  For `H`
    `ContDiffAt ℝ 2` on `s`, the mixed spatial second jet `(τ,z) ↦ ∂_i∂_j [H(τ,·)] z` is
    `ContinuousOn s`.  The inner jet-field `G(τ,z) = DH(τ,z)[(0,e_j)]` is again `ContDiffAt ℝ 1`, so
    its own `fderiv` is continuous; `ContDiffAt.eventually` supplies the local slice-differentiability
    that transports the outer `pd` (`pd_congr_nhds`). -/
theorem pd_pd_snd_jointContinuousOn (H : ℝ × Point n → ℝ) {s : Set (ℝ × Point n)}
    (hH : ∀ p ∈ s, ContDiffAt ℝ 2 H p) (i j : Fin n) :
    ContinuousOn (fun p : ℝ × Point n =>
      pd (fun y => pd (fun w => H (p.1, w)) j y) i p.2) s := by
  -- the once-differentiated jet field `G q = DH(q)[(0,e_j)]`.
  set G : ℝ × Point n → ℝ :=
    fun q => fderiv ℝ H q ((0 : ℝ), (Pi.single j (1 : ℝ) : Point n)) with hGdef
  -- `G` is `ContDiffAt ℝ 1` on `s` (apply-CLM ∘ `fderiv H`).
  have hG1 : ∀ p ∈ s, ContDiffAt ℝ 1 G p := by
    intro p hp
    have h := (hH p hp).fderiv_right (m := 1) (by norm_num)
    exact (((ContinuousLinearMap.apply ℝ ℝ
      ((0 : ℝ), (Pi.single j (1 : ℝ) : Point n))).contDiff).contDiffAt).comp p h
  -- hence `fderiv G` is continuous on `s`.
  have hfdG : ContinuousOn (fun p => fderiv ℝ G p) s := fun p hp =>
    (((hG1 p hp).fderiv_right (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  have hknown : ContinuousOn
      (fun p : ℝ × Point n => fderiv ℝ G p ((0 : ℝ), (Pi.single i (1 : ℝ) : Point n))) s :=
    hfdG.clm_apply continuousOn_const
  refine hknown.congr (fun p hp => ?_)
  -- local slice differentiability near `p.2`.
  have hCDev : ∀ᶠ q in nhds p, ContDiffAt ℝ 2 H q := (hH p hp).eventually (by norm_num)
  have htend : Filter.Tendsto (fun y : Point n => (p.1, y)) (nhds p.2) (nhds p) := by
    have hc : Continuous (fun y : Point n => (p.1, y)) := by fun_prop
    simpa using hc.tendsto p.2
  have hslicedev : ∀ᶠ y in nhds p.2, DifferentiableAt ℝ H (p.1, y) := by
    filter_upwards [htend.eventually hCDev] with y hy
    exact hy.differentiableAt (by norm_num)
  -- the inner `pd` equals the `G`-slice near `p.2`.
  have hinner : (fun y => pd (fun w => H (p.1, w)) j y) =ᶠ[nhds p.2] (fun y => G (p.1, y)) := by
    filter_upwards [hslicedev] with y hy
    exact pd_snd_eq_fderiv H p.1 y j hy
  rw [QIQTH.PullbackMetric.pd_congr_nhds i p.2 hinner,
    pd_snd_eq_fderiv G p.1 p.2 i ((hG1 p hp).differentiableAt (by norm_num))]

/-! ###############################################################################
    ### §B — THE FLAT GAUSSIAN, JOINTLY SMOOTH FOR `τ > 0`.
    ############################################################################### -/

/-- **`heatKernel1D_contDiffAt_pos`.**  The 1-D heat kernel `(τ,x) ↦ (√(4πτ))⁻¹·exp(−x²/4τ)` is
    `ContDiffAt ℝ ⊤` jointly at every `(τ,x)` with `τ > 0`. -/
theorem heatKernel1D_contDiffAt_pos (τ x : ℝ) (hτ : 0 < τ) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun p : ℝ × ℝ => heatKernel1D p.1 p.2) (τ, x) := by
  have h4 : (0 : ℝ) < 4 * Real.pi * τ := by positivity
  have hsqrt : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.sqrt (4 * Real.pi * p.1)) (τ, x) := by
    have hb : ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun p : ℝ × ℝ => 4 * Real.pi * p.1) (τ, x) := by
      fun_prop
    exact hb.sqrt (by simpa using h4.ne')
  have hinv : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (Real.sqrt (4 * Real.pi * p.1))⁻¹) (τ, x) :=
    hsqrt.inv (by simpa using (Real.sqrt_pos.mpr h4).ne')
  have hexparg : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => -p.2 ^ 2 / (4 * p.1)) (τ, x) := by
    refine ContDiffAt.div (by fun_prop) (by fun_prop) ?_
    have : (0 : ℝ) < 4 * τ := by positivity
    simpa using this.ne'
  have hexp : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Real.exp (-p.2 ^ 2 / (4 * p.1))) (τ, x) :=
    (Real.contDiff_exp.contDiffAt).comp (τ, x) hexparg
  have hrw : (fun p : ℝ × ℝ => heatKernel1D p.1 p.2)
      = fun p : ℝ × ℝ => (Real.sqrt (4 * Real.pi * p.1))⁻¹ * Real.exp (-p.2 ^ 2 / (4 * p.1)) := by
    funext p; rw [heatKernel1D]
  rw [hrw]
  exact hinv.mul hexp

/-- **★ `gaussDdim_contDiffAt_pos`.**  The `d`-dimensional flat Gaussian `(τ,x) ↦ gaussDdim τ x` is
    `ContDiffAt ℝ ⊤` jointly at every `(τ,x)` with `τ > 0` — the `d`-fold product of jointly-smooth
    1-D factors. -/
theorem gaussDdim_contDiffAt_pos (τ : ℝ) (x : Point n) (hτ : 0 < τ) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (fun p : ℝ × Point n => gaussDdim p.1 p.2) (τ, x) := by
  have hfac : ∀ k : Fin n, ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun p : ℝ × Point n => heatKernel1D p.1 (p.2 k)) (τ, x) := by
    intro k
    have hpair : ContDiffAt ℝ (⊤ : WithTop ℕ∞)
        (fun p : ℝ × Point n => (p.1, p.2 k)) (τ, x) := by
      refine contDiffAt_fst.prodMk ?_
      exact ((contDiff_apply ℝ ℝ k).contDiffAt).comp (τ, x) contDiffAt_snd
    exact (heatKernel1D_contDiffAt_pos τ (x k) hτ).comp (τ, x) hpair
  have hrw : (fun p : ℝ × Point n => gaussDdim p.1 p.2)
      = fun p : ℝ × Point n => ∏ k : Fin n, heatKernel1D p.1 (p.2 k) := by
    funext p; rw [gaussDdim]
  rw [hrw]
  exact contDiffAt_prod (fun k _ => hfac k)

/-! ###############################################################################
    ### §C — THE WHITENED CUT KERNEL, JOINTLY `C²` FOR `τ > 0`.
    ############################################################################### -/

/-- **★ `whiteCutKernel_contDiffAt_joint`.**  The whitened cutoff kernel base-`0` field slice
    `(τ,z) ↦ whiteCutKernel κ … τ z 0 = χ(V₀ z)·(√det g^κ(0)·G_τ(V₀ z))` is jointly `ContDiffAt ℝ 2`
    at `(τ,z)` whenever `τ > 0` and the raw chart `uniformInverseChart … 0` is `ContDiffAt ℝ 2` at
    `z`.  Joint analogue of `whiteCut_contDiffAt_of_chartC2`: the cutoff is `C^∞`, the flat Gaussian
    is jointly smooth off `τ = 0` (§B), the whitening is a CLM, the amplitude is a constant. -/
theorem whiteCutKernel_contDiffAt_joint (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (a b : ℝ) (τ : ℝ) (z : Point n) (hτ : 0 < τ)
    (hC2 : ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0) z) :
    ContDiffAt ℝ 2 (fun p : ℝ × Point n => whiteCutKernel κ hκ hKc a b p.1 p.2 0) (τ, z) := by
  have hV0z : ContDiffAt ℝ 2 (fun x : Point n => whiteInvChart κ hκ hKc 0 x) z := by
    have hcd : ContDiff ℝ (2 : WithTop ℕ∞) (fun v : Point n => whiteUnvel κ (0 : Point n) v) :=
      (whiteUnvel κ (0 : Point n)).contDiff
    have hlin : ContDiffAt ℝ 2 (fun v : Point n => whiteUnvel κ (0 : Point n) v)
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0 z) := hcd.contDiffAt
    have h := hlin.comp z hC2
    simpa [whiteInvChart, Function.comp] using h
  have hsnd : ContDiffAt ℝ 2 (fun p : ℝ × Point n => p.2) (τ, z) := contDiffAt_snd
  have hV : ContDiffAt ℝ 2 (fun p : ℝ × Point n => whiteInvChart κ hκ hKc 0 p.2) (τ, z) := by
    have he : (fun p : ℝ × Point n => whiteInvChart κ hκ hKc 0 p.2)
        = (fun x : Point n => whiteInvChart κ hκ hKc 0 x) ∘ (fun p : ℝ × Point n => p.2) := rfl
    rw [he]; exact hV0z.comp (τ, z) hsnd
  have hpair : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => (p.1, whiteInvChart κ hκ hKc 0 p.2)) (τ, z) :=
    contDiffAt_fst.prodMk hV
  have hgauss : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc 0 p.2)) (τ, z) := by
    have he : (fun p : ℝ × Point n => gaussDdim p.1 (whiteInvChart κ hκ hKc 0 p.2))
        = (fun q : ℝ × Point n => gaussDdim q.1 q.2)
          ∘ (fun p : ℝ × Point n => (p.1, whiteInvChart κ hκ hKc 0 p.2)) := rfl
    rw [he]
    exact ((gaussDdim_contDiffAt_pos τ (whiteInvChart κ hκ hKc 0 z) hτ).of_le le_top).comp (τ, z) hpair
  have hχ : ContDiffAt ℝ 2
      (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc 0 p.2)) (τ, z) := by
    have hcut : ContDiffAt ℝ 2 (radialCutoff a b : Point n → ℝ) (whiteInvChart κ hκ hKc 0 z) :=
      (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have he : (fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc 0 p.2))
        = (fun v : Point n => radialCutoff a b v)
          ∘ (fun p : ℝ × Point n => whiteInvChart κ hκ hKc 0 p.2) := rfl
    rw [he]; exact hcut.comp (τ, z) hV
  have hrw : (fun p : ℝ × Point n => whiteCutKernel κ hκ hKc a b p.1 p.2 0)
      = fun p : ℝ × Point n => radialCutoff a b (whiteInvChart κ hκ hKc 0 p.2)
          * (Real.sqrt (Matrix.det (curvedRNCMetric κ (0 : Point n)))
              * gaussDdim p.1 (whiteInvChart κ hκ hKc 0 p.2)) := by
    funext p; simp only [whiteCutKernel, whiteAmbientKernel]
  rw [hrw]
  exact hχ.mul (contDiffAt_const.mul hgauss)

/-! ###############################################################################
    ### §D — THE `hGradCont` / `hHessCont` SUPPLIERS AND THE CAPSTONE.
    ############################################################################### -/

/-- **★★ `white_hGradCont` — THE FIRST-JET CONTINUITY.**  On the in-window in-gate positive-time box
    the gated witness equals the cut kernel on a `z`-neighbourhood (`whiteFieldDeriv_gate_congr`,
    `S 0` open), so its spatial first jet equals the cut kernel's, which is jointly continuous by the
    §A engine at the §C joint `C²`.  Exactly the `hGradCont` slot of
    `whiteDefectKernel_jointContinuousOn_modulo_jets`.  NOT `a₁ = R/6`. -/
theorem white_hGradCont (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0) z)
    (k : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) k p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 0) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint κ hκ hKc a b p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 0) hHbox k
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S 0 := hballS hp.2
  simpa [whiteFieldDeriv] using
    whiteFieldDeriv_gate_congr κ hκ hKc S a b k p.1 0 p.2 h0K hSopen hpS

/-- **★★ `white_hHessCont` — THE SECOND-JET CONTINUITY.**  The order-2 analogue of `white_hGradCont`
    via `whiteFieldDeriv2_gate_congr` and the §A second-jet engine.  Exactly the `hHessCont` slot of
    `whiteDefectKernel_jointContinuousOn_modulo_jets`.  NOT `a₁ = R/6`. -/
theorem white_hHessCont (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0) z)
    (i j : Fin n) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun z => whiteGatedWitness κ hκ hKc S a b p.1 z 0) j y) i p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hHbox : ∀ p ∈ (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R),
      ContDiffAt ℝ 2 (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 0) p := by
    intro p hp
    have hτ : 0 < p.1 := lt_of_lt_of_le ht₁ hp.1.1
    exact whiteCutKernel_contDiffAt_joint κ hκ hKc a b p.1 p.2 hτ (hchart p.2 hp.2)
  have heng := pd_pd_snd_jointContinuousOn
    (fun p' : ℝ × Point n => whiteCutKernel κ hκ hKc a b p'.1 p'.2 0) hHbox i j
  refine heng.congr (fun p hp => ?_)
  have hpS : p.2 ∈ S 0 := hballS hp.2
  simpa [whiteFieldDeriv2] using
    whiteFieldDeriv2_gate_congr κ hκ hKc S a b i j p.1 0 p.2 h0K hSopen hpS

/-- **★★★ `whiteDefectKernel_jointContinuousOn_of_flowBall` — THE `Δ_z` SIDE FULLY DISCHARGED.**  Joint
    `ContinuousOn` of the whitened one-step Levi residual on the in-window positive-time box, with BOTH
    the `∂_τ` side (`hVcont` via the flow-ball germ) AND the `Δ_z` side (the two chart-jet continuities
    `hGradCont`/`hHessCont`, here DISCHARGED from the same flow-ball chart germ) resolved.  The chart
    `C²` at each ball point comes from the flow-ball reachability `{closedBall 0 R ⊆ flowExp 0 '' ball c,
    c < δ₀}` + the germ `hspec`; the gate openness `hSopen` closes the gated↔cut congruence.  The SOLE
    surviving residues of the whitened `hbase` are therefore `{hEmeas, hstep}` on the other side of
    `whiteDefectKernel_jointContinuousOn_modulo_rep_and_L`.  NOT `a₁ = R/6`. -/
theorem whiteDefectKernel_jointContinuousOn_of_flowBall (hn : 0 < n) (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (Wg : Point n × Point n → Point n)
    (hagree : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ Kset → w.2.1 ∈ S w.2.2 →
        whiteInvChart κ hκ hKc w.2.2 w.2.1 = Wg (w.2.2, w.2.1))
    (t₁ t₂ R c δ₀ : ℝ) (ht₁ : 0 < t₁) (ht₂ : t₂ ≤ 1)
    (h0K : (0 : Point n) ∈ Kset) (hSopen : IsOpen (S 0))
    (hballS : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcδ : c < δ₀)
    (hspec : (∀ v : Point n, ‖v‖ < δ₀ →
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc 0 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc 0 z)) =ᶠ[nhds v] (fun z => z) ∧
        ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc 0)
          (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 v)))
    (hballC : Metric.closedBall (0 : Point n) R ⊆
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc 0 ''
          Metric.ball (0 : Point n) c) :
    ContinuousOn (fun p : ℝ × Point n => whiteDefectKernel κ hκ hKc S a b p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  -- the chart `C²` at every ball point, from the flow-ball reachability + germ.
  have hchart : ∀ z ∈ Metric.closedBall (0 : Point n) R,
      ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc 0) z := by
    intro z hz
    obtain ⟨v, hv, hvz⟩ := hballC hz
    have hvδ : ‖v‖ < δ₀ := lt_trans (mem_ball_zero_iff.mp hv) hcδ
    have := (hspec v hvδ).2
    rwa [hvz] at this
  exact whiteDefectKernel_jointContinuousOn_modulo_jets hn κ hκ hKc S a b Wg hagree
    t₁ t₂ R c δ₀ ht₁ ht₂ h0K hballS hcδ hspec hballC
    (white_hGradCont κ hκ hKc S a b t₁ t₂ R ht₁ h0K hSopen hballS hchart)
    (white_hHessCont κ hκ hKc S a b t₁ t₂ R ht₁ h0K hSopen hballS hchart)

#check @pd_snd_jointContinuousOn
#check @pd_pd_snd_jointContinuousOn
#check @gaussDdim_contDiffAt_pos
#check @white_hGradCont
#check @white_hHessCont
#check @whiteDefectKernel_jointContinuousOn_of_flowBall

end QIQTH.WhiteHJetCont

section AxiomChecks
open QIQTH.WhiteHJetCont
#print axioms pd_snd_jointContinuousOn
#print axioms pd_pd_snd_jointContinuousOn
#print axioms gaussDdim_contDiffAt_pos
#print axioms white_hGradCont
#print axioms white_hHessCont
#print axioms whiteDefectKernel_jointContinuousOn_of_flowBall
end AxiomChecks
