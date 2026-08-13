/-
  CurvedA1ReBaseHBdomW2 — J4-685: LAYER 5, first sub-brick — the width-2 producer-re-assembly
  VERDICT for route (c).  The just-landed width-2 center residual (`CurvedA1CenterResidW2`,
  J4-684) is confronted against the EXACT `hbound`-antecedent envelope of the fat-`K` dom-pkg
  consumer `CurvedA1ReBaseHBdom.gated_hBdom_of_defect_bound` — `(C·(1+t'))·baseKernelW 2 0 τ p q`
  — and the `ε₀/τ` term is consumed HONESTLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient.  `a₁ = R/6` remains
  CONDITIONAL — this brick is a SHAPE-DECISION verdict at the consumer interface.

  ── THE `ε₀/τ` RESOLUTION (the finding — no unsound absorption).  The width-2 center residual
  (`CurvedA1CenterResidW2.curvedRNC_resid_width2_bound_center`) has the honest form
      `|R₀(τ,v)| ≤ (C₀ + Cεu·ε₀·(1/τ)) · gaussDdim (2·τ) v` ,   ∀ τ > 0 ,   ε₀ = (|κ|/3)·n·r² ,
  while the fat-`K` dom-pkg consumer `gated_hBdom_of_defect_bound` (J4-603) demands its `hbound`
  antecedent in the τ-independent-coefficient envelope
      `|E(τ,p,q)| ≤ (C·(1 + t')) · baseKernelW 2 0 τ p q` ,   ∀ 0 < τ ≤ t' ,
  where `baseKernelW 2 0 τ p q = gaussDdim (2·τ) (p − q)`.  For FIXED outer time `t'` the RHS
  coefficient `C·(1+t')` is τ-INDEPENDENT, but the residual's `Cεu·ε₀·(1/τ)` term has NO uniform
  majorant on `(0,t']` for `ε₀ > 0` — it diverges as `τ → 0`.  This is EXACTLY the J4-608 route
  verdict (`CurvedA1CenterN1.centerShape_no_uniform_majorant`) re-pinned at the width-2 consumer
  envelope: routes (a) [τ₀-threshold] and (b) [ε₀→0-first] cannot feed this consumer, because the
  D2 Volterra engine requires the bound on ALL of `(0,T]`.  The ACTUAL all-`τ`, `ε₀`-free
  resolution is route (c) — per-`q` frozen-Gaussian / WHITENING re-basing (the `WhiteWitness` →
  `WhiteAnnulus.white_hpkgBound_discharged` thread, J4-620..626): whitening removes the trace
  floor `(tr g⁻¹(q) − n)/(2τ)` STRUCTURALLY (the `ε₀/τ` floor is gone in the whitened chart
  velocity), landing the UNCONDITIONAL all-`τ` fat-`K` `hpkgBound` — but at the *whitened* gated
  witness and a *widened* width `whiteLam = 2(nC₀²+1)`, so it feeds the width-`w` BridgeWidth
  engine, NOT this literal width-2 vanVleck consumer.  Hence for THE VANVLECK CONSUMER the
  `ε₀/τ` term genuinely OBSTRUCTS the all-`τ` width-2 bound at fat `K`; the honest partials are the
  τ-windowed producer and the ε₀ = 0 envelope-embedding, both landed below.

  ── WHAT LANDS HERE (all proved, std-3; NO sorry, NO `:= True`, NO new axioms).
    • `width2CenterEnvelope_no_uniform_majorant` — ★ THE SCALAR VERDICT at the consumer envelope:
      for `Cεu·ε₀ > 0` and fixed `T = t'`, the `Cεu·ε₀·(1/τ)` term admits NO `C·(1+T)` majorant on
      `(0,T]`.  Reduces to J4-608's `centerShape_no_uniform_majorant`.
    • `width2CenterEnvelope_no_kernel_majorant` — ★ THE KERNEL VERDICT at the actual `baseKernelW 2`
      diagonal: the `Cεu·ε₀·(1/τ)`-weighted width-2 Gaussian is not majorized by `C·(1+T)`-times
      the SAME width-2 Gaussian on `(0,T]` (cancel the strictly-positive diagonal Gaussian).
    • `curvedRNC_resid_width2_bound_center_windowed` — ★ THE ROUTE-(a) τ-WINDOWED PARTIAL: on
      `τ₀ ≤ τ` the fat-`K` width-2 center bound becomes the CLEAN τ-independent-coefficient shape
      `|R₀| ≤ (C₀ + Cεu·ε₀·(1/τ₀))·gaussDdim(2τ) v`.  ⚠ HONESTY: non-consumable by the D2 engine
      (bound needed on ALL of `(0,T]`), constant blows up as `τ₀ → 0`; the honest content of what a
      threshold buys.  Mirrors `CurvedA1CenterN1.curvedRNC_residN1_bound_center_thresholded`.
    • `width2Center_epsZero_envelope_embed` — ★ THE ε₀ = 0 SHAPE-COMPATIBILITY certificate: the
      `ε₀ = 0` residual coefficient `C₀·gaussDdim(2τ)v` DOES embed into the consumer envelope
      `(C₀·(1+t'))·baseKernelW 2 0 τ v 0` (∀ 0 < τ ≤ t').  So the consumer interface is REAL and
      `ε₀` is the SOLE obstruction.
    • `width2Center_epsZero_feeds_envelope` — ★ the abstract consumption: ANY residual satisfying
      the `ε₀ = 0` width-2 bound feeds the `(C·(1+t'))·baseKernelW 2` slot.
    • `width2CenterEnvelope_obstruction_genuine` — ★ non-vacuity of the verdict at the FAT curved
      base: at `κ < 0`, `r > 0`, `n ≥ 1` the explicit `ε₀ = (|κ|/3)·n·r² > 0`, so the no-majorant
      obstruction genuinely FIRES (not vacuous).

  ── HONEST RESIDUAL (unchanged from J4-603/684, refined).  OPEN for THIS consumer: the all-`τ`
  width-2 vanVleck `hbound`-fat producer is OBSTRUCTED by `ε₀/τ` (verdict above); the route-(c)
  resolution routes through the *whitened* witness / widened width (`white_hpkgBound_discharged`),
  a DIFFERENT consumer.  Reconciling the whitened all-`τ` bound with the literal width-2 vanVleck
  dom-pkg (or re-basing the dom-pkg onto the whitened witness) is the downstream work; then fat-`K`
  `hEmeas`/`hAdom`/`hcont`/`hContDom`, mass pre-ρ discharge, the joint cp466 audit, and the
  capstone co-instantiation.  `a₁ = R/6` established non-vacuously ONLY for the FLAT tower.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as discharge,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1CenterResidW2
import QIQTH.CurvedA1CenterN1
import QIQTH.ParametrixHEboundWiring

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.CurvedA1CenterResidW2 QIQTH.CurvedA1CenterN1 QIQTH.CConvV2GaussianPairing
open Set Filter
open scoped Topology BigOperators ContDiff

namespace QIQTH.CurvedA1ReBaseHBdomW2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### ★ The scalar and kernel route-decision verdicts at the consumer envelope `C·(1+t')`. -/

/-- **★ J4-685 (SCALAR VERDICT) — `width2CenterEnvelope_no_uniform_majorant`.**  For any
    `Cεu·ε₀ > 0` (i.e. any fixed fat radius `r > 0` at `κ ≠ 0`) and fixed outer time `T = t'`, the
    `Cεu·ε₀·(1/τ)` term of the width-2 center residual admits NO `C·(1+T)` majorant on `(0,T]`:
    the fat-`K` width-2 residual CANNOT be cast into the τ-independent-coefficient envelope
    `(C·(1+t'))·baseKernelW 2 0 τ p q` demanded by `gated_hBdom_of_defect_bound`.  Reduces to the
    J4-608 scalar route gate.  NOT `a₁ = R/6`. -/
theorem width2CenterEnvelope_no_uniform_majorant (Cεu ε₀ T : ℝ)
    (hCεu : 0 < Cεu) (hε₀ : 0 < ε₀) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T → Cεu * ε₀ * (1 / τ) ≤ C * (1 + T) := by
  rintro ⟨C, hC⟩
  exact QIQTH.CurvedA1CenterN1.centerShape_no_uniform_majorant Cεu ε₀ T hCεu hε₀ hT
    ⟨C * (1 + T), hC⟩

/-- **★ J4-685 (KERNEL VERDICT) — `width2CenterEnvelope_no_kernel_majorant`.**  The same
    obstruction against the ACTUAL consumer target: the `Cεu·ε₀·(1/τ)`-weighted width-2 Gaussian
    `baseKernelW 2 0 τ 0 0` is not majorized by `C·(1+T)` times the SAME width-2 Gaussian uniformly
    on `(0,T]` — cancel the strictly-positive diagonal Gaussian `gaussDdim (2τ) 0 > 0` and reduce
    to the scalar verdict.  (Here — unlike J4-608's width-3/2-vs-2 kernel gate — both sides share
    width 2, so the diagonal Gaussian cancels directly.)  NOT `a₁ = R/6`. -/
theorem width2CenterEnvelope_no_kernel_majorant (Cεu ε₀ T : ℝ)
    (hCεu : 0 < Cεu) (hε₀ : 0 < ε₀) (hT : 0 < T) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T →
        Cεu * ε₀ * (1 / τ) * baseKernelW (2 : ℝ) (0 : ℝ) τ (0 : Point n) (0 : Point n)
          ≤ C * (1 + T) * baseKernelW (2 : ℝ) (0 : ℝ) τ (0 : Point n) (0 : Point n) := by
  rintro ⟨C, hC⟩
  refine width2CenterEnvelope_no_uniform_majorant Cεu ε₀ T hCεu hε₀ hT ⟨C, fun τ hτ hτT => ?_⟩
  have hbk : baseKernelW (2 : ℝ) (0 : ℝ) τ (0 : Point n) (0 : Point n)
      = gaussDdim (2 * τ) (0 : Point n) := by
    rw [baseKernelW_zero_apply, sub_zero]
  have hpos : 0 < gaussDdim (2 * τ) (0 : Point n) := by
    rw [gaussDdim_zero]
    have hs : (0 : ℝ) < Real.sqrt (4 * Real.pi * (2 * τ)) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  have h := hC τ hτ hτT
  rw [hbk] at h
  exact le_of_mul_le_mul_right h hpos

/-! ### ★ The route-(a) τ-windowed positive partial (honest, non-consumable). -/

/-- **★ J4-685 — `curvedRNC_resid_width2_bound_center_windowed`: THE ROUTE-(a) τ-WINDOWED PARTIAL.**
    On the restricted range `τ₀ ≤ τ` the fat-`K` width-2 center residual bound becomes the CLEAN
    τ-independent-coefficient shape
        `|R₀(τ,v)| ≤ (C₀ + Cεu·ε₀·(1/τ₀)) · gaussDdim (2·τ) v` ,
    with the full threshold constant `C₀ + Cεu·ε₀·(1/τ₀)` exposed.  ⚠ HONESTY (the route decision):
    this does NOT feed the D2 Volterra engine (`gated_hBdom_of_defect_bound` needs the bound on ALL
    of `(0,T]`; the `iterE` time-convolutions integrate down to `0` even at interior evaluation
    times), and its constant blows up as `τ₀ → 0`.  It is the honest content of route (a), recorded
    so downstream can see exactly what a threshold buys.  Width-2 mirror of
    `CurvedA1CenterN1.curvedRNC_residN1_bound_center_thresholded`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_resid_width2_bound_center_windowed (κ r : ℝ) (hκ : κ ≤ 0)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C₀ Cεu : ℝ, 0 ≤ C₀ ∧ 0 ≤ Cεu ∧
      ∀ (τ₀ : ℝ), 0 < τ₀ → ∀ (τ : ℝ), τ₀ ≤ τ →
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 0
            (uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q)
            (uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q) Θ u τ v|
          ≤ (C₀ + Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ₀)) * gaussDdim (2 * τ) v := by
  obtain ⟨ρ_u, hρ_u0, C₀, Cεu, hC₀0, hCεu0, hmain⟩ :=
    curvedRNC_resid_width2_bound_center κ r hκ Θ u hw0smooth hw0flat
  refine ⟨ρ_u, hρ_u0, C₀, Cεu, hC₀0, hCεu0, ?_⟩
  intro τ₀ hτ₀ τ hττ₀ q hq v hv
  have hτ : 0 < τ := lt_of_lt_of_le hτ₀ hττ₀
  refine (hmain τ hτ q hq v hv).trans
    (mul_le_mul_of_nonneg_right ?_ (gaussDdim_nonneg _ v))
  have hinv : 1 / τ ≤ 1 / τ₀ := one_div_le_one_div_of_le hτ₀ hττ₀
  have hε : (0 : ℝ) ≤ |κ| / 3 * ((n : ℝ) * r ^ 2) := by positivity
  have hstep : Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ)
      ≤ Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ₀) :=
    mul_le_mul_of_nonneg_left hinv (mul_nonneg hCεu0 hε)
  linarith

/-! ### ★ The ε₀ = 0 envelope-embedding certificates (the consumer interface is real). -/

/-- **★ J4-685 — `width2Center_epsZero_envelope_embed`: THE ε₀ = 0 SHAPE-COMPATIBILITY.**  At
    `ε₀ = 0` the width-2 center residual coefficient `C₀·gaussDdim(2τ)v` embeds into the EXACT
    consumer envelope `(C₀·(1+t'))·baseKernelW 2 0 τ v 0` for every `0 < τ`, `0 ≤ t'`
    (`baseKernelW 2 0 τ v 0 = gaussDdim (2τ) v`, and `C₀ ≤ C₀·(1+t')`).  So the
    `gated_hBdom_of_defect_bound` interface is genuinely fillable once the `ε₀/τ` term is absent —
    `ε₀` is the SOLE obstruction.  NOT `a₁ = R/6`. -/
theorem width2Center_epsZero_envelope_embed (C₀ t' : ℝ) (hC₀ : 0 ≤ C₀) (ht' : 0 ≤ t')
    (τ : ℝ) (v : Point n) :
    C₀ * gaussDdim (2 * τ) v
      ≤ (C₀ * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ v (0 : Point n) := by
  rw [baseKernelW_zero_apply, sub_zero]
  have hG : 0 ≤ gaussDdim (2 * τ) v := gaussDdim_nonneg _ v
  have hcoef : C₀ ≤ C₀ * (1 + t') := by nlinarith
  exact mul_le_mul_of_nonneg_right hcoef hG

/-- **★ J4-685 — `width2Center_epsZero_feeds_envelope`: the abstract consumption.**  ANY residual
    `R` obeying the `ε₀ = 0` width-2 center bound `|R τ v| ≤ (C₀ + Cεu·0·(1/τ))·gaussDdim(2τ)v`
    (the `ε₀ → 0` specialization of the J4-684 shape) fills the `gated_hBdom_of_defect_bound`
    `hbound` envelope `(C₀·(1+t'))·baseKernelW 2 0 τ v 0` on `0 < τ ≤ t'`.  Certifies the interface
    end-to-end at `ε₀ = 0`.  NOT `a₁ = R/6`. -/
theorem width2Center_epsZero_feeds_envelope (C₀ Cεu : ℝ) (hC₀ : 0 ≤ C₀)
    (R : ℝ → Point n → ℝ)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ v : Point n,
      |R τ v| ≤ (C₀ + Cεu * 0 * (1 / τ)) * gaussDdim (2 * τ) v)
    (t' τ : ℝ) (hτ : 0 < τ) (hτt' : τ ≤ t') (v : Point n) :
    |R τ v| ≤ (C₀ * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ v (0 : Point n) := by
  have ht' : (0 : ℝ) ≤ t' := le_trans hτ.le hτt'
  have h1 : |R τ v| ≤ C₀ * gaussDdim (2 * τ) v := by
    have := hbd τ hτ v
    simpa [mul_zero, zero_mul, add_zero] using this
  exact h1.trans (width2Center_epsZero_envelope_embed C₀ t' hC₀ ht' τ v)

/-! ### Non-vacuity of the verdict at the fat curved base (cp466). -/

/-- **★ J4-685 — `width2CenterEnvelope_obstruction_genuine`: the verdict FIRES at fat curved `K`.**
    At `κ < 0`, `r > 0`, `n ≥ 1` the explicit deviation `ε₀ = (|κ|/3)·n·r²` is strictly POSITIVE,
    so for any `Cεu > 0` the no-uniform-majorant obstruction genuinely applies — the width-2 center
    residual's `ε₀/τ` term is a real, non-vacuous obstruction to the fat-`K` dom-pkg consumer
    envelope (not a shape artifact of a vacuous `ε₀ = 0`).  NOT `a₁ = R/6`. -/
theorem width2CenterEnvelope_obstruction_genuine (κ r T Cεu : ℝ)
    (hκ : κ < 0) (hr : 0 < r) (hn : 1 ≤ n) (hT : 0 < T) (hCεu : 0 < Cεu) :
    0 < |κ| / 3 * ((n : ℝ) * r ^ 2) ∧
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T →
        Cεu * (|κ| / 3 * ((n : ℝ) * r ^ 2)) * (1 / τ) ≤ C * (1 + T) := by
  have hκabs : (0 : ℝ) < |κ| := abs_pos.mpr hκ.ne
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hε : 0 < |κ| / 3 * ((n : ℝ) * r ^ 2) := by positivity
  exact ⟨hε, width2CenterEnvelope_no_uniform_majorant Cεu (|κ| / 3 * ((n : ℝ) * r ^ 2)) T
    hCεu hε hT⟩

end QIQTH.CurvedA1ReBaseHBdomW2

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1ReBaseHBdomW2

#print axioms width2CenterEnvelope_no_uniform_majorant
#print axioms width2CenterEnvelope_no_kernel_majorant
#print axioms curvedRNC_resid_width2_bound_center_windowed
#print axioms width2Center_epsZero_envelope_embed
#print axioms width2Center_epsZero_feeds_envelope
#print axioms width2CenterEnvelope_obstruction_genuine

end AxiomChecks
