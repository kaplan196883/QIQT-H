/-
  WhiteW1 — J4-641: the `w₁` leg — (L-a) the LOCAL ray-integral interchange CLOSED at C²
  (finite-order tower + bump-cutoff extension, NO C^∞ extension hypothesis), (L-b) gate-local C²
  of the transport source `T̂û₀ = Θ̂^{−1/2}·Δ_ĝ(Θ̂^{1/2})` CONDITIONAL on the chart-C⁵ residue,
  the assembled gate-local `hw1C2`, and the whiteDelta binder LOCALIZATION.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE ORDER LEDGER (the binding count of this brick — checked against the bank).
    The banked chart regularity is `uniformFlowExp_contDiffAt_four` (ChartThirdJet, C⁴ per reachable
    point), derived from `expMap_contDiffOn_four` — the bespoke Jet-4 tower (ExpMapFDeriv3 +
    ExpJet4* fundamental-solution/Grönwall machinery).  There is NO banked C⁵/C^k/C^∞ chart fact,
    and Mathlib has no smooth-dependence-of-ODE-flows shortcut; each order is its own tower rung.
      chart C^{k+1} ⟹ Jacobian columns C^k ⟹ ĝ entries C^k ⟹ det ĝ, Θ̂ C^k.
    The transport source `T̂û₀ = Θ̂^{−1/2}·Δ_ĝ(Θ̂^{1/2})` spends TWO derivatives of `Θ̂^{1/2}`
    (and one of the ĝ entries, through the Christoffels), so
      `T̂û₀ ∈ C²` ⟸ `Θ̂ ∈ C⁴` ⟸ `ĝ entries ∈ C⁴` ⟸ chart `∈ C⁵`.
    ⚠ THE BANKED C⁴ CHART DOES **NOT** CLOSE THE LEDGER: it yields `T̂û₀ ∈ C¹` only.  The
    missing input is ONE chart order — the Jet-5 rung (`expMap_contDiffOn_five`), a genuine
    multi-brick campaign mirroring the Jet-4 tower (NOT an assembly gap).  It is carried here as
    the LABELLED antecedent `hch5` (the exact C⁵ analogue of the banked C⁴ conclusion; the
    monotonicity gate `chartC5_implies_banked_chartC4` certifies it strengthens the bank
    consistently).  Inhabitance of `hch5` is NOT claimed in-repo (cp466 discipline): it is the
    scoped residue of the `w₁` leg.

  ★ WHAT LANDS (all axiom-free).
    (L-a) — CLOSED UNCONDITIONALLY at C²:
      • `rayIntegral_hasFDerivAt_C1` + `rayIntegral_contDiff_nat_of_contDiff_nat` — the banked
        HuInftyRebase ray tower REBASED at finite order (`C^N` source ⟹ `C^N` solve; the banked
        tower consumed `C^∞` sources only, but its derivative-bumping induction never needed more
        than one order of headroom).
      • `contDiff_two_cutoff_extension_of_ball` — the Whitney/cutoff residue of J4-640 DISCHARGED
        at C²: a `ContDiffAt ℝ 2`-on-a-ball function extends to a GLOBAL C² function agreeing on
        any strictly smaller ball (Mathlib `ContDiffBump`; no Whitney machinery needed at fixed
        finite order).
      • ★ `radialTransportSolve_contDiffAt_two_of_ball` — THE LOCAL INTERCHANGE: a gate-local-C²
        source has a gate-local-C² ray solve (star-shaped locality `radialTransportSolve_congrOn_ball`
        + cutoff extension + finite tower).  The J4-640 `(L-a)` item, closed.
    (L-b) — CONDITIONAL on `hch5`:
      • `uniformFlowPullbackMetric_entry_contDiffAt4_of_chartC5` / `white_metric_entry_contDiffAt4_of_chartC5`
        — chart C⁵ ⟹ ĝ entries C⁴ on a per-`q` gate (the WhiteW0 §1 chain one order up).
      • `white_transport_source_contDiffAt2_of_chartC5` — ★ gate-local C² of `T̂û₀` (det/√det C⁴,
        Θ̂ C⁴ > 0, ĝ⁻¹ C² via `Ring.inverse` at the Neumann unit, Christoffels C², Δ_ĝ assembly).
      • `white_u1_contDiffAt2_of_chartC5` / ★★ `white_w1_contDiffAt2_of_chartC5` — the gate-local
        `hw1C2` leg, conditional on exactly `hch5`.
    BINDER LOCALIZATION (unconditional):
      • `jet_bounds_on_closedBall_of_ballC2` + ★ `whiteDelta_discharged_C2_local` — the J4-639/640
        `hΔ` discharge consuming only BALL-LOCAL C² of `w₁` (the jet bounds are compact-ball
        suprema; the global binder of `whiteDelta_discharged_C2` was never needed).
      • ★★ `white_K1BudgetW_C2_w0Free_localW1` — the K1 `t²` budget with the `hw1C2` binder
        weakened from GLOBAL `ContDiff ℝ 2` to gate-local `ContDiffAt ℝ 2` (the J4-640 scope
        note executed).
      • ★★★ `white_K1BudgetW_h0h1_of_chartC5` — THE HEADLINE: conditional on the labelled
        chart-C⁵ residue, THE K1 INPUT LIST IS `{h0, h1}` — BOTH regularity legs discharged.

  ⚠ HONEST SCOPE (binding).
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      owes the remaining K1 inputs — now `{h0, h1}` GIVEN the chart-C⁵ residue (`hch5`), or
      `{hw1C2-gate-local, h0, h1}` unconditionally — + the Duhamel-split integrability carry +
      the fat-`K` carrier piles + the capstone co-instantiation at the whitened witness + the
      prior analytic piles.
    • `hch5` inhabitance is NOT claimed (the Jet-5 rung is the precisely-scoped residue); the
      monotonicity gate certifies only that it is the faithful C⁵ analogue of the banked C⁴ fact.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteW0

open Finset Filter Topology Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag QIQTH.WhiteAmbient
open QIQTH.WhiteAnnulus QIQTH.WidthFree QIQTH.WhiteCapstoneWire
open QIQTH.WhiteOrder1 QIQTH.WhiteGauss QIQTH.WhiteDelta QIQTH.WhiteSmooth
open QIQTH.ExpMap QIQTH.PullbackMetric QIQTH.ChartThirdJet QIQTH.RNCExpansion
open QIQTH.EquivProbe QIQTH.CurvedA1CenterAmp QIQTH.HuInftyRebase QIQTH.RadialTransport
open QIQTH.CurvedRNCGaugeBundle QIQTH.WhiteW0
open MeasureTheory intervalIntegral
open scoped ContDiff Interval

namespace QIQTH.WhiteW1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. (L-a core) The finite-order ray tower: `C^N` source ⟹ `C^N` ray integral. -/

section RayFinite

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`rayIntegral_hasFDerivAt_C1` — the derivative-bumping rung at `C¹` sources.**  The banked
    `rayIntegral_hasFDerivAt` (HuInftyRebase) verbatim, with the `C^∞` hypothesis weakened to the
    `C¹` it actually uses (differentiability + continuity of `fderiv`).  NOT `a₁ = R/6`. -/
theorem rayIntegral_hasFDerivAt_C1 (m : ℕ) (g : Point n → F)
    (hg : ContDiff ℝ 1 g) (v₀ : Point n) :
    HasFDerivAt (rayIntegral m g)
      (rayIntegral (m + 1) (fun x => fderiv ℝ g x) v₀) v₀ := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ g x :=
    fun x => (hg.differentiable one_ne_zero).differentiableAt
  have hcfd : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv one_ne_zero
  -- uniform bound on `‖Dg‖` over the compact ray tube.
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall v₀ 1)).exists_bound_of_continuousOn
    (f := fun p : ℝ × Point n => fderiv ℝ g (p.1 • p.2))
    ((hcfd.comp (continuous_fst.smul continuous_snd)).continuousOn)
  -- continuity of the integrand and its parameter-derivative (for each base point).
  have hcF : ∀ v : Point n, Continuous (fun s : ℝ => s ^ m • g (s • v)) :=
    fun v => (continuous_pow m).smul (hg.continuous.comp (continuous_id.smul continuous_const))
  have hcF' : ∀ v : Point n,
      Continuous (fun s : ℝ => s ^ m • (s • fderiv ℝ g (s • v))) :=
    fun v => (continuous_pow m).smul
      (continuous_id.smul (hcfd.comp (continuous_id.smul continuous_const)))
  -- the dominating bound.
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
      ∀ x ∈ Metric.closedBall v₀ 1,
        ‖s ^ m • (s • fderiv ℝ g (s • x))‖ ≤ (fun _ => M) s := by
    refine Filter.Eventually.of_forall (fun s hs x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [norm_smul, norm_smul]
    have hb := hM (s, x) ⟨⟨le_of_lt hs0, hs1⟩, hx⟩
    have h1 : ‖s ^ m‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (le_of_lt hs0) hs1
    have h2 : ‖s‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs0)]; exact hs1
    calc ‖s ^ m‖ * (‖s‖ * ‖fderiv ℝ g (s • x)‖)
        ≤ 1 * (1 * M) :=
          mul_le_mul h1 (mul_le_mul h2 hb (norm_nonneg _) (by norm_num))
            (by positivity) (by norm_num)
      _ = M := by ring
  -- the pointwise `v`-derivative of the integrand (chain rule on the ray).
  have hderiv : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
      ∀ x ∈ Metric.closedBall v₀ 1,
        HasFDerivAt (fun x => s ^ m • g (s • x))
          (s ^ m • (s • fderiv ℝ g (s • x))) x := by
    refine Filter.Eventually.of_forall (fun s _ x _ => ?_)
    have hray : HasFDerivAt (fun x : Point n => s • x)
        (s • ContinuousLinearMap.id ℝ (Point n)) x := (hasFDerivAt_id x).const_smul s
    have hfd : HasFDerivAt g (fderiv ℝ g (s • x)) (s • x) := (hdiffbl (s • x)).hasFDerivAt
    have hcomp := hfd.comp x hray
    have hcomp_eq : (fderiv ℝ g (s • x)).comp (s • ContinuousLinearMap.id ℝ (Point n))
        = s • fderiv ℝ g (s • x) := by
      ext w
      simp [ContinuousLinearMap.smul_apply]
    rw [hcomp_eq] at hcomp
    exact hcomp.const_smul (s ^ m)
  -- assemble the dominated Leibniz rule.
  have main := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun v s => s ^ m • g (s • v))
    (F' := fun v s => s ^ m • (s • fderiv ℝ g (s • v)))
    (bound := fun _ => M) (a := 0) (b := 1) (μ := volume)
    (s := Metric.closedBall v₀ 1) (x₀ := v₀)
    (Metric.closedBall_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall (fun v => (hcF v).aestronglyMeasurable))
    ((hcF v₀).intervalIntegrable 0 1)
    ((hcF' v₀).aestronglyMeasurable)
    hbound _root_.intervalIntegrable_const hderiv
  -- rewrite the raw derivative `∫ sᵐ•(s•Dg)` into `rayIntegral (m+1) (fderiv g)`.
  have hcongr : (∫ s in (0:ℝ)..1, s ^ m • (s • fderiv ℝ g (s • v₀)))
      = rayIntegral (m + 1) (fun x => fderiv ℝ g x) v₀ := by
    rw [rayIntegral]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [smul_smul, pow_succ]
  rw [← hcongr]
  exact main

end RayFinite

/-- **★ `rayIntegral_contDiff_nat_of_contDiff_nat` — the finite-order tower with FINITE-order
    sources** (`C^N` source ⟹ `C^N` ray integral; the banked tower consumed `C^∞` sources only).
    Induction on `N` exactly as in the banked `rayIntegral_contDiff_nat`, with the derivative rung
    replaced by `rayIntegral_hasFDerivAt_C1`.  NOT `a₁ = R/6`. -/
theorem rayIntegral_contDiff_nat_of_contDiff_nat (N : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ) (g : Point n → F),
      ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) g →
      ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) (rayIntegral m g) := by
  induction N with
  | zero =>
      intro F _ _ m g hg
      rw [Nat.cast_zero] at hg ⊢
      exact contDiff_zero.mpr (rayIntegral_continuous m g (contDiff_zero.mp hg))
  | succ N ih =>
      intro F _ _ m g hg
      rw [Nat.cast_succ] at hg ⊢
      have hg1 : ContDiff ℝ 1 g := hg.of_le le_add_self
      refine contDiff_succ_iff_fderiv.mpr
        ⟨fun v₀ => (rayIntegral_hasFDerivAt_C1 m g hg1 v₀).differentiableAt, ?_, ?_⟩
      · exact fun hω => absurd hω (WithTop.natCast_ne_top N)
      · have hfe : fderiv ℝ (rayIntegral m g) = rayIntegral (m + 1) (fun x => fderiv ℝ g x) :=
          funext fun v => (rayIntegral_hasFDerivAt_C1 m g hg1 v).fderiv
        rw [hfe]
        exact ih (m + 1) (fun x => fderiv ℝ g x) (contDiff_succ_iff_fderiv.mp hg).2.2

/-- **`radialTransportSolve_contDiff_two` — the scalar `C²` corollary**: a globally-C² transport
    source has a globally-C² ray solve.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_contDiff_two (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (radialTransportSolve k f) := by
  have h2 : ((2 : ℕ) : WithTop ℕ∞) = (2 : WithTop ℕ∞) := by norm_cast
  rw [radialTransportSolve_eq_rayIntegral]
  have h := rayIntegral_contDiff_nat_of_contDiff_nat (n := n) 2 (k - 1) f (by rw [h2]; exact hf)
  rw [h2] at h
  exact h

/-! ### §2. (L-a) The bump-cutoff extension and ★ the LOCAL interchange. -/

/-- **`contDiff_two_cutoff_extension_of_ball` — the J4-640 Whitney/cutoff residue DISCHARGED at
    C²**: a function `ContDiffAt ℝ 2` at every point of `ball 0 r` agrees on `ball 0 r₁`
    (`r₁ < r`) with a GLOBAL C² function — multiply by a `ContDiffBump` with
    `rIn = r₁ < rOut = (r₁+r)/2 < r`.  No Whitney extension machinery is needed at a fixed
    finite order.  NOT `a₁ = R/6`. -/
theorem contDiff_two_cutoff_extension_of_ball (f : Point n → ℝ) (r r₁ : ℝ)
    (h0 : 0 < r₁) (h1 : r₁ < r)
    (hf : ∀ x : Point n, ‖x‖ < r → ContDiffAt ℝ 2 f x) :
    ∃ f' : Point n → ℝ, ContDiff ℝ 2 f'
      ∧ Set.EqOn f f' (Metric.ball (0 : Point n) r₁) := by
  have hmid : r₁ < (r₁ + r) / 2 := by linarith
  set b : ContDiffBump (0 : Point n) := ⟨r₁, (r₁ + r) / 2, h0, hmid⟩ with hbdef
  have hb2 : ContDiff ℝ 2 (fun y : Point n => b y) := by
    have h : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) (⇑b) := b.contDiff
    exact_mod_cast h
  refine ⟨fun x => b x * f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < r
    · exact (hb2.contDiffAt).mul (hf x hx)
    · rw [not_lt] at hx
      have hopen : IsOpen {y : Point n | (r₁ + r) / 2 < ‖y‖} :=
        isOpen_lt continuous_const continuous_norm
      have hmem : x ∈ {y : Point n | (r₁ + r) / 2 < ‖y‖} := by
        have hlt : (r₁ + r) / 2 < r := by linarith
        exact lt_of_lt_of_le hlt hx
      have hzero : Set.EqOn (fun y => b y * f y) (fun _ => (0 : ℝ))
          {y : Point n | (r₁ + r) / 2 < ‖y‖} := by
        intro y hy
        have hb0 : b y = 0 := b.zero_of_le_dist (by rw [dist_zero_right]; exact le_of_lt hy)
        show b y * f y = 0
        rw [hb0, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) hzero)
  · intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    have hb1 : b y = 1 :=
      b.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hy)
    show f y = b y * f y
    rw [hb1, one_mul]

/-- **★ `radialTransportSolve_contDiffAt_two_of_ball` — THE LOCAL INTERCHANGE (the J4-640 (L-a)
    item, CLOSED)**: a source that is `ContDiffAt ℝ 2` on `ball 0 r` has a ray solve
    `radialTransportSolve k f` that is `ContDiffAt ℝ 2` at every point of the SAME ball.
    Route: shrink to `r₁ = (‖x‖+r)/2`, cutoff-extend the source (§2), replace the solve by the
    solve of the extension on the star-shaped ball (`radialTransportSolve_congrOn_ball`, J4-640),
    and apply the finite-order tower (§1).  NO C^∞ hypothesis anywhere.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_contDiffAt_two_of_ball (k : ℕ) (f : Point n → ℝ) (r : ℝ)
    (hf : ∀ x : Point n, ‖x‖ < r → ContDiffAt ℝ 2 f x)
    (x : Point n) (hx : ‖x‖ < r) :
    ContDiffAt ℝ 2 (radialTransportSolve k f) x := by
  have hxnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  set r₁ : ℝ := (‖x‖ + r) / 2 with hr₁def
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; linarith
  have hr₁r : r₁ < r := by rw [hr₁def]; linarith
  have hxr₁ : ‖x‖ < r₁ := by rw [hr₁def]; linarith
  obtain ⟨f', hf'2, hE⟩ := contDiff_two_cutoff_extension_of_ball f r r₁ hr₁0 hr₁r hf
  have hEball : Set.EqOn f f' (Metric.ball (0 : Point n) r₁) := hE
  have hsolveEq : Set.EqOn (radialTransportSolve k f) (radialTransportSolve k f')
      (Metric.ball (0 : Point n) r₁) :=
    radialTransportSolve_congrOn_ball k f f' r₁ hEball
  have hglob : ContDiff ℝ 2 (radialTransportSolve k f') :=
    radialTransportSolve_contDiff_two k f' hf'2
  have hxball : x ∈ Metric.ball (0 : Point n) r₁ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hxr₁
  exact hglob.contDiffAt.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxball) hsolveEq)

/-! ### §3. The finite-order `pd` extractors (the pointwise partial-derivative calculus). -/

/-- `ContDiffAt ℝ 4 f x ⟹ ContDiffAt ℝ 3 (∂ᵢf) x` — the fourth-partial extractor. -/
theorem contDiffAt_pd_of_contDiffAt_four (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 4 f x) : ContDiffAt ℝ 3 (fun y => pd f m y) x := by
  have hfd : ContDiffAt ℝ 3 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 3) (by norm_num)
  have happ : ContDiffAt ℝ 3 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact happ.congr_of_eventuallyEq e1

/-- `ContDiffAt ℝ 3 f x ⟹ ContDiffAt ℝ 2 (∂ᵢf) x` — the third-partial extractor. -/
theorem contDiffAt_pd_of_contDiffAt_three (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 (fun y => pd f m y) x := by
  have hfd : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 2) (by norm_num)
  have happ : ContDiffAt ℝ 2 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact happ.congr_of_eventuallyEq e1

/-- `ContDiffAt ℝ 2 f x ⟹ ContDiffAt ℝ 1 (∂ᵢf) x` — the second-partial extractor. -/
theorem contDiffAt_pd_of_contDiffAt_two (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (fun y => pd f m y) x := by
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 1) (by norm_num)
  have happ : ContDiffAt ℝ 1 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact happ.congr_of_eventuallyEq e1

/-- `ContDiffAt ℝ 1 f x ⟹ ContinuousAt (∂ᵢf) x` — the first-partial continuity extractor. -/
theorem continuousAt_pd_of_contDiffAt_one (f : Point n → ℝ) (m : Fin n) (x : Point n)
    (hf : ContDiffAt ℝ 1 f x) : ContinuousAt (fun y => pd f m y) x := by
  have hfd : ContDiffAt ℝ 0 (fun y => fderiv ℝ f y) x := hf.fderiv_right (m := 0) (by norm_num)
  have happ : ContDiffAt ℝ 0 (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) x :=
    hfd.clm_apply contDiffAt_const
  have hdf_ev : ∀ᶠ y in nhds x, DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have e1 : (fun y => pd f m y) =ᶠ[nhds x] (fun y => (fderiv ℝ f y) (Pi.single m (1 : ℝ))) := by
    filter_upwards [hdf_ev] with y hy using pd_eq_fderiv f m y hy
  exact (happ.congr_of_eventuallyEq e1).continuousAt

/-! ### §4. (L-b, conditional) chart C⁵ ⟹ ĝ entries C⁴ ⟹ the source `T̂û₀` is C². -/

/-- **The generic C⁵-chart ⟹ C⁴-pullback-entry step** — the WhiteW0 §1 chain one Fréchet order
    up, with the chart regularity CARRIED as `hF5` (the labelled Jet-5 residue).  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_entry_contDiffAt4_of_chartC5
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (v : Point n)
    (hF5 : ContDiffAt ℝ 5 (uniformFlowExp g gi hC hK q) v) (i j : Fin n) :
    ContDiffAt ℝ 4 (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v := by
  have hF4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK q) v := hF5.of_le (by norm_num)
  have hJentry : ∀ c a : Fin n, ContDiffAt ℝ 4
      (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single c 1) a) v := by
    intro c a
    have h1 : ContDiffAt ℝ 4
        (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single c (1 : ℝ))) v :=
      (hF5.fderiv_right (m := 4) (by norm_num)).clm_apply contDiffAt_const
    exact (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).contDiff.comp_contDiffAt v h1
  have hgF : ∀ a b : Fin n, ContDiffAt ℝ 4
      (fun w => g (uniformFlowExp g gi hC hK q w) a b) v := fun a b =>
    ((hg a b).contDiffAt.of_le le_top).comp v hF4
  simp only [uniformFlowPullbackMetric]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    ((hgF a b).mul (hJentry i a)).mul (hJentry j b)

/-- **Chart C⁵ ⟹ whitened metric entries C⁴ on a per-`q` gate** — the `white_w0_pack` entry leg
    one order up, conditional on the labelled `hch5`.  NOT `a₁ = R/6`. -/
theorem white_metric_entry_contDiffAt4_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (_hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      ∀ i j, ContDiffAt ℝ 4 (fun w => whiteMetric κ hκ hKc q w i j) x := by
  classical
  set ρ : ℝ := min (expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q)
    (uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc)
    with hρdef
  have hρ0 : 0 < ρ := lt_min (expRho_pos _ _ _ _) (uniformFlowRadius_pos _ _ _ _)
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  refine ⟨ρ / (Real.sqrt n + 1), by positivity, ?_⟩
  intro y hy i j
  -- velocity confinement `‖E_q y‖ < ρ`.
  have hvel : ‖whiteVel κ q y‖ < ρ := by
    have h1 : ‖whiteVel κ q y‖ ≤ Real.sqrt n * ‖y‖ := whiteVel_norm_le κ hκ q y
    have h2 : Real.sqrt n * ‖y‖ ≤ Real.sqrt n * (ρ / (Real.sqrt n + 1)) :=
      mul_le_mul_of_nonneg_left hy.le hsn
    have h4 : Real.sqrt n * (ρ / (Real.sqrt n + 1)) < ρ := by
      have hlt : Real.sqrt n / (Real.sqrt n + 1) < 1 :=
        (div_lt_one (by positivity)).mpr (by linarith)
      calc Real.sqrt n * (ρ / (Real.sqrt n + 1))
          = (Real.sqrt n / (Real.sqrt n + 1)) * ρ := by ring
        _ < 1 * ρ := mul_lt_mul_of_pos_right hlt hρ0
        _ = ρ := one_mul ρ
    linarith
  have hvexp : ‖whiteVel κ q y‖
      < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q :=
    lt_of_lt_of_le hvel (min_le_left _ _)
  have hvuf : ‖whiteVel κ q y‖
      < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc :=
    lt_of_lt_of_le hvel (min_le_right _ _)
  -- the whitening is a fixed CLM (C⁴ at any order).
  have hlinAt : ContDiffAt ℝ 4 (whiteVel κ q) y := by
    have heq : whiteVel κ q = ⇑(matToCLM (curvedWhitening κ q)) := by
      funext w
      funext i
      rw [matToCLM_apply]
      rfl
    rw [heq]
    exact (matToCLM (curvedWhitening κ q)).contDiff.contDiffAt
  have hrwm : (fun w => whiteMetric κ hκ hKc q w i j)
      = fun w => ∑ k, ∑ l, curvedWhitening κ q i k
          * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
          * curvedWhitening κ q l j := by
    funext w
    simp only [whiteMetric, whitePullbackMetric]
  rw [hrwm]
  refine ContDiffAt.sum fun k _ => ContDiffAt.sum fun l _ =>
    (contDiffAt_const.mul ?_).mul contDiffAt_const
  have hUF := uniformFlowPullbackMetric_entry_contDiffAt4_of_chartC5 (curvedRNCMetric κ)
    (curvedRNCInv κ) (fun a b => curvedRNCMetric_contDiff κ a b) (curvedRNC_hChr κ hκ)
    hKc q (whiteVel κ q y) (hch5 (whiteVel κ q y) hvexp hvuf) k l
  exact hUF.comp y hlinAt

/-- Finite product of `ContDiffAt ℝ 4` fields is `ContDiffAt ℝ 4` (order-4 clone of the banked
    order-2 `contDiffAt_prod`). -/
theorem contDiffAt_prod_four {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (x : Point n)
    (hF : ∀ i ∈ s, ContDiffAt ℝ 4 (fun y => F i y) x) :
    ContDiffAt ℝ 4 (fun y => ∏ i ∈ s, F i y) x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact contDiffAt_const
  | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hF a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- `det ∘ g` is `ContDiffAt ℝ 4` when the entries are (order-4 clone of the banked
    `det_contDiffAt_two`; `det` is a polynomial in the entries). -/
theorem det_contDiffAt_four (g : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hg4 : ∀ a b, ContDiffAt ℝ 4 (fun y => g y a b) x) :
    ContDiffAt ℝ 4 (fun y => Matrix.det (g y)) x := by
  rw [show (fun y => Matrix.det (g y))
        = (fun y => ∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, g y (σ i) i)
      from funext (fun y => Matrix.det_apply' _)]
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul
    (contDiffAt_prod_four univ (fun i y => g y (σ i) i) x (fun i _ => hg4 (σ i) i))

/-- **The whitened inverse-metric entries are `ContDiffAt ℝ 2`** at a point where the entries are
    C² and `matToCLM ĝ` is a unit — `Ring.inverse` is `C^∞` at units of the operator Banach
    algebra (`contDiffAt_ringInverse`), and entry extraction is continuous-linear.  Mirror of the
    banked `expPullbackMetricInv_contDiffAt_one`, at the whitened chart and order 2. -/
theorem whiteMetricInv_entry_contDiffAt_two (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (x : Point n)
    (hE : ∀ a b, ContDiffAt ℝ 2 (fun w => whiteMetric κ hκ hKc q w a b) x)
    (hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q x a b))) (i j : Fin n) :
    ContDiffAt ℝ 2 (fun w => whiteMetricInv κ hκ hKc q w i j) x := by
  have hE' : ∀ a b, ContDiffAt ℝ 2
      (fun w => whitePullbackMetric κ hκ hKc q w a b) x := hE
  have hmet_cd : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun w => matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b)) x := by
    show ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun w => ∑ a, ∑ b, whitePullbackMetric κ hκ hKc q w a b • elemCLM a b) x
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    exact (hE' a b).smul contDiffAt_const
  have hinv_cd := contDiffAt_ringInverse (n := (2 : WithTop ℕ∞)) ℝ hU.unit
  rw [IsUnit.unit_spec] at hinv_cd
  have hcomp := hinv_cd.comp x hmet_cd
  have hfull := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).contDiff
      (n := (2 : WithTop ℕ∞))).contDiffAt.comp x
    (((ContinuousLinearMap.apply ℝ (Point n) (Pi.single j (1 : ℝ) : Point n)).contDiff
      (n := (2 : WithTop ℕ∞))).contDiffAt.comp x hcomp)
  have heq : (fun w => whiteMetricInv κ hκ hKc q w i j) = fun w =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        ((ContinuousLinearMap.apply ℝ (Point n) (Pi.single j (1 : ℝ) : Point n))
          (Ring.inverse (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b)))) := by
    funext w
    simp only [whiteMetricInv, whitePullbackMetricInv, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.proj_apply]
  rw [heq]
  exact hfull

/-- **`Δ_g f` is `ContDiffAt ℝ 2`** from `gi` entries C², `g` entries C³ and `f` C⁴ at the point —
    the coordinate Laplace–Beltrami regularity assembly (Christoffels C² from `gi`·∂`g`; the two
    `f`-derivatives spend two of the four orders). -/
theorem laplaceBeltrami_contDiffAt_two_of_data (g gi : Point n → Fin n → Fin n → ℝ)
    (f : Point n → ℝ) (x : Point n)
    (hgi : ∀ a b, ContDiffAt ℝ 2 (fun y => gi y a b) x)
    (hg : ∀ a b, ContDiffAt ℝ 3 (fun y => g y a b) x)
    (hf : ContDiffAt ℝ 4 f x) :
    ContDiffAt ℝ 2 (fun z => laplaceBeltrami g gi f z) x := by
  have hΓ : ∀ μ ν ρ : Fin n, ContDiffAt ℝ 2 (fun z => christoffel g gi μ ν ρ z) x := by
    intro μ ν ρ
    simp only [christoffel]
    refine contDiffAt_const.mul (ContDiffAt.sum fun α _ => (hgi μ α).mul ?_)
    exact ((contDiffAt_pd_of_contDiffAt_three _ ν x (hg α ρ)).add
        (contDiffAt_pd_of_contDiffAt_three _ ρ x (hg α ν))).sub
      (contDiffAt_pd_of_contDiffAt_three _ α x (hg ν ρ))
  have hf3 : ContDiffAt ℝ 3 f x := hf.of_le (by norm_num)
  have hfirst : ∀ k : Fin n, ContDiffAt ℝ 2 (fun z => pd f k z) x :=
    fun k => contDiffAt_pd_of_contDiffAt_three f k x hf3
  have hsec : ∀ i j : Fin n, ContDiffAt ℝ 2 (fun z => pd (fun y => pd f j y) i z) x := by
    intro i j
    exact contDiffAt_pd_of_contDiffAt_three _ i x (contDiffAt_pd_of_contDiffAt_four f j x hf)
  simp only [laplaceBeltrami]
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (hgi i j).mul ((hsec i j).sub (ContDiffAt.sum fun k _ => (hΓ k i j).mul (hfirst k)))

/-- **★ `white_transport_source_contDiffAt2_of_chartC5` — (L-b): the transport source
    `T̂û₀ = Θ̂^{−1/2}·Δ_ĝ(Θ̂^{1/2}·û₀)` is gate-locally `ContDiffAt ℝ 2`, CONDITIONAL on the
    labelled chart-C⁵ residue `hch5`.**  The order ledger executed: entries C⁴ (chart C⁵) ⟹
    det/√det/Θ̂ C⁴ (positivity from the banked `white_w0_pack` gate) ⟹ Θ̂^{±1/2} C⁴; ĝ⁻¹ C² via
    `Ring.inverse` at the Neumann unit; the Δ_ĝ assembly spends two orders.  NOT `a₁ = R/6`. -/
theorem white_transport_source_contDiffAt2_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) x := by
  obtain ⟨r₄, hr₄0, hE4⟩ := white_metric_entry_contDiffAt4_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rP, hrP0, hpackP⟩ := white_w0_pack κ hκ hKc q hq
  obtain ⟨rN, hrN0, M, hM0, hpkgN⟩ := whitePullbackMetric_neumann κ hκ hKc
  refine ⟨min (min r₄ rP) rN, lt_min (lt_min hr₄0 hrP0) hrN0, ?_⟩
  intro x hx
  have hx4 : ‖x‖ < r₄ := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_left _ _))
  have hxP : ‖x‖ < rP := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_right _ _))
  have hxN : ‖x‖ < rN := lt_of_lt_of_le hx (min_le_right _ _)
  have hE : ∀ i j, ContDiffAt ℝ 4 (fun w => whiteMetric κ hκ hKc q w i j) x := hE4 x hx4
  obtain ⟨-, -, hdetpos, -, hθpos, -⟩ := hpackP x hxP
  -- det/√det/Θ̂ at C⁴.
  have hdet4 : ContDiffAt ℝ 4 (fun w => Matrix.det (whiteMetric κ hκ hKc q w)) x :=
    det_contDiffAt_four _ x hE
  have hsq4 : ContDiffAt ℝ 4
      (fun w => Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q w))) x :=
    hdet4.sqrt (ne_of_gt hdetpos)
  have hsqpos : 0 < Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q x)) :=
    Real.sqrt_pos.mpr hdetpos
  have hθ4 : ContDiffAt ℝ 4 (whiteTheta κ hκ hKc q) x := by
    have hrwθ : whiteTheta κ hκ hKc q
        = fun w => (Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q w)))⁻¹ := rfl
    rw [hrwθ]
    exact hsq4.inv (ne_of_gt hsqpos)
  -- ĝ⁻¹ at C² (Neumann unit).
  have hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q x a b)) :=
    (hpkgN q hq x hxN).2.1
  have hgi2 : ∀ i j, ContDiffAt ℝ 2 (fun w => whiteMetricInv κ hκ hKc q w i j) x :=
    fun i j => whiteMetricInv_entry_contDiffAt_two κ hκ hKc q x
      (fun a b => (hE a b).of_le (by norm_num)) hU i j
  -- the folded half-power inner function at C⁴.
  have hhalf : ContDiffAt ℝ 4 (fun y => whiteTheta κ hκ hKc q y ^ ((1/2) : ℝ)) x :=
    hθ4.rpow_const_of_ne (ne_of_gt hθpos)
  have hh4 : ContDiffAt ℝ 4
      (fun y => whiteTheta κ hκ hKc q y ^ ((1/2) : ℝ) * (fun _ : Point n => (1 : ℝ)) y) x :=
    hhalf.mul contDiffAt_const
  have hlap : ContDiffAt ℝ 2 (fun z =>
      laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (fun y => whiteTheta κ hκ hKc q y ^ ((1/2) : ℝ) * (fun _ : Point n => (1 : ℝ)) y) z) x :=
    laplaceBeltrami_contDiffAt_two_of_data _ _ _ x hgi2
      (fun a b => (hE a b).of_le (by norm_num)) hh4
  have hneg : ContDiffAt ℝ 2 (fun z => whiteTheta κ hκ hKc q z ^ (-(1/2) : ℝ)) x :=
    (hθ4.rpow_const_of_ne (ne_of_gt hθpos)).of_le (by norm_num)
  have hrw : whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)) = fun z =>
      whiteTheta κ hκ hKc q z ^ (-(1/2) : ℝ)
        * laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
            (fun y => whiteTheta κ hκ hKc q y ^ ((1/2) : ℝ) * (fun _ : Point n => (1 : ℝ)) y)
            z := rfl
  rw [hrw]
  exact hneg.mul hlap

/-- **★ `white_u1_contDiffAt2_of_chartC5` — gate-local C² of `û₁`, conditional on `hch5`**:
    the source C² (L-b) fed through the LOCAL interchange (L-a).  NOT `a₁ = R/6`. -/
theorem white_u1_contDiffAt2_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (whiteCoeffs κ hκ hKc q 1) x := by
  obtain ⟨r₀, hr₀0, hsrc⟩ := white_transport_source_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  refine ⟨r₀, hr₀0, ?_⟩
  intro x hx
  have hu1 : whiteCoeffs κ hκ hKc q 1
      = radialTransportSolve 1 (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) := rfl
  rw [hu1]
  exact radialTransportSolve_contDiffAt_two_of_ball 1 _ r₀ hsrc x hx

/-- **★★ `white_w1_contDiffAt2_of_chartC5` — the gate-local `hw1C2` leg, conditional on exactly
    `hch5`**: fold `û₁` with the banked C² `Θ̂^{−1/2}` chain (`white_w0_pack`).  NOT `a₁ = R/6`. -/
theorem white_w1_contDiffAt2_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₁ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₁ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x := by
  obtain ⟨rU, hrU0, hu1⟩ := white_u1_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rP, hrP0, hpack⟩ := white_w0_pack κ hκ hKc q hq
  refine ⟨min rP rU, lt_min hrP0 hrU0, ?_⟩
  intro x hx
  have hxP : ‖x‖ < rP := lt_of_lt_of_le hx (min_le_left _ _)
  have hxU : ‖x‖ < rU := lt_of_lt_of_le hx (min_le_right _ _)
  obtain ⟨-, -, -, hθC2, hθpos, -⟩ := hpack x hxP
  have hrwf : foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1
      = fun y => (whiteTheta κ hκ hKc q y) ^ (-(1 : ℝ) / 2) * whiteCoeffs κ hκ hKc q 1 y :=
    rfl
  rw [hrwf]
  exact (hθC2.rpow_const_of_ne (ne_of_gt hθpos)).mul (hu1 x hxU)

/-! ### §5. The whiteDelta binder LOCALIZATION (`hΔ` from BALL-LOCAL C² of `w₁`). -/

/-- **First/second partial-sum bounds on `closedBall 0 r` from BALL-LOCAL C²** (`‖·‖ < R`,
    `r < R`) — the J4-639 `smooth_jet_bounds_on_closedBall_C2` with the GLOBAL binder dropped:
    per-direction continuity from the pointwise extractors + per-direction compactness bounds
    (no sum-continuity needed).  NOT `a₁ = R/6`. -/
theorem jet_bounds_on_closedBall_of_ballC2 (f : Point n → ℝ) (r R : ℝ) (hrR : r < R)
    (hf : ∀ x : Point n, ‖x‖ < R → ContDiffAt ℝ 2 f x) :
    ∃ M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ ∀ x : Point n, ‖x‖ ≤ r →
      (∑ k, |pd f k x|) ≤ M1 ∧ (∑ i, ∑ j, |pd (fun y => pd f j y) i x|) ≤ M2 := by
  classical
  have hmem : ∀ x : Point n, x ∈ Metric.closedBall (0 : Point n) r → ‖x‖ < R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    linarith
  have hc1 : ∀ k : Fin n, ContinuousOn (fun z => pd f k z)
      (Metric.closedBall (0 : Point n) r) := fun k x hx =>
    (continuousAt_pd_of_contDiffAt_one f k x
      ((hf x (hmem x hx)).of_le (by norm_num))).continuousWithinAt
  have hc2 : ∀ i j : Fin n, ContinuousOn (fun z => pd (fun y => pd f j y) i z)
      (Metric.closedBall (0 : Point n) r) := by
    intro i j x hx
    have hpd1 : ContDiffAt ℝ 1 (fun y => pd f j y) x :=
      contDiffAt_pd_of_contDiffAt_two f j x (hf x (hmem x hx))
    exact (continuousAt_pd_of_contDiffAt_one _ i x hpd1).continuousWithinAt
  choose C1 hC1 using fun k : Fin n =>
    (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn (hc1 k)
  choose C2 hC2 using fun ij : Fin n × Fin n =>
    (isCompact_closedBall (0 : Point n) r).exists_bound_of_continuousOn (hc2 ij.1 ij.2)
  refine ⟨∑ k, max (C1 k) 0, ∑ i, ∑ j, max (C2 (i, j)) 0,
    Finset.sum_nonneg (fun k _ => le_max_right _ _),
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => le_max_right _ _)), ?_⟩
  intro x hx
  have hxmem : x ∈ Metric.closedBall (0 : Point n) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx
  constructor
  · refine Finset.sum_le_sum fun k _ => ?_
    have h := hC1 k x hxmem
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h := hC2 (i, j) x hxmem
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)

/-- **★ `whiteDelta_discharged_C2_local` — the `hΔ` existence from BALL-LOCAL C² of `w₁`** —
    the J4-639 `whiteDelta_discharged_C2` with the GLOBAL `ContDiff ℝ 2` binder weakened to
    `ContDiffAt ℝ 2` on `ball 0 rW` (the jet bounds are compact-ball suprema; the gate shrinks
    into the ball).  NOT `a₁ = R/6`. -/
theorem whiteDelta_discharged_C2_local (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (rW : ℝ) (hrW0 : 0 < rW)
    (hw1loc : ∀ x : Point n, ‖x‖ < rW →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x) :
    ∃ rΔ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∀ x : Point n, ‖x‖ < rΔ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ := by
  classical
  obtain ⟨r₁, hr₁0, Gb, hGb0, hgib⟩ := whiteInv_entry_bound κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  set rΔ : ℝ := min (min r₁ rΓ) (rW / 2) with hrΔdef
  have hrΔ0 : 0 < rΔ := lt_min (lt_min hr₁0 hrΓ0) (by linarith)
  have hrΔW : rΔ < rW := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨M1, M2, hM10, hM20, hM⟩ := jet_bounds_on_closedBall_of_ballC2
    (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) rΔ rW hrΔW hw1loc
  have hcoef0 : 0 ≤ Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg hGb0 (mul_nonneg hCΓ0 hrΔ0.le))
      (pow_nonneg (Nat.cast_nonneg n) 2)
  refine ⟨rΔ, hrΔ0, Gb * M2 + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 * M1,
    add_nonneg (mul_nonneg hGb0 hM20) (mul_nonneg hcoef0 hM10), ?_⟩
  intro x hx
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_left _ _))
  have hxΓ : ‖x‖ < rΓ := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_right _ _))
  have hbound := laplaceBeltrami_abs_le_of_entry_bounds
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
    (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x
    Gb (CΓ * rΔ) hGb0 (mul_nonneg hCΓ0 hrΔ0.le)
    (fun i j => hgib q hq x hx1 i j)
    (fun k i j => (hΓ q hq x hxΓ k i j).trans
      (mul_le_mul_of_nonneg_left hx.le hCΓ0))
  obtain ⟨hS1le, hS2le⟩ := hM x hx.le
  calc |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x|
      ≤ Gb * (∑ i, ∑ j, |pd (fun y =>
            pd (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) j y) i x|)
          + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2
            * ∑ k, |pd (foldedCoeff (whiteTheta κ hκ hKc q)
                (whiteCoeffs κ hκ hKc q) 1) k x| := hbound
    _ ≤ Gb * M2 + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 * M1 :=
        add_le_add (mul_le_mul_of_nonneg_left hS2le hGb0)
          (mul_le_mul_of_nonneg_left hS1le hcoef0)

/-! ### §6. ★★ The K1 budgets: gate-local `hw1C2` binder; `{h0, h1}` under the chart-C⁵ label. -/

/-- **★★ `white_K1BudgetW_C2_w0Free_localW1` — the K1 `t²` budget with the `hw1C2` input
    weakened from GLOBAL `ContDiff ℝ 2` to BALL-LOCAL `ContDiffAt ℝ 2`** (the J4-640 scope note
    executed: both the pair binder and the `hΔ` discharge now consume only the gate-local
    shadow).  Inputs: {hw1C2-ball-local, h0, h1}.  ⚠ CONDITIONAL; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_C2_w0Free_localW1 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w) (rW : ℝ) (hrW0 : 0 < rW)
    (hw1loc : ∀ x : Point n, ‖x‖ < rW →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x) :
    ∃ rGΔ > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rGΔ →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  obtain ⟨rWg, hrWg0, hW0gate⟩ := white_w0_contDiffAt2_gate κ hκ hKc q hq
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged κ hκ hKc q hq
  obtain ⟨rΔ, hrΔ0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged_C2_local κ hκ hKc q hq rW hrW0 hw1loc
  refine ⟨min (min (min rG rΔ) rWg) rW,
    lt_min (lt_min (lt_min hrG0 hrΔ0) hrWg0) hrW0, ?_⟩
  intro r₀ hr₀ h0 h1 H C_H hCH hH hH0
  have hrG' : r₀ ≤ rG :=
    hr₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hrΔ' : r₀ ≤ rΔ :=
    hr₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hrWg' : r₀ ≤ rWg := hr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrW' : r₀ ≤ rW := hr₀.trans (min_le_right _ _)
  exact white_K1BudgetW_of_transport_C2 κ hκ hKc q r₀ w C_Δ hw2 hCΔ0
    (fun x hx => ⟨hW0gate x (lt_of_lt_of_le hx hrWg'), hw1loc x (lt_of_lt_of_le hx hrW')⟩)
    (fun x hx i => hG x (lt_of_lt_of_le hx hrG') i)
    h0 h1
    (fun x hx => hΔd x (lt_of_lt_of_le hx hrΔ'))
    H C_H hCH hH hH0

/-- **★★★ `white_K1BudgetW_h0h1_of_chartC5` — THE HEADLINE: conditional on the labelled
    chart-C⁵ residue `hch5`, THE K1 INPUT LIST IS `{h0, h1}`** — both regularity legs (`hw0C2`
    J4-640, `hw1C2` this brick) are discharged internally.  ⚠ `hch5` (the Jet-5 chart rung)
    is the precisely-scoped remaining regularity residue; its inhabitance is NOT claimed here.
    NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_h0h1_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ rGΔ > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rGΔ →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      (∀ x : Point n, ‖x‖ < r₀ →
        totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0) →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  obtain ⟨rW, hrW0, hw1loc⟩ := white_w1_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  exact white_K1BudgetW_C2_w0Free_localW1 κ hκ hKc q hq w hw2 rW hrW0 hw1loc

/-! ### §7. Non-vacuity and no-silent-strengthening gates (cp466 discipline). -/

/-- **Monotonicity record — NO silent strengthening of the `hw1C2` binder**: the previous GLOBAL
    `ContDiff ℝ 2` input implies the new ball-local shape at every radius. -/
theorem hw1C2_global_implies_ball (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (rW : ℝ)
    (h : ContDiff ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1)) :
    ∀ x : Point n, ‖x‖ < rW →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x :=
  fun _x _ => h.contDiffAt

/-- **Faithfulness record for the chart-C⁵ label**: `hch5` is the EXACT one-order-up analogue of
    the banked C⁴ conclusion — it implies (and is only consumed through) the
    `uniformFlowExp_contDiffAt_four` shape.  (Its inhabitance — the Jet-5 rung — is the scoped
    residue and is NOT claimed.) -/
theorem chartC5_implies_banked_chartC4 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 4 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v :=
  fun v h1 h2 => (hch5 v h1 h2).of_le (by norm_num)

/-- **★ The (L-a) interchange gate — UNCONDITIONAL, at a NON-globally-smooth-looking source**:
    the source `v ↦ (1 − v 0)⁻¹` on `Point 2` is `C²` only where `v 0 ≠ 1` (the antecedent is
    genuinely BALL-LOCAL in form), and the local interchange delivers `C²` of its ray solve at a
    NONZERO gate point of `ball 0 (1/2)`.  No `{0}`-collapse; no global-smoothness input. -/
theorem rayLocal_interchange_witness_gate :
    ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < (1/2 : ℝ) ∧
      ContDiffAt ℝ 2
        (radialTransportSolve 1 (fun v : Point 2 => (1 - v 0)⁻¹)) x := by
  have hf : ∀ v : Point 2, ‖v‖ < (1/2 : ℝ) →
      ContDiffAt ℝ 2 (fun w : Point 2 => (1 - w 0)⁻¹) v := by
    intro v hv
    have h0 : |v 0| ≤ ‖v‖ := by
      have h := norm_le_pi_norm v 0
      rwa [Real.norm_eq_abs] at h
    have habs : |v 0| < 1/2 := lt_of_le_of_lt h0 hv
    have hne : (1 : ℝ) - v 0 ≠ 0 := by
      have h2 := (abs_lt.mp habs).2
      intro h
      linarith
    have hcoord : ContDiffAt ℝ 2 (fun w : Point 2 => w 0) v :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff.contDiffAt
    exact (contDiffAt_const.sub hcoord).inv hne
  have hb : ‖(fun _ => 1/4 : Point 2)‖ ≤ (1/4 : ℝ) := by
    refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr fun i => ?_
    show ‖(1/4 : ℝ)‖ ≤ (1/4 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
  have hxlt : ‖(fun _ => 1/4 : Point 2)‖ < (1/2 : ℝ) := lt_of_le_of_lt hb (by norm_num)
  refine ⟨(fun _ => 1/4), ?_, hxlt,
    radialTransportSolve_contDiffAt_two_of_ball 1 _ (1/2) hf _ hxlt⟩
  intro hx0
  have h := congrFun hx0 (0 : Fin 2)
  rw [Pi.zero_apply] at h
  norm_num at h

/-- **★ The localized-`hΔ` witness gate at the genuinely curved witness** (`n = 2`, `κ = −1`,
    fat `K = closedBall 0 2`, off-centre row `q = (1,1)`): GIVEN only the BALL-LOCAL C² of `w₁`
    (the new, strictly weaker antecedent), the localized discharge instantiates to a positive
    gate with a NONZERO gate point carrying the `hΔ` bound.  Honest antecedent record: only the
    ball-local `w₁` regularity blocks unconditional instantiation (its chart-C⁵-conditional
    supplier is `white_w1_contDiffAt2_of_chartC5`). -/
theorem whiteDelta_local_witness_gate
    (hw1loc : ∀ x : Point 2, ‖x‖ < 1 →
      ContDiffAt ℝ 2 (foldedCoeff
        (whiteTheta (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        1) x) :
    ∃ r₀ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧
      |laplaceBeltrami
        (whiteMetric (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteMetricInv (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (foldedCoeff
          (whiteTheta (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
          (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
          1) x| ≤ C_Δ := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨r₀, hr₀0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged_C2_local (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq 1 one_pos hw1loc
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  have hxlt : ‖(fun _ => r₀ / 2 : Point 2)‖ < r₀ := lt_of_le_of_lt hb (by linarith)
  refine ⟨r₀, hr₀0, C_Δ, hCΔ0, (fun _ => r₀ / 2), ?_, hxlt, hΔd _ hxlt⟩
  intro hx0
  have h := congrFun hx0 (0 : Fin 2)
  rw [Pi.zero_apply] at h
  linarith

end QIQTH.WhiteW1

section AxiomChecks
open QIQTH.WhiteW1
#print axioms QIQTH.WhiteW1.rayIntegral_hasFDerivAt_C1
#print axioms QIQTH.WhiteW1.rayIntegral_contDiff_nat_of_contDiff_nat
#print axioms QIQTH.WhiteW1.radialTransportSolve_contDiff_two
#print axioms QIQTH.WhiteW1.contDiff_two_cutoff_extension_of_ball
#print axioms QIQTH.WhiteW1.radialTransportSolve_contDiffAt_two_of_ball
#print axioms QIQTH.WhiteW1.contDiffAt_pd_of_contDiffAt_four
#print axioms QIQTH.WhiteW1.contDiffAt_pd_of_contDiffAt_three
#print axioms QIQTH.WhiteW1.contDiffAt_pd_of_contDiffAt_two
#print axioms QIQTH.WhiteW1.continuousAt_pd_of_contDiffAt_one
#print axioms QIQTH.WhiteW1.uniformFlowPullbackMetric_entry_contDiffAt4_of_chartC5
#print axioms QIQTH.WhiteW1.white_metric_entry_contDiffAt4_of_chartC5
#print axioms QIQTH.WhiteW1.contDiffAt_prod_four
#print axioms QIQTH.WhiteW1.det_contDiffAt_four
#print axioms QIQTH.WhiteW1.whiteMetricInv_entry_contDiffAt_two
#print axioms QIQTH.WhiteW1.laplaceBeltrami_contDiffAt_two_of_data
#print axioms QIQTH.WhiteW1.white_transport_source_contDiffAt2_of_chartC5
#print axioms QIQTH.WhiteW1.white_u1_contDiffAt2_of_chartC5
#print axioms QIQTH.WhiteW1.white_w1_contDiffAt2_of_chartC5
#print axioms QIQTH.WhiteW1.jet_bounds_on_closedBall_of_ballC2
#print axioms QIQTH.WhiteW1.whiteDelta_discharged_C2_local
#print axioms QIQTH.WhiteW1.white_K1BudgetW_C2_w0Free_localW1
#print axioms QIQTH.WhiteW1.white_K1BudgetW_h0h1_of_chartC5
#print axioms QIQTH.WhiteW1.hw1C2_global_implies_ball
#print axioms QIQTH.WhiteW1.chartC5_implies_banked_chartC4
#print axioms QIQTH.WhiteW1.rayLocal_interchange_witness_gate
#print axioms QIQTH.WhiteW1.whiteDelta_local_witness_gate
end AxiomChecks
