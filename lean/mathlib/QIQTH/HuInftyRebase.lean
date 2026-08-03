/-
  HuInftyRebase — J4-175: closing the transport-coefficient smoothness carry `hu` at the `C^∞`
  (`∞`) level, rebasing the downstream consumer chain off the unreachable analytic (`ω`) level.
  ONE brick of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity-plumbing brick: it upgrades J4-174's proven C¹ ray-integral rung to the FULL finite /
  `C^∞` tower and closes `hu` at `∞`.  No conclusion-in-disguise; no vacuous / unsatisfiable
  hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── THE ANALYTIC WALL J4-174 HIT (recap).  In the toolchain's `WithTop ℕ∞`, the smoothness level
     `(⊤ : WithTop ℕ∞) = ω` is the ANALYTIC level, whereas `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` is
     `C^∞` (all finite orders).  J4-174 proved `radialTransportSolve` preserves `C¹` by
     differentiation-under-the-integral, and noted the induction reaches every finite order `C^N`
     (hence `C^∞`) but NOT `ω` (parametric analyticity of a ray integral is a theorem Mathlib
     lacks).  So the `ω`-level `hu` was blocked ON THE SOLVE SIDE ONLY.

  ── THE REBASE THESIS (verified in PART A below).  Downstream consumers of the `hu`/`hw` carry
     never GENUINELY need `ω`: they use it only through `.continuous`, `.of_le` down to a finite
     order (`C²`), or LEVEL-PRESERVING algebra (`.mul`/`.sum`/`.add`) that reproduces exactly the
     level it consumes.  Therefore restating the chain at `∞` loses nothing, and `hu∞` closes fully.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── PART A — CONSUMER-ORDER AUDIT (the `hu` / `hw` carry, VERBATIM verdicts).

    Legend: "interface" = the consumer reproduces the SAME level it consumes via `.mul`/`.sum`/
    `.add` (works verbatim at `∞`); "downcast" = the consumer immediately drops to a strictly
    smaller order via `.continuous` (`C⁰`) or `.of_le` (`C²`).  NONE uses `ω` genuinely.

    ┌──────────────────────────────────────────────┬─────────┬──────────────┬──────────────────┐
    │ consumer (file:line)                          │ stated  │ genuine use  │ verdict          │
    ├──────────────────────────────────────────────┼─────────┼──────────────┼──────────────────┤
    │ foldedCoeff_vanVleck_contDiff                 │ ⊤ (hu)  │ ⊤ via `.mul` │ interface        │
    │   (FoldedCoeffChartMeas:83)                   │         │ (Θ^-½·u_k)   │ (level-preserv.) │
    │ hw_discharged (FoldedCoeffChartMeas:106)      │ ⊤ (hu)  │ ⊤ (delegate) │ interface        │
    │ witnessInner_continuous                       │ ⊤ (hw)  │ C⁰           │ downcast         │
    │   (GateChartMeasurability:98)                 │         │ `.continuous`│ (`.continuous`)  │
    │ heatParametrix_contDiff_space                 │ ⊤ (hw)  │ ⊤ via `.mul` │ interface; its   │
    │   (ResidualN1GaussianBound:124)               │         │ (G·Σ w_k tᵏ) │ callers take C⁰  │
    │                                               │         │              │ or C²            │
    │ innerKernel_contDiffAt_field                  │ ⊤ (hu)  │ C² via       │ downcast         │
    │   (OnGateFieldRegularity:127)                 │         │ `.of_le ⊤`   │ (`.of_le le_top`)│
    │ gatedWitness_contDiffAt_field                 │ ⊤ (hu)  │ C² (delegate)│ downcast         │
    │   (OnGateFieldRegularity:171)                 │         │              │                  │
    │ hCH_discharge (SpatialC2:69)                  │ ⊤ (hu)  │ C² via       │ downcast         │
    │                                               │         │ `.of_le ⊤`   │                  │
    │ a1_R6_of_residue_hCH_discharged (SpatialC2:   │ ⊤ (hu)  │ C² (via      │ downcast         │
    │   165) — `hu` slot only; `hsrc` is SEPARATE   │         │ hCH_discharge)│                 │
    └──────────────────────────────────────────────┴─────────┴──────────────┴──────────────────┘

    VERDICT.  Every consumer of the `hu`/`hw` carry is `∞`-safe: interface consumers reproduce
    the `∞` they are fed (all their algebra — `ContDiff.mul`/`.sum`/`.add` — is level-generic);
    downcast consumers only need `C²` or `C⁰`, both `≤ ∞`.  The ONLY friction is that the
    consumer STATEMENTS are typed at `⊤`; rebasing each statement `⊤ ↦ ∞` is a purely
    interface-level edit whose proof body is UNCHANGED (nothing in any body uses `AnalyticOnNhd`
    or the `n = ω` branch of `contDiff_succ_iff_fderiv`).  This file supplies the `∞`-typed
    building blocks and re-derives one representative consumer conclusion from `hu∞` to CERTIFY
    composability.

  ── PART B — the generic ray-integral `C^∞` tower (the real mathematics).  For a Banach target
     `F`, the operator `rayIntegral m g v = ∫₀¹ sᵐ • g(s•v) ds` satisfies the induction-step
     identity `fderiv (rayIntegral m g) = rayIntegral (m+1) (fderiv g)` (the extra `s` from the
     ray chain rule bumps `m ↦ m+1`).  Iterating over `N : ℕ` gives `ContDiff ℝ N` for every
     finite `N`, hence `ContDiff ℝ ∞` (`contDiff_infty`).  The scalar (`F = ℝ`) corollary is
     `radialTransportSolve_contDiff_infty`.

  ── PART C — `hu∞` FULLY CLOSED + consumer re-thread.  `transportOp_preserves_contDiff_infty`
     (the `∞` mirror of J4-174's `hT`, all geometric coefficients downcast `ω ↦ ∞`) + Part B
     drive the `k`-induction `hu_infty_closed`.  `hw_discharged_infty`,
     `heatParametrix_contDiff_space_infty`, and `witnessInner_continuous_ofInfty` re-thread the
     GateChartMeasurability continuity conclusion straight from `hu∞`, certifying the rebase.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.RadialTransport
import QIQTH.TransportOpSmoothness
import QIQTH.ParametrixFunction
import QIQTH.CutoffResidualGlobalBound
import QIQTH.FoldedCoeffChartMeas
import QIQTH.GateChartMeasurability
import QIQTH.ResidualN1GaussianBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RadialTransport
open QIQTH.ResidueBound QIQTH.HeatResidualBound QIQTH.HeatParametrixAnsatz
open QIQTH.FlatHeatEquation QIQTH.HeatParametrixOrder
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HuInftyRebase

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART B — the generic ray-integral operator and its `C^∞` tower.
    ############################################################################### -/

/-- **The generic (Banach-valued) ray-integral operator** `rayIntegral m g v = ∫₀¹ sᵐ • g(s•v) ds`.
    For `F = ℝ` this is `radialTransportSolve (m+1)` (see `radialTransportSolve_eq_rayIntegral`);
    generalizing the target `F` is exactly what makes the derivative-bumping induction close
    (`fderiv g` is `(Point n →L[ℝ] F)`-valued).  NOT `a₁ = R/6`. -/
noncomputable def rayIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : Point n → F) (v : Point n) : F :=
  ∫ s in (0:ℝ)..1, s ^ m • g (s • v)

section RayIntegral

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`rayIntegral_continuous` — the `C⁰` base rung.**  For continuous `g`, `rayIntegral m g` is
    continuous, being a parametric interval integral of the jointly continuous integrand
    `(v,s) ↦ sᵐ • g(s•v)`.  NOT `a₁ = R/6`. -/
theorem rayIntegral_continuous (m : ℕ) (g : Point n → F) (hg : Continuous g) :
    Continuous (rayIntegral m g) := by
  have huc : Continuous (Function.uncurry (fun (v : Point n) (s : ℝ) => s ^ m • g (s • v))) := by
    have he : (Function.uncurry (fun (v : Point n) (s : ℝ) => s ^ m • g (s • v)))
        = fun p : Point n × ℝ => p.2 ^ m • g (p.2 • p.1) := rfl
    rw [he]
    exact (continuous_snd.pow m).smul (hg.comp (continuous_snd.smul continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huc 0 1

/-- **★ `rayIntegral_hasFDerivAt` — the derivative-bumping first-order rung.**  For `g ∈ C^∞`
    (in particular `C¹`), `rayIntegral m g` is Fréchet-differentiable at every `v₀` with derivative
      `D(rayIntegral m g)(v₀) = rayIntegral (m+1) (fderiv ℝ g) v₀ = ∫₀¹ s^{m+1} • Dg(s•v₀) ds`.
    The extra factor `s` (the tangent of the ray `s•v₀`, chain rule) bumps the power `m ↦ m+1`,
    which is exactly why the induction closes.  Proof: Mathlib's `F`-valued dominated-derivative
    Leibniz rule, with the `v`-derivative dominated over the compact ray tube `[0,1] × closedBall`
    by the continuity of `Dg`, then the pointwise scalar identity `sᵐ • (s • X) = s^{m+1} • X`.
    NOT `a₁ = R/6`. -/
theorem rayIntegral_hasFDerivAt (m : ℕ) (g : Point n → F)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g) (v₀ : Point n) :
    HasFDerivAt (rayIntegral m g)
      (rayIntegral (m + 1) (fun x => fderiv ℝ g x) v₀) v₀ := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ g x :=
    fun x => (hg.differentiable (by simp)).differentiableAt
  have hcfd : Continuous (fun x => fderiv ℝ g x) := hg.continuous_fderiv (by simp)
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
    hbound intervalIntegrable_const hderiv
  -- rewrite the raw derivative `∫ sᵐ•(s•Dg)` into `rayIntegral (m+1) (fderiv g)`.
  have hcongr : (∫ s in (0:ℝ)..1, s ^ m • (s • fderiv ℝ g (s • v₀)))
      = rayIntegral (m + 1) (fun x => fderiv ℝ g x) v₀ := by
    rw [rayIntegral]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [smul_smul, pow_succ]
  rw [← hcongr]
  exact main

/-- **`rayIntegral_differentiable`** — `rayIntegral m g` is differentiable everywhere for `g ∈ C^∞`.
    NOT `a₁ = R/6`. -/
theorem rayIntegral_differentiable (m : ℕ) (g : Point n → F)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g) :
    Differentiable ℝ (rayIntegral m g) :=
  fun v₀ => (rayIntegral_hasFDerivAt m g hg v₀).differentiableAt

/-- **★ `rayIntegral_fderiv` — the induction-step identity.**  `fderiv (rayIntegral m g)
    = rayIntegral (m+1) (fderiv ℝ g)` (pointwise), read off `rayIntegral_hasFDerivAt`.  This is the
    `∂ I_m = I_{m+1} ∘ fderiv` recursion that closes the tower.  NOT `a₁ = R/6`. -/
theorem rayIntegral_fderiv (m : ℕ) (g : Point n → F)
    (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g) (v₀ : Point n) :
    fderiv ℝ (rayIntegral m g) v₀ = rayIntegral (m + 1) (fun x => fderiv ℝ g x) v₀ :=
  (rayIntegral_hasFDerivAt m g hg v₀).fderiv

end RayIntegral

/-- **★★ `rayIntegral_contDiff_nat` — the finite-order tower (the core induction).**  For every
    `N : ℕ`, every Banach target `F`, every `m` and `C^∞` integrand `g`, `rayIntegral m g` is
    `ContDiff ℝ N`.  Induction on `N`: the base is `rayIntegral_continuous`; the step uses
    `contDiff_succ_iff_fderiv` with the derivative rewritten by `rayIntegral_fderiv` to
    `rayIntegral (m+1) (fderiv ℝ g)` — to which the induction hypothesis applies (generalized over
    the codomain `F`, here bumped to `Point n →L[ℝ] F`).  The `n = ω` analyticity side goal is
    vacuous (`WithTop.natCast_ne_top`).  NOT `a₁ = R/6`. -/
theorem rayIntegral_contDiff_nat (N : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ) (g : Point n → F),
      ContDiff ℝ (∞ : WithTop ℕ∞) g →
      ContDiff ℝ ((N : ℕ) : WithTop ℕ∞) (rayIntegral m g) := by
  induction N with
  | zero =>
      intro F _ _ m g hg
      rw [Nat.cast_zero]
      exact contDiff_zero.mpr (rayIntegral_continuous m g hg.continuous)
  | succ N ih =>
      intro F _ _ m g hg
      rw [Nat.cast_succ]
      refine contDiff_succ_iff_fderiv.mpr ⟨rayIntegral_differentiable m g hg, ?_, ?_⟩
      · exact fun hω => absurd hω (WithTop.natCast_ne_top N)
      · have hfe : fderiv ℝ (rayIntegral m g) = rayIntegral (m + 1) (fun x => fderiv ℝ g x) :=
          funext (fun v => rayIntegral_fderiv m g hg v)
        rw [hfe]
        exact ih (m + 1) (fun x => fderiv ℝ g x) (contDiff_infty_iff_fderiv.mp hg).2

/-- **★★ `rayIntegral_contDiff_infty` — the `C^∞` tower.**  `rayIntegral m g` is `ContDiff ℝ ∞`
    for `C^∞` `g`, by `contDiff_infty` (`∞ ↔ ∀ finite N`) applied to `rayIntegral_contDiff_nat`.
    NOT `a₁ = R/6`. -/
theorem rayIntegral_contDiff_infty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g : Point n → F) (hg : ContDiff ℝ (∞ : WithTop ℕ∞) g) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (rayIntegral m g) :=
  contDiff_infty.mpr (fun N => rayIntegral_contDiff_nat N m g hg)

/-! ###############################################################################
    ### PART B (scalar corollary) — `radialTransportSolve` is `C^∞`.
    ############################################################################### -/

/-- **`radialTransportSolve_eq_rayIntegral`** — the scalar (`F = ℝ`) identification
    `radialTransportSolve k f = rayIntegral (k-1) f` (via `smul_eq_mul`).  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_eq_rayIntegral (k : ℕ) (f : Point n → ℝ) :
    radialTransportSolve k f = rayIntegral (k - 1) f := by
  funext v
  simp only [radialTransportSolve, rayIntegral, smul_eq_mul]

/-- **★ `radialTransportSolve_contDiff_infty` — the FULL `hSolve` rung at `∞`.**  For `C^∞ f`,
    `radialTransportSolve k f` is `ContDiff ℝ ∞`.  This is J4-174's C¹ rung upgraded to all finite
    orders via the generic ray-integral tower — the honest `∞`-level replacement of the analytic
    (`ω`) `hSolve` premise J4-174 could not reach.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_contDiff_infty (k : ℕ) (f : Point n → ℝ)
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (radialTransportSolve k f) := by
  rw [radialTransportSolve_eq_rayIntegral]
  exact rayIntegral_contDiff_infty (k - 1) f hf

/-! ###############################################################################
    ### PART C — the `∞` transport operator, `hu∞` closure, and consumer re-thread.
    ############################################################################### -/

/-- **`laplaceBeltrami_contDiff_infty` — `Δ_g` preserves `C^∞` (the `∞` mirror).**  Same content as
    `TransportOpSmoothness.laplaceBeltrami_contDiff`, but with the FIELD `f` only at `∞`: the
    geometric coefficients (`gi`, Christoffel) are `ω`-smooth (`hg`/`hgi`) and downcast `.of_le
    le_top` to `∞`, while the field's partials ride `contDiff_pd_inf`.  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_contDiff_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (f : Point n → ℝ) (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (fun x => laplaceBeltrami g gi f x) := by
  simp only [laplaceBeltrami]
  refine ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => ?_))
  refine ((hgi i j).of_le le_top).mul ?_
  refine (contDiff_pd_inf (fun y => pd f j y) (contDiff_pd_inf f hf j) i).sub ?_
  exact ContDiff.sum (fun k _ =>
    ((christoffel_contDiff g gi hg hgi k i j).of_le le_top).mul (contDiff_pd_inf f hf k))

/-- **★ `transportOp_preserves_contDiff_infty` — the `∞` mirror of J4-174's `hT`.**  For the `C^∞`
    metric/inverse-metric pair with `det g > 0`, `transportOp (vanVleck g) g gi` maps `C^∞ f` to
    `C^∞`.  The van-Vleck prefactors `Θ^{±½}` are `ω`-smooth (`vanVleck_contDiffAt` at level `∞`,
    non-vanishing from `vanVleck_pos`), the conjugated field is their product with `f`, and `Δ_g`
    preserves `C^∞` (`laplaceBeltrami_contDiff_infty`).  Crucially the INPUT is only `∞` (what the
    `hu` induction provides), not `ω`.  NOT `a₁ = R/6`. -/
theorem transportOp_preserves_contDiff_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (f : Point n → ℝ) (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (transportOp (vanVleck g) g gi f) := by
  have hΘpow : ∀ c : ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) (fun y => (vanVleck g y) ^ c) := by
    intro c
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (vanVleck_contDiffAt g hg v (hgpos v)).rpow_const_of_ne
      (ne_of_gt (vanVleck_pos g v (hgpos v)))
  have hinner : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun y => (vanVleck g y) ^ ((1 / 2 : ℝ)) * f y) := (hΘpow _).mul hf
  have hlap : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun x => laplaceBeltrami g gi (fun y => (vanVleck g y) ^ ((1 / 2 : ℝ)) * f y) x) :=
    laplaceBeltrami_contDiff_infty g gi hg hgi _ hinner
  unfold transportOp
  exact (hΘpow _).mul hlap

/-- **★★★ `hu_infty_closed` — `hu` FULLY CLOSED at `∞`.**  For the `C^∞` metric/inverse-metric pair
    with `det g > 0`, EVERY transport coefficient `transportCoeff (transportOp (vanVleck g) g gi) k`
    is `ContDiff ℝ ∞`.  Induction on `k`: `u_0 ≡ 1` is smooth; the step chains
    `transportOp_preserves_contDiff_infty` (from the `∞` IH — NOT `ω`) into
    `radialTransportSolve_contDiff_infty`.  This is the honest `∞`-level closure of the carry that
    J4-173/J4-174 left reduced to the analytic (`ω`) `hSolve` wall.  NOT `a₁ = R/6`. -/
theorem hu_infty_closed (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k) := by
  intro k
  induction k with
  | zero => rw [transportCoeff_zero]; exact contDiff_const
  | succ k ih =>
      rw [transportCoeff_succ]
      exact radialTransportSolve_contDiff_infty (k + 1) _
        (transportOp_preserves_contDiff_infty g gi hg hgi hgpos _ ih)

/-! ### Consumer re-thread — certifying `hu∞` composes. -/

/-- **`hw_discharged_infty` — the `hw` carry discharged at `∞` from `hu∞`.**  The `∞` mirror of
    `FoldedCoeffChartMeas.foldedCoeff_vanVleck_contDiff`: `foldedCoeff (vanVleck g) u k =
    (vanVleck g)^{-½}·u_k`, the prefactor `ω`-smooth (downcast `∞`), the product with the `∞`
    coefficient `u_k` staying `∞`.  Shows the interface (`.mul`) consumer composes verbatim at `∞`.
    NOT `a₁ = R/6`. -/
theorem hw_discharged_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k) := by
  intro k
  have hΘ : ContDiff ℝ (∞ : WithTop ℕ∞) (fun y => (vanVleck g y) ^ (-(1 : ℝ) / 2)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (vanVleck_contDiffAt g hg v (hgpos v)).rpow_const_of_ne
      (ne_of_gt (vanVleck_pos g v (hgpos v)))
  have hrw : foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k
      = fun y => (vanVleck g y) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (vanVleck g) g gi) k y := rfl
  rw [hrw]
  exact hΘ.mul (hu k)

/-- **`heatParametrix_contDiff_space_infty` — the `∞` mirror of the parametrix space-smoothness.**
    Same content as `ResidualN1GaussianBound.heatParametrix_contDiff_space`, but at `∞`: `H_N(t,·)
    = G(t,·)·Σ_{k≤N} w_k·tᵏ` with the Gaussian `ω`-smooth (downcast `∞`) and each folded coefficient
    `w_k` at `∞` (`hw`).  NOT `a₁ = R/6`. -/
theorem heatParametrix_contDiff_space_infty (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t : ℝ) (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (heatParametrix N Θ u t) := by
  have hHeq : heatParametrix N Θ u t
      = (fun y => gaussDdim t y * ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) :=
    funext (fun y => heatParametrix_folded N Θ u t y)
  rw [hHeq]
  exact ((gaussDdim_contDiff t).of_le le_top).mul
    (ContDiff.sum fun k _ => (hw k).mul contDiff_const)

/-- **★★ `witnessInner_continuous_ofInfty` — the GateChartMeasurability continuity conclusion,
    re-threaded straight from `hu∞`.**  For every time `τ`, the inner-slice spatial function
    `w ↦ radialCutoff a b w · heatParametrix 1 Θ u τ w` is `Continuous` — the SAME conclusion as
    `GateChartMeasurability.witnessInner_continuous`, but obtained from the `∞`-level folded-coeff
    carry `hw` (via `heatParametrix_contDiff_space_infty`, downcast `.continuous`).  CERTIFIES that
    the downstream measurability chain composes with `hu∞`: no consumer needed `ω`.  NOT `a₁ = R/6`. -/
theorem witnessInner_continuous_ofInfty (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (τ : ℝ)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    Continuous (fun w : Point n => radialCutoff a b w * heatParametrix 1 Θ u τ w) :=
  (radialCutoff_contDiff a b).continuous.mul
    (heatParametrix_contDiff_space_infty 1 Θ u τ hw).continuous

/-- **★★ `vanVleck_witnessInner_continuous_ofGeom` — end-to-end certificate from the raw geometry.**
    For the concrete `Θ = vanVleck g`, `u = transportCoeff (transportOp (vanVleck g) g gi)`, the
    inner-slice continuity is delivered from `{hg, hgi, hgpos}` ALONE: `hu_infty_closed` closes the
    coefficient carry at `∞`, `hw_discharged_infty` folds in the van-Vleck prefactor, and
    `witnessInner_continuous_ofInfty` downcasts to continuity.  This threads the WHOLE `hu → hw →
    parametrix → continuity` chain through the `∞` rebase, with `ω` nowhere required.
    NOT `a₁ = R/6`. -/
theorem vanVleck_witnessInner_continuous_ofGeom (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) (a b : ℝ) (τ : ℝ) :
    Continuous (fun w : Point n => radialCutoff a b w
      * heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) τ w) :=
  witnessInner_continuous_ofInfty (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) a b τ
    (hw_discharged_infty g gi hg hgpos (hu_infty_closed g gi hg hgi hgpos))

end QIQTH.HuInftyRebase

section AxiomChecks
open QIQTH.HuInftyRebase
#print axioms rayIntegral_continuous
#print axioms rayIntegral_hasFDerivAt
#print axioms rayIntegral_fderiv
#print axioms rayIntegral_differentiable
#print axioms rayIntegral_contDiff_nat
#print axioms rayIntegral_contDiff_infty
#print axioms radialTransportSolve_eq_rayIntegral
#print axioms radialTransportSolve_contDiff_infty
#print axioms laplaceBeltrami_contDiff_infty
#print axioms transportOp_preserves_contDiff_infty
#print axioms hu_infty_closed
#print axioms hw_discharged_infty
#print axioms heatParametrix_contDiff_space_infty
#print axioms witnessInner_continuous_ofInfty
#print axioms vanVleck_witnessInner_continuous_ofGeom
end AxiomChecks
