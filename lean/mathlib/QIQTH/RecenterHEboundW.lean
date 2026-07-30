/-
# RECENTER brick R6 — the ALL-BASE-POINT residual bound `hEboundW`, assembled from the
  per-base-point q-centered bound (the CULMINATING assembly of the RECENTER campaign toward `a₁=R/6`).

This file performs the FINAL R6 assembly step of the RECENTER campaign
(`docs/qg_roadmap/RECENTER_CAMPAIGN_PLAN.md`).  R5 (`RecenterCutoffC3.lean`,
`cutoffResidual_expPullback_hEboundW`) produced, for each base point, the PER-BASE-POINT q-centered
cutoff residual bound in the WIDE Gaussian `gaussDdimWide t v` (`v` = the q-centered normal
coordinate).  The reduction `RecenterReduction.hEboundW_of_uniform_perBasePoint` needs a SINGLE
constant across all base points, and the AMBIENT-difference Gaussian `gaussDdim (2τ) (p − q)`.  This
file bridges the two via three genuine, labeled, non-vacuous pieces and lands the `hEboundW` SHAPE —
exactly the single hardest carry of `TrueKernelA1.trueKernel_diagonal_a1_eq_R6`.

══════════════════════════════════════════════════════════════════════════════════════════════════════
THE THREE R6 PIECES (mapped honestly).

  1. WIDTH IDENTITY (proved, not carried): `gaussDdimWide τ v = (√2)ⁿ · gaussDdim (2τ) v`
     (`gaussDdimWide_eq_scaled_gaussDdim`).  So the R5 wide-Gaussian bound IS a `gaussDdim (2τ)`
     bound in the q-centered coordinate, up to the explicit constant `(√2)ⁿ`.

  2. UNIFORMITY-IN-q (CARRIED `hunif`): R5's per-base-point constant `B(q)` (built from `M/W/L` and
     the annulus constants) must be uniform in the base point `q`.  This is a genuine geometric fact
     — uniform on a compact region with bounded geometry — carried as an explicit hypothesis
     `hunif : ∀ q τ, 0 < τ → ∀ p, |E τ p q| ≤ B · gaussDdimWide τ (Vmap q p)` with a SINGLE `B`.  It
     is NOT vacuous: it constrains `E` by a specific Gaussian dominator; it is satisfiable because on
     a compact bounded-geometry region the per-`q` constants of R5 admit a common bound.

  3. COORDINATE-CHANGE `v ↔ p − q` (CARRIED `hcoord`): R5's bound is in the q-centered normal
     coordinate `v = Vmap q p = exp_q⁻¹(p)`; the reduction wants the ambient difference `p − q`.  Near
     the diagonal on the injectivity ball `v ≈ p − q`, so `gaussDdim (2τ) (Vmap q p) ≤ D · gaussDdim
     (2τ) (p − q)`.  This is a genuine near-diagonal metric comparison, carried as an explicit
     hypothesis `hcoord`.  NOT vacuous: it is a pointwise domination between two concrete Gaussians;
     satisfiable with `D` depending on the (bounded) geometry on the injectivity ball.

Feeding (1)+(2)+(3) into `hEboundW_of_uniform_perBasePoint` yields the width-2 target
`∀ τ p q, 0 < τ → |E τ p q| ≤ C · baseKernelW 2 0 τ p q` with `C = B · (√2)ⁿ · D`.

══════════════════════════════════════════════════════════════════════════════════════════════════════
ALSO DELIVERED — the `ContinuousOn`-on-annulus discharge of R5's `hgi_ann`/`hLapChi_ann` SHAPE.

R5 carries `hgi_ann`/`hLapChi_ann` (annulus bounds for `g̃⁻¹`/`Δ_g̃χ`) because the base-`0`
`CutoffAnnulusBounds` bricks demand GLOBAL continuity, unavailable for the locally-`ContDiffOn ℝ 2`
pullback objects.  This file supplies the fix: the compact annulus needs only LOCAL continuity ON the
annulus (`ContinuousOn`), which the pullback objects DO have wherever the annulus lies inside the
exp-ball.  `exists_bound_on_annulus_of_continuousOn` / `..._subset_of_continuousOn` /
`gi_bound_on_annulus_of_continuousOn` / `laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn`
produce the exact `hgi_ann`/`hLapChi_ann` shapes from `ContinuousOn`-on-annulus (or `ContinuousOn` on
a ball containing the annulus).  These are reusable bricks; wiring them into R5's `∀ a b`-quantified
carries additionally needs `annulus ⊆ exp-ball` for the specific radii, noted honestly.

══════════════════════════════════════════════════════════════════════════════════════════════════════
⚠ HONEST SCOPE (binding).  This lands the `hEboundW` SHAPE (the single hardest carry of
`trueKernel_diagonal_a1_eq_R6`) CONDITIONAL on the two genuine geometric residues `hunif` (uniformity)
and `hcoord` (coordinate-change), plus the `ContinuousOn`-on-annulus bricks.  It does NOT claim
`a₁ = R/6` and does NOT discharge the OTHER carries of `trueKernel_diagonal_a1_eq_R6`
(`hInt`/`hE`/`hDuhamel`/`hInter`/`hHdiag`/`hCorrHigher` + RNC data).  No `sorry`, no new axioms, no
vacuous hypotheses.
-/
import Mathlib
import QIQTH.RecenterCutoffC3
import QIQTH.RecenterReduction
import QIQTH.CutoffAnnulusBounds
import QIQTH.PullbackMetric
import QIQTH.PullbackMetricC3

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open QIQTH.FlatHeatEquation QIQTH.ResidueBound QIQTH.GaussianWidthTolerant
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. ★ THE R6 ASSEMBLY — per-base-point wide-Gaussian bound (uniform in `q`) ⟹ `hEboundW`. -/

/-- **★ R6 — THE ALL-BASE-POINT RESIDUAL BOUND `hEboundW`, from the per-base-point q-centered bound.**

    For a residual kernel `E`, a q-centered coordinate map `Vmap` (`Vmap q p = exp_q⁻¹(p)`), and
    nonneg constants `B, D`, if

      • `hunif`  : `∀ q τ, 0 < τ → ∀ p, |E τ p q| ≤ B · gaussDdimWide τ (Vmap q p)`
                   (R5's per-base-point WIDE-Gaussian bound, UNIFORM in the base point `q`), and
      • `hcoord` : `∀ q τ, 0 < τ → ∀ p, gaussDdim (2τ) (Vmap q p) ≤ D · gaussDdim (2τ) (p − q)`
                   (the near-diagonal COORDINATE-CHANGE comparison, q-centered `v` vs ambient `p − q`),

    then the GLOBAL width-2 target holds with `C = B · (√2)ⁿ · D`:

      `∀ τ p q, 0 < τ → |E τ p q| ≤ C · baseKernelW 2 0 τ p q`.

    Route: the width identity `gaussDdimWide τ v = (√2)ⁿ · gaussDdim (2τ) v`
    (`gaussDdimWide_eq_scaled_gaussDdim`) turns `hunif` into a `gaussDdim (2τ) (Vmap q p)` bound;
    `hcoord` transports it to the ambient `gaussDdim (2τ) (p − q)`; then
    `hEboundW_of_uniform_perBasePoint` repackages the resulting per-base-point family as the
    width-kernel `baseKernelW 2 0`.  This DISCHARGES the `hEboundW` SHAPE — the single hardest carry
    of `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` — conditional on the two genuine geometric residues
    `hunif`/`hcoord`.  Both are load-bearing (each is used) and non-vacuous (they dominate `E`, resp.
    compare two concrete Gaussians).  NOT `a₁ = R/6`. -/
theorem hEboundW_of_perBasePoint_bound
    (E : ℝ → Point n → Point n → ℝ) (Vmap : Point n → Point n → Point n)
    (B D : ℝ) (hB : 0 ≤ B)
    (hunif : ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
        |E τ p q| ≤ B * gaussDdimWide τ (Vmap q p))
    (hcoord : ∀ (q : Point n) (τ : ℝ), 0 < τ → ∀ p : Point n,
        gaussDdim (2 * τ) (Vmap q p) ≤ D * gaussDdim (2 * τ) (p - q)) :
    ∀ (τ : ℝ) (p q : Point n), 0 < τ →
      |E τ p q| ≤ (B * Real.sqrt 2 ^ n * D) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  -- The per-base-point AMBIENT Gaussian family with the single constant `C = B·(√2)ⁿ·D`.
  have huniform : UniformPerBasePointGaussian E (B * Real.sqrt 2 ^ n * D) := by
    intro q τ hτ p
    have hBs : (0 : ℝ) ≤ B * Real.sqrt 2 ^ n := mul_nonneg hB (by positivity)
    calc |E τ p q|
        ≤ B * gaussDdimWide τ (Vmap q p) := hunif q τ hτ p
      _ = (B * Real.sqrt 2 ^ n) * gaussDdim (2 * τ) (Vmap q p) := by
            rw [gaussDdimWide_eq_scaled_gaussDdim hτ]; ring
      _ ≤ (B * Real.sqrt 2 ^ n) * (D * gaussDdim (2 * τ) (p - q)) :=
            mul_le_mul_of_nonneg_left (hcoord q τ hτ p) hBs
      _ = (B * Real.sqrt 2 ^ n * D) * gaussDdim (2 * τ) (p - q) := by ring
  -- Repackage as the width kernel `baseKernelW 2 0` via the reduction.
  exact hEboundW_of_uniform_perBasePoint E (B * Real.sqrt 2 ^ n * D) huniform

/-! ### 2. ★ The `ContinuousOn`-on-annulus discharge of R5's `hgi_ann`/`hLapChi_ann` SHAPE. -/

/-- **Compactness → bound, from `ContinuousOn` on the annulus.**  The `ContinuousOn` analogue of
    `exists_bound_on_annulus` (`CutoffAnnulusBounds`): a function `f` that is merely `ContinuousOn` the
    COMPACT annulus `{a² ≤ rncRadialSq ≤ b²}` is bounded there.  This is the fix for the locally-`C²`
    pullback objects: GLOBAL continuity (which they lack) is not needed — LOCAL continuity on the
    compact annulus suffices (`IsCompact.exists_bound_of_continuousOn` on `annulus_isCompact`). -/
theorem exists_bound_on_annulus_of_continuousOn (f : Point n → ℝ) (a b : ℝ)
    (hf : ContinuousOn f {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2}) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |f w| ≤ K := by
  obtain ⟨C, hC⟩ := (annulus_isCompact a b).exists_bound_of_continuousOn hf
  refine ⟨max C 0, le_max_right _ _, fun w h1 h2 => ?_⟩
  have hw := hC w ⟨h1, h2⟩
  rw [Real.norm_eq_abs] at hw
  exact hw.trans (le_max_left _ _)

/-- **Compactness → bound, from `ContinuousOn` on a BALL CONTAINING the annulus.**  When the annulus
    `{a² ≤ rncRadialSq ≤ b²}` is contained in a ball `Metric.ball 0 R` on which `f` is `ContinuousOn`
    (the locally-`C²` situation of `g̃⁻¹`/`Γ̃` on the exp-ball), `f` is bounded on the annulus.  This is
    the honest resolution of R5's "global continuity not available" concern: LOCAL continuity on the
    exp-ball discharges the annulus bound for any annulus inside that ball
    (`ContinuousOn.mono` + `exists_bound_on_annulus_of_continuousOn`). -/
theorem exists_bound_on_annulus_subset_of_continuousOn (f : Point n → ℝ) (a b R : ℝ)
    (hsub : {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2}
        ⊆ Metric.ball (0 : Point n) R)
    (hf : ContinuousOn f (Metric.ball (0 : Point n) R)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |f w| ≤ K :=
  exists_bound_on_annulus_of_continuousOn f a b (hf.mono hsub)

/-- **`hgi_ann` from `ContinuousOn` on the annulus.**  The `ContinuousOn` analogue of
    `gi_bound_on_annulus`: an inverse-metric family `gi` that is `ContinuousOn` the annulus in each
    component is uniformly bounded there — exactly the shape R5's `hgi_ann` carries (at a single
    `(a,b)`).  This is what the locally-`C²` `expPullbackMetricInv` supplies on any annulus inside the
    exp-ball, replacing the base-`0` brick's demand for global continuity. -/
theorem gi_bound_on_annulus_of_continuousOn (gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hgi_cont : ∀ i j, ContinuousOn (fun w => gi w i j)
        {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2}) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |gi w i j| ≤ Kg := by
  classical
  have hbd : ∀ i j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |gi w i j| ≤ K :=
    fun i j => exists_bound_on_annulus_of_continuousOn (fun w => gi w i j) a b (hgi_cont i j)
  choose K hK0 hKbd using hbd
  refine ⟨∑ i, ∑ j, K i j, Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hK0 i j, ?_⟩
  intro w i j h1 h2
  refine (hKbd i j w h1 h2).trans ?_
  calc K i j ≤ ∑ j', K i j' :=
        Finset.single_le_sum (f := fun j' => K i j')
          (fun j' _ => hK0 i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', K i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', K i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => hK0 i' j') (Finset.mem_univ i)

/-- **`Δ_gχ` is `ContinuousOn` a set, from `ContinuousOn` metric/Christoffel data.**  The `ContinuousOn`
    analogue of `laplaceBeltrami_radialCutoff_continuous`: `Δ_gχ = ∑ᵢⱼ gⁱʲ (∂ᵢ∂ⱼχ − ∑ₖ Γᵏᵢⱼ ∂ₖχ)` is
    `ContinuousOn S` whenever `gⁱʲ` and `Γ` are (`∂ᵢ∂ⱼχ`, `∂ₖχ` are globally continuous since
    `radialCutoff a b` is `C∞`).  Lets the locally-`C²` pullback metric/Christoffel supply `Δ_g̃χ`
    continuity on any annulus inside the exp-ball. -/
theorem laplaceBeltrami_radialCutoff_continuousOn
    (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ) (S : Set (Point n))
    (hgi_cont : ∀ i j, ContinuousOn (fun w => gi w i j) S)
    (hchris_cont : ∀ k i j, ContinuousOn (fun w => christoffel g gi k i j w) S) :
    ContinuousOn (fun w => laplaceBeltrami g gi (radialCutoff a b) w) S := by
  simp only [laplaceBeltrami]
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  refine (hgi_cont i j).mul (ContinuousOn.sub ?_ ?_)
  · exact ((contDiff_pd_inf (fun y => pd (radialCutoff a b) j y)
      (contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) j) i).continuous).continuousOn
  · refine continuousOn_finsetSum _ fun k _ => ?_
    exact (hchris_cont k i j).mul
      ((contDiff_pd_inf (radialCutoff a b) (radialCutoff_contDiff a b) k).continuous).continuousOn

/-- **`hLapChi_ann` from `ContinuousOn` metric/Christoffel data on the annulus.**  The `ContinuousOn`
    analogue of `laplaceBeltrami_radialCutoff_bound_on_annulus`: `Δ_gχ` is uniformly bounded on the
    annulus given `ContinuousOn`-on-annulus metric/Christoffel data — exactly R5's `hLapChi_ann` shape
    (at a single `(a,b)`), discharged from LOCAL (not global) continuity. -/
theorem laplaceBeltrami_radialCutoff_bound_on_annulus_of_continuousOn
    (g gi : Point n → Fin n → Fin n → ℝ) (a b : ℝ)
    (hgi_cont : ∀ i j, ContinuousOn (fun w => gi w i j)
        {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2})
    (hchris_cont : ∀ k i j, ContinuousOn (fun w => christoffel g gi k i j w)
        {w : Point n | a ^ 2 ≤ rncRadialSq w ∧ rncRadialSq w ≤ b ^ 2}) :
    ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2 :=
  exists_bound_on_annulus_of_continuousOn
    (fun w => laplaceBeltrami g gi (radialCutoff a b) w) a b
    (laplaceBeltrami_radialCutoff_continuousOn g gi a b _ hgi_cont hchris_cont)

end QIQTH.HeatResidualBound
