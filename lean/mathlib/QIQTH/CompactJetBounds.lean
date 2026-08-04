/-
  CompactJetBounds — J4-190 (Sol hEgrad plan, step (i)): the FINITE JET PACK of uniform sup-bounds
  on the geometric coefficient fields over a compact ball, and the honest `τ²`-weighted amplitude
  bound that the coming Gaussian-absorption step of the `∇E` (`hEgrad`) tail consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is ONE
  brick of the `a₁ = R/6` heat-kernel campaign: Sol's step (i) "finite jet pack on the relevant
  compact set" — collect UNIFORM sup-bounds for the metric / inverse-metric / Christoffel / folded
  DeWitt transport coefficients and their needed first jets, over the cutoff-support closure
  `closedBall 0 b`, and repackage the Laurent-in-`τ` residual amplitude `residualCoeffA` (from
  `ErrorKernelFactorization`) into its honest `τ²`-weighted bounded form.  No new heat-kernel content,
  no `sorry`, no new axioms, no vacuous/unsatisfiable hypotheses, no conclusion-in-disguise.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## Why this shape (the J4-188 τ-structure finding).

  `ErrorKernelJointMeas` / `ErrorKernelFactorization` record the HONEST fact that `residualCoeffA`
  is a genuine Laurent polynomial in `τ` with a `1/τ` and `1/τ²` head: as `τ↓0` the amplitude BLOWS
  UP, so `A` is NOT bounded across `τ = 0`.  The honest bounded forms are therefore the `τ`-weighted
  one — the `τ²`-CLEARED amplitude `τ²·A` is a genuine polynomial in `τ` whose coefficients are
  BOUNDED fields on the ball — exactly what this file delivers.  This mirrors the banked zeroth-order
  envelope: `RestrictedEboundW.hEboundW_le` bounds the residual by `C·baseKernelW 2 0 τ`, i.e. the
  Gaussian `G_τ` tames the `1/τ²·A` combination `E = G_τ·A`.  Here we supply the amplitude side of
  that product in bounded-coefficient form.

  ## What this file delivers (ns `QIQTH.CompactJetBounds`).

    * (1) `exists_bound_closedBall` — THE GENERIC COMPACT-BOUND LEVER.  Any continuous scalar field on
      `Point n` has a NON-NEGATIVE uniform sup-bound over `closedBall 0 b`
      (`IsCompact.exists_bound_of_continuousOn` + `max _ 0`).  `exists_bound_closedBall_family` is the
      simultaneous form for a finite index family (one `C` uniform over the family).

    * (2) `JetBoundPack` — THE PROP JET PACK.  A pure-`Prop` bundle of `∃`-sup-bounds over
      `closedBall 0 b` for every coefficient field the `∇E` amplitude needs: `gⁱʲ`, `Γᵏᵢⱼ`, the folded
      DeWitt coefficients `w_k`, their radial derivatives `r∂_r w_k`, their Laplace–Beltramis `Δ_g w_k`,
      and their first partials `∂ⱼ w_k` (the poly-gradient ingredients) — each field carrying its OWN
      non-negative constant (cleaner than one global `C`).

    * (3) `jetBoundPack_from_geometry` — THE BUILDER.  From the standard `C^∞` carries of the metric
      pair `(g, gi)` and the folded coefficients `w_k`, every pack field is discharged mechanically:
      each is continuous (`christoffel_contDiff` / `laplaceBeltrami_contDiff` / `continuous_pd` /
      the radial-sum), so the compact-bound lever applies.

    * (4a) `pd_poly_eq_sum` — the PARAMETRIX-POLYNOMIAL GRADIENT REDUCTION.  The field-gradient of the
      time-polynomial `∂ⱼ(Σ_k w_k·τ^k) = Σ_k (∂ⱼ w_k)·τ^k` (`pd_sum` + `pd_const_mul`), turning the
      genuine poly-gradient carry into the per-`k` first partials the pack already bounds.

    * (4b) `residualCoeffA_tau_weighted_bound` — ★ THE HONEST `τ²`-WEIGHTED AMPLITUDE BOUND.  On
      `(0,T] × closedBall 0 b`, `τ²·|residualCoeffA N g gi Θ u τ v| ≤ C` for a NON-NEGATIVE constant
      `C` assembled from the pack constants, `N`, `T`, `b`.  This is the `τ`-cleared bounded form of
      the Laurent amplitude — the honest object composing with the Gaussian-absorption step.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  Diagonal-chart amplitude, single base point.  The pack carries only the
  EXISTENCE of the sup-bounds (uniform-over-base-point constants are the recognized J3 residue, not
  claimed here).  NOT the `∇E` bound itself (that mixed-third-jet Gaussian-moment estimate is the
  downstream multi-brick layer); this file supplies its AMPLITUDE input.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ErrorKernelFactorization
import QIQTH.TransportOpSmoothness
import QIQTH.RadialTransport
import QIQTH.ChristoffelSmooth

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.TransportOpSmoothness QIQTH.RadialTransport
open QIQTH.ErrorKernelFactorization
open scoped BigOperators ContDiff

namespace QIQTH.CompactJetBounds

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ## 1.  The generic compact-bound lever. -/

/-- **(1) THE COMPACT-BOUND LEVER.**  A continuous scalar field on `Point n` admits a NON-NEGATIVE
    uniform sup-bound over the closed ball `closedBall 0 b`.  Direct from Mathlib's
    `IsCompact.exists_bound_of_continuousOn` (the ball is compact — `Point n = Fin n → ℝ` is a proper
    space), the `‖·‖ = |·|` identification on `ℝ`, and `max _ 0` for non-negativity. -/
theorem exists_bound_closedBall {f : Point n → ℝ} (b : ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Metric.closedBall (0 : Point n) b, |f v| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Point n) b).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun v hv => ?_⟩
  have h := hC v hv
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **(1′) THE SIMULTANEOUS FAMILY FORM.**  A finite family of continuous fields admits ONE
    non-negative sup-bound uniform over the whole family.  Iterated `exists_bound_closedBall` + `max`
    (`Finset.induction`); ergonomic when a single constant over an index set is wanted. -/
theorem exists_bound_closedBall_family {ι : Type*} (s : Finset ι) (F : ι → Point n → ℝ) (b : ℝ)
    (hF : ∀ i ∈ s, Continuous (F i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ v ∈ Metric.closedBall (0 : Point n) b, |F i v| ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | insert a s ha ih =>
      obtain ⟨Ca, hCa0, hCa⟩ := exists_bound_closedBall b (hF a (Finset.mem_insert_self a s))
      obtain ⟨Cs, hCs0, hCs⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      refine ⟨max Ca Cs, le_max_of_le_left hCa0, fun i hi v hv => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact le_trans (hCa v hv) (le_max_left _ _)
      · exact le_trans (hCs i hi' v hv) (le_max_right _ _)

/-! ## 2.  The Prop jet pack. -/

/-- **(2) THE JET BOUND PACK.**  A pure-`Prop` bundle of uniform sup-bounds over `closedBall 0 b` for
    every coefficient field the `∇E` amplitude `residualCoeffA` is built from.  Each field carries its
    own non-negative constant (the ergonomic per-field form; a single global `C` is recoverable via
    the family lever).  Satisfiable by the geometry builder below from the standard `C^∞` carries. -/
structure JetBoundPack (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (b : ℝ) : Prop where
  /-- Inverse-metric components. -/
  gi_bnd : ∀ i j, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |gi v i j| ≤ C
  /-- Christoffel symbols. -/
  chr_bnd : ∀ k i j, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |christoffel g gi k i j v| ≤ C
  /-- Folded DeWitt coefficients `w_k`. -/
  fold_bnd : ∀ k, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |foldedCoeff Θ u k v| ≤ C
  /-- Radial derivatives `r∂_r w_k`. -/
  rad_bnd : ∀ k, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |radialDeriv (foldedCoeff Θ u k) v| ≤ C
  /-- Laplace–Beltramis `Δ_g w_k`. -/
  lap_bnd : ∀ k, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |laplaceBeltrami g gi (foldedCoeff Θ u k) v| ≤ C
  /-- First partials `∂ⱼ w_k` (the poly-gradient ingredients). -/
  pd_bnd : ∀ k j, ∃ C : ℝ, 0 ≤ C ∧
    ∀ v ∈ Metric.closedBall (0 : Point n) b, |pd (foldedCoeff Θ u k) j v| ≤ C

/-! ## 3.  The builder from the standard geometric `C^∞` carries. -/

/-- **(3) THE BUILDER.**  From the standard `C^∞` carries of the metric pair `(g, gi)` and the folded
    coefficients `w_k`, the whole `JetBoundPack` is discharged: every field is continuous
    (`christoffel_contDiff`, `laplaceBeltrami_contDiff`, `continuous_pd`, and the radial-derivative
    coordinate sum), so the compact-bound lever `exists_bound_closedBall` applies field by field. -/
theorem jetBoundPack_from_geometry (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (b : ℝ)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    JetBoundPack g gi Θ u b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact exists_bound_closedBall b (hgi i j).continuous
  · intro k i j
    exact exists_bound_closedBall b (christoffel_contDiff g gi hg hgi k i j).continuous
  · intro k
    exact exists_bound_closedBall b (hw k).continuous
  · intro k
    have hcont : Continuous (fun v : Point n => radialDeriv (foldedCoeff Θ u k) v) := by
      simp only [radialDeriv]
      exact continuous_finsetSum Finset.univ
        (fun i _ => (continuous_apply i).mul (continuous_pd (foldedCoeff Θ u k) (hw k) i))
    exact exists_bound_closedBall b hcont
  · intro k
    exact exists_bound_closedBall b
      (laplaceBeltrami_contDiff g gi hg hgi (foldedCoeff Θ u k) (hw k)).continuous
  · intro k j
    exact exists_bound_closedBall b (continuous_pd (foldedCoeff Θ u k) (hw k) j)

/-! ## 4a.  The parametrix-polynomial gradient reduction. -/

/-- **(4a) THE POLY-GRADIENT REDUCTION.**  The field-gradient of the time-polynomial commutes with the
    finite sum and pulls the `τ`-power constants out:
      `∂ⱼ(Σ_{k≤N} w_k·τ^k)(v) = Σ_{k≤N} (∂ⱼ w_k)(v)·τ^k`.
    Direct from `pd_sum` + `pd_const_mul` (each `w_k` is `C^∞`, hence `PdiffAt`).  This turns the
    genuine poly-gradient carry into the per-`k` first partials the pack bounds via `pd_bnd`. -/
theorem pd_poly_eq_sum (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (j : Fin n) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
      = ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j v * t ^ k := by
  have hpc : ∀ k, (fun y => foldedCoeff Θ u k y * t ^ k) = fun y => t ^ k * foldedCoeff Θ u k y :=
    fun k => funext (fun y => by ring)
  have hpdiff : ∀ k ∈ Finset.range (N + 1),
      PdiffAt (fun y => foldedCoeff Θ u k y * t ^ k) j v := by
    intro k _
    rw [hpc k]
    exact PdiffAt_of_contDiff _ ((contDiff_const (c := t ^ k)).mul (hw k)) j v
  rw [pd_sum (Finset.range (N + 1)) (fun k y => foldedCoeff Θ u k y * t ^ k) j v hpdiff]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hpc k, pd_const_mul (t ^ k) (foldedCoeff Θ u k) j v
      (PdiffAt_of_contDiff _ (hw k) j v)]
  ring

/-! ## 4b.  The honest `τ²`-weighted amplitude bound. -/

/-- **The `τ²`-CLEARED amplitude** — `τ²·residualCoeffA` with the `1/τ` / `1/τ²` poles algebraically
    removed.  Each `1/τ`-headed piece of `residualCoeffA` is multiplied through by `τ²`, turning the
    Laurent amplitude into a genuine polynomial in `τ` whose coefficient fields are bounded on the
    ball.  Equal to `τ²·residualCoeffA` for `τ ≠ 0` (`residualCoeffAWeighted_eq`) and JOINTLY
    CONTINUOUS in `(τ,v)` (no pole at `τ = 0`), so bounded on any compact box. -/
noncomputable def residualCoeffAWeighted (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (v : Point n) : ℝ :=
  (t * ((1 / 2) * (∑ i, (gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
      + ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))))
      * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * t ^ k)
    + t ^ 2 * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * ((k : ℝ) * t ^ (k - 1)))
    + (t * radialDeriv (foldedCoeff Θ u 0) v
        + t ^ 2 * ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) v * t ^ k)
    - t ^ 2 * (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) v * t ^ k)
    - t
        * ((-1 / 2) * ∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) j v
                + v j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * t ^ k) i v))

/-- **The pole-clearing identity** `τ²·residualCoeffA = residualCoeffAWeighted` for `τ ≠ 0`.  Pure
    field arithmetic (`field_simp`): every `1/τ` / `1/τ²` head cancels against the `τ²` weight; the
    Finset-sum fields are opaque atoms untouched by the clearing. -/
theorem residualCoeffAWeighted_eq (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (t : ℝ) (ht : t ≠ 0) (v : Point n) :
    t ^ 2 * residualCoeffA N g gi Θ u t v = residualCoeffAWeighted N g gi Θ u t v := by
  simp only [residualCoeffA, residualCoeffAWeighted]
  field_simp

/-- **Joint continuity of the `τ²`-cleared amplitude.**  `(τ,v) ↦ residualCoeffAWeighted` is jointly
    continuous — the `τ²`-weighting has removed every pole, so it is a genuine polynomial in `τ` with
    continuous coefficient fields.  The proof is the continuity analogue of the measurable-algebra
    reduction `residualCoeffA_measurable_of_factors`: every factor field is continuous
    (`christoffel_contDiff` / `laplaceBeltrami_contDiff` / `continuous_pd` / the radial sum), the
    poly-gradient is reduced by `pd_poly_eq_sum`, and `Continuous.{add,sub,mul}` / `continuous_finsetSum`
    assemble the whole. -/
theorem residualCoeffAWeighted_continuous (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    Continuous (fun p : ℝ × Point n => residualCoeffAWeighted N g gi Θ u p.1 p.2) := by
  -- factor-field continuities as functions of `(τ,v)`.
  have mv : ∀ i, Continuous (fun p : ℝ × Point n => p.2 i) :=
    fun i => (continuous_apply i).comp continuous_snd
  have mt : Continuous (fun p : ℝ × Point n => p.1) := continuous_fst
  have mtk : ∀ k : ℕ, Continuous (fun p : ℝ × Point n => p.1 ^ k) :=
    fun k => continuous_fst.pow k
  have mgi : ∀ i j, Continuous (fun p : ℝ × Point n => gi p.2 i j) :=
    fun i j => ((hgi i j).continuous).comp continuous_snd
  have mchr : ∀ k i j, Continuous (fun p : ℝ × Point n => christoffel g gi k i j p.2) :=
    fun k i j => (christoffel_contDiff g gi hg hgi k i j).continuous.comp continuous_snd
  have mw : ∀ k, Continuous (fun p : ℝ × Point n => foldedCoeff Θ u k p.2) :=
    fun k => (hw k).continuous.comp continuous_snd
  have hradv : ∀ k, Continuous (fun v : Point n => radialDeriv (foldedCoeff Θ u k) v) := by
    intro k
    simp only [radialDeriv]
    exact continuous_finsetSum Finset.univ
      (fun i _ => (continuous_apply i).mul (continuous_pd (foldedCoeff Θ u k) (hw k) i))
  have mrad : ∀ k, Continuous (fun p : ℝ × Point n => radialDeriv (foldedCoeff Θ u k) p.2) :=
    fun k => (hradv k).comp continuous_snd
  have mlap : ∀ k, Continuous (fun p : ℝ × Point n => laplaceBeltrami g gi (foldedCoeff Θ u k) p.2) :=
    fun k => (laplaceBeltrami_contDiff g gi hg hgi (foldedCoeff Θ u k) (hw k)).continuous.comp
      continuous_snd
  have mpd : ∀ k j, Continuous (fun p : ℝ × Point n => pd (foldedCoeff Θ u k) j p.2) :=
    fun k j => (continuous_pd (foldedCoeff Θ u k) (hw k) j).comp continuous_snd
  have hpdP : ∀ j, Continuous (fun p : ℝ × Point n =>
      pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2) := by
    intro j
    have heq : (fun p : ℝ × Point n =>
        pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2)
        = (fun p : ℝ × Point n =>
            ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j p.2 * p.1 ^ k) := by
      funext p; exact pd_poly_eq_sum N Θ u p.1 j p.2 hw
    rw [heq]
    exact continuous_finsetSum _ (fun k _ => (mpd k j).mul (mtk k))
  simp only [residualCoeffAWeighted]
  -- the metric-deviation brackets and the folded polynomials.
  have hb1e : Continuous (fun p : ℝ × Point n =>
      (1 / 2 : ℝ) * (∑ i, (gi p.2 i i - 1))
        - (1 / 2 : ℝ) * (∑ i, ∑ j, ∑ k, gi p.2 i j * christoffel g gi k i j p.2 * p.2 k)) :=
    ((continuous_finsetSum _ (fun i _ => (mgi i i).sub continuous_const)).const_mul _).sub
      ((continuous_finsetSum _ (fun i _ =>
        continuous_finsetSum _ (fun j _ =>
          continuous_finsetSum _ (fun k _ =>
            ((mgi i j).mul (mchr k i j)).mul (mv k))))).const_mul _)
  have hb2e : Continuous (fun p : ℝ × Point n =>
      (-1 / 4 : ℝ) * (∑ i, ∑ j, (gi p.2 i j - (if i = j then (1 : ℝ) else 0)) * (p.2 i * p.2 j))) :=
    (continuous_finsetSum _ (fun i _ =>
      continuous_finsetSum _ (fun j _ =>
        ((mgi i j).sub continuous_const).mul ((mv i).mul (mv j))))).const_mul _
  have hP : Continuous (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * p.1 ^ k) :=
    continuous_finsetSum _ (fun k _ => (mw k).mul (mtk k))
  have hS2 : Continuous (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * ((k : ℝ) * p.1 ^ (k - 1))) :=
    continuous_finsetSum _ (fun k _ => (mw k).mul (continuous_const.mul (mtk (k - 1))))
  have hRtail : Continuous (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range N, radialDeriv (foldedCoeff Θ u (k + 1)) p.2 * p.1 ^ k) :=
    continuous_finsetSum _ (fun k _ => (mrad (k + 1)).mul (mtk k))
  have hLap : Continuous (fun p : ℝ × Point n =>
      ∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) p.2 * p.1 ^ k) :=
    continuous_finsetSum _ (fun k _ => (mlap k).mul (mtk k))
  have hdevP : Continuous (fun p : ℝ × Point n =>
      (-1 / 2 : ℝ) * ∑ i, ∑ j, (gi p.2 i j - (if i = j then (1 : ℝ) else 0))
          * (p.2 i * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) j p.2
              + p.2 j * pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * p.1 ^ k) i p.2)) :=
    (continuous_finsetSum _ (fun i _ =>
      continuous_finsetSum _ (fun j _ =>
        ((mgi i j).sub continuous_const).mul
          (((mv i).mul (hpdP j)).add ((mv j).mul (hpdP i)))))).const_mul _
  -- assemble the five weighted pieces.
  exact ((((((mt.mul hb1e).add hb2e).mul hP).add ((mtk 2).mul hS2)).add
    ((mt.mul (mrad 0)).add ((mtk 2).mul hRtail))).sub ((mtk 2).mul hLap)).sub (mt.mul hdevP)

/-- **★ (4b) THE HONEST `τ²`-WEIGHTED AMPLITUDE BOUND.**  On the box `(0,T] × closedBall 0 b`, the
    `τ²`-weighted Laurent amplitude is bounded by a NON-NEGATIVE constant:
      `τ² · |residualCoeffA N g gi Θ u τ v| ≤ C`   for all `0 < τ ≤ T`, `v ∈ closedBall 0 b`.
    This is the honest bounded form of the pole-carrying amplitude `A` (which BLOWS UP as `τ↓0`): the
    `τ²`-cleared amplitude `residualCoeffAWeighted` is jointly continuous, hence bounded on the compact
    box `Icc 0 T ×ˢ closedBall 0 b` (the compact-bound lever), and equals `τ²·A` for `τ ≠ 0`.  The
    constant is assembled from the geometry via compactness — the amplitude input the coming
    Gaussian-absorption (`G_τ·A`) step of the `∇E` tail consumes.  NOT `a₁ = R/6`. -/
theorem residualCoeffA_tau_weighted_bound (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (T b : ℝ)
    (hg : ∀ a c, ContDiff ℝ ⊤ (fun y => g y a c))
    (hgi : ∀ a c, ContDiff ℝ ⊤ (fun y => gi y a c))
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (v : Point n), 0 < t → t ≤ T →
      v ∈ Metric.closedBall (0 : Point n) b →
      t ^ 2 * |residualCoeffA N g gi Θ u t v| ≤ C := by
  have hKcpt : IsCompact (Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) b) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) b)
  obtain ⟨C, hC⟩ := hKcpt.exists_bound_of_continuousOn
    (residualCoeffAWeighted_continuous N g gi Θ u hg hgi hw).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v ht htT hv => ?_⟩
  have hmem : (t, v) ∈ Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Point n) b :=
    ⟨⟨ht.le, htT⟩, hv⟩
  have hbnd := hC (t, v) hmem
  rw [Real.norm_eq_abs] at hbnd
  have hid : t ^ 2 * |residualCoeffA N g gi Θ u t v|
      = |residualCoeffAWeighted N g gi Θ u t v| := by
    rw [← residualCoeffAWeighted_eq N g gi Θ u t (ne_of_gt ht) v, abs_mul,
      abs_of_nonneg (sq_nonneg t)]
  rw [hid]
  exact le_trans hbnd (le_max_left _ _)

/-! ## Axiom checks — every main result is `std-3` (propext, Classical.choice, Quot.sound). -/

section AxiomChecks

#print axioms exists_bound_closedBall
#print axioms exists_bound_closedBall_family
#print axioms jetBoundPack_from_geometry
#print axioms pd_poly_eq_sum
#print axioms residualCoeffAWeighted_eq
#print axioms residualCoeffAWeighted_continuous
#print axioms residualCoeffA_tau_weighted_bound

end AxiomChecks

end QIQTH.CompactJetBounds
