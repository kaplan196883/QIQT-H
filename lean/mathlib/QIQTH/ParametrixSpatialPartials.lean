/-
  ParametrixSpatialPartials — J4-285: the parametrix SPATIAL-partial joint `(τ,z)`-continuities
  (the (ii) slot) and the STANDALONE ungated `heatOp = parametrixResidualN` identity (the (iii)
  slot) — the two residuals `QIQTH.ParametrixPartsContinuity` (J4-284) left open when it fully
  proved the `∂_τ`-part (i).  Together they let the concrete heatOp-witness joint continuity carry
  only genuine coefficient-regularity + geometry hypotheses.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  parametric-continuity / defining-identity brick for the Levi/boundary-continuity chain.  No `sorry`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited.

  ── CONTEXT.  J4-284 reduced the (ii) `Δ_z`-term joint continuity to the FIRST and SECOND spatial
     partials of the parametrix (`laplaceBeltrami_jointContinuousOn_of_parts` consumes `hpd1`/`hpd2`),
     and reduced (iii) — via the gate transfer — to the UNGATED identity `heatOp g gi H =
     parametrixResidualN`, which was buried inside `CoeffU1Fix`'s L4 proof (`htransport`, ~853) with
     no standalone banked lemma (per the J4-284 finding).  This file discharges both.

  ── THE PARAMETRIX FORMULA (folded).  `heatParametrix N Θ u τ z = G_τ(z)·Σ_{k≤N} w_k(z)·τᵏ`, where
     `w_k = foldedCoeff Θ u k = Θ^{−1/2}u_k` and `G_τ = gaussDdim τ`.  The banked first-partial closed
     form (`ParametrixGradientMeas.heatParametrix_pd_eq`, `τ>0`) is
       `∂ⱼH(τ,v) = (−vⱼ/(2τ)·G)·(Σ_k w_k·τᵏ) + G·(Σ_k (∂ⱼw_k)·τᵏ)`,
     using the banked Gaussian gradient `gaussDdim_pd_eq` (`∂ⱼG = (−vⱼ/2τ)G`).  Differentiating once
     more in the `i`-direction (product rule `pd_mul`, coordinate partial `pd_coord`, and the same
     Gaussian gradient) gives the SECOND-partial closed form, a finite sum of the jointly-continuous
     Gaussian times `τ>0`-regular rational factors and the (twice-)partials of the folded coefficients.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `heatParametrix_pd_jointContinuousOn` — ★ (ii-3) the FIRST spatial-partial joint `(τ,z)`-continuity
      on `{0<τ}`, from the folded-coefficient smoothness `hw` (each `w_k ∈ C^∞`).  `ContinuousOn.congr`
      onto the BANKED closed form `heatParametrix_pd_eq`.  This is EXACTLY the `hpd1` slot of
      `laplaceBeltrami_jointContinuousOn_of_parts`.

    * `heatParametrix_pd_pd_eq` — the SECOND spatial-partial CLOSED FORM at `τ>0` (product rule on the
      first-partial closed form; `pd_mul`/`pd_sum`/`pd_const_mul`/`pd_coord`/`gaussDdim_pd_eq`).

    * `heatParametrix_pd_pd_jointContinuousOn` — ★ (ii-4) the SECOND spatial-partial joint continuity on
      `{0<τ}`, carrying `hw`.  `ContinuousOn.congr` onto the closed form.  The `hpd2` slot.

    * `heatParametrix_laplaceBeltrami_jointContinuousOn` — ★ (ii) FULLY DISCHARGED.  Joint continuity of
      the `Δ_z` term on the positive-time compact, from `hw` + the geometry continuities of `gi` and the
      Christoffel symbols.  Threads (ii-3)+(ii-4) into `laplaceBeltrami_jointContinuousOn_of_parts`.

    * `heatOp_heatParametrix_eq_residual` — ★ (iii) the STANDALONE ungated identity.  For the plain
      parametrix kernel `H(s,p,·) := heatParametrix N Θ u s p`, `heatOp g gi H = parametrixResidualN`
      holds BY DEFINITION (both sides are `∂_τ H − Δ_g H`; eta on the `Δ_g` argument).  This is the
      standalone banked lemma J4-284 found missing — for the PLAIN (un-cutoff, un-transported) kernel.
      The chart-transported cutoff witness's identity stays the deeper `CoeffU1Fix.htransport` content.

    * `heatOpWitness_jointContinuousOn_final` — ★★ (COMPOSE) the concrete heatOp-witness joint continuity
      with (i) AND (iii) DISCHARGED (plain kernel), carrying only `hΘc`/`hΘne`/`huc` (the `∂_τ`-part (i))
      and `hLcont` (the `Δ_z`-part (ii)).  Threads the standalone identity into
      `ParametrixPartsContinuity.heatOpWitness_jointContinuousOn_concrete`.

    * `heatOpWitness_jointContinuousOn_geometry` — ★★ (COMPOSE, (ii) internal too).  Same, but with
      `hLcont` DISCHARGED via `heatParametrix_laplaceBeltrami_jointContinuousOn`: carries only `hΘc`/
      `hΘne`/`huc`/`hw` (coefficient regularity) and the geometry continuities of `gi`/`christoffel`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     • The plain-kernel identity (iii) is the DEFINING property of the plain parametrix; the concrete
       CUTOFF + CHART-TRANSPORTED witness's identity remains the `CoeffU1Fix.htransport` derivation
       (chart naturality + germ equalities) — NOT restated here (it is L4-local, not self-contained).
     • The carried coefficient/geometry hypotheses (`hw`, `hΘc`, `hΘne`, `huc`, `hgi`, `hChr`) are all
       genuine, satisfiable at the concrete van-Vleck witness (chart-jet smoothness banks / metric
       continuity); none is the conclusion.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParametrixPartsContinuity
import QIQTH.ParametrixGradientMeas
import QIQTH.ErrorKernelJointMeas

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.InnerKernelJointMeas QIQTH.HeatOpWitnessContinuity
open QIQTH.ParametrixGradientMeas QIQTH.ErrorKernelJointMeas QIQTH.ParametrixPartsContinuity
open QIQTH.HeatParametrixOrder
open scoped Topology ContDiff

namespace QIQTH.ParametrixSpatialPartials

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (ii-3) — the FIRST spatial-partial joint continuity.
    ############################################################################### -/

/-- **★ (ii-3) `heatParametrix_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the parametrix
    first spatial partial `p ↦ pd (heatParametrix N Θ u p.1) j p.2` on `{0<τ}`, from the folded
    coefficient smoothness `hw` (each `w_k = foldedCoeff Θ u k ∈ C^∞`).  Route: `ContinuousOn.congr`
    onto the BANKED closed form `ParametrixGradientMeas.heatParametrix_pd_eq`
      `∂ⱼH = (−vⱼ/(2τ)·G)·Σ_k w_k·τᵏ + G·Σ_k (∂ⱼw_k)·τᵏ`,
    whose factors are jointly continuous on `{0<τ}`: `−vⱼ/(2τ)` (division, `2τ≠0`), `G`
    (`gaussDdim_continuousOn_pos`), the folded sums (`hw`.continuous) and their partials
    (`contDiff_pd_inf`.continuous) times the continuous `τ`-powers.  This is EXACTLY the `hpd1` slot of
    `ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts`.  `hw` is a genuine
    coefficient-regularity fact, not the conclusion.  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (j : Fin n) (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ContinuousOn (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) j p.2)
      {q : ℝ × Point n | 0 < q.1} := by
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        (-(p.2 j) / (2 * p.1) * gaussDdim p.1 p.2)
            * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * p.1 ^ k)
          + gaussDdim p.1 p.2
            * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j p.2 * p.1 ^ k))
      {q : ℝ × Point n | 0 < q.1} := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul
      · apply ContinuousOn.mul _ gaussDdim_continuousOn_pos
        apply ContinuousOn.div
        · exact (((continuous_apply j).comp continuous_snd).neg).continuousOn
        · exact (by fun_prop : Continuous (fun p : ℝ × Point n => 2 * p.1)).continuousOn
        · intro q hq
          have hq' : (0 : ℝ) < q.1 := hq
          exact (mul_pos (by norm_num : (0 : ℝ) < 2) hq').ne'
      · apply continuousOn_finsetSum
        intro k _
        exact ((((hw k).continuous).comp continuous_snd).mul (continuous_fst.pow k)).continuousOn
    · apply ContinuousOn.mul gaussDdim_continuousOn_pos
      apply continuousOn_finsetSum
      intro k _
      exact ((((contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j).continuous).comp continuous_snd).mul
        (continuous_fst.pow k)).continuousOn
  refine hClosed.congr ?_
  intro p hp
  have hp' : (0 : ℝ) < p.1 := hp
  exact heatParametrix_pd_eq N Θ u p.1 hp' j p.2 hw

/-! ###############################################################################
    ## (ii-4) — the SECOND spatial-partial closed form + joint continuity.
    ############################################################################### -/

/-- **The SECOND spatial-partial CLOSED FORM at `τ>0`.**  Differentiating the banked first-partial
    closed form (`heatParametrix_pd_eq`, valid ∀`y`) once more in the `i`-direction (product rule
    `pd_mul`; the coordinate partial `pd_coord`; the Gaussian gradient `gaussDdim_pd_eq`; `pd_polySum_eq`
    and its `pd∘pd` analogue for the two DeWitt sums) yields
      `∂ᵢ∂ⱼH(τ,v) =
         ( (−1/(2τ)·δ⟨j,i⟩)·G + (−vⱼ/(2τ))·((−vᵢ/(2τ))·G) )·(Σ_k w_k·τᵏ)
         + (−vⱼ/(2τ)·G)·(Σ_k (∂ᵢw_k)·τᵏ)
         + (−vᵢ/(2τ)·G)·(Σ_k (∂ⱼw_k)·τᵏ)
         + G·(Σ_k (∂ᵢ∂ⱼw_k)·τᵏ)`,
    with `δ⟨j,i⟩ = if j = i then 1 else 0`.  Every factor is jointly continuous on `{0<τ}`.  Carries
    the folded smoothness `hw`.  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_pd_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (i j : Fin n) (v : Point n)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    pd (fun y => pd (heatParametrix N Θ u τ) j y) i v
      = ((-(1 : ℝ) / (2 * τ) * (if j = i then (1 : ℝ) else 0)) * gaussDdim τ v
            + (-(v j) / (2 * τ)) * ((-(v i) / (2 * τ)) * gaussDdim τ v))
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * τ ^ k)
        + (-(v j) / (2 * τ) * gaussDdim τ v)
          * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) i v * τ ^ k)
        + ((-(v i) / (2 * τ) * gaussDdim τ v)
            * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j v * τ ^ k)
          + gaussDdim τ v
            * (∑ k ∈ Finset.range (N + 1),
                pd (fun y => pd (foldedCoeff Θ u k) j y) i v * τ ^ k)) := by
  -- Rewrite the inner function via the banked first-partial closed form (valid ∀ y at τ>0).
  have hinner : (fun y => pd (heatParametrix N Θ u τ) j y)
      = (fun y =>
          (-(y j) / (2 * τ) * gaussDdim τ y)
              * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k)
            + gaussDdim τ y
              * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j y * τ ^ k)) :=
    funext (fun y => heatParametrix_pd_eq N Θ u τ hτ j y hw)
  rw [hinner]
  -- PdiffAt facts (explicit lambdas; all smooth via `hw` / `gaussDdim_contDiff`).
  have hG_pd : PdiffAt (fun z => gaussDdim τ z) i v :=
    PdiffAt_of_contDiff _ (gaussDdim_contDiff τ) i v
  have hLj_pd : PdiffAt (fun y => -(y j) / (2 * τ)) i v := by
    have hLeq : (fun y : Point n => -(y j) / (2 * τ)) = (fun y => (-(1 : ℝ) / (2 * τ)) * (y j)) := by
      funext y; ring
    rw [hLeq]
    exact (differentiableAt_const _).mul (PdiffAt_coord j i v)
  have hP_pd : PdiffAt (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k) i v :=
    PdiffAt_sum (Finset.range (N + 1)) (fun k y => foldedCoeff Θ u k y * τ ^ k) i v
      (fun k _ => (PdiffAt_of_contDiff_inf (foldedCoeff Θ u k) (hw k) i v).mul
        (differentiableAt_const _))
  have hQj_pd : PdiffAt (fun y => ∑ k ∈ Finset.range (N + 1),
      pd (foldedCoeff Θ u k) j y * τ ^ k) i v :=
    PdiffAt_sum (Finset.range (N + 1)) (fun k y => pd (foldedCoeff Θ u k) j y * τ ^ k) i v
      (fun k _ => (PdiffAt_of_contDiff_inf _ (contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j) i v).mul
        (differentiableAt_const _))
  have hM_pd : PdiffAt (fun y => -(y j) / (2 * τ) * gaussDdim τ y) i v := hLj_pd.mul hG_pd
  -- ∂ᵢ of the coordinate factor Lⱼ = −yⱼ/(2τ): `(−1/2τ)·δ⟨j,i⟩`.
  have hpdLj : pd (fun y => -(y j) / (2 * τ)) i v
      = (-(1 : ℝ) / (2 * τ)) * (if j = i then (1 : ℝ) else 0) := by
    have hLeq : (fun y : Point n => -(y j) / (2 * τ)) = (fun y => (-(1 : ℝ) / (2 * τ)) * (y j)) := by
      funext y; ring
    rw [hLeq, pd_const_mul _ _ i v (PdiffAt_coord j i v), pd_coord]
  -- ∂ᵢ of the amplitude M = Lⱼ·G (Leibniz; the Gaussian gradient `gaussDdim_pd_eq`).
  have hpdM : pd (fun y => -(y j) / (2 * τ) * gaussDdim τ y) i v
      = (-(1 : ℝ) / (2 * τ) * (if j = i then (1 : ℝ) else 0)) * gaussDdim τ v
          + (-(v j) / (2 * τ)) * ((-(v i) / (2 * τ)) * gaussDdim τ v) := by
    rw [pd_mul _ _ i v hLj_pd hG_pd, gaussDdim_pd_eq τ hτ v i, hpdLj]
  -- ∂ᵢ of the two `t`-polynomial sums (commute with the sum, factor `τᵏ`).
  have hpdP : pd (fun y => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k) i v
      = ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) i v * τ ^ k :=
    pd_polySum_eq N Θ u τ i v hw
  have hpdQj : pd (fun y => ∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j y * τ ^ k) i v
      = ∑ k ∈ Finset.range (N + 1), pd (fun y => pd (foldedCoeff Θ u k) j y) i v * τ ^ k := by
    rw [pd_sum (Finset.range (N + 1)) (fun k y => pd (foldedCoeff Θ u k) j y * τ ^ k) i v
        (fun k _ => (PdiffAt_of_contDiff_inf _ (contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j) i v).mul
          (differentiableAt_const _))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (fun y => pd (foldedCoeff Θ u k) j y * τ ^ k)
          = (fun y => τ ^ k * pd (foldedCoeff Θ u k) j y) from funext (fun y => mul_comm _ _),
      pd_const_mul (τ ^ k) (fun y => pd (foldedCoeff Θ u k) j y) i v
        (PdiffAt_of_contDiff_inf _ (contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j) i v)]
    ring
  -- ∂ᵢ of the two-summand first partial: `pd_add` then Leibniz on each product.
  have hpdA : pd (fun y => (-(y j) / (2 * τ) * gaussDdim τ y)
        * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k y * τ ^ k)) i v
      = ((-(1 : ℝ) / (2 * τ) * (if j = i then (1 : ℝ) else 0)) * gaussDdim τ v
            + (-(v j) / (2 * τ)) * ((-(v i) / (2 * τ)) * gaussDdim τ v))
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k v * τ ^ k)
        + (-(v j) / (2 * τ) * gaussDdim τ v)
          * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) i v * τ ^ k) := by
    rw [pd_mul _ _ i v hM_pd hP_pd, hpdM, hpdP]
  have hpdB : pd (fun y => gaussDdim τ y
        * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j y * τ ^ k)) i v
      = (-(v i) / (2 * τ) * gaussDdim τ v)
          * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j v * τ ^ k)
        + gaussDdim τ v
          * (∑ k ∈ Finset.range (N + 1),
              pd (fun y => pd (foldedCoeff Θ u k) j y) i v * τ ^ k) := by
    rw [pd_mul _ _ i v hG_pd hQj_pd, gaussDdim_pd_eq τ hτ v i, hpdQj]
  rw [pd_add _ _ i v (hM_pd.mul hP_pd) (hG_pd.mul hQj_pd), hpdA, hpdB]

/-- **★ (ii-4) `heatParametrix_pd_pd_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the parametrix
    second spatial partial `p ↦ pd (fun y => pd (heatParametrix N Θ u p.1) j y) i p.2` on `{0<τ}`, from
    the folded coefficient smoothness `hw`.  `ContinuousOn.congr` onto the closed form
    `heatParametrix_pd_pd_eq`; every factor is jointly continuous on `{0<τ}` (`G`, the `τ>0`-regular
    rationals, the once/twice partials of the smooth `w_k`).  This is EXACTLY the `hpd2` slot of
    `ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts`.  NOT `a₁ = R/6`. -/
theorem heatParametrix_pd_pd_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (i j : Fin n) (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k)) :
    ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (heatParametrix N Θ u p.1) j y) i p.2)
      {q : ℝ × Point n | 0 < q.1} := by
  -- continuity building blocks
  have hInvTau : ContinuousOn (fun p : ℝ × Point n => -(1 : ℝ) / (2 * p.1))
      {q : ℝ × Point n | 0 < q.1} := by
    apply ContinuousOn.div continuousOn_const
      (by fun_prop : Continuous (fun p : ℝ × Point n => 2 * p.1)).continuousOn
    intro q hq
    have hq' : (0 : ℝ) < q.1 := hq
    exact (mul_pos (by norm_num : (0 : ℝ) < 2) hq').ne'
  have hVi : ∀ l : Fin n, ContinuousOn (fun p : ℝ × Point n => -(p.2 l) / (2 * p.1))
      {q : ℝ × Point n | 0 < q.1} := by
    intro l
    apply ContinuousOn.div (((continuous_apply l).comp continuous_snd).neg).continuousOn
      (by fun_prop : Continuous (fun p : ℝ × Point n => 2 * p.1)).continuousOn
    intro q hq
    have hq' : (0 : ℝ) < q.1 := hq
    exact (mul_pos (by norm_num : (0 : ℝ) < 2) hq').ne'
  have hPsum : ContinuousOn
      (fun p : ℝ × Point n => ∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * p.1 ^ k)
      {q : ℝ × Point n | 0 < q.1} :=
    continuousOn_finsetSum _ (fun k _ =>
      ((((hw k).continuous).comp continuous_snd).mul (continuous_fst.pow k)).continuousOn)
  -- the smooth partial-of-partial factors (each continuous via `contDiff_pd_inf` twice)
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        ((-(1 : ℝ) / (2 * p.1) * (if j = i then (1 : ℝ) else 0)) * gaussDdim p.1 p.2
            + (-(p.2 j) / (2 * p.1)) * ((-(p.2 i) / (2 * p.1)) * gaussDdim p.1 p.2))
          * (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k p.2 * p.1 ^ k)
        + (-(p.2 j) / (2 * p.1) * gaussDdim p.1 p.2)
          * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) i p.2 * p.1 ^ k)
        + ((-(p.2 i) / (2 * p.1) * gaussDdim p.1 p.2)
            * (∑ k ∈ Finset.range (N + 1), pd (foldedCoeff Θ u k) j p.2 * p.1 ^ k)
          + gaussDdim p.1 p.2
            * (∑ k ∈ Finset.range (N + 1),
                pd (fun y => pd (foldedCoeff Θ u k) j y) i p.2 * p.1 ^ k)))
      {q : ℝ × Point n | 0 < q.1} := by
    refine ((ContinuousOn.mul ?_ hPsum).add ?_).add ?_
    · -- the amplitude bracket
      refine ((hInvTau.mul continuousOn_const).mul gaussDdim_continuousOn_pos).add
        ((hVi j).mul ((hVi i).mul gaussDdim_continuousOn_pos))
    · exact ((hVi j).mul gaussDdim_continuousOn_pos).mul
        (continuousOn_finsetSum _ (fun k _ =>
          ((((contDiff_pd_inf (foldedCoeff Θ u k) (hw k) i).continuous).comp continuous_snd).mul
            (continuous_fst.pow k)).continuousOn))
    · refine (((hVi i).mul gaussDdim_continuousOn_pos).mul
        (continuousOn_finsetSum _ (fun k _ =>
          ((((contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j).continuous).comp continuous_snd).mul
            (continuous_fst.pow k)).continuousOn))).add
        (gaussDdim_continuousOn_pos.mul
          (continuousOn_finsetSum _ (fun k _ =>
            (((contDiff_pd_inf _ (contDiff_pd_inf (foldedCoeff Θ u k) (hw k) j) i).continuous.comp
              continuous_snd).mul (continuous_fst.pow k)).continuousOn)))
  refine hClosed.congr ?_
  intro p hp
  have hp' : (0 : ℝ) < p.1 := hp
  exact heatParametrix_pd_pd_eq N Θ u p.1 hp' i j p.2 hw

/-! ###############################################################################
    ## (ii) — the `Δ_z` term joint continuity, FULLY DISCHARGED from `hw` + geometry.
    ############################################################################### -/

/-- **★ (ii) `heatParametrix_laplaceBeltrami_jointContinuousOn` — FULLY DISCHARGED.**  Joint
    `(τ,z)`-continuity of the parametrix `Δ_z` term on the positive-time compact
    `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`), from the folded coefficient smoothness `hw` and the
    geometry continuities of `gi` and the Christoffel symbols.  Threads the FIRST (ii-3) and SECOND
    (ii-4) spatial-partial joint continuities (restricted to the compact, which sits inside `{0<τ}`)
    into `ParametrixPartsContinuity.laplaceBeltrami_jointContinuousOn_of_parts`.  Carried inputs are
    genuine regularity facts; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatParametrix_laplaceBeltrami_jointContinuousOn
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hsub : (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      ⊆ {q : ℝ × Point n | 0 < q.1} := by
    intro q hq
    exact lt_of_lt_of_le ht₁ hq.1.1
  exact laplaceBeltrami_jointContinuousOn_of_parts N g gi Θ u
    (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) hgi hChr
    (fun k => (heatParametrix_pd_jointContinuousOn N Θ u k hw).mono hsub)
    (fun i j => (heatParametrix_pd_pd_jointContinuousOn N Θ u i j hw).mono hsub)

/-! ###############################################################################
    ## (iii) — the STANDALONE ungated `heatOp = parametrixResidualN` identity.
    ############################################################################### -/

/-- **★ (iii) `heatOp_heatParametrix_eq_residual` — the STANDALONE ungated identity.**  For the plain
    parametrix kernel `H(s,p,q) := heatParametrix N Θ u s p` (ignoring the base point `q`), the spatial
    heat operator equals the parametrix residual BY DEFINITION:
      `heatOp g gi H t x y = ∂_t H − Δ_g H = parametrixResidualN N g gi Θ u t x`.
    Both sides unfold to `deriv (fun s => heatParametrix N Θ u s x) t − laplaceBeltrami g gi
    (heatParametrix N Θ u t) x` (eta on the `Δ_g` argument).  This is the standalone banked lemma J4-284
    reported missing — for the PLAIN (un-cutoff, un-transported) kernel; the chart-transported cutoff
    witness's identity stays the deeper `CoeffU1Fix.htransport` content.  NOT `a₁ = R/6`. -/
theorem heatOp_heatParametrix_eq_residual (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (x y : Point n) :
    heatOp g gi (fun s p _ => heatParametrix N Θ u s p) t x y
      = parametrixResidualN N g gi Θ u t x := by
  simp only [heatOp, parametrixResidualN]

/-! ###############################################################################
    ## (COMPOSE) — the concrete heatOp-witness joint continuity, (i)+(iii) discharged.
    ############################################################################### -/

/-- **★★ (COMPOSE) `heatOpWitness_jointContinuousOn_final`.**  The concrete (R-base) heatOp-witness
    joint continuity on the positive-time compact for the PLAIN parametrix kernel, with the `∂_τ`-part
    (i) AND the ungated identity (iii) DISCHARGED.  Threads the standalone identity
    `heatOp_heatParametrix_eq_residual` as `hIdent` into
    `ParametrixPartsContinuity.heatOpWitness_jointContinuousOn_concrete`, carrying only `hΘc`/`hΘne`/
    `huc` (the (i) coefficient regularity) and `hLcont` (the (ii) `Δ_z`-term joint continuity).  None of
    the carried hypotheses is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_jointContinuousOn_final
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => heatOp g gi (fun s p _ => heatParametrix N Θ u s p) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  heatOpWitness_jointContinuousOn_concrete N g gi Θ u
    (fun s p _ => heatParametrix N Θ u s p) t₁ t₂ R ht₁ hΘc hΘne huc hLcont
    (fun p _ => heatOp_heatParametrix_eq_residual N g gi Θ u p.1 p.2 0)

/-- **★★ (COMPOSE, (ii) internal) `heatOpWitness_jointContinuousOn_geometry`.**  Same as
    `heatOpWitness_jointContinuousOn_final` but with `hLcont` also DISCHARGED via
    `heatParametrix_laplaceBeltrami_jointContinuousOn`: the concrete heatOp-witness joint continuity
    for the PLAIN parametrix kernel carrying ONLY the coefficient regularity
    (`hΘc`/`hΘne`/`huc`/`hw`) and the geometry continuities of `gi`/`christoffel` — every parametric
    ingredient of the Levi/boundary-continuity witness is now a genuine, satisfiable regularity input.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_jointContinuousOn_geometry
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hw : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n => heatOp g gi (fun s p _ => heatParametrix N Θ u s p) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
  heatOpWitness_jointContinuousOn_final N g gi Θ u t₁ t₂ R ht₁ hΘc hΘne huc
    (heatParametrix_laplaceBeltrami_jointContinuousOn N g gi Θ u t₁ t₂ R ht₁ hw hgi hChr)

#check @heatParametrix_pd_jointContinuousOn
#check @heatParametrix_pd_pd_eq
#check @heatParametrix_pd_pd_jointContinuousOn
#check @heatParametrix_laplaceBeltrami_jointContinuousOn
#check @heatOp_heatParametrix_eq_residual
#check @heatOpWitness_jointContinuousOn_final
#check @heatOpWitness_jointContinuousOn_geometry

end QIQTH.ParametrixSpatialPartials

/-! ## Axiom checks — every theorem `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ParametrixSpatialPartials
#print axioms heatParametrix_pd_jointContinuousOn
#print axioms heatParametrix_pd_pd_eq
#print axioms heatParametrix_pd_pd_jointContinuousOn
#print axioms heatParametrix_laplaceBeltrami_jointContinuousOn
#print axioms heatOp_heatParametrix_eq_residual
#print axioms heatOpWitness_jointContinuousOn_final
#print axioms heatOpWitness_jointContinuousOn_geometry
end AxiomChecks
