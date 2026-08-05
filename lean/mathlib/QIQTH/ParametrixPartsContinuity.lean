/-
  ParametrixPartsContinuity — J4-284: the parametrix `∂_τ`-part JOINT `(τ,z)`-continuity (FULLY
  proven), the `Δ_z`-part joint-continuity REDUCTION brick, and the gate-transfer identity brick —
  discharging the (i) slot of `QIQTH.HeatOpWitnessContinuity.parametrixResidualN_jointContinuousOn_of_parts`
  (J4-283) and honestly reducing (ii)/(iii).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  parametric-continuity (regularity) brick for the Levi/boundary-continuity chain.  No `sorry` (header
  prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis
  equal to (or trivially yielding) the conclusion, no existing file edited.

  ── CONTEXT.  J4-283 (`HeatOpWitnessContinuity`) reduced the concrete (R-base) heatOp-witness joint
     continuity to three genuine ingredients:
       (i)   joint `(τ,z)`-continuity of the `∂_τ` term `p ↦ deriv (fun s => heatParametrix N Θ u s p.2) p.1`;
       (ii)  joint `(τ,z)`-continuity of the `Δ_z` term `p ↦ laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2`;
       (iii) the gate-local identity `heatOp g gi Wit = parametrixResidualN`-shaped `F` on the compact.
     `parametrixResidualN_jointContinuousOn_of_parts` consumes (i)+(ii) as `hDcont`/`hLcont`;
     `heatOpWitness_jointContinuousOn_of_identity` consumes (iii) as `hIdent`.

  ── THE PARAMETRIX FORMULA.  `heatParametrix N Θ u s z = gaussDdim s z · (Θ z)^{−1/2} · Σ_{k≤N} u_k(z)·s^k`.
     Its `s`-derivative is EXPLICIT: `(Θ z)^{−1/2}` is an `s`-constant, so the product rule gives
       `∂_s H_N(s,z)|_{s=τ} = (Θ z)^{−1/2}·( (∂_s gaussDdim)(τ,z)·Σ u_k z τ^k  +  gaussDdim τ z·Σ u_k z·(k τ^{k−1}) )`.
     And the Gaussian's `τ`-derivative has the CLOSED FORM (`FlatHeatEquation.gaussDdim_heat_eqn` +
     `gaussDdim_pd_pd_i`):  `∂_s gaussDdim(τ,z) = Σ_i ((z_i)²/(4τ²) − 1/(2τ))·gaussDdim τ z`, a finite
     sum of the banked-jointly-continuous Gaussian times rational functions of `τ` (regular for `τ>0`).

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `gaussDdim_deriv_t_eq` — the Gaussian `τ`-derivative CLOSED FORM at `τ>0`
      (`FlatHeatEquation.gaussDdim_heat_eqn` + `gaussDdim_pd_pd_i`, one `sum_congr`).

    * `gaussDdim_deriv_t_jointContinuousOn` — ★ joint `(τ,z)`-continuity of `p ↦ deriv (fun s =>
      gaussDdim s p.2) p.1` on `{0<τ}`, via `ContinuousOn.congr` onto the closed form (banked
      `gaussDdim_continuousOn_pos` × the `τ>0`-regular rational scalar).

    * `heatParametrix_deriv_t_eq` — the FULL parametrix `τ`-derivative CLOSED FORM at `τ>0` (product/
      sum rule: `HasDerivAt`-built by hand, `.deriv`).

    * `heatParametrix_deriv_jointContinuousOn` — ★★ (i) FULLY PROVEN.  Joint `(τ,z)`-continuity of
      `p ↦ deriv (fun s => heatParametrix N Θ u s p.2) p.1` on `{0<τ}`, from `Θ` continuous /
      non-vanishing (the `Θ^{−1/2}` factor) and each `u_k` continuous.  `ContinuousOn.congr` onto the
      closed form.  This is EXACTLY the `hDcont` slot of `parametrixResidualN_jointContinuousOn_of_parts`.

    * `laplaceBeltrami_jointContinuousOn_of_parts` — ★ (ii) the honest REDUCTION brick.  Joint
      continuity of `p ↦ laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2` from the joint continuity
      of `gi`, `christoffel`, and the FIRST and SECOND spatial partials of the parametrix.  Route:
      unfold `laplaceBeltrami`; `continuousOn_finsetSum`/`.mul`/`.sub`.  This decomposes (ii) into the
      partial-continuities — the genuine remaining analytic work (the second-partial formula involves
      `∂²Θ^{−1/2}`, `∂²u_k`, needing `Θ,u ∈ C²` with continuous second derivatives — a separate brick).

    * `hIdent_gateTransfer` — ★ (iii) the gate-transfer brick.  On the positive-time compact with a
      closedBall INSIDE the open gate `S 0` (and `0 ∈ K`), the GATED witness's heat operator EQUALS the
      UNGATED one (`GlobalHunifAssembly.gatedKernel_heatOp_eq_of_mem_nhds`).  Reduces the (iii) `hIdent`
      to the UNGATED identity `heatOp g gi H = F` (the `CoeffU1Fix.htransport` normal form, valid
      in-gate at `τ>0`; that ungated identity remains the buried transport carry).

    * `heatOpWitness_jointContinuousOn_concrete` — ★★ (COMPOSE) the concrete (R-base) heatOp-witness
      joint continuity with (i) DISCHARGED.  Threads the proven `heatParametrix_deriv_jointContinuousOn`
      as `hDcont` into `parametrixResidualN_jointContinuousOn_of_parts`, carrying only `hLcont` (=(ii))
      and `hIdent` (=(iii)), then `heatOpWitness_jointContinuousOn_of_identity`.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT `a₁ = R/6`).
     (i)  is FULLY PROVEN here (`heatParametrix_deriv_jointContinuousOn`).
     (ii) is REDUCED to the first/second spatial-partial joint continuities of the parametrix — the
          genuine remaining brick (an explicit `∂²(gaussDdim·Θ^{−1/2}·poly)` computation carrying
          `Θ,u ∈ C²` and their continuous second derivatives); NOT attempted here.
     (iii) is REDUCED (via the gate transfer) to the UNGATED `heatOp g gi H = parametrixResidualN`
          identity — the `CoeffU1Fix.htransport` normal form, currently only available buried inside
          `CoeffU1Fix`'s L4 proof (not a standalone banked lemma); carried as `hIdent`/`hUngated`.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HeatOpWitnessContinuity
import QIQTH.InnerKernelJointMeas
import QIQTH.GlobalHunifAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.InnerKernelJointMeas QIQTH.HeatOpWitnessContinuity
open scoped Topology

namespace QIQTH.ParametrixPartsContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (i) — the `∂_τ` term joint continuity.  FULLY PROVEN.
    ############################################################################### -/

/-- **The Gaussian `τ`-derivative CLOSED FORM at `τ>0`.**  `∂_s gaussDdim(τ,z) =
    Σ_i ((z_i)²/(4τ²) − 1/(2τ))·gaussDdim τ z`.  Route: `FlatHeatEquation.gaussDdim_heat_eqn`
    (`∂_s G = Σ_i ∂_i² G`) followed by `gaussDdim_pd_pd_i` on each summand.  NOT `a₁ = R/6`. -/
theorem gaussDdim_deriv_t_eq (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    deriv (fun s => gaussDdim s z) τ
      = ∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) * gaussDdim τ z := by
  rw [gaussDdim_heat_eqn τ hτ z]
  exact Finset.sum_congr rfl (fun i _ => gaussDdim_pd_pd_i τ hτ z i)

/-- **★ (i-ingredient) `gaussDdim_deriv_t_jointContinuousOn`.**  Joint `(τ,z)`-continuity of the
    Gaussian `τ`-derivative `p ↦ deriv (fun s => gaussDdim s p.2) p.1` on `{0<τ}`.  Route:
    `ContinuousOn.congr` onto the closed form `gaussDdim_deriv_t_eq` — a finite sum of the banked
    jointly-continuous Gaussian (`gaussDdim_continuousOn_pos`) times the `τ>0`-regular rational scalar
    `(z_i)²/(4τ²) − 1/(2τ)`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_deriv_t_jointContinuousOn :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => gaussDdim s p.2) p.1)
      {q : ℝ × Point n | 0 < q.1} := by
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n =>
        ∑ i, ((p.2 i) ^ 2 / (4 * p.1 ^ 2) - 1 / (2 * p.1)) * gaussDdim p.1 p.2)
      {q : ℝ × Point n | 0 < q.1} := by
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.mul _ gaussDdim_continuousOn_pos
    apply ContinuousOn.sub
    · apply ContinuousOn.div
      · exact (((continuous_apply i).comp continuous_snd).pow 2).continuousOn
      · exact (by fun_prop : Continuous (fun p : ℝ × Point n => 4 * p.1 ^ 2)).continuousOn
      · intro q hq
        have hq' : (0 : ℝ) < q.1 := hq
        exact (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos hq' 2)).ne'
    · apply ContinuousOn.div continuousOn_const
      · exact (by fun_prop : Continuous (fun p : ℝ × Point n => 2 * p.1)).continuousOn
      · intro q hq
        have hq' : (0 : ℝ) < q.1 := hq
        exact (mul_pos (by norm_num : (0 : ℝ) < 2) hq').ne'
  refine hClosed.congr ?_
  intro p hp
  have hp' : (0 : ℝ) < p.1 := hp
  exact gaussDdim_deriv_t_eq p.1 hp' p.2

/-- **The FULL parametrix `τ`-derivative CLOSED FORM at `τ>0`.**  The `(Θ z)^{−1/2}` factor is an
    `s`-constant, so the product rule on `gaussDdim s z · Σ_{k≤N} u_k(z)·s^k` gives
      `∂_s H_N(s,z)|_{s=τ} = (Θ z)^{−1/2}·( (∂_s gaussDdim)(τ,z)·Σ u_k z τ^k + gaussDdim τ z·Σ u_k z·(k τ^{k−1}) )`.
    Route: `HasDerivAt` built by hand (`gaussDdim` differentiable via `HasDerivAt.fun_finsetProd`,
    the polynomial via `HasDerivAt.sum`), `HasDerivAt.mul`, `.const_mul`, then `.deriv`.  NOT `a₁ = R/6`. -/
theorem heatParametrix_deriv_t_eq (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    deriv (fun s => heatParametrix N Θ u s z) τ
      = (Θ z) ^ (-(1 : ℝ) / 2)
        * ((deriv (fun s => gaussDdim s z) τ) * (∑ k ∈ Finset.range (N + 1), u k z * τ ^ k)
            + gaussDdim τ z * (∑ k ∈ Finset.range (N + 1), u k z * ((k : ℝ) * τ ^ (k - 1)))) := by
  -- the Gaussian is `s`-differentiable at `τ` (finite product of `heatKernel1D`, each differentiable)
  have hgaussHD : HasDerivAt (fun s => gaussDdim s z) (deriv (fun s => gaussDdim s z) τ) τ := by
    have hdiff : DifferentiableAt ℝ (fun s => gaussDdim s z) τ := by
      simp only [gaussDdim]
      exact (HasDerivAt.fun_finsetProd
        (fun (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
          heatKernel1D_hasDerivAt_t τ (z i) hτ)).differentiableAt
    exact hdiff.hasDerivAt
  -- the DeWitt polynomial `Σ u_k z s^k` and its `s`-derivative
  have hpoly : HasDerivAt (fun s => ∑ k ∈ Finset.range (N + 1), u k z * s ^ k)
      (∑ k ∈ Finset.range (N + 1), u k z * ((k : ℝ) * τ ^ (k - 1))) τ := by
    have key : HasDerivAt (∑ k ∈ Finset.range (N + 1), fun s : ℝ => u k z * s ^ k)
        (∑ k ∈ Finset.range (N + 1), u k z * ((k : ℝ) * τ ^ (k - 1))) τ :=
      HasDerivAt.sum (fun k _ => (hasDerivAt_pow k τ).const_mul (u k z))
    have hfun : (∑ k ∈ Finset.range (N + 1), fun s : ℝ => u k z * s ^ k)
        = (fun s => ∑ k ∈ Finset.range (N + 1), u k z * s ^ k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hfun] at key
    exact key
  -- product rule, then multiply by the `s`-constant `(Θ z)^{−1/2}`
  have hmul := hgaussHD.mul hpoly
  have hfull := hmul.const_mul ((Θ z) ^ (-(1 : ℝ) / 2))
  have hEqfun : (fun s => heatParametrix N Θ u s z)
      = (fun s => (Θ z) ^ (-(1 : ℝ) / 2)
          * (gaussDdim s z * ∑ k ∈ Finset.range (N + 1), u k z * s ^ k)) := by
    funext s; simp only [heatParametrix]; ring
  have hd : HasDerivAt (fun s => heatParametrix N Θ u s z)
      ((Θ z) ^ (-(1 : ℝ) / 2)
        * ((deriv (fun s => gaussDdim s z) τ) * (∑ k ∈ Finset.range (N + 1), u k z * τ ^ k)
            + gaussDdim τ z * (∑ k ∈ Finset.range (N + 1), u k z * ((k : ℝ) * τ ^ (k - 1))))) τ := by
    rw [hEqfun]; exact hfull
  exact hd.deriv

/-- **★★ (i) `heatParametrix_deriv_jointContinuousOn` — FULLY PROVEN.**  Joint `(τ,z)`-continuity of
    the parametrix `∂_τ` term `p ↦ deriv (fun s => heatParametrix N Θ u s p.2) p.1` on `{0<τ}`, from
    `Θ` continuous / non-vanishing (for the `Θ^{−1/2}` factor) and each `u_k` continuous.  Route:
    `ContinuousOn.congr` onto the closed form `heatParametrix_deriv_t_eq`, whose four pieces are all
    jointly continuous on `{0<τ}` (`Θ^{−1/2}` by `Continuous.rpow_const`; the Gaussian `τ`-derivative
    by `gaussDdim_deriv_t_jointContinuousOn`; `gaussDdim` by `gaussDdim_continuousOn_pos`; the two
    DeWitt polynomials by `continuousOn_finsetSum`).  This is EXACTLY the `hDcont` slot of
    `HeatOpWitnessContinuity.parametrixResidualN_jointContinuousOn_of_parts`.  Carried hypotheses are
    genuine coefficient-regularity facts — none is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatParametrix_deriv_jointContinuousOn (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k)) :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => heatParametrix N Θ u s p.2) p.1)
      {q : ℝ × Point n | 0 < q.1} := by
  have hcc : ContinuousOn (fun p : ℝ × Point n => (Θ p.2) ^ (-(1 : ℝ) / 2))
      {q : ℝ × Point n | 0 < q.1} :=
    ((hΘc.comp continuous_snd).rpow_const (fun q => Or.inl (hΘne q.2))).continuousOn
  have hsum1 : ContinuousOn
      (fun p : ℝ × Point n => ∑ k ∈ Finset.range (N + 1), u k p.2 * p.1 ^ k)
      {q : ℝ × Point n | 0 < q.1} := by
    apply continuousOn_finsetSum
    intro k _
    exact (((huc k).comp continuous_snd).mul (continuous_fst.pow k)).continuousOn
  have hsum2 : ContinuousOn
      (fun p : ℝ × Point n => ∑ k ∈ Finset.range (N + 1), u k p.2 * ((k : ℝ) * p.1 ^ (k - 1)))
      {q : ℝ × Point n | 0 < q.1} := by
    apply continuousOn_finsetSum
    intro k _
    exact (((huc k).comp continuous_snd).mul
      (continuous_const.mul (continuous_fst.pow (k - 1)))).continuousOn
  have hClosed : ContinuousOn
      (fun p : ℝ × Point n => (Θ p.2) ^ (-(1 : ℝ) / 2)
        * ((deriv (fun s => gaussDdim s p.2) p.1) * (∑ k ∈ Finset.range (N + 1), u k p.2 * p.1 ^ k)
            + gaussDdim p.1 p.2
              * (∑ k ∈ Finset.range (N + 1), u k p.2 * ((k : ℝ) * p.1 ^ (k - 1)))))
      {q : ℝ × Point n | 0 < q.1} :=
    hcc.mul ((gaussDdim_deriv_t_jointContinuousOn.mul hsum1).add
      (gaussDdim_continuousOn_pos.mul hsum2))
  refine hClosed.congr ?_
  intro p hp
  have hp' : (0 : ℝ) < p.1 := hp
  exact heatParametrix_deriv_t_eq N Θ u p.1 hp' p.2

/-! ###############################################################################
    ## (ii) — the `Δ_z` term joint continuity.  HONEST REDUCTION brick.
    ############################################################################### -/

/-- **★ (ii) `laplaceBeltrami_jointContinuousOn_of_parts` — the honest REDUCTION brick.**  Joint
    `(τ,z)`-continuity of the parametrix `Δ_z` term `p ↦ laplaceBeltrami g gi (heatParametrix N Θ u
    p.1) p.2` on any set `s`, from the joint continuity of its constituents:
      • `hgi`  — the inverse-metric components `p ↦ gi p.2 i j`;
      • `hChr` — the Christoffel symbols `p ↦ christoffel g gi k i j p.2`;
      • `hpd1` — the FIRST spatial partials `p ↦ pd (heatParametrix N Θ u p.1) k p.2`;
      • `hpd2` — the SECOND spatial partials `p ↦ pd (fun y => pd (heatParametrix N Θ u p.1) j y) i p.2`.
    Route: unfold `laplaceBeltrami` (a finite `∑_i ∑_j gi·(∂²f − Σ_k Γ·∂f)`); `continuousOn_finsetSum`
    / `.mul` / `.sub`.  This decomposes (ii) into the partial-continuities — the genuine remaining
    analytic work: the explicit second-partial `∂²(gaussDdim·Θ^{−1/2}·poly)` (carrying `Θ,u ∈ C²` and
    their continuous second derivatives), a separate brick.  None of the carried pieces is the
    conclusion (they are STRICTLY lower-level partial continuities).  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_jointContinuousOn_of_parts
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (s : Set (ℝ × Point n))
    (hgi : ∀ i j, ContinuousOn (fun p : ℝ × Point n => gi p.2 i j) s)
    (hChr : ∀ k i j, ContinuousOn (fun p : ℝ × Point n => christoffel g gi k i j p.2) s)
    (hpd1 : ∀ k, ContinuousOn (fun p : ℝ × Point n => pd (heatParametrix N Θ u p.1) k p.2) s)
    (hpd2 : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n => pd (fun y => pd (heatParametrix N Θ u p.1) j y) i p.2) s) :
    ContinuousOn (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2) s := by
  have hEq : (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi p.2 i j *
            (pd (fun y => pd (heatParametrix N Θ u p.1) j y) i p.2
              - ∑ k, christoffel g gi k i j p.2 * pd (heatParametrix N Θ u p.1) k p.2) := by
    funext p; rw [laplaceBeltrami]
  rw [hEq]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  refine (hgi i j).mul ((hpd2 i j).sub ?_)
  apply continuousOn_finsetSum
  intro k _
  exact (hChr k i j).mul (hpd1 k)

/-! ###############################################################################
    ## (iii) — the gate-transfer identity brick.
    ############################################################################### -/

/-- **★ (iii) `hIdent_gateTransfer` — the gate-transfer identity brick.**  On the positive-time
    compact `Icc t₁ t₂ ×ˢ closedBall 0 R` with the closedBall INSIDE the OPEN gate `S 0` (and
    `0 ∈ K`), the GATED witness's heat operator EQUALS the UNGATED one:
      `heatOp g gi (gatedKernel K S H) p.1 p.2 0 = heatOp g gi H p.1 p.2 0`.
    Route: `S 0` open + `closedBall ⊆ S 0` ⟹ `S 0 ∈ 𝓝 p.2` for every `p.2 ∈ closedBall`, then
    `GlobalHunifAssembly.gatedKernel_heatOp_eq_of_mem_nhds`.  This reduces the (iii) `hIdent` (gated
    `= F`) to the UNGATED identity `heatOp g gi H = F` (the `CoeffU1Fix.htransport`
    `parametrixResidualN` normal form).  Carried inputs are genuine geometric facts (gate openness /
    containment / `0∈K`); none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hIdent_gateTransfer (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (t₁ t₂ R : ℝ) (hK0 : (0 : Point n) ∈ K) (hopen : IsOpen (S 0))
    (hsub : Metric.closedBall (0 : Point n) R ⊆ S 0) :
    ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      heatOp g gi (gatedKernel K S H) p.1 p.2 0 = heatOp g gi H p.1 p.2 0 := by
  intro p hp
  have hp2 : p.2 ∈ Metric.closedBall (0 : Point n) R := hp.2
  have hS : S 0 ∈ nhds p.2 := hopen.mem_nhds (hsub hp2)
  exact gatedKernel_heatOp_eq_of_mem_nhds g gi K S H p.1 p.2 0 hK0 hS

/-! ###############################################################################
    ## (COMPOSE) — the concrete heatOp-witness joint continuity, (i) DISCHARGED.
    ############################################################################### -/

/-- **★★ (COMPOSE) `heatOpWitness_jointContinuousOn_concrete`.**  The concrete (R-base) heatOp-witness
    joint continuity on the positive-time compact `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`), with the
    `∂_τ`-part (i) DISCHARGED via `heatParametrix_deriv_jointContinuousOn`.  Threads:
      • the PROVEN `hDcont` from (i) — `Θ` continuous / non-vanishing, each `u_k` continuous;
      • the CARRIED `hLcont` — the `Δ_z`-term joint continuity (=(ii), reducible by
        `laplaceBeltrami_jointContinuousOn_of_parts`);
      • the CARRIED `hIdent` — the gate-local identity `heatOp g gi Wit = parametrixResidualN` on the
        compact (=(iii), reducible via `hIdent_gateTransfer` + the ungated transport normal form),
    through `parametrixResidualN_jointContinuousOn_of_parts` and
    `heatOpWitness_jointContinuousOn_of_identity`.  Carried hypotheses are all genuine and non-vacuous;
    none is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatOpWitness_jointContinuousOn_concrete
    (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (Wit : ℝ → Point n → Point n → ℝ) (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    (hLcont : ContinuousOn
      (fun p : ℝ × Point n => laplaceBeltrami g gi (heatParametrix N Θ u p.1) p.2)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hIdent : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      heatOp g gi Wit p.1 p.2 0 = parametrixResidualN N g gi Θ u p.1 p.2) :
    ContinuousOn (fun p : ℝ × Point n => heatOp g gi Wit p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  -- the compact sits strictly inside `{0<τ}` (since `0 < t₁`)
  have hsub : (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
      ⊆ {q : ℝ × Point n | 0 < q.1} := by
    intro q hq
    have hq1 : t₁ ≤ q.1 := hq.1.1
    exact lt_of_lt_of_le ht₁ hq1
  -- (i): the proven `hDcont`, restricted to the compact
  have hDcont : ContinuousOn
      (fun p : ℝ × Point n => deriv (fun s => heatParametrix N Θ u s p.2) p.1)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) :=
    (heatParametrix_deriv_jointContinuousOn N Θ u hΘc hΘne huc).mono hsub
  -- the explicit residual `F = parametrixResidualN` is jointly continuous (i)+(ii)
  have hFcont := parametrixResidualN_jointContinuousOn_of_parts N g gi Θ u
    (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) hDcont hLcont
  -- congr-transfer onto `heatOp g gi Wit` via the gate-local identity (iii)
  exact heatOpWitness_jointContinuousOn_of_identity g gi Wit
    (fun τ z => parametrixResidualN N g gi Θ u τ z) t₁ t₂ R hIdent hFcont

#check @gaussDdim_deriv_t_eq
#check @gaussDdim_deriv_t_jointContinuousOn
#check @heatParametrix_deriv_t_eq
#check @heatParametrix_deriv_jointContinuousOn
#check @laplaceBeltrami_jointContinuousOn_of_parts
#check @hIdent_gateTransfer
#check @heatOpWitness_jointContinuousOn_concrete

end QIQTH.ParametrixPartsContinuity

/-! ## Axiom checks — every theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ParametrixPartsContinuity
#print axioms gaussDdim_deriv_t_eq
#print axioms gaussDdim_deriv_t_jointContinuousOn
#print axioms heatParametrix_deriv_t_eq
#print axioms heatParametrix_deriv_jointContinuousOn
#print axioms laplaceBeltrami_jointContinuousOn_of_parts
#print axioms hIdent_gateTransfer
#print axioms heatOpWitness_jointContinuousOn_concrete
end AxiomChecks
