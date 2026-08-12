/-
  WhiteF1Reg — J4-644: the CORRECTED-FOLD REGULARITY RE-INSTANTIATION and the assembled
  h0h1-free K1 budget at the corrected witness.  ONE brick of the `a₁ = R/6` heat-kernel
  campaign.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★ WHAT LANDS (executing the WhiteF1 (b)/(h) owed re-instantiations + the final assembly).
  (1) `white_w0C_contDiffAt2_gate` (§4) — the J4-640 `w₀`-regularity discharge RE-INSTANTIATED at
      the CORRECTED fold `w₀' = Θ̂'^{−1/2}` with `Θ̂' = whiteThetaC = (whiteTheta)⁻¹ = √det ĝ`:
      the WhiteW0 §2–§3 chain replayed through ONE extra `inv` (the mechanism was fold-sign
      agnostic, as flagged; near-verbatim).
  (2) `whiteDeltaC_discharged_C2_local` (§5) — the J4-638/641 `hΔ` discharge at the corrected
      `w₁' = Θ̂'^{−1/2}·û₁`: the WhiteW1 localized mechanism (`jet_bounds_on_closedBall_of_ballC2`
      + `laplaceBeltrami_abs_le_of_entry_bounds` + the banked `|ĝ⁻¹|`/`|Γ̂|` suppliers) is
      GENERIC in the folded coefficient — verbatim replay at the corrected fold.
  (3) `white_w1C_contDiffAt2_of_chartC5` (§6) — the chart-C⁵-conditional `w₁'` C²: the banked
      `û₁`-leg (`white_u1_contDiffAt2_of_chartC5` — û₁ is UNCHANGED by F1) folded with the
      corrected `Θ̂'^{−1/2}` C² chain of (1).
  (4) `white_hinvC_discharged` / `white_hdetC_discharged` (§7) — the GEOMETRIC legs of the
      corrected budget instantiated from the bank: the pointwise right inverse
      `Σ_k ĝ·ĝ⁻¹ = δ` from the Neumann unit (`whitePullbackMetric_neumann` + `sum_mul_invMat`),
      and gate-local `det ĝ > 0` from the pos-def IVT pack (`white_w0_pack`).  PLUS the NEW
      GLOBAL `white_metric_det_nonneg` (§2): `det ĝ ≥ 0` EVERYWHERE (congruence factorization
      `ĝ = E·(Jᵀ·g·J)·E` ⟹ `det ĝ = det g·(det J)²·(det E)² ≥ 0`, `det g > 0` from the banked
      pos-def) — this discharges the `hdet0` legs of the banked `radialDeriv_correctedFold` /
      `white_h0_corrected` WITHOUT a (false) global `det > 0` assumption.
  (5) THE LOCAL ODE (§1) — the ONE genuinely fold-independent NEW mechanism this brick needed:
      `radialTransportSolve_transport_eq_of_ball` — the J3 transport ODE `(k + r∂_r)u_k = f`
      at a point of a ball on which the source is only `ContDiffAt ℝ 2` (J3's banked version
      consumed GLOBAL `C^∞`).  Route: C¹ rebase of the J3 Leibniz/IBP proof
      (`radialTransportSolve_transport_eq_C1` — the proof never used more than C¹) + the
      WhiteW1 cutoff extension + star-shaped locality + `pd`-germ transfer.  This lets the
      k = 1 transport equation `h1` fire at gate points GIVEN ONLY the chart-C⁵ residue
      (which supplies gate-local C² of the source `T̂û₀`), eliminating the GLOBAL
      source-smoothness leg `hsm` that `white_h1_corrected` carried.
      `totalRadialO1_coeff_level1_corrected_vanishes_nonneg` (§8) is the matching engine
      replay with `hΘpos` (global strict) weakened to `hΘ0` (global NONNEG — true
      unconditionally for `Θ̂' = √det ĝ`) + strict positivity AT the point only.
  (6) ★★★ `white_K1BudgetW_final` (§9) — THE ASSEMBLED CORRECTED BUDGET: for every row
      `q ∈ K`, `w ≥ 2`, CONDITIONAL ON EXACTLY the labelled chart-C⁵ residue `hch5`
      (the Jet-5 rung), the K1 `t²` budget `K1TransportBudgetW w H (whiteDefect1' … r₀)`
      holds for every gate radius below the joint gate — ALL of
      {h0, h1, hamp, htr, hGauss, hdGauss, hsymI, hgsym, hinv, hdet, hwsm/hw0C2, hu1d, hsm,
      hΔ, hw1C2} are DISCHARGED INTERNALLY.  THE K1 INPUT LIST AFTER THIS BRICK:
      `{hch5 (chart-C⁵ / Jet-5)}` (+ the generic `H`-side comparison data, discharged at the
      concrete Gaussian witness in `white_K1BudgetW_final_concreteH`).
  (7) GATES (§10): `white_h0_final_witness_gate` — K₀ = 0 at the GENUINELY CURVED whitened
      witness (`n = 2`, `κ = −1`, fat `K`, off-centre row) at a NONZERO gate point,
      UNCONDITIONALLY (no `hch5`, no antecedents — full supplier assembly exercised);
      `white_final_R6_carrier_repin` — the diagonal `R/6` CARRIER re-pinned at the corrected
      witness (same banked `whiteCoeffs`/`whiteU1` family as the final budget; carrier ≠ proof).

  ⚠ HONEST SCOPE (binding).
    • THE POST-J4-644 K1 RESIDUE of `white_K1BudgetW_final`: `{hch5}` — the chart-C⁵ (Jet-5)
      rung, whose inhabitance is NOT claimed in-repo (it is the labelled scoped residue; the
      faithfulness gate is the banked `chartC5_implies_banked_chartC4`).  Nothing else remains:
      every other leg of `white_K1BudgetW_corrected` is supplied internally here.
    • `C_Δ` (inside the budget) is per-row `q`; `w ≥ 2` and the `H`-side data are the generic
      budget-shape binders (H discharged at the banked concrete witness in `_concreteH`).
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      owes the Jet-5 rung (`hch5`) + the Duhamel-split integrability carry + the fat-`K`
      carrier piles + the capstone co-instantiation at the CORRECTED witness + the prior
      analytic piles.  The diagonal `R/6` is a labelled CARRIER value (`hu1`), NOT derived.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteF1
import QIQTH.WhiteW1

open Finset Filter Topology MeasureTheory Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag QIQTH.WhiteAmbient
open QIQTH.WhiteAnnulus QIQTH.WidthFree QIQTH.WhiteCapstoneWire
open QIQTH.WhiteOrder1 QIQTH.WhiteTransport QIQTH.WhiteGauss QIQTH.WhiteDelta
open QIQTH.WhiteSmooth QIQTH.WhiteW0 QIQTH.WhiteW1 QIQTH.WhiteF1
open QIQTH.ExpMap QIQTH.PullbackMetric QIQTH.ChartThirdJet QIQTH.RNCExpansion
open QIQTH.EquivProbe QIQTH.CurvedA1CenterAmp QIQTH.HuInftyRebase QIQTH.RadialTransport
open QIQTH.CurvedRNCGaugeBundle
open scoped ContDiff Interval Matrix

namespace QIQTH.WhiteF1Reg

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §0. `radialDeriv` germ congruence (assembly helper). -/

/-- `radialDeriv` depends only on the germ at the point (per-direction `pd_congr_nhds`). -/
theorem radialDeriv_congr_nhds (f h : Point n → ℝ) (x : Point n)
    (hfh : ∀ᶠ y in nhds x, f y = h y) : radialDeriv f x = radialDeriv h x := by
  unfold radialDeriv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QIQTH.LaplaceBeltrami.pd_congr_nhds i x hfh]

/-! ### §1. ★ THE LOCAL TRANSPORT ODE — the J3 engine rebased at C¹ and localized to a ball. -/

/-- **`radialTransportSolve_transport_eq_C1` — the J3 transport ODE at a `C¹` source.**  The
    banked `radialTransportSolve_transport_eq` verbatim, with the `ContDiff ℝ ⊤` hypothesis
    weakened to the `C¹` it actually uses (global differentiability + continuity of the
    partials).  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_transport_eq_C1 (k : ℕ) (hk : 1 ≤ k) (f : Point n → ℝ)
    (hf : ContDiff ℝ 1 f) (v : Point n) :
    (k : ℝ) * radialTransportSolve k f v + radialDeriv (radialTransportSolve k f) v = f v := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ f x :=
    fun x => (hf.differentiable one_ne_zero).differentiableAt
  have hcpd : ∀ i : Fin n, Continuous (fun x => pd f i x) :=
    fun i => continuous_pd_of_contDiff_one f hf i
  -- `s^{k-1}·s = s^k` for `k ≥ 1`.
  have hpow : ∀ s : ℝ, s ^ (k - 1) * s = s ^ k := fun s => by
    rw [← pow_succ]; congr 1; omega
  -- === Leibniz: the `i`-th partial of `u_k` at `v`. ===
  have hpd : ∀ i : Fin n, pd (radialTransportSolve k f) i v
      = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := by
    intro i
    -- a uniform bound on `∂ᵢf` over the compact ray tube `[0,1] × closedBall (v i) 1`.
    obtain ⟨M, hM⟩ :=
      (isCompact_Icc.prod (isCompact_closedBall (v i) 1)).exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ => pd f i (p.1 • Function.update v i p.2))
      (((hcpd i).comp
        (continuous_fst.smul ((continuous_updatePt v i).comp continuous_snd))).continuousOn)
    -- continuity of the integrand and its parameter-derivative.
    have hcF : ∀ t : ℝ, Continuous (fun s : ℝ => s ^ (k - 1) * f (s • Function.update v i t)) :=
      fun t => (continuous_pow (k - 1)).mul
        (hf.continuous.comp (continuous_id.smul continuous_const))
    have hcF' : ∀ t : ℝ,
        Continuous (fun s : ℝ => s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) :=
      fun t => (continuous_pow (k - 1)).mul (continuous_id.mul
        ((hcpd i).comp (continuous_id.smul continuous_const)))
    -- the dominating bound.
    have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          ‖s ^ (k - 1) * (s * pd f i (s • Function.update v i t))‖ ≤ (fun _ => M) s := by
      refine Filter.Eventually.of_forall (fun s hs t ht => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      obtain ⟨hs0, hs1⟩ := hs
      have hmem : (s, t) ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v i) 1 :=
        ⟨⟨le_of_lt hs0, hs1⟩, Metric.ball_subset_closedBall ht⟩
      have hb := hM (s, t) hmem
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_mul, abs_mul]
      have h1 : |s ^ (k - 1)| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (le_of_lt hs0) hs1
      have h2 : |s| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hs0)]; exact hs1
      have hpdnn : (0:ℝ) ≤ |pd f i (s • Function.update v i t)| := abs_nonneg _
      have step : |s| * |pd f i (s • Function.update v i t)| ≤ M :=
        le_trans (mul_le_mul h2 hb hpdnn (by norm_num)) (le_of_eq (one_mul M))
      calc |s ^ (k - 1)| * (|s| * |pd f i (s • Function.update v i t)|)
          ≤ 1 * M := mul_le_mul h1 step (by positivity) (by norm_num)
        _ = M := one_mul M
    -- the pointwise `t`-derivative.
    have hderiv : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          HasDerivAt (fun t => s ^ (k - 1) * f (s • Function.update v i t))
            (s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) t := by
      refine Filter.Eventually.of_forall (fun s _ t _ => ?_)
      have hup : HasDerivAt (fun t => s • Function.update v i t) (s • Pi.single i 1) t :=
        (hasDerivAt_update v i t).const_smul s
      have hff : HasFDerivAt f (fderiv ℝ f (s • Function.update v i t))
          (s • Function.update v i t) := (hdiffbl _).hasFDerivAt
      have hcomp := hff.comp_hasDerivAt t hup
      have hval : (fderiv ℝ f (s • Function.update v i t)) (s • Pi.single i 1)
          = s * pd f i (s • Function.update v i t) := by
        rw [map_smul, smul_eq_mul, ← pd_eq_fderiv f i (s • Function.update v i t) (hdiffbl _)]
      rw [hval] at hcomp
      exact HasDerivAt.const_mul (s ^ (k - 1)) hcomp
    -- apply the parametric Leibniz rule.
    have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t s => s ^ (k - 1) * f (s • Function.update v i t))
      (F' := fun t s => s ^ (k - 1) * (s * pd f i (s • Function.update v i t)))
      (bound := fun _ => M) (x₀ := v i) (s := Metric.ball (v i) 1) (a := 0) (b := 1)
      (Metric.ball_mem_nhds (v i) one_pos)
      (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
      ((hcF (v i)).intervalIntegrable 0 1)
      ((hcF' (v i)).aestronglyMeasurable)
      hbound intervalIntegrable_const hderiv
    -- read off `pd u_k i v`, rewriting `update v i (v i) = v`.
    have h0 : HasDerivAt
        (fun t => ∫ s in (0:ℝ)..1, s ^ (k - 1) * f (s • Function.update v i t))
        (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v))) (v i) := by
      have := leibniz.2
      rw [show (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • Function.update v i (v i))))
            = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) from
          intervalIntegral.integral_congr (fun s _ => by rw [Function.update_eq_self])] at this
      exact this
    have hval2 : deriv (fun t => radialTransportSolve k f (Function.update v i t)) (v i)
        = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := h0.deriv
    rw [pd]; exact hval2
  -- === radialDeriv u_k as a single ray integral. ===
  have hRD : radialDeriv (radialTransportSolve k f) v
      = ∫ s in (0:ℝ)..1, s ^ k * (∑ i, v i * pd f i (s • v)) := by
    rw [radialDeriv]
    have hswap : ∀ i, v i * pd (radialTransportSolve k f) i v
        = ∫ s in (0:ℝ)..1, v i * (s ^ (k - 1) * (s * pd f i (s • v))) := by
      intro i; rw [hpd i, ← intervalIntegral.integral_const_mul]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        IntervalIntegrable (fun s => v i * (s ^ (k - 1) * (s * pd f i (s • v)))) volume 0 1 :=
      fun i _ => (continuous_const.mul ((continuous_pow (k - 1)).mul (continuous_id.mul
        ((hcpd i).comp (continuous_id.smul continuous_const))))).intervalIntegrable 0 1
    rw [Finset.sum_congr rfl (fun i _ => hswap i), ← intervalIntegral.integral_finsetSum hInt]
    apply intervalIntegral.integral_congr
    intro s _
    show (∑ i, v i * (s ^ (k - 1) * (s * pd f i (s • v))))
        = s ^ k * ∑ i, v i * pd f i (s • v)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hpow s]; ring
  -- === integration by parts. ===
  have hv'int : IntervalIntegrable (fun s => ∑ i, v i * pd f i (s • v)) volume 0 1 :=
    (continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul
      ((hcpd i).comp (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s ^ k) (v := fun s => f (s • v))
    (u' := fun s => (k : ℝ) * s ^ (k - 1)) (v' := fun s => ∑ i, v i * pd f i (s • v))
    (fun s _ => hasDerivAt_pow k s)
    (fun s _ => hasDerivAt_ray f v s (hdiffbl _))
    ((continuous_const.mul (continuous_pow (k - 1))).intervalIntegrable 0 1)
    hv'int
  have hInt2 : (∫ s in (0:ℝ)..1, ((k : ℝ) * s ^ (k - 1)) * f (s • v))
      = (k : ℝ) * radialTransportSolve k f v := by
    rw [radialTransportSolve, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _; ring
  rw [hRD, hIBP, hInt2]
  simp only [one_pow, one_smul, one_mul, zero_pow (show k ≠ 0 by omega), zero_mul, sub_zero]
  ring

/-- **★ `radialTransportSolve_transport_eq_of_ball` — the LOCAL transport ODE.**  At any point
    of a ball on which the source is merely `ContDiffAt ℝ 2`, the ray solve satisfies the
    transport ODE `(k + r∂_r)u_k = f`.  Route: cutoff-extend the source to a global C²
    function (WhiteW1), replay the ODE for the extension at C¹ (§1), and transfer back by
    star-shaped locality + the `pd` germ.  This is the leg that lets `h1` fire from the
    chart-C⁵ residue alone (the banked ODE consumed GLOBAL `C^∞`).  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_transport_eq_of_ball (k : ℕ) (hk : 1 ≤ k) (f : Point n → ℝ)
    (r : ℝ) (hf : ∀ x : Point n, ‖x‖ < r → ContDiffAt ℝ 2 f x)
    (v : Point n) (hv : ‖v‖ < r) :
    (k : ℝ) * radialTransportSolve k f v + radialDeriv (radialTransportSolve k f) v = f v := by
  have hxnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  set r₁ : ℝ := (‖v‖ + r) / 2 with hr₁def
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; linarith
  have hr₁r : r₁ < r := by rw [hr₁def]; linarith
  have hxr₁ : ‖v‖ < r₁ := by rw [hr₁def]; linarith
  obtain ⟨f', hf'2, hE⟩ := contDiff_two_cutoff_extension_of_ball f r r₁ hr₁0 hr₁r hf
  have hvball : v ∈ Metric.ball (0 : Point n) r₁ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hxr₁
  have hEq : Set.EqOn (radialTransportSolve k f) (radialTransportSolve k f')
      (Metric.ball (0 : Point n) r₁) :=
    radialTransportSolve_congrOn_ball k f f' r₁ hE
  have hev : ∀ᶠ y in nhds v, radialTransportSolve k f y = radialTransportSolve k f' y :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hvball) hEq
  have hODE := radialTransportSolve_transport_eq_C1 k hk f'
    (hf'2.of_le (by norm_num)) v
  rw [hEq hvball, radialDeriv_congr_nhds _ _ v hev, hE hvball]
  exact hODE

/-! ### §2. ★ GLOBAL `det ĝ ≥ 0` — the congruence factorization (discharging `hdet0`). -/

/-- The uniform-flow pullback metric has NONNEGATIVE determinant EVERYWHERE, given a base
    metric of positive determinant: `g̃ = Jᵀ·g(F)·J ⟹ det g̃ = det g(F)·(det J)² ≥ 0`. -/
theorem uniformFlowPullbackMetric_det_nonneg (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgpos : ∀ y, 0 < Matrix.det (Matrix.of (fun a b => g y a b))) (q v : Point n) :
    0 ≤ Matrix.det (Matrix.of (fun k l => uniformFlowPullbackMetric g gi hC hK q v k l)) := by
  classical
  set J : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun a k => (fderiv ℝ (uniformFlowExp g gi hC hK q) v) (Pi.single k 1) a)
    with hJdef
  set G : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun a b => g (uniformFlowExp g gi hC hK q v) a b) with hGdef
  have hfac : Matrix.of (fun k l => uniformFlowPullbackMetric g gi hC hK q v k l)
      = Jᵀ * G * J := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hJdef, hGdef,
      uniformFlowPullbackMetric]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hfac, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hG : 0 < G.det := hgpos (uniformFlowExp g gi hC hK q v)
  calc (0 : ℝ) ≤ G.det * (J.det * J.det) :=
        mul_nonneg hG.le (mul_self_nonneg _)
    _ = J.det * G.det * J.det := by ring

/-- **★ `white_metric_det_nonneg` — GLOBAL `det ĝ ≥ 0` at the whitened chart.**
    `ĝ = E·g̃(E·)·E ⟹ det ĝ = det g̃·(det E)² ≥ 0` with `det g̃ ≥ 0` from the base pos-def
    (`curvedRNCMetric_det_pos`).  This is the honest global sign leg of the corrected fold
    (`hdet0`): global STRICT positivity is false territory (the flow Jacobian may degenerate
    far away), but nonnegativity holds EVERYWHERE.  NOT `a₁ = R/6`. -/
theorem white_metric_det_nonneg (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) :
    ∀ y : Point n, 0 ≤ Matrix.det (whiteMetric κ hκ hKc q y) := by
  classical
  intro y
  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i k => curvedWhitening κ q i k) with hEdef
  set Gt : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of (fun k l => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q y) k l) with hGtdef
  have hfac : Matrix.det (whiteMetric κ hκ hKc q y) = Matrix.det (E * Gt * E) := by
    congr 1
    ext i j
    show whiteMetric κ hκ hKc q y i j = (E * Gt * E) i j
    simp only [Matrix.mul_apply, Matrix.of_apply, hEdef, hGtdef, whiteMetric,
      whitePullbackMetric]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
  have hGt : 0 ≤ Gt.det :=
    uniformFlowPullbackMetric_det_nonneg (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc
      (fun z => curvedRNCMetric_det_pos κ hκ z) q (whiteVel κ q y)
  rw [hfac, Matrix.det_mul, Matrix.det_mul]
  calc (0 : ℝ) ≤ Gt.det * (E.det * E.det) := mul_nonneg hGt (mul_self_nonneg _)
    _ = E.det * Gt.det * E.det := by ring

/-! ### §3. The corrected weight is globally NONNEG and gate-locally positive/C². -/

/-- The corrected ansatz weight `Θ̂' = whiteThetaC` is NONNEGATIVE EVERYWHERE, unconditionally
    (`Θ̂' = ((√det ĝ)⁻¹)⁻¹` and `√· ≥ 0`) — the global `hΘ0` leg of the §8 engine. -/
theorem whiteThetaC_nonneg (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (y : Point n) :
    0 ≤ whiteThetaC κ hκ hKc q y := by
  show 0 ≤ ((Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q y)))⁻¹)⁻¹
  exact inv_nonneg.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- **`white_w0C_pack` — the corrected-fold gate pack**: on a per-`q` gate radius, at every gate
    point: metric entries C², `det ĝ > 0`, `Θ̂'` C² and `> 0`, and the CORRECTED amplitude
    `w₀' = Θ̂'^{−1/2}` is `ContDiffAt ℝ 2` — the WhiteW0 §2–§3 chain replayed through one
    extra `inv` at the inverted weight.  NOT `a₁ = R/6`. -/
theorem white_w0C_pack (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      (∀ i j, ContDiffAt ℝ 2 (fun w => whiteMetric κ hκ hKc q w i j) x)
      ∧ 0 < Matrix.det (whiteMetric κ hκ hKc q x)
      ∧ ContDiffAt ℝ 2 (whiteThetaC κ hκ hKc q) x
      ∧ 0 < whiteThetaC κ hκ hKc q x
      ∧ ContDiffAt ℝ 2
          (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x := by
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0_pack κ hκ hKc q hq
  refine ⟨r₀, hr₀0, fun x hx => ?_⟩
  obtain ⟨hentry, _hdet2, hdetpos, hθC2, hθpos, _⟩ := hpack x hx
  have hrwC : whiteThetaC κ hκ hKc q = fun y => (whiteTheta κ hκ hKc q y)⁻¹ := rfl
  have hθCC2 : ContDiffAt ℝ 2 (whiteThetaC κ hκ hKc q) x := by
    rw [hrwC]
    exact hθC2.inv (ne_of_gt hθpos)
  have hθCpos : 0 < whiteThetaC κ hκ hKc q x := by
    show 0 < (whiteTheta κ hκ hKc q x)⁻¹
    exact inv_pos.mpr hθpos
  refine ⟨hentry, hdetpos, hθCC2, hθCpos, ?_⟩
  have hrw0 : foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0
      = fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2) := by
    funext y
    show (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2) * whiteCoeffs κ hκ hKc q 0 y = _
    have h0 : whiteCoeffs κ hκ hKc q 0 y = 1 := rfl
    rw [h0, mul_one]
  rw [hrw0]
  exact hθCC2.rpow_const_of_ne (ne_of_gt hθCpos)

/-! ### §4. (Deliverable 1) ★ `white_w0C_contDiffAt2_gate` — the corrected `hw0C2` leg. -/

/-- **★ The J4-640 `w₀`-regularity discharge RE-INSTANTIATED at the corrected fold**: there is
    a per-`q` gate on which `w₀' = Θ̂'^{−1/2} = (det ĝ)^{−1/4}` is `ContDiffAt ℝ 2` — the exact
    first component of the corrected C² pair binder.  NOT `a₁ = R/6`. -/
theorem white_w0C_contDiffAt2_gate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x := by
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0C_pack κ hκ hKc q hq
  exact ⟨r₀, hr₀0, fun x hx => (hpack x hx).2.2.2.2⟩

/-! ### §5. (Deliverable 2) ★ the corrected `hΔ` local discharge. -/

/-- **★ `whiteDeltaC_discharged_C2_local` — the `hΔ` discharge at the CORRECTED fold from
    BALL-LOCAL C² of `w₁' = Θ̂'^{−1/2}·û₁`.**  The WhiteW1 localized mechanism was generic in
    the folded coefficient (jet bounds are compact-ball suprema of a C²-on-ball field; the
    operator decomposition is pure abs algebra; the `|ĝ⁻¹|`/`|Γ̂|` suppliers mention no fold)
    — verbatim replay at `whiteThetaC`.  NOT `a₁ = R/6`. -/
theorem whiteDeltaC_discharged_C2_local (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (rW : ℝ) (hrW0 : 0 < rW)
    (hw1loc : ∀ x : Point n, ‖x‖ < rW →
      ContDiffAt ℝ 2 (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x) :
    ∃ rΔ > (0 : ℝ), ∃ C_Δ : ℝ, 0 ≤ C_Δ ∧ ∀ x : Point n, ‖x‖ < rΔ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ := by
  classical
  obtain ⟨r₁, hr₁0, Gb, hGb0, hgib⟩ := whiteInv_entry_bound κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  set rΔ : ℝ := min (min r₁ rΓ) (rW / 2) with hrΔdef
  have hrΔ0 : 0 < rΔ := lt_min (lt_min hr₁0 hrΓ0) (by linarith)
  have hrΔW : rΔ < rW := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨M1, M2, hM10, hM20, hM⟩ := jet_bounds_on_closedBall_of_ballC2
    (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) rΔ rW hrΔW hw1loc
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
    (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x
    Gb (CΓ * rΔ) hGb0 (mul_nonneg hCΓ0 hrΔ0.le)
    (fun i j => hgib q hq x hx1 i j)
    (fun k i j => (hΓ q hq x hxΓ k i j).trans
      (mul_le_mul_of_nonneg_left hx.le hCΓ0))
  obtain ⟨hS1le, hS2le⟩ := hM x hx.le
  calc |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x|
      ≤ Gb * (∑ i, ∑ j, |pd (fun y =>
            pd (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) j y) i x|)
          + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2
            * ∑ k, |pd (foldedCoeff (whiteThetaC κ hκ hKc q)
                (whiteCoeffs κ hκ hKc q) 1) k x| := hbound
    _ ≤ Gb * M2 + Gb * (CΓ * rΔ) * (n : ℝ) ^ 2 * M1 :=
        add_le_add (mul_le_mul_of_nonneg_left hS2le hGb0)
          (mul_le_mul_of_nonneg_left hS1le hcoef0)

/-! ### §6. (Deliverable 3) ★ the corrected `w₁'` chart-C⁵-conditional C². -/

/-- **★ `white_w1C_contDiffAt2_of_chartC5` — gate-local C² of the CORRECTED
    `w₁' = Θ̂'^{−1/2}·û₁`, conditional on exactly the labelled chart-C⁵ residue.**  `û₁` is
    UNCHANGED by F1 (`whiteCoeffsC_matched`), so the banked chart-C⁵ `û₁` leg feeds directly;
    the fold factor is the §3 corrected chain.  NOT `a₁ = R/6`. -/
theorem white_w1C_contDiffAt2_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₁ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₁ →
      ContDiffAt ℝ 2
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x := by
  obtain ⟨rU, hrU0, hu1⟩ := white_u1_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rP, hrP0, hpack⟩ := white_w0C_pack κ hκ hKc q hq
  refine ⟨min rP rU, lt_min hrP0 hrU0, ?_⟩
  intro x hx
  have hxP : ‖x‖ < rP := lt_of_lt_of_le hx (min_le_left _ _)
  have hxU : ‖x‖ < rU := lt_of_lt_of_le hx (min_le_right _ _)
  obtain ⟨-, -, hθCC2, hθCpos, -⟩ := hpack x hxP
  have hrwf : foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1
      = fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2)
          * whiteCoeffs κ hκ hKc q 1 y := rfl
  rw [hrwf]
  exact (hθCC2.rpow_const_of_ne (ne_of_gt hθCpos)).mul (hu1 x hxU)

/-! ### §7. (Deliverable 4) the geometric legs: `hinv` from the Neumann unit, `hdet` from the
pos-def pack. -/

/-- **★ `white_hinvC_discharged` — the pointwise right-inverse leg from the banked Neumann
    package**: on the Neumann radius, `Σ_k ĝ_{ik}·ĝ^{kj} = δ_{ij}` — the exact `hinv` binder of
    the corrected budget (via `sum_mul_invMat` at the Neumann unit).  NOT `a₁ = R/6`. -/
theorem white_hinvC_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∀ q ∈ Kset, ∀ x : Point n, ‖x‖ < r₀ → ∀ i j : Fin n,
      (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0 := by
  obtain ⟨rN, hrN0, M, _hM0, hpkg⟩ := whitePullbackMetric_neumann κ hκ hKc
  refine ⟨rN, hrN0, fun q hq x hx i j => ?_⟩
  have hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q x a b)) :=
    (hpkg q hq x hx).2.1
  exact sum_mul_invMat (fun a b => whitePullbackMetric κ hκ hKc q x a b) hU i j

/-- **`white_hdetC_discharged` — gate-local `det ĝ > 0`** (the pos-def IVT leg of the banked
    `white_w0_pack`, re-exported as the corrected budget's `hdet` gate).  NOT `a₁ = R/6`. -/
theorem white_hdetC_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      0 < Matrix.det (whiteMetric κ hκ hKc q x) := by
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0_pack κ hκ hKc q hq
  exact ⟨r₀, hr₀0, fun x hx => (hpack x hx).2.2.1⟩

/-! ### §8. The k = 1 transport equation at gate points from the chart-C⁵ residue alone. -/

/-- **The h1 conjugation engine with the positivity binder weakened to NONNEG-global +
    strict-at-the-point** — the WhiteTransport `totalRadialO1_coeff_level1_corrected_vanishes`
    replay: the proof used `hΘpos` globally only through `(·).le` (the funext fold rewrite);
    strictness was consumed at `v` alone (the `a·a⁻¹ = 1` cancellation).  This matches the
    corrected weight `Θ̂' = √det ĝ`, which is nonneg EVERYWHERE (§3) but strictly positive
    only on the gate.  NOT `a₁ = R/6`. -/
theorem totalRadialO1_coeff_level1_corrected_vanishes_nonneg
    (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (hdGauss : ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
        = (if i = j then (1 : ℝ) else 0) - g v i j)
    (htr : (∑ i, ∑ j, gi v i j * g v i j) = (n : ℝ))
    (hΘ0 : ∀ y, 0 ≤ Θ y) (hΘv : 0 < Θ v)
    (haa : ∀ i, PdiffAt (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) i v)
    (hu1d : ∀ i, PdiffAt (u 1) i v)
    (hamp : radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v
        = -((1 / 4) * radialLogDetSym g gi v * (Θ v) ^ (-(1 : ℝ) / 2)))
    (hODE : u 1 v + radialDeriv (u 1) v
        = transportOp (fun y => (Θ y)⁻¹) g gi (u 0) v) :
    totalRadialO1_coeff_level1 g gi Θ u v = 0 := by
  -- the matched transport source IS `Θ^{1/2}·Δ_g(w₀)`
  have hT : transportOp (fun y => (Θ y)⁻¹) g gi (u 0) v
      = (Θ v) ^ ((1 : ℝ) / 2) * laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
    unfold transportOp
    have h1 : ((Θ v)⁻¹) ^ (-(1 / 2) : ℝ) = (Θ v) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hΘv.le, Real.rpow_neg hΘv.le, inv_inv]
    have h2 : (fun y => ((Θ y)⁻¹) ^ ((1 / 2) : ℝ) * u 0 y) = foldedCoeff Θ u 0 := by
      funext y
      unfold foldedCoeff
      rw [Real.inv_rpow (hΘ0 y), ← Real.rpow_neg (hΘ0 y), neg_div]
    rw [h1, h2]
  -- the folded level-1 coefficient and its radial Leibniz split
  have hw1 : foldedCoeff Θ u 1 = fun y => (Θ y) ^ (-(1 : ℝ) / 2) * u 1 y := rfl
  have hrad : radialDeriv (foldedCoeff Θ u 1) v
      = (Θ v) ^ (-(1 : ℝ) / 2) * radialDeriv (u 1) v
        + u 1 v * radialDeriv (fun y => (Θ y) ^ (-(1 : ℝ) / 2)) v := by
    rw [hw1]
    exact radialDeriv_mul _ _ v haa hu1d
  -- the `a·a⁻¹ = 1` conjugation algebra (strictness at `v` only)
  have hcancel : (Θ v) ^ (-(1 : ℝ) / 2) * (Θ v) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hΘv,
        show (-(1 : ℝ) / 2 + (1 : ℝ) / 2) = 0 by norm_num, Real.rpow_zero]
  -- the reduced ODE: `a·(u₁ + r∂_r u₁) = Δ_g w₀`
  have hkey : (Θ v) ^ (-(1 : ℝ) / 2) * (u 1 v + radialDeriv (u 1) v)
      = laplaceBeltrami g gi (foldedCoeff Θ u 0) v := by
    rw [hODE, hT, ← mul_assoc, hcancel, one_mul]
  -- assemble through the K₁ Gauss reduction
  have hw1v : foldedCoeff Θ u 1 v = (Θ v) ^ (-(1 : ℝ) / 2) * u 1 v := rfl
  rw [totalRadialO1_coeff_level1_gauss_reduction g gi Θ u v hsym hGauss hdGauss htr,
      hrad, hamp, hw1v]
  linear_combination hkey

/-- **The gate ODE from the chart-C⁵ residue**: `û₁ + r∂_r û₁ = T̂û₀` at every point of a
    per-`q` gate, CONDITIONAL on `hch5` alone — the (L-b) gate-local C² of the transport
    source fed through the LOCAL ODE (§1).  This replaces the GLOBAL `hsm` leg of
    `white_h1_corrected`.  NOT `a₁ = R/6`. -/
theorem white_ODE_of_chartC5 (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      whiteCoeffs κ hκ hKc q 1 x + radialDeriv (whiteCoeffs κ hκ hKc q 1) x
        = whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)) x := by
  obtain ⟨r₀, hr₀0, hsrc⟩ := white_transport_source_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  refine ⟨r₀, hr₀0, fun x hx => ?_⟩
  have hu1 : whiteCoeffs κ hκ hKc q 1
      = radialTransportSolve 1 (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) := rfl
  have h := radialTransportSolve_transport_eq_of_ball 1 le_rfl
    (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) r₀ hsrc x hx
  rw [Nat.cast_one, one_mul] at h
  rw [hu1]
  exact h

/-- **★ `white_h1C_local` — the k = 1 transport equation at a gate point of the CORRECTED
    witness, from LOCAL data only**: the `white_h1_corrected` re-instantiation with the two
    global legs replaced — global `det > 0` by {global `det ≥ 0` (§2) + strict at the point},
    and the global source-smoothness `hsm` by the pointwise ODE value (§8 supplies it from
    `hch5`).  NOT `a₁ = R/6`. -/
theorem white_h1C_local (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (x : Point n)
    (hsym : ∀ i j, whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ i, (∑ j, (whiteMetricInv κ hκ hKc q x i j
        - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ i j, (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (htr : (∑ i, ∑ j, whiteMetricInv κ hκ hKc q x i j * whiteMetric κ hκ hKc q x i j)
        = (n : ℝ))
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ i j, (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hdet0 : ∀ y, 0 ≤ Matrix.det (whiteMetric κ hκ hKc q y))
    (hdetx : 0 < Matrix.det (whiteMetric κ hκ hKc q x))
    (hu1d : ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i x)
    (hODE : whiteCoeffs κ hκ hKc q 1 x + radialDeriv (whiteCoeffs κ hκ hKc q 1) x
        = whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)) x) :
    totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0 := by
  -- global nonneg + strict at the point for the corrected weight
  have hΘ0 : ∀ y, 0 ≤ whiteThetaC κ hκ hKc q y := whiteThetaC_nonneg κ hκ hKc q
  have hΘx : 0 < whiteThetaC κ hκ hKc q x := by
    show 0 < (whiteTheta κ hκ hKc q x)⁻¹
    have hpos : 0 < whiteTheta κ hκ hKc q x := by
      show 0 < (Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q x)))⁻¹
      exact inv_pos.mpr (Real.sqrt_pos.mpr hdetx)
    exact inv_pos.mpr hpos
  -- the fold PdiffAt legs (via the det-rpow rewrite; global det ≥ 0)
  have haa : ∀ i, PdiffAt (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2)) i x := by
    intro i
    have hfun : (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2))
        = fun y => (Matrix.det (whiteMetric κ hκ hKc q y)) ^ (-(1 : ℝ) / 4) :=
      correctedFold_eq_det_rpow (whiteMetric κ hκ hKc q) hdet0
    rw [hfun]
    have hslice := det_slice_hasDerivAt (whiteMetric κ hκ hKc q) x i (hd i)
    have hne : Matrix.det (Matrix.of (whiteMetric κ hκ hKc q
        (Function.update x i (x i)))) ≠ 0 := by
      rw [Function.update_eq_self]
      exact hdetx.ne'
    exact (hslice.rpow_const (p := (-(1 : ℝ) / 4)) (Or.inl hne)).differentiableAt
  -- the corrected chain rule (banked; global-nonneg + strict-at-x binders)
  have hamp : radialDeriv (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2)) x
      = -((1 / 4) * radialLogDetSym (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) x
          * (whiteThetaC κ hκ hKc q x) ^ (-(1 : ℝ) / 2)) :=
    radialDeriv_correctedFold (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) x
      hd hsym hinv hdet0 hdetx
  -- the pointwise ODE at the matched conjugation
  have hOp := whiteThetaC_matched_op κ hκ hKc q
  have hODE' : whiteCoeffs κ hκ hKc q 1 x + radialDeriv (whiteCoeffs κ hκ hKc q 1) x
      = transportOp (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
          (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteCoeffs κ hκ hKc q 0) x := by
    rw [hOp]
    exact hODE
  exact totalRadialO1_coeff_level1_corrected_vanishes_nonneg
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) (whiteThetaC κ hκ hKc q)
    (whiteCoeffs κ hκ hKc q) x hsym hGauss hdGauss htr hΘ0 hΘx haa hu1d hamp hODE'

/-! ### §9. (Deliverable 5) ★★★ THE FINAL ASSEMBLED CORRECTED BUDGET. -/

/-- **★★★ `white_K1BudgetW_final` — the corrected h0h1-free K1 `t²` budget, ALL discharged
    legs internal.**  For every row `q ∈ K` and `w ≥ 2`, CONDITIONAL ON EXACTLY the labelled
    chart-C⁵ residue `hch5` (the Jet-5 rung — inhabitance NOT claimed in-repo), the budget
    `K1TransportBudgetW w H (whiteDefect1' … r₀)` holds for every gate radius `r₀` below the
    joint gate.  DISCHARGED INTERNALLY: hGauss (J4-637), hsymI/hgsym (banked global symmetry),
    hdGauss (`hdGauss_of_metric_gauss` + banked pointwise Gauss), hinv (Neumann, §7), hdet
    (pos-def IVT gate + NEW global `det ≥ 0`, §2/§7), hd/hw0C2 (corrected pack, §3–§4),
    hu1d/hw1C2 (chart-C⁵ û₁ leg + corrected fold, §6), hΔ (corrected local discharge, §5),
    h0 (`white_h0_corrected`, banked), h1 (`white_h1C_local` + the LOCAL ODE, §1/§8 — the
    global `hsm` leg is GONE), hamp/htr (banked F1 theorems).
    THE K1 INPUT LIST AFTER THIS BRICK: `{hch5}` (+ the generic `H`-side comparison data,
    discharged concretely below).  ⚠ CONDITIONAL; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_final (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : ℝ) (hw2 : 2 ≤ w)
    (hch5 : ∀ v : Point n,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ rF > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rF →
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        K1TransportBudgetW w H (whiteDefect1' κ hκ hKc q r₀) := by
  classical
  have hw1 : (1 : ℝ) ≤ w := le_trans one_le_two hw2
  -- the internal supplier gates
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged κ hκ hKc q hq
  obtain ⟨rP, hrP0, hpack⟩ := white_w0C_pack κ hκ hKc q hq
  obtain ⟨rMG, hrMG0, hMG⟩ := whitePullbackMetric_gauss κ hκ hKc q hq
  obtain ⟨rI, hrI0, hIpkg⟩ := white_hinvC_discharged κ hκ hKc
  obtain ⟨rU, hrU0, hu1C2⟩ := white_u1_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rO, hrO0, hODEg⟩ := white_ODE_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rW1, hrW10, hw1loc⟩ := white_w1C_contDiffAt2_of_chartC5 κ hκ hKc q hq hch5
  obtain ⟨rΔ, hrΔ0, C_Δ, hCΔ0, hΔd⟩ :=
    whiteDeltaC_discharged_C2_local κ hκ hKc q hq rW1 hrW10 hw1loc
  have hdet0 : ∀ y, 0 ≤ Matrix.det (whiteMetric κ hκ hKc q y) :=
    white_metric_det_nonneg κ hκ hKc q
  -- the joint gate
  set rF : ℝ := min (min (min rG rP) (min rMG rI)) (min (min rU rO) (min rW1 rΔ)) with hrFdef
  have hrF0 : 0 < rF :=
    lt_min (lt_min (lt_min hrG0 hrP0) (lt_min hrMG0 hrI0))
      (lt_min (lt_min hrU0 hrO0) (lt_min hrW10 hrΔ0))
  refine ⟨rF, hrF0, ?_⟩
  intro r₀ hr₀ H C_H hCH hH hH0
  have hrG' : r₀ ≤ rG :=
    hr₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hrP' : r₀ ≤ rP :=
    hr₀.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hrMG' : r₀ ≤ rMG :=
    hr₀.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hrI' : r₀ ≤ rI :=
    hr₀.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hrU' : r₀ ≤ rU :=
    hr₀.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hrO' : r₀ ≤ rO :=
    hr₀.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hrW1' : r₀ ≤ rW1 :=
    hr₀.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hrΔ' : r₀ ≤ rΔ :=
    hr₀.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  -- the pointwise linear-gain column bound with everything internal
  have hgain : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |whiteDefect1' κ hκ hKc q r₀ s p 0|
        ≤ (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) (p - 0)) := by
    intro s p hs hs1
    rw [sub_zero]
    have hG0 : 0 ≤ gaussDdim (w * s) p := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    by_cases hp : ‖p‖ < r₀
    · -- the per-point supplier instantiation
      obtain ⟨hentry, hdetp, _hθCC2, _hθCpos, hw0C2p⟩ :=
        hpack p (lt_of_lt_of_le hp hrP')
      have hd : ∀ (a i j : Fin n),
          PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a p :=
        fun a i j => PdiffAt_of_contDiffAt _ a p ((hentry i j).of_le (by norm_num))
      have hsymI : ∀ i j, whiteMetricInv κ hκ hKc q p i j
          = whiteMetricInv κ hκ hKc q p j i :=
        fun i j => whitePullbackMetricInv_symm_global κ hκ hKc q p i j
      have hgsym : ∀ y i j, whiteMetric κ hκ hKc q y i j = whiteMetric κ hκ hKc q y j i :=
        fun y i j => whitePullbackMetric_symm κ hκ hKc q y i j
      have hinvp : ∀ i j,
          (∑ k, whiteMetric κ hκ hKc q p i k * whiteMetricInv κ hκ hKc q p k j)
            = if i = j then (1 : ℝ) else 0 :=
        hIpkg q hq p (lt_of_lt_of_le hp hrI')
      have hGaussp : ∀ i, (∑ j, (whiteMetricInv κ hκ hKc q p i j
          - (if i = j then (1 : ℝ) else 0)) * p j) = 0 :=
        hG p (lt_of_lt_of_le hp hrG')
      have hdGaussp : ∀ i j,
          (∑ a, p a * pd (fun y => whiteMetric κ hκ hKc q y a j) i p)
            = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q p i j :=
        hdGauss_of_metric_gauss (whiteMetric κ hκ hKc q) rMG p
          (lt_of_lt_of_le hp hrMG') (fun y hy j => hMG y hy j) hgsym hd
      have htrp : (∑ i, ∑ j, whiteMetricInv κ hκ hKc q p i j
          * whiteMetric κ hκ hKc q p i j) = (n : ℝ) :=
        htr_of_inv_symm _ _ p hinvp (hgsym p)
      have h0 : totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
          (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) p = 0 :=
        white_h0_corrected κ hκ hKc q p hsymI hGaussp hdGaussp htrp hd hinvp hdet0 hdetp
      have hu1dp : ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i p :=
        fun i => PdiffAt_of_contDiffAt _ i p
          ((hu1C2 p (lt_of_lt_of_le hp hrU')).of_le (by norm_num))
      have h1 : totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q)
          (whiteMetricInv κ hκ hKc q) (whiteThetaC κ hκ hKc q)
          (whiteCoeffs κ hκ hKc q) p = 0 :=
        white_h1C_local κ hκ hKc q p hsymI hGaussp hdGaussp htrp hd hinvp hdet0 hdetp
          hu1dp (hODEg p (lt_of_lt_of_le hp hrO'))
      have hval : whiteDefect1' κ hκ hKc q r₀ s p (0 : Point n)
          = parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s p := by
        unfold whiteDefect1'
        rw [if_pos ⟨hs, hs1, hp⟩]
      rw [hval, parametrixResidual_N1_linear_gain_C2 _ _ _ _ s hs p hw0C2p
        (hw1loc p (lt_of_lt_of_le hp hrW1')) hGaussp h0 h1, abs_neg]
      have hGs : 0 < gaussDdim s p := gaussDdim_pos s hs p
      have hwid : gaussDdim s p ≤ Real.sqrt w ^ n * gaussDdim (w * s) p := by
        have h := gaussDdim_le_of_width_le 1 w one_pos hw1 (τ := s) hs p
        rwa [one_mul, div_one] at h
      calc |s * gaussDdim s p
            * laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
                (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p|
          = s * gaussDdim s p
            * |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
                (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p| := by
            rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hGs]
        _ ≤ s * gaussDdim s p * C_Δ :=
            mul_le_mul_of_nonneg_left (hΔd p (lt_of_lt_of_le hp hrΔ'))
              (mul_nonneg hs.le hGs.le)
        _ ≤ s * (Real.sqrt w ^ n * gaussDdim (w * s) p) * C_Δ := by
            have := mul_le_mul_of_nonneg_left hwid hs.le
            exact mul_le_mul_of_nonneg_right this hCΔ0
        _ = (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) p) := by ring
    · have hval : whiteDefect1' κ hκ hKc q r₀ s p (0 : Point n) = 0 := by
        unfold whiteDefect1'
        rw [if_neg (fun h => hp h.2.2)]
      rw [hval, abs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ0)
        (mul_nonneg hs.le hG0)
  exact k1BudgetW_of_pointwise_linear_gain w hw2 (whiteDefect1' κ hκ hKc q r₀)
    (Real.sqrt w ^ n * C_Δ)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ0)
    hgain H C_H hCH hH hH0

/-- **The final budget at the CONCRETE Gaussian `H`-witness** (`n = 2`, `w = 8`, banked
    `frozenK2Sharp_H_witness`): the `H`-side binders are discharged too — the FULL conditional
    list of the corrected K1 budget at this instantiation is `{hch5}`.  NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_final_concreteH (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point 2)}
    (hKc : IsCompact Kset) (q : Point 2) (hq : q ∈ Kset)
    (hch5 : ∀ v : Point 2,
      ‖v‖ < expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q →
      ‖v‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc →
      ContDiffAt ℝ 5 (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q) v) :
    ∃ rF > (0 : ℝ), ∀ r₀ : ℝ, r₀ ≤ rF →
      K1TransportBudgetW 8 (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ))
        (whiteDefect1' κ hκ hKc q r₀) := by
  obtain ⟨rF, hrF0, hbud⟩ := white_K1BudgetW_final κ hκ hKc q hq 8 (by norm_num) hch5
  refine ⟨rF, hrF0, fun r₀ hr₀ => ?_⟩
  have hW := QIQTH.FrozenK2Sharp.frozenK2Sharp_H_witness (n := 2) (by norm_num)
  exact hbud r₀ hr₀ (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) 1 zero_le_one
    (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)

/-! ### §10. (Deliverable 6) Non-vacuity gates + the R/6 carrier re-pin (cp466 discipline). -/

/-- **★ GATE — `K₀ = 0` at the GENUINELY CURVED whitened witness, UNCONDITIONALLY**
    (`n = 2`, `κ = −1`, fat `K = closedBall 0 2`, off-centre row `q = (1,1)`): the FULL h0
    supplier assembly of the final budget (Gauss + Neumann inverse + pos-def gate + global
    `det ≥ 0` + entry regularity + symmetry) instantiates at a NONZERO gate point and yields
    the k = 0 transport identity at the corrected witness — no `hch5`, no antecedents, no
    `{0}`-collapse.  NOT `a₁ = R/6`. -/
theorem white_h0_final_witness_gate :
    ∃ r₀ > (0 : ℝ), ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧
      totalRadialO1_coeff
        (whiteMetric (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteMetricInv (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteThetaC (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        x = 0 := by
  classical
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
  obtain ⟨rP, hrP0, hpack⟩ := white_w0C_pack (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
  obtain ⟨rMG, hrMG0, hMG⟩ := whitePullbackMetric_gauss (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
  obtain ⟨rI, hrI0, hIpkg⟩ := white_hinvC_discharged (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2)
  have hdet0 := white_metric_det_nonneg (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1)
  set r₀ : ℝ := min (min rG rP) (min rMG rI) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min (lt_min hrG0 hrP0) (lt_min hrMG0 hrI0)
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  have hxlt : ‖(fun _ => r₀ / 2 : Point 2)‖ < r₀ := lt_of_le_of_lt hb (by linarith)
  set p : Point 2 := (fun _ => r₀ / 2) with hpdef
  have hpG : ‖p‖ < rG := lt_of_lt_of_le hxlt ((min_le_left _ _).trans (min_le_left _ _))
  have hpP : ‖p‖ < rP := lt_of_lt_of_le hxlt ((min_le_left _ _).trans (min_le_right _ _))
  have hpMG : ‖p‖ < rMG := lt_of_lt_of_le hxlt ((min_le_right _ _).trans (min_le_left _ _))
  have hpI : ‖p‖ < rI := lt_of_lt_of_le hxlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hentry, hdetp, -, -, -⟩ := hpack p hpP
  have hd : ∀ (a i j : Fin 2), PdiffAt (fun y => whiteMetric (-1) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) y i j) a p :=
    fun a i j => PdiffAt_of_contDiffAt _ a p ((hentry i j).of_le (by norm_num))
  have hgsym : ∀ y i j, whiteMetric (-1) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) y i j
      = whiteMetric (-1) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) y j i :=
    fun y i j => whitePullbackMetric_symm (-1) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) y i j
  have hinvp := hIpkg (fun _ => 1) hq p hpI
  refine ⟨r₀, hr₀0, p, ?_, hxlt,
    white_h0_corrected (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2)
      (fun _ => 1) p
      (fun i j => whitePullbackMetricInv_symm_global (-1) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) p i j)
      (hG p hpG)
      (hdGauss_of_metric_gauss _ rMG p hpMG (fun y hy j => hMG y hy j) hgsym hd)
      (htr_of_inv_symm _ _ p hinvp (hgsym p))
      hd hinvp hdet0 hdetp⟩
  intro hx0
  have h := congrFun hx0 (0 : Fin 2)
  rw [Pi.zero_apply] at h
  rw [hpdef] at h
  simp only at h
  linarith

/-- **The R/6 CARRIER re-pin at the corrected witness (labelled; carrier ≠ proof).**  The final
    budget's coefficient family is the SAME banked `whiteCoeffs` (preserved by
    `whiteCoeffsC_matched`), so GIVEN the labelled DeWitt normalization `û₁(0) = R/6` (NOT
    derived), the corrected order-1 witness still carries the diagonal `a₁` value:
        `W₁'(t,0) = √det g^κ(q) · (4πt)^{−n/2}·(1 + (R/6)·t)`.
    Direct re-export of the banked `whiteChartKernel1'_diagonal_a1` — J4-644 touches the
    REGULARITY legs only and leaves the carrier untouched.  NOT `a₁ = R/6`. -/
theorem white_final_R6_carrier_repin (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (t R : ℝ)
    (hu1 : whiteU1 κ hκ hKc q (0 : Point n) = R / 6) :
    whiteChartKernel1' κ hκ hKc q t (0 : Point n)
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * ((heatKernel1D t 0) ^ n * (1 + R / 6 * t)) :=
  whiteChartKernel1'_diagonal_a1 κ hκ hKc q hq t R hu1

/-- **No-silent-strengthening record for the ODE leg**: the OLD global source-smoothness input
    `hsm` of `white_h1_corrected` implies the new pointwise ODE values at EVERY point (via the
    banked global transport recursion) — the §8 gate input is STRICTLY WEAKER. -/
theorem white_ODE_of_global_smooth (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n)
    (hsm : ContDiff ℝ ⊤ (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)))) :
    ∀ x : Point n,
      whiteCoeffs κ hκ hKc q 1 x + radialDeriv (whiteCoeffs κ hκ hKc q 1) x
        = whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)) x := by
  intro x
  have h := transportCoeff_succ_transport_eq (whiteTransportOp κ hκ hKc q) 0 hsm x
  simpa using h

end QIQTH.WhiteF1Reg

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteF1Reg.radialDeriv_congr_nhds
#print axioms QIQTH.WhiteF1Reg.radialTransportSolve_transport_eq_C1
#print axioms QIQTH.WhiteF1Reg.radialTransportSolve_transport_eq_of_ball
#print axioms QIQTH.WhiteF1Reg.uniformFlowPullbackMetric_det_nonneg
#print axioms QIQTH.WhiteF1Reg.white_metric_det_nonneg
#print axioms QIQTH.WhiteF1Reg.whiteThetaC_nonneg
#print axioms QIQTH.WhiteF1Reg.white_w0C_pack
#print axioms QIQTH.WhiteF1Reg.white_w0C_contDiffAt2_gate
#print axioms QIQTH.WhiteF1Reg.whiteDeltaC_discharged_C2_local
#print axioms QIQTH.WhiteF1Reg.white_w1C_contDiffAt2_of_chartC5
#print axioms QIQTH.WhiteF1Reg.white_hinvC_discharged
#print axioms QIQTH.WhiteF1Reg.white_hdetC_discharged
#print axioms QIQTH.WhiteF1Reg.totalRadialO1_coeff_level1_corrected_vanishes_nonneg
#print axioms QIQTH.WhiteF1Reg.white_ODE_of_chartC5
#print axioms QIQTH.WhiteF1Reg.white_h1C_local
#print axioms QIQTH.WhiteF1Reg.white_K1BudgetW_final
#print axioms QIQTH.WhiteF1Reg.white_K1BudgetW_final_concreteH
#print axioms QIQTH.WhiteF1Reg.white_h0_final_witness_gate
#print axioms QIQTH.WhiteF1Reg.white_final_R6_carrier_repin
#print axioms QIQTH.WhiteF1Reg.white_ODE_of_global_smooth
