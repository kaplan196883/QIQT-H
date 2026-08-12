/-
  WhiteW0 — J4-640: the `hw0C2` rung — GATE-LOCAL C² of `w₀ = Θ̂^{−1/2}` at the whitened chart,
  from the banked per-point flow regularity.  ONE brick of the `a₁ = R/6` heat-kernel campaign.
  NOT `a₁ = R/6`; proves NOTHING about the coefficient value.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE CHAIN (all suppliers banked; NO new analytic input).
    (1) `uniformFlowExp_contDiffAt_four` (ChartThirdJet) gives `C⁴` of the flow chart at every
        `‖v‖ < min(expRho q, uniformFlowRadius)` — a PER-`q` gate (`expRho_pos` + banked positivity;
        NO `hReach`, since the gate is per-row, not `K`-uniform).  `ContDiffAt.fderiv_right (m := 2)`
        turns this into `C²` of the Jacobian entries, hence `C²` of every
        `uniformFlowPullbackMetric` entry (§1) — STRICTLY MORE than the banked `IsC2At`
        (`uniformFlowPullbackMetric_entry_isC2At`), at the price of the `expRho` gate.
    (2) The whitening `E_q` is a FIXED matrix (`whiteVel = matToCLM (curvedWhitening κ q)`), so the
        whitened entries `ĝ_q = E_qᵀ·g̃(E_q·)·E_q` inherit gate-local `C²` (§2, velocity confinement
        `‖E_q w‖ ≤ √n·‖w‖`).
    (3) `Θ̂ = vanVleck ĝ = (√det ĝ)⁻¹`: det is `C²` (banked generic-point `det_contDiffAt_two`),
        POSITIVE on the gate (Neumann unit `whitePullbackMetric_neumann` ⟹ `det ≠ 0` via
        `isUnit_matToCLM_iff` + `Matrix.isUnit_iff_isUnit_det`; sign pinned by the segment IVT from
        `det ĝ(0) = 1`, `whiteMetric_det_center`), so `Θ̂` is `C²` and `> 0` gate-locally, and
        `w₀ = Θ̂^{−1/2}·û₀ = Θ̂^{−1/2}` is `C²` (`ContDiffAt.rpow_const_of_ne`; `û₀ ≡ 1`).
    (4) ★★ `white_K1BudgetW_C2_w0Free`: the J4-639 K1 `t²` budget with the `hw0C2` leg DISCHARGED —
        THE K1 INPUT LIST AFTER THIS BRICK: `{hw1C2, h0, h1}` (was `{hw0C2, hw1C2, h0, h1}`).
        The discharge feeds the GATE-LOCAL binder of `white_K1BudgetW_of_transport_C2` (`hwsm2`,
        `ContDiffAt` at gate points) — exactly the shape the budget consumes; the GLOBAL
        `ContDiff ℝ 2` binder of `white_K1BudgetW_C2_gaussDeltaFree` was a convenience wrapper, not
        the consumer's need (`hwsm_top_implies_pair_C2` recorded the same monotonicity in J4-639).

  ★ THE `w₁` SCOPE (the remaining regularity leg).
    `hw1C2` needs `C²` of `û₁ = radialTransportSolve 1 (T̂ û₀)` — the ray integral
    `∫₀¹ f(s·v) ds`.  The banked tower (`rayIntegral_hasFDerivAt` → `rayIntegral_contDiff_nat` →
    `radialTransportSolve_contDiff_infty`, HuInftyRebase) is GLOBAL-`C^∞`-source ONLY.  Landed here:
      • `radialTransportSolve_congrOn_ball` — the STAR-SHAPED LOCALITY of the solve: on `ball 0 r`
        the solve reads ONLY the ball values of the source (s·v stays in the ball).  This reduces
        the local variant to a LOCAL-EXTENSION problem.
      • `white_u1_contDiffAt2_of_smooth_extension` / `white_w1_contDiffAt2_of_smooth_extension` —
        gate-local `C²` of `û₁` (and of `w₁ = Θ̂^{−1/2}·û₁`) GIVEN a global-`C^∞` function agreeing
        with the transport source `T̂ û₀` on a ball (the Whitney/cutoff-extension shape: any
        `C^∞`-on-a-ball source extends by a cutoff, so the residue is the OPEN-BALL smoothness of
        `T̂ û₀` itself — which needs `C^{k+2}` of `Θ̂`/`ĝ` on the ball, i.e. iterating (1)–(3) at
        higher order: the flow chart is banked only at `C⁴`, so `C²`-of-`û₁` via this route needs
        `C⁴`-source ⟸ the banked `C⁴` chart EXACTLY saturates; the assembly is the natural J4-641).
      • `white_w1_extension_of_global` — no-silent-strengthening record: the extension input is
        implied by global smoothness of the source.
    ⚠ THE PRECISE MISSING LEMMA (either closes the leg):
      (L-a) local interchange: `ContDiffOn ℝ 2 f (ball 0 r) → ContDiffOn ℝ 2
            (radialTransportSolve k f) (ball 0 r)` — re-proving `rayIntegral_hasFDerivAt` with a
            `ContDiffOn` source (dominated convergence on the compact star `{s·v}`), or
      (L-b) the gate-local `C²` of the SOURCE `T̂ û₀` (needs the `C⁴` analogue of §2–§3 for
            `Δ_ĝ(Θ̂^{1/2}·)`: gate-local `C²` of `ĝ⁻¹` entries + Christoffels + `Θ̂^{±1/2}` one
            order deeper) feeding (L-a).  Both are genuine sub-bricks, not assembly gaps.

  ⚠ HONEST SCOPE (binding).
    • `a₁ = R/6` remains CONDITIONAL: the flat tower is closed and non-vacuous; the curved side
      still owes the remaining K1 inputs — now `{hw1C2, h0, h1}` (this brick discharged the `hw0C2`
      leg gate-locally) — + the Duhamel-split integrability carry + the fat-`K` carrier piles +
      the capstone co-instantiation at the whitened witness + the prior analytic piles.
    • The `hΔ` discharge (`whiteDelta_discharged_C2`) still consumes GLOBAL `C²` of `w₁`; the
      budget here therefore carries `hw1C2` GLOBAL (as J4-639 did), while the pair binder needs
      only its gate-local shadow.  Weakening `hΔ` to a gate-local `C²`-on-`closedBall` is routine
      (the jet bounds are compact-ball suprema) and can ride J4-641.
  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteSmooth
import QIQTH.ChartThirdJet
import QIQTH.RNCExpansionFiniteReg
import QIQTH.PullbackNondegFromFDeriv

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
open QIQTH.CurvedRNCGaugeBundle
open scoped ContDiff

namespace QIQTH.WhiteW0

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. Per-point `ContDiffAt ℝ 2` of the flow pullback-metric entries (C⁴ chart ⟹ C² g̃). -/

/-- **The uniform-flow pullback-metric entries are `ContDiffAt ℝ 2`** at every `v` inside BOTH the
    flow radius AND the per-`q` exp radius — the strict upgrade of the banked `IsC2At`
    (`uniformFlowPullbackMetric_entry_isC2At`) obtained from the banked `C⁴` chart
    (`uniformFlowExp_contDiffAt_four`) via `ContDiffAt.fderiv_right`: `g̃_{ij} = (g∘F)·J_i·J_j`
    with `g∘F` `C⁴`-composed and the Jacobian columns `C²`.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_entry_contDiffAt2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (v : Point n)
    (hvexp : ‖v‖ < expRho g gi hC q) (hvuf : ‖v‖ < uniformFlowRadius g gi hC hK) (i j : Fin n) :
    ContDiffAt ℝ 2 (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v := by
  have hF4 : ContDiffAt ℝ 4 (uniformFlowExp g gi hC hK q) v :=
    uniformFlowExp_contDiffAt_four g gi hC hK q hq v hvexp hvuf
  have hF2 : ContDiffAt ℝ 2 (uniformFlowExp g gi hC hK q) v := hF4.of_le (by norm_num)
  have hJentry : ∀ c a : Fin n, ContDiffAt ℝ 2
      (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single c 1) a) v := by
    intro c a
    have h1 : ContDiffAt ℝ 2
        (fun w => (fderiv ℝ (uniformFlowExp g gi hC hK q) w) (Pi.single c (1 : ℝ))) v :=
      (hF4.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
    exact (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).contDiff.comp_contDiffAt v h1
  have hgF : ∀ a b : Fin n, ContDiffAt ℝ 2
      (fun w => g (uniformFlowExp g gi hC hK q w) a b) v := fun a b =>
    ((hg a b).contDiffAt.of_le le_top).comp v hF2
  simp only [uniformFlowPullbackMetric]
  exact ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ =>
    ((hgF a b).mul (hJentry i a)).mul (hJentry j b)

/-! ### §2–§3. ★ The whitened w₀ pack: gate-local C² of ĝ entries, det, Θ̂, and w₀ = Θ̂^{−1/2}. -/

/-- **★ `white_w0_pack` — the full gate-local C² chain `ĝ → det ĝ → Θ̂ → w₀` of row `q`.**
    There is a per-`q` gate radius `r₀ > 0` (below the per-`q` exp/flow confinement AND the banked
    Neumann radius) on which, at EVERY gate point `x`:
      (i)   every whitened metric entry `ĝ_{ij}` is `ContDiffAt ℝ 2` (§1 + linear whitening);
      (ii)  `det ĝ` is `ContDiffAt ℝ 2` (banked `det_contDiffAt_two`);
      (iii) `det ĝ(x) > 0` — the Neumann unit gives `det ≠ 0`, and the segment IVT from
            `det ĝ(0) = 1` (`whiteMetric_det_center`) pins the sign on the star-shaped gate;
      (iv)  `Θ̂ = (√det ĝ)⁻¹` is `ContDiffAt ℝ 2` and (v) `Θ̂(x) > 0`;
      (vi)  `w₀ = Θ̂^{−1/2}·û₀ = Θ̂^{−1/2}` is `ContDiffAt ℝ 2` — the `hw0C2` gate-local leg.
    NOT `a₁ = R/6`. -/
theorem white_w0_pack (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      (∀ i j, ContDiffAt ℝ 2 (fun w => whiteMetric κ hκ hKc q w i j) x)
      ∧ ContDiffAt ℝ 2 (fun w => Matrix.det (whiteMetric κ hκ hKc q w)) x
      ∧ 0 < Matrix.det (whiteMetric κ hκ hKc q x)
      ∧ ContDiffAt ℝ 2 (whiteTheta κ hκ hKc q) x
      ∧ 0 < whiteTheta κ hκ hKc q x
      ∧ ContDiffAt ℝ 2
          (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x := by
  classical
  obtain ⟨rN, hrN0, M, hM0, hpkgN⟩ := whitePullbackMetric_neumann κ hκ hKc
  set ρ : ℝ := min (expRho (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) q)
    (uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc)
    with hρdef
  have hρ0 : 0 < ρ := lt_min (expRho_pos _ _ _ _) (uniformFlowRadius_pos _ _ _ _)
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set r₀ : ℝ := min rN (ρ / (Real.sqrt n + 1)) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hrN0 (by positivity)
  refine ⟨r₀, hr₀0, ?_⟩
  -- (i) — entry regularity at EVERY gate point (also consumed along the IVT segment).
  have hentry : ∀ y : Point n, ‖y‖ < r₀ →
      ∀ i j, ContDiffAt ℝ 2 (fun w => whiteMetric κ hκ hKc q w i j) y := by
    intro y hy i j
    -- velocity confinement `‖E_q y‖ < ρ`.
    have hvel : ‖whiteVel κ q y‖ < ρ := by
      have h1 : ‖whiteVel κ q y‖ ≤ Real.sqrt n * ‖y‖ := whiteVel_norm_le κ hκ q y
      have h2 : Real.sqrt n * ‖y‖ ≤ Real.sqrt n * r₀ :=
        mul_le_mul_of_nonneg_left hy.le hsn
      have h3 : Real.sqrt n * r₀ ≤ Real.sqrt n * (ρ / (Real.sqrt n + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hsn
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
    -- the whitening is a fixed CLM.
    have hlinAt : ContDiffAt ℝ 2 (whiteVel κ q) y := by
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
    have hUF := uniformFlowPullbackMetric_entry_contDiffAt2 (curvedRNCMetric κ)
      (curvedRNCInv κ) (fun a b => curvedRNCMetric_contDiff κ a b) (curvedRNC_hChr κ hκ)
      hKc q hq (whiteVel κ q y) hvexp hvuf k l
    exact hUF.comp y hlinAt
  -- (ii) — det C² at every gate point.
  have hdet2 : ∀ y : Point n, ‖y‖ < r₀ →
      ContDiffAt ℝ 2 (fun w => Matrix.det (whiteMetric κ hκ hKc q w)) y := fun y hy =>
    det_contDiffAt_two (whiteMetric κ hκ hKc q) y (fun a b => hentry y hy a b)
  -- Neumann unit ⟹ det ≠ 0 at every gate point.
  have hdetne : ∀ y : Point n, ‖y‖ < r₀ →
      Matrix.det (whiteMetric κ hκ hKc q y) ≠ 0 := by
    intro y hy
    have hyN : ‖y‖ < rN := lt_of_lt_of_le hy (min_le_left _ _)
    have hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q y a b)) :=
      (hpkgN q hq y hyN).2.1
    have hUm : IsUnit (Matrix.of (fun a b => whitePullbackMetric κ hκ hKc q y a b)) :=
      (isUnit_matToCLM_iff (Matrix.of fun a b => whitePullbackMetric κ hκ hKc q y a b)).mp hU
    have hdU : IsUnit (Matrix.det
        (Matrix.of (fun a b => whitePullbackMetric κ hκ hKc q y a b))) :=
      (Matrix.isUnit_iff_isUnit_det _).mp hUm
    exact hdU.ne_zero
  -- (iii) — sign pinned by the segment IVT from `det ĝ(0) = 1`.
  have hdetpos : ∀ y : Point n, ‖y‖ < r₀ →
      0 < Matrix.det (whiteMetric κ hκ hKc q y) := by
    intro y hy
    rcases lt_or_gt_of_ne (hdetne y hy) with hneg | hpos
    · exfalso
      have hmemseg : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖t • y‖ < r₀ := by
        intro t ht
        rw [norm_smul, Real.norm_eq_abs]
        calc |t| * ‖y‖ ≤ 1 * ‖y‖ :=
              mul_le_mul_of_nonneg_right
                (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (norm_nonneg y)
          _ = ‖y‖ := one_mul _
          _ < r₀ := hy
      have hcont : ContinuousOn
          (fun t : ℝ => Matrix.det (whiteMetric κ hκ hKc q (t • y)))
          (Set.Icc (0 : ℝ) 1) := by
        intro t ht
        have h1 : ContinuousAt (fun w => Matrix.det (whiteMetric κ hκ hKc q w)) (t • y) :=
          (hdet2 (t • y) (hmemseg t ht)).continuousAt
        have h2 : ContinuousAt (fun s : ℝ => s • y) t :=
          (continuous_id.smul continuous_const).continuousAt
        have h3 : ContinuousAt ((fun w => Matrix.det (whiteMetric κ hκ hKc q w))
            ∘ (fun s : ℝ => s • y)) t :=
          ContinuousAt.comp (x := t) (f := fun s : ℝ => s • y) h1 h2
        exact h3.continuousWithinAt
      have hsub := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont
      have h0mem : (0 : ℝ) ∈ Set.Icc
          (Matrix.det (whiteMetric κ hκ hKc q ((1 : ℝ) • y)))
          (Matrix.det (whiteMetric κ hκ hKc q ((0 : ℝ) • y))) := by
        constructor
        · rw [one_smul]
          exact hneg.le
        · rw [zero_smul, whiteMetric_det_center κ hκ hKc q hq]
          norm_num
      obtain ⟨t, ht, hφt⟩ := hsub h0mem
      exact hdetne (t • y) (hmemseg t ht) hφt
    · exact hpos
  -- (iv)/(v) — Θ̂ = (√det ĝ)⁻¹ is C² and positive on the gate.
  have hθ : ∀ y : Point n, ‖y‖ < r₀ →
      ContDiffAt ℝ 2 (whiteTheta κ hκ hKc q) y ∧ 0 < whiteTheta κ hκ hKc q y := by
    intro y hy
    have hdp := hdetpos y hy
    have hsq0 : 0 < Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q y)) :=
      Real.sqrt_pos.mpr hdp
    have hrwθ : whiteTheta κ hκ hKc q
        = fun w => (Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q w)))⁻¹ := rfl
    constructor
    · rw [hrwθ]
      have hs : ContDiffAt ℝ 2
          (fun w => Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q w))) y :=
        sqrtdet_contDiffAt_two (whiteMetric κ hκ hKc q) y
          (fun a b => hentry y hy a b) (ne_of_gt hdp)
      exact hs.inv (ne_of_gt hsq0)
    · rw [hrwθ]
      exact inv_pos.mpr hsq0
  -- (vi) — assemble `w₀ = Θ̂^{−1/2}`.
  intro x hx
  refine ⟨hentry x hx, hdet2 x hx, hdetpos x hx, (hθ x hx).1, (hθ x hx).2, ?_⟩
  have hu0 : whiteCoeffs κ hκ hKc q 0 = fun _ : Point n => (1 : ℝ) := rfl
  have hrw0 : foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0
      = fun y => (whiteTheta κ hκ hKc q y) ^ (-(1 : ℝ) / 2) := by
    funext y
    simp only [foldedCoeff, hu0, mul_one]
  rw [hrw0]
  exact ((hθ x hx).1).rpow_const_of_ne (ne_of_gt (hθ x hx).2)

/-- **★ `white_w0_contDiffAt2_gate` — the `hw0C2` leg DISCHARGED gate-locally.**  The exact first
    component of the `hwsm2` binder of `white_K1BudgetW_of_transport_C2`, supplied from the bank
    alone (per-`q` gate; unconditional in the whitened chart data).  NOT `a₁ = R/6`. -/
theorem white_w0_contDiffAt2_gate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x := by
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0_pack κ hκ hKc q hq
  exact ⟨r₀, hr₀0, fun x hx => (hpack x hx).2.2.2.2.2⟩

/-! ### §4. ★★ The K1 budget with the `hw0C2` leg GONE. -/

/-- **★★ `white_K1BudgetW_C2_w0Free` — the K1 `t²` budget with `hGauss` (J4-637), `hΔ` (J4-638/639
    at C²) AND now the `hw0C2` leg (this brick) DISCHARGED.**
    THE K1 INPUT LIST AFTER THIS BRICK: `{hw1C2, h0, h1}` — the `w₀`-regularity input is GONE
    (supplied internally, gate-locally, from the banked chart regularity).
    `hw1C2` is carried GLOBAL because the `hΔ` discharge consumes global jet bounds (honest scope
    note in the header).  ⚠ CONDITIONAL; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_C2_w0Free (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (w : ℝ) (hw2 : 2 ≤ w)
    (hw1C2 : ContDiff ℝ 2
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1)) :
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
  obtain ⟨rW, hrW0, hW0gate⟩ := white_w0_contDiffAt2_gate κ hκ hKc q hq
  obtain ⟨rG, hrG0, hG⟩ := whiteGauss_discharged κ hκ hKc q hq
  obtain ⟨rΔ, hrΔ0, C_Δ, hCΔ0, hΔd⟩ := whiteDelta_discharged_C2 κ hκ hKc q hq hw1C2
  refine ⟨min (min rG rΔ) rW, lt_min (lt_min hrG0 hrΔ0) hrW0, ?_⟩
  intro r₀ hr₀ h0 h1 H C_H hCH hH hH0
  have hrG : r₀ ≤ rG := hr₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrΔ : r₀ ≤ rΔ := hr₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrW : r₀ ≤ rW := hr₀.trans (min_le_right _ _)
  exact white_K1BudgetW_of_transport_C2 κ hκ hKc q r₀ w C_Δ hw2 hCΔ0
    (fun x hx => ⟨hW0gate x (lt_of_lt_of_le hx hrW), hw1C2.contDiffAt⟩)
    (fun x hx i => hG x (lt_of_lt_of_le hx hrG) i)
    h0 h1
    (fun x hx => hΔd x (lt_of_lt_of_le hx hrΔ))
    H C_H hCH hH hH0

/-! ### §5. The `w₁` leg: star-shaped locality of the ray-integral solve + the extension route. -/

/-- **★ `radialTransportSolve_congrOn_ball` — star-shaped locality of the transport solve.**  On the
    ball the solve `∫₀¹ s^{k−1}·f(s·v) ds` reads ONLY the ball values of the source (`s·v` stays in
    the star-shaped ball).  This is the lever reducing the LOCAL solve-regularity variant to a
    local-extension problem for the source.  NOT `a₁ = R/6`. -/
theorem radialTransportSolve_congrOn_ball (k : ℕ) (f f' : Point n → ℝ) (r : ℝ)
    (hE : Set.EqOn f f' (Metric.ball (0 : Point n) r)) :
    Set.EqOn (radialTransportSolve k f) (radialTransportSolve k f')
      (Metric.ball (0 : Point n) r) := by
  intro v hv
  rw [Metric.mem_ball, dist_zero_right] at hv
  simp only [radialTransportSolve]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hmem : s • v ∈ Metric.ball (0 : Point n) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩) (norm_nonneg v)
      _ = ‖v‖ := one_mul _
      _ < r := hv
  show s ^ (k - 1) * f (s • v) = s ^ (k - 1) * f' (s • v)
  rw [hE hmem]

/-- **`white_u1_contDiffAt2_of_smooth_extension` — gate-local C² of `û₁` GIVEN a global-`C^∞`
    extension of the transport source off the ball.**  `û₁ = radialTransportSolve 1 (T̂ û₀)`; if a
    global `C^∞` `f'` agrees with `T̂ û₀` on `ball 0 r`, then on that ball `û₁` coincides with
    `radialTransportSolve 1 f'` (star-shaped locality), which is globally `C^∞` by the banked
    `radialTransportSolve_contDiff_infty` — so `û₁` is `ContDiffAt ℝ 2` at every ball point.
    ⚠ The extension antecedent is the LABELLED scoped residue of the `w₁` leg (cutoff/Whitney
    shape; its in-repo discharge = the open-ball smoothness of `T̂ û₀`, the J4-641 target).
    NOT `a₁ = R/6`. -/
theorem white_u1_contDiffAt2_of_smooth_extension (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (r : ℝ)
    (f' : Point n → ℝ) (hf' : ContDiff ℝ (∞ : WithTop ℕ∞) f')
    (hE : Set.EqOn (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) f'
      (Metric.ball (0 : Point n) r)) :
    ∀ x : Point n, ‖x‖ < r → ContDiffAt ℝ 2 (whiteCoeffs κ hκ hKc q 1) x := by
  intro x hx
  have hxball : x ∈ Metric.ball (0 : Point n) r := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hx
  have hu1 : whiteCoeffs κ hκ hKc q 1
      = radialTransportSolve 1 (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) := rfl
  have hEq : Set.EqOn (whiteCoeffs κ hκ hKc q 1) (radialTransportSolve 1 f')
      (Metric.ball (0 : Point n) r) := by
    rw [hu1]
    exact radialTransportSolve_congrOn_ball 1 _ f' r hE
  have hglob : ContDiff ℝ (∞ : WithTop ℕ∞) (radialTransportSolve 1 f') :=
    radialTransportSolve_contDiff_infty 1 f' hf'
  have hle : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    simpa using h
  have hCA : ContDiffAt ℝ 2 (radialTransportSolve 1 f') x :=
    (hglob.of_le hle).contDiffAt
  exact hCA.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxball) hEq)

/-- **`white_w1_contDiffAt2_of_smooth_extension` — the gate-local `hw1` shadow from the extension.**
    Combining the `û₁` route with the §2–§3 `Θ̂^{−1/2}` chain: given the source extension, the FULL
    folded coefficient `w₁ = Θ̂^{−1/2}·û₁` is `ContDiffAt ℝ 2` on a joint gate.  (The `hΔ` discharge
    still wants the GLOBAL `C²` of `w₁`; this lemma delivers the gate-local shadow — the honest
    remaining gap between the two binders is recorded in the header.)  NOT `a₁ = R/6`. -/
theorem white_w1_contDiffAt2_of_smooth_extension (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset)
    (r : ℝ) (hr : 0 < r) (f' : Point n → ℝ) (hf' : ContDiff ℝ (∞ : WithTop ℕ∞) f')
    (hE : Set.EqOn (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) f'
      (Metric.ball (0 : Point n) r)) :
    ∃ r₁ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₁ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x := by
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0_pack κ hκ hKc q hq
  refine ⟨min r₀ r, lt_min hr₀0 hr, ?_⟩
  intro x hx
  have hx0 : ‖x‖ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxr : ‖x‖ < r := lt_of_lt_of_le hx (min_le_right _ _)
  obtain ⟨-, -, -, hθC2, hθpos, -⟩ := hpack x hx0
  have hu1C2 := white_u1_contDiffAt2_of_smooth_extension κ hκ hKc q r f' hf' hE x hxr
  have hrw : foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1
      = fun y => (whiteTheta κ hκ hKc q y) ^ (-(1 : ℝ) / 2) * whiteCoeffs κ hκ hKc q 1 y :=
    rfl
  rw [hrw]
  exact (hθC2.rpow_const_of_ne (ne_of_gt hθpos)).mul hu1C2

/-- **No-silent-strengthening record for the extension input**: global `C^∞` of the transport source
    itself supplies the extension antecedent at every radius (with `f'` the source) — the extension
    input is STRICTLY WEAKER than global source smoothness.  NOT `a₁ = R/6`. -/
theorem white_w1_extension_of_global (κ : ℝ) (hκ : κ ≤ 0)
    {Kset : Set (Point n)} (hKc : IsCompact Kset) (q : Point n)
    (h : ContDiff ℝ (∞ : WithTop ℕ∞) (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))))
    (r : ℝ) :
    ∃ f' : Point n → ℝ, ContDiff ℝ (∞ : WithTop ℕ∞) f'
      ∧ Set.EqOn (whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ))) f'
          (Metric.ball (0 : Point n) r) :=
  ⟨whiteTransportOp κ hκ hKc q (fun _ => (1 : ℝ)), h, fun _ _ => rfl⟩

/-! ### §6. Non-vacuity gates (cp466 discipline). -/

/-- **Monotonicity record — NO silent strengthening**: the previous GLOBAL `hw0C2` binder
    (`white_K1BudgetW_C2_gaussDeltaFree`) implies the gate-local shape discharged here, at every
    gate radius — the new supplier feeds a consumer whose demand was already weaker. -/
theorem hw0C2_global_implies_gate (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ : ℝ)
    (h : ContDiff ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0)) :
    ∀ x : Point n, ‖x‖ < r₀ →
      ContDiffAt ℝ 2 (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0) x :=
  fun _x _ => h.contDiffAt

/-- **★ The curved-witness gate for the `hw0C2` discharge (UNCONDITIONAL).**  At the genuinely
    curved witness (`n = 2`, `κ = −1`, fat `K = closedBall 0 2`, off-centre row `q = (1,1)`), the
    §2–§3 chain instantiates to a positive gate with a NONZERO gate point at which `w₀ = Θ̂^{−1/2}`
    is `ContDiffAt ℝ 2` and `Θ̂ > 0` — no `{0}`-collapse, no antecedents.  NOT `a₁ = R/6`. -/
theorem white_w0_witness_gate :
    ∃ r₀ > (0 : ℝ), ∃ x : Point 2, x ≠ 0 ∧ ‖x‖ < r₀ ∧
      ContDiffAt ℝ 2 (foldedCoeff
        (whiteTheta (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        (whiteCoeffs (-1) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1))
        0) x
      ∧ 0 < whiteTheta (-1) (by norm_num)
          (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) x := by
  have hq : ((fun _ => 1) : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_) one_le_two
    simp
  obtain ⟨r₀, hr₀0, hpack⟩ := white_w0_pack (-1) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (fun _ => 1) hq
  have hb : ‖(fun _ => r₀ / 2 : Point 2)‖ ≤ r₀ / 2 := by
    refine pi_norm_le_iff_of_nonneg (by linarith) |>.mpr fun i => ?_
    show ‖r₀ / 2‖ ≤ r₀ / 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₀ / 2)]
  have hxlt : ‖(fun _ => r₀ / 2 : Point 2)‖ < r₀ := lt_of_le_of_lt hb (by linarith)
  refine ⟨r₀, hr₀0, (fun _ => r₀ / 2), ?_, hxlt,
    (hpack _ hxlt).2.2.2.2.2, (hpack _ hxlt).2.2.2.2.1⟩
  intro hx0
  have h := congrFun hx0 (0 : Fin 2)
  rw [Pi.zero_apply] at h
  linarith

end QIQTH.WhiteW0

section AxiomChecks
open QIQTH.WhiteW0
#print axioms QIQTH.WhiteW0.uniformFlowPullbackMetric_entry_contDiffAt2
#print axioms QIQTH.WhiteW0.white_w0_pack
#print axioms QIQTH.WhiteW0.white_w0_contDiffAt2_gate
#print axioms QIQTH.WhiteW0.white_K1BudgetW_C2_w0Free
#print axioms QIQTH.WhiteW0.radialTransportSolve_congrOn_ball
#print axioms QIQTH.WhiteW0.white_u1_contDiffAt2_of_smooth_extension
#print axioms QIQTH.WhiteW0.white_w1_contDiffAt2_of_smooth_extension
#print axioms QIQTH.WhiteW0.white_w1_extension_of_global
#print axioms QIQTH.WhiteW0.hw0C2_global_implies_gate
#print axioms QIQTH.WhiteW0.white_w0_witness_gate
end AxiomChecks
