/-
  WhiteOffDiag — J4-623: the whitened `hpkgBound` OFF-DIAGONAL layer.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: the chart→ambient naturality transfer of this bound (J4-624, scoped in §5 below) +
  `hEbound`/`hInt` at the transport kernel + the `K1TransportBudget` + the fat-`K` carrier piles +
  the capstone co-instantiation at the whitened witness + the prior analytic piles.

  ── ★ ITEM (1): THE OFF-DIAGONAL GAUSSIAN DOMINATION OF THE WHITENED CHART DEFECT.
    • `whiteChart_heatOp_offdiag_bound` — for the whitened chart metric pair `(ĝ_q, ĝ⁻¹_q)`
      (J4-621/622) there are ONE radius `r₀ > 0` and ONE constant `C ≥ 0` with
          `|heatOp ĝ_q ĝ⁻¹_q (flat phase G) τ x 0| ≤ C · G_{2τ}(x)`
      for EVERY row `q ∈ K`, EVERY `τ > 0` (a fortiori all `τ ∈ (0,1]`) and every chart point
      `‖x‖ < r₀` — THE (hpkgBound)-shape bound the as-built witness provably LACKS
      (`flatPhase_hpkgBound_fails`, J4-621) and the whitened chart family satisfies.
      MECHANISM (the globalized CenterZero ledger):
        (a) the EXACT normal form (banked `flatCurvatureResidue_leading`, valid for ANY pair):
            `heatOp = (1/τ)·G·[½·tr(ĝ⁻¹−δ) − ½·Σ ĝ⁻¹·Γ̂·x] + (1/τ²)·G·[−¼·Σ (ĝ⁻¹−δ)·xx]`;
        (b) dev × Hessian: `|ĝ⁻¹(x)−δ| ≤ M·‖x‖²` at EVERY row (the J4-622 whitened replay,
            `whitePullbackMetricInv_dev_uniform` — quadratic at every `q`, not just `q = 0`) eats
            both the `1/τ` trace floor (k = 1) and the `1/τ²` quadratic (k = 2);
        (c) Christoffel × gradient: the NEW linear decay `|Γ̂(x)| ≤ C_Γ·‖x‖` (built here:
            `whitePullbackMetric_pd_linear_uniform` — the banked frame-free first jet `∂ĝ(0)=0`
            + the uniform C² packet, composed through `E_q` — feeding
            `whiteChart_christoffel_linear_uniform`), so `Γ̂·∂G ~ (‖x‖²/τ)·G` (k = 1);
        (d) widths: the banked absorption levers `gaussDdim_absorb_one`/`_two`
            (`(r²/τ)^k·G_τ ≤ C·G_{2τ}`, GaussianWidthTransfer) — the widening `τ → 2τ` is where
            the polynomial-in-`1/τ` prefactors are PAID, exactly accounted.
      ⚠ GATE (honest): the bound is stated on the chart gate `‖x‖ < r₀` — the region where the
      quadratic dev bound holds; off the gate the gated witness is cut off by construction (the
      banked gate machinery), so the on-gate bound is the analytically meaningful layer.  The
      column is the chart center (`y = 0`): each ambient row `q` carries its OWN chart, so
      quantifying over `q ∈ K` and `x` IS the general-row per-chart form.
    • `whiteChart_heatOp_offdiag_bound_amp` — the same bound for the AMPLITUDE-carrying kernel
      `√det g^κ(q) · (flat phase G)` (= the whitened witness Gaussian `whiteW` in chart velocity,
      `whiteW_eq_det_mul_gaussDdim`), with the `√det` paid by the det bounds of item (3).

  ── ITEM (2): CHART→AMBIENT NATURALITY — LANDED PIECE + PRECISE SCOPE (J4-624).
    • `whiteExp_fderiv` (landed) — the whitened chart Jacobian chain
      `D(whiteExp_q) w = D(uniformFlowExp_q)(E_q w) ∘ E_q` — the first ingredient of the weld.
    • ⚠ SCOPED (NOT here): the naturality identity for the whitened chart,
          `Δ_{ĝ_q}(f ∘ whiteExp_q)(w) = (Δ_{g^κ} f)(whiteExp_q w)`,
      via the banked general engine `laplaceBeltrami_pullback_naturality_local`
      (PullbackNaturalityLocal) at `φ := whiteExp_q`, which needs:
        (i)  `IsUnit (fderiv ℝ (whiteExp_q) w)` — from `whiteExp_fderiv` (here) +
             `uniformFlowExp_common_nondeg_radius` (banked) + invertibility of `E_q` (from the
             banked two-sided bound `whiteVel_radialSq_ge`);
        (ii) `pullbackMet g^κ (whiteExp_q) = ĝ_q` — BANKED (J4-622,
             `whitePullbackMetric_eq_fderiv_pullback`);
        (iii) the two-sided entrywise inverse `ĝ⁻¹_q·ĝ_q = δ = ĝ_q·ĝ⁻¹_q` on the gate — from the
             banked Neumann package `whitePullbackMetric_neumann` (`IsUnit` + `Ring.inverse`).
      This is a genuine but bounded weld (no new analysis) — the labelled J4-624 residue.

  ── ITEM (3): THE `√det` AMPLITUDE BOOKKEEPING.
    • `curvedRNC_det_bounds_on_ball` — explicit two-sided det control on the fat ball:
      `1 ≤ det g^κ(q) ≤ (1 − (κ/3)·n·r²)^{n−1}` for `q ∈ closedBall 0 r` (`κ ≤ 0`), from the
      banked exact rank-one formula `curvedRNCMetric_det` (CurvedRNCVanVleckBound).
    • `curvedRNC_sqrtDet_bounds_on_ball`, `whiteW_flat_comparable_on_ball` — the whitened witness
      Gaussian is two-sidedly comparable to the flat Gaussian, uniformly over the fat ball:
      `G_τ(w) ≤ whiteW_q(τ,w) ≤ √((1 − (κ/3)·n·r²)^{n−1}) · G_τ(w)`.

  ── NON-VACUITY (cp466 discipline): `whiteOffDiag_witness_gate` — the ★ bound is INSTANTIATED at
  the genuinely curved fat witness (`n = 2`, `κ = −1`, `K = closedBall 0 2`) where (i) the AMBIENT
  flat-phase pair provably admits NO such bound (the J4-621 pin, same witness), and (ii) the frame
  change is genuinely non-identity (`whiteVel_nondegenerate`) — the whitened bound is not the flat
  tower in disguise, and it holds exactly where the as-built bound provably fails.

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.WhiteReplay
import QIQTH.ParametrixFlatCurvatureResidue
import QIQTH.CurvedRNCVanVleckBound

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterN1 QIQTH.EquivProbe
open QIQTH.CConvV2GaussianPairing QIQTH.GaussianWidthTransfer
open QIQTH.FrozenGauss QIQTH.LeviSeries QIQTH.WhiteWitness QIQTH.WhiteReplay
open QIQTH.CurvedRNCVanVleckBound
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.WhiteOffDiag

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 0. The abstract absolute-value assembly of the `(1/τ) + (1/τ²)` normal form. -/

/-- **The pure-arithmetic assembly**: if the two normal-form coefficients satisfy
    `|S₁| ≤ c_A·r²` and `|S₂| ≤ c_B·(r²)²`, and the width levers absorb `(r²/τ)^k·G ≤ CL_k·G₂`,
    then `|(1/τ)·G·S₁ + (1/τ²)·G·S₂| ≤ (c_A·CL₁ + c_B·CL₂)·G₂`.  Separated from the calculus. -/
theorem normalform_abs_bound (τ G G2 S1 S2 r2 cA cB CL1 CL2 : ℝ)
    (hτ : 0 < τ) (hG : 0 < G) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hS1 : |S1| ≤ cA * r2) (hS2 : |S2| ≤ cB * r2 ^ 2)
    (hlev1 : r2 / τ * G ≤ CL1 * G2) (hlev2 : (r2 / τ) ^ 2 * G ≤ CL2 * G2) :
    |1 / τ * G * S1 + 1 / τ ^ 2 * G * S2| ≤ (cA * CL1 + cB * CL2) * G2 := by
  have hτG : 0 ≤ 1 / τ * G := by positivity
  have hτG2 : 0 ≤ 1 / τ ^ 2 * G := by positivity
  have ha : |1 / τ * G * S1| ≤ cA * (CL1 * G2) := by
    rw [abs_mul, abs_of_nonneg hτG]
    calc 1 / τ * G * |S1| ≤ 1 / τ * G * (cA * r2) := mul_le_mul_of_nonneg_left hS1 hτG
      _ = cA * (r2 / τ * G) := by ring
      _ ≤ cA * (CL1 * G2) := mul_le_mul_of_nonneg_left hlev1 hcA
  have hb : |1 / τ ^ 2 * G * S2| ≤ cB * (CL2 * G2) := by
    rw [abs_mul, abs_of_nonneg hτG2]
    calc 1 / τ ^ 2 * G * |S2| ≤ 1 / τ ^ 2 * G * (cB * r2 ^ 2) :=
          mul_le_mul_of_nonneg_left hS2 hτG2
      _ = cB * ((r2 / τ) ^ 2 * G) := by ring
      _ ≤ cB * (CL2 * G2) := mul_le_mul_of_nonneg_left hlev2 hcB
  calc |1 / τ * G * S1 + 1 / τ ^ 2 * G * S2|
      ≤ |1 / τ * G * S1| + |1 / τ ^ 2 * G * S2| := abs_add_le _ _
    _ ≤ cA * (CL1 * G2) + cB * (CL2 * G2) := add_le_add ha hb
    _ = (cA * CL1 + cB * CL2) * G2 := by ring

/-! ### 1. The base gradient decay: `‖D g̃_q(v)‖ ≤ M·‖v‖`, uniform over `q ∈ K` (frame-free). -/

/-- **The frame-free uniform gradient decay of the per-`q` chart metric**: ONE radius, ONE
    constant with `‖fderiv (g̃_q)ᵢⱼ (v)‖ ≤ M·‖v‖` for all `q ∈ K`, `‖v‖ ≤ r₀`.  The banked
    frame-free first jet `∂g̃_q(0) = 0` (`uniformFlowPullbackMetric_pd_zero_center`) + the uniform
    C² packet (`uniformFlowPullbackMetric_c2_uniform_full`) through the mean-value gradient decay
    (`fderiv_decay`, RNCDecay).  NOT `a₁ = R/6`. -/
theorem uniformFlow_fderiv_linear_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ i j : Fin n,
      ‖fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) v‖ ≤ M * ‖v‖ := by
  obtain ⟨r₁, hr₁0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₁ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro q hq v hv i j
  set f : Point n → ℝ := fun w => uniformFlowPullbackMetric g gi hC hK q w i j with hf
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₁ / 2) → ‖w‖ < r₁ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have h0mem : ‖(0 : Point n)‖ < r₁ := by rw [norm_zero]; exact hr₁0
  have hdf0 : fderiv ℝ f 0 = 0 :=
    fderiv_zero_of_pd_zero ((hpk q hq 0 h0mem i j).1.differentiableAt)
      (fun e => uniformFlowPullbackMetric_pd_zero_center g gi hC hK hg hgsymm hinvF q hq i j e)
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₁ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w :=
    fun w hw => (hpk q hq w (hballs w hw) i j).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₁ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M :=
    fun w hw => le_trans (hpk q hq w (hballs w hw) i j).2.2.2.2 (le_max_right _ _)
  have hmem : v ∈ Metric.closedBall (0 : Point n) (r₁ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv
  exact fderiv_decay f (max 0 M) (r₁ / 2) (by positivity) hdf0 hdiff2 hbound2 hmem

/-! ### 2. The whitened first-derivative decay: `|∂ĝ_q(x)| ≤ C·‖x‖` at EVERY row. -/

/-- **★ The whitened metric first-derivative linear decay, uniform over `q ∈ K`**:
    `|∂ₑ ĝ_q(x)ᵢⱼ| ≤ C·‖x‖` on a uniform gate — the base gradient decay composed through the
    whitening `E_q` (entry contraction `|E_q| ≤ 1`, `√n` velocity confinement, chain rule through
    the continuous linear `E_q`).  This is the Christoffel-decay engine: the whitened Christoffels
    vanish at the chart origin at every row and grow at most linearly.  NOT `a₁ = R/6`. -/
theorem whitePullbackMetric_pd_linear_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ x : Point n, ‖x‖ ≤ r₀ → ∀ i j e : Fin n,
      |pd (fun w => whitePullbackMetric κ hκ hKc q w i j) e x| ≤ C * ‖x‖ := by
  classical
  obtain ⟨r₁, hr₁0, M₁, hM₁0, hfd⟩ :=
    uniformFlow_fderiv_linear_uniform (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
  obtain ⟨r₂, hr₂0, M₂, hpk⟩ :=
    uniformFlowPullbackMetric_c2_uniform_full (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun a b => curvedRNCMetric_contDiff κ a b) (curvedRNC_hChr κ hκ) hKc
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set ρ : ℝ := min r₁ r₂ with hρdef
  have hρ0 : 0 < ρ := lt_min hr₁0 hr₂0
  refine ⟨ρ / (Real.sqrt n + 1), by positivity,
    (n : ℝ) ^ 2 * (Real.sqrt n * M₁),
    mul_nonneg (by positivity) (mul_nonneg hsn hM₁0), ?_⟩
  intro q hq x hx i j e
  -- velocity confinement into the base radii
  have hEx_norm : ‖whiteVel κ q x‖ ≤ Real.sqrt n * ‖x‖ := whiteVel_norm_le κ hκ q x
  have hEx_lt : ‖whiteVel κ q x‖ < ρ := by
    have h1 : Real.sqrt n * ‖x‖ ≤ Real.sqrt n * (ρ / (Real.sqrt n + 1)) :=
      mul_le_mul_of_nonneg_left hx hsn
    have h2 : Real.sqrt n * (ρ / (Real.sqrt n + 1)) < ρ := by
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [hρ0]
    linarith
  have hEx_r₁ : ‖whiteVel κ q x‖ ≤ r₁ := le_of_lt (lt_of_lt_of_le hEx_lt (min_le_left _ _))
  have hEx_r₂ : ‖whiteVel κ q x‖ < r₂ := lt_of_lt_of_le hEx_lt (min_le_right _ _)
  -- the whitening as a continuous linear map
  set E : Point n →L[ℝ] Point n := matToCLM (curvedWhitening κ q) with hE
  have hEfun : ∀ v : Point n, E v = whiteVel κ q v := by
    intro v; funext k
    rw [hE, matToCLM_apply]
    rfl
  -- component-level suppliers at the whitened velocity
  have hdF : ∀ k l : Fin n, DifferentiableAt ℝ
      (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q v k l) (E x) := by
    intro k l
    rw [hEfun x]
    exact (hpk q hq (whiteVel κ q x) hEx_r₂ k l).1.differentiableAt
  have hcomp : ∀ k l : Fin n,
      (fun w => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l)
      = (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v k l) ∘ ⇑E := by
    intro k l
    funext v
    rw [Function.comp_apply, hEfun v]
  have hcompdiff : ∀ k l : Fin n, DifferentiableAt ℝ
      (fun w => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l) x := by
    intro k l
    rw [hcomp k l]
    exact (hdF k l).comp x E.differentiableAt
  -- ‖E eₑ‖ ≤ 1 (entry contraction)
  have hEs : ‖E (Pi.single e (1 : ℝ))‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro a
    rw [hEfun (Pi.single e (1 : ℝ)), Real.norm_eq_abs,
      curvedWhitening_eq_whiteVel_single κ q a e]
    exact curvedWhitening_entry_abs_le_one κ hκ q a e
  -- the composed pd bound
  have hpd_comp : ∀ k l : Fin n,
      |pd (fun w => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l) e x|
      ≤ Real.sqrt n * M₁ * ‖x‖ := by
    intro k l
    have hval : pd (fun w => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l) e x
        = (fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q v k l) (E x)) (E (Pi.single e 1)) := by
      rw [hcomp k l]
      rw [pd_eq_fderiv _ e x ((hdF k l).comp x E.differentiableAt)]
      rw [fderiv_comp x (hdF k l) E.differentiableAt, E.fderiv,
        ContinuousLinearMap.comp_apply]
    have hLn : ‖fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ)
        (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q v k l) (E x)‖
        ≤ M₁ * (Real.sqrt n * ‖x‖) := by
      rw [hEfun x]
      calc ‖fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q v k l) (whiteVel κ q x)‖
          ≤ M₁ * ‖whiteVel κ q x‖ := hfd q hq (whiteVel κ q x) hEx_r₁ k l
        _ ≤ M₁ * (Real.sqrt n * ‖x‖) := mul_le_mul_of_nonneg_left hEx_norm hM₁0
    rw [hval]
    calc |(fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q v k l) (E x)) (E (Pi.single e 1))|
        = ‖(fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q v k l) (E x)) (E (Pi.single e 1))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fun v => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q v k l) (E x)‖ * ‖E (Pi.single e (1 : ℝ))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M₁ * (Real.sqrt n * ‖x‖)) * 1 :=
          mul_le_mul hLn hEs (norm_nonneg _)
            (mul_nonneg hM₁0 (mul_nonneg hsn (norm_nonneg _)))
      _ = Real.sqrt n * M₁ * ‖x‖ := by ring
  -- pd through the double sum
  have hPdTerm : ∀ k l : Fin n, PdiffAt
      (fun w => curvedWhitening κ q i k
        * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e x := fun k l =>
    QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ e x
      (((differentiableAt_const _).mul (hcompdiff k l)).mul (differentiableAt_const _))
  have hPdInner : ∀ k : Fin n, PdiffAt
      (fun w => ∑ l, curvedWhitening κ q i k
        * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e x := fun k =>
    PdiffAt_sum Finset.univ _ e x fun l _ => hPdTerm k l
  have hterm : ∀ k l : Fin n,
      |pd (fun w => curvedWhitening κ q i k
        * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e x| ≤ Real.sqrt n * M₁ * ‖x‖ := by
    intro k l
    have hshape : (fun w => curvedWhitening κ q i k
        * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteVel κ q w) k l
        * curvedWhitening κ q l j)
        = (fun w => (curvedWhitening κ q i k * curvedWhitening κ q l j)
          * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
              hKc q (whiteVel κ q w) k l) := funext fun w => by ring
    rw [hshape, pd_const_mul _ _ e x
      (QIQTH.LaplaceBeltrami.pdiffAt_of_differentiableAt _ e x (hcompdiff k l))]
    rw [abs_mul]
    have hc : |curvedWhitening κ q i k * curvedWhitening κ q l j| ≤ 1 := by
      rw [abs_mul]
      have h1 := curvedWhitening_entry_abs_le_one κ hκ q i k
      have h2 := curvedWhitening_entry_abs_le_one κ hκ q l j
      nlinarith [abs_nonneg (curvedWhitening κ q i k), abs_nonneg (curvedWhitening κ q l j)]
    calc |curvedWhitening κ q i k * curvedWhitening κ q l j|
          * |pd (fun w => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l) e x|
        ≤ 1 * (Real.sqrt n * M₁ * ‖x‖) :=
          mul_le_mul hc (hpd_comp k l) (abs_nonneg _) zero_le_one
      _ = Real.sqrt n * M₁ * ‖x‖ := by ring
  simp only [whitePullbackMetric]
  rw [pd_sum Finset.univ _ e x fun k _ => hPdInner k]
  calc |∑ k, pd (fun w => ∑ l, curvedWhitening κ q i k
        * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteVel κ q w) k l
        * curvedWhitening κ q l j) e x|
      ≤ ∑ k, |pd (fun w => ∑ l, curvedWhitening κ q i k
          * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
              hKc q (whiteVel κ q w) k l
          * curvedWhitening κ q l j) e x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ((n : ℝ) * (Real.sqrt n * M₁ * ‖x‖)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [pd_sum Finset.univ _ e x fun l _ => hPdTerm k l]
        calc |∑ l, pd (fun w => curvedWhitening κ q i k
              * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                  (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
              * curvedWhitening κ q l j) e x|
            ≤ ∑ l, |pd (fun w => curvedWhitening κ q i k
                * uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                    (curvedRNC_hChr κ hκ) hKc q (whiteVel κ q w) k l
                * curvedWhitening κ q l j) e x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l : Fin n, (Real.sqrt n * M₁ * ‖x‖) :=
              Finset.sum_le_sum fun l _ => hterm k l
          _ = (n : ℝ) * (Real.sqrt n * M₁ * ‖x‖) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) ^ 2 * (Real.sqrt n * M₁) * ‖x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### 3. The whitened Christoffel linear decay. -/

/-- **★ The whitened Christoffel bound `|Γ̂ᵏᵢⱼ(x)| ≤ C_Γ·‖x‖`, uniform over `q ∈ K`** — the
    first-derivative linear decay (§2) contracted against the bounded whitened inverse metric
    (from the J4-622 replayed dev bound).  The whitened Christoffels vanish at the chart origin
    at EVERY row and grow at most linearly on the gate — the globalized J4-605 pattern.
    NOT `a₁ = R/6`. -/
theorem whiteChart_christoffel_linear_uniform (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ x : Point n, ‖x‖ < r₀ → ∀ k i j : Fin n,
      |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| ≤ C * ‖x‖ := by
  classical
  obtain ⟨r₁, hr₁0, M₁, hM₁0, hdev⟩ := whitePullbackMetricInv_dev_uniform κ hκ hKc
  obtain ⟨r₂, hr₂0, C₂, hC₂0, hpd⟩ := whitePullbackMetric_pd_linear_uniform κ hκ hKc
  set r₀ : ℝ := min r₁ r₂ with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 hr₂0
  set Gb : ℝ := 1 + M₁ * ((n : ℝ) * r₀ ^ 2) with hGbdef
  have hGb0 : 0 ≤ Gb := add_nonneg zero_le_one (mul_nonneg hM₁0 (by positivity))
  refine ⟨r₀, hr₀0, 3 / 2 * (n : ℝ) * (Gb * C₂),
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (mul_nonneg hGb0 hC₂0), ?_⟩
  intro q hq x hx k i j
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ ≤ r₂ := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
  have hr2b : rncRadialSq x ≤ (n : ℝ) * r₀ ^ 2 := by
    refine rncRadialSq_le_of_mem_closedBall (q := x) (r := r₀) ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.le
  -- the whitened inverse entries are bounded
  have hgib : ∀ a b : Fin n, |whitePullbackMetricInv κ hκ hKc q x a b| ≤ Gb := by
    intro a b
    have hd := hdev q hq x hx1 a b
    have hδ : |(if a = b then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases h : a = b <;> simp [h]
    have htri : |whitePullbackMetricInv κ hκ hKc q x a b|
        ≤ |whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0)|
          + |(if a = b then (1 : ℝ) else 0)| := by
      calc |whitePullbackMetricInv κ hκ hKc q x a b|
          = |(whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0))
              + (if a = b then (1 : ℝ) else 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hmono : M₁ * rncRadialSq x ≤ M₁ * ((n : ℝ) * r₀ ^ 2) :=
      mul_le_mul_of_nonneg_left hr2b hM₁0
    calc |whitePullbackMetricInv κ hκ hKc q x a b|
        ≤ M₁ * rncRadialSq x + 1 := by linarith [htri, hd, hδ]
      _ ≤ Gb := by rw [hGbdef]; linarith
  -- the three-pd triangle
  have hpd3 : ∀ α : Fin n,
      |pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
        + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x
        - pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x| ≤ 3 * (C₂ * ‖x‖) := by
    intro α
    have h1 := hpd q hq x hx2 α j i
    have h2 := hpd q hq x hx2 α i j
    have h3 := hpd q hq x hx2 i j α
    have ht1 : |pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
        + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x|
        ≤ |pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x|
          + |pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x| := abs_add_le _ _
    have ht2 : |pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
        + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x
        - pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x|
        ≤ |pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
            + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x|
          + |pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x| := by
      rw [sub_eq_add_neg]
      calc _ ≤ _ + |-pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith
  -- assemble
  simp only [christoffel]
  rw [abs_mul]
  have hhalf : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
  rw [hhalf]
  calc (1 : ℝ) / 2 * |∑ α, whitePullbackMetricInv κ hκ hKc q x k α
        * (pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
          + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x
          - pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x)|
      ≤ 1 / 2 * ∑ α, |whitePullbackMetricInv κ hκ hKc q x k α
          * (pd (fun y => whitePullbackMetric κ hκ hKc q y α j) i x
            + pd (fun y => whitePullbackMetric κ hκ hKc q y α i) j x
            - pd (fun y => whitePullbackMetric κ hκ hKc q y i j) α x)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 1 / 2 * ∑ _α : Fin n, Gb * (3 * (C₂ * ‖x‖)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => ?_) (by norm_num)
        rw [abs_mul]
        exact mul_le_mul (hgib k α) (hpd3 α) (abs_nonneg _) hGb0
    _ = 3 / 2 * (n : ℝ) * (Gb * C₂) * ‖x‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### 4. ★ THE OFF-DIAGONAL BOUND. -/

/-- **★★ J4-623 capstone — the whitened off-diagonal Gaussian domination.**  For the whitened
    chart metric pair `(ĝ_q, ĝ⁻¹_q)`, ONE gate radius `r₀ > 0` and ONE constant `C ≥ 0` with
        `|heatOp ĝ_q ĝ⁻¹_q (flat phase G) τ x 0| ≤ C · gaussDdim (2τ) x`
    for EVERY `q ∈ K`, EVERY `τ > 0` and every `‖x‖ < r₀` — the (hpkgBound)-shape bound the
    as-built witness provably LACKS (`flatPhase_hpkgBound_fails`) and the whitened family HAS:
    the CenterZero mechanism (J4-612) globalized to every row.  Ledger: the exact normal form
    (`flatCurvatureResidue_leading`, banked) exposes `(1/τ)`- and `(1/τ²)`-orders; the whitened
    quadratic dev (`whitePullbackMetricInv_dev_uniform`, J4-622, NO frame hypotheses) bounds the
    trace floor and the Hessian-deviation quadratic; the NEW whitened Christoffel linear decay
    (§3) bounds the gradient contraction; the banked width levers `gaussDdim_absorb_one/_two`
    absorb `(r²/τ)^k` into the widened Gaussian `G_{2τ}`.  Stated for all `τ > 0`, a fortiori on
    `(0,1]`.  NOT `a₁ = R/6`. -/
theorem whiteChart_heatOp_offdiag_bound (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ x : Point n, ‖x‖ < r₀ →
      |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)|
      ≤ C * gaussDdim (2 * τ) x := by
  classical
  obtain ⟨r₁, hr₁0, M₁, hM₁0, hdev⟩ := whitePullbackMetricInv_dev_uniform κ hκ hKc
  obtain ⟨rΓ, hrΓ0, CΓ, hCΓ0, hΓ⟩ := whiteChart_christoffel_linear_uniform κ hκ hKc
  obtain ⟨CL1, hCL1, hlev1⟩ :=
    gaussDdim_absorb_one (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CL2, hCL2, hlev2⟩ :=
    gaussDdim_absorb_two (n := n) (η := 0) (lam := 2) (by norm_num) (by norm_num) (by norm_num)
  set r₀ : ℝ := min r₁ rΓ with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 hrΓ0
  set Gb : ℝ := 1 + M₁ * ((n : ℝ) * r₀ ^ 2) with hGbdef
  have hGb0 : 0 ≤ Gb := add_nonneg zero_le_one (mul_nonneg hM₁0 (by positivity))
  set cA : ℝ := 1 / 2 * ((n : ℝ) * M₁) + 1 / 2 * ((n : ℝ) ^ 3 * (Gb * CΓ)) with hcAdef
  set cB : ℝ := 1 / 4 * ((n : ℝ) ^ 2 * M₁) with hcBdef
  have hcA0 : 0 ≤ cA :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hM₁0))
      (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (mul_nonneg hGb0 hCΓ0)))
  have hcB0 : 0 ≤ cB := mul_nonneg (by norm_num) (mul_nonneg (by positivity) hM₁0)
  refine ⟨r₀, hr₀0, cA * CL1 + cB * CL2,
    add_nonneg (mul_nonneg hcA0 hCL1.le) (mul_nonneg hcB0 hCL2.le), ?_⟩
  intro q hq τ hτ x hx
  have hx1 : ‖x‖ < r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxΓ : ‖x‖ < rΓ := lt_of_lt_of_le hx (min_le_right _ _)
  have hG : 0 < gaussDdim τ x := gaussDdim_pos τ hτ x
  -- rewrite the heat operator into the flat-Gaussian normal form
  have hK1 : (fun u => flatPhaseModel u x (0 : Point n)) = (fun u => gaussDdim u x) := by
    funext u
    simp only [flatPhaseModel]
    congr 1
    funext i
    simp
  have hK2 : (fun p => flatPhaseModel τ p (0 : Point n)) = gaussDdim τ := by
    funext p
    simp only [flatPhaseModel]
    congr 1
    funext i
    simp
  have hexpr : heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
      (fun w => whitePullbackMetricInv κ hκ hKc q w)
      (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)
      = deriv (fun s => gaussDdim s x) τ
        - laplaceBeltrami (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) (gaussDdim τ) x := by
    simp only [heatOp]
    rw [hK1, hK2]
  have hlead := flatCurvatureResidue_leading τ hτ
    (fun w => whitePullbackMetric κ hκ hKc q w)
    (fun w => whitePullbackMetricInv κ hκ hKc q w) x
  rw [hexpr, hlead]
  -- the geometric radial data
  have hr2b : rncRadialSq x ≤ (n : ℝ) * r₀ ^ 2 := by
    refine rncRadialSq_le_of_mem_closedBall (q := x) (r := r₀) ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx.le
  have hdev' : ∀ i j : Fin n,
      |whitePullbackMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)|
        ≤ M₁ * rncRadialSq x := fun i j => hdev q hq x hx1 i j
  have hxk : ∀ k : Fin n, |x k| ≤ Real.sqrt (rncRadialSq x) :=
    fun k => QIQTH.FrozenDefect.abs_apply_le_sqrt_radialSq x k
  have hxn : ‖x‖ ≤ Real.sqrt (rncRadialSq x) := by
    have h := norm_le_rncRadial x
    simpa only [rncRadial] using h
  have hxk_prod : ∀ k : Fin n, ‖x‖ * |x k| ≤ rncRadialSq x := by
    intro k
    calc ‖x‖ * |x k| ≤ Real.sqrt (rncRadialSq x) * Real.sqrt (rncRadialSq x) :=
          mul_le_mul hxn (hxk k) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq x := Real.mul_self_sqrt (rncRadialSq_nonneg x)
  have hxij : ∀ i j : Fin n, |x i * x j| ≤ rncRadialSq x := by
    intro i j
    rw [abs_mul]
    calc |x i| * |x j| ≤ Real.sqrt (rncRadialSq x) * Real.sqrt (rncRadialSq x) :=
          mul_le_mul (hxk i) (hxk j) (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = rncRadialSq x := Real.mul_self_sqrt (rncRadialSq_nonneg x)
  -- bounded whitened inverse entries
  have hgib : ∀ a b : Fin n, |whitePullbackMetricInv κ hκ hKc q x a b| ≤ Gb := by
    intro a b
    have hd := hdev' a b
    have hδ : |(if a = b then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases h : a = b <;> simp [h]
    have htri : |whitePullbackMetricInv κ hκ hKc q x a b|
        ≤ |whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0)|
          + |(if a = b then (1 : ℝ) else 0)| := by
      calc |whitePullbackMetricInv κ hκ hKc q x a b|
          = |(whitePullbackMetricInv κ hκ hKc q x a b - (if a = b then (1 : ℝ) else 0))
              + (if a = b then (1 : ℝ) else 0)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hmono : M₁ * rncRadialSq x ≤ M₁ * ((n : ℝ) * r₀ ^ 2) :=
      mul_le_mul_of_nonneg_left hr2b hM₁0
    calc |whitePullbackMetricInv κ hκ hKc q x a b| ≤ M₁ * rncRadialSq x + 1 := by
          linarith [htri, hd, hδ]
      _ ≤ Gb := by rw [hGbdef]; linarith
  -- T1: the trace deviation
  have hT1 : |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
      ≤ (n : ℝ) * (M₁ * rncRadialSq x) := by
    calc |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
        ≤ ∑ i, |whitePullbackMetricInv κ hκ hKc q x i i - 1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, M₁ * rncRadialSq x := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hdev' i i
          rw [if_pos rfl] at h
          exact h
      _ = (n : ℝ) * (M₁ * rncRadialSq x) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- T2: the Christoffel contraction
  have hΓ' : ∀ k i j : Fin n,
      |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| ≤ CΓ * ‖x‖ :=
    fun k i j => hΓ q hq x hxΓ k i j
  have hT2term : ∀ i j k : Fin n,
      |whitePullbackMetricInv κ hκ hKc q x i j
        * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
        * x k| ≤ Gb * (CΓ * rncRadialSq x) := by
    intro i j k
    rw [abs_mul, abs_mul]
    have hbc : |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
        ≤ CΓ * rncRadialSq x := by
      calc |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
          ≤ (CΓ * ‖x‖) * |x k| :=
            mul_le_mul_of_nonneg_right (hΓ' k i j) (abs_nonneg _)
        _ = CΓ * (‖x‖ * |x k|) := by ring
        _ ≤ CΓ * rncRadialSq x := mul_le_mul_of_nonneg_left (hxk_prod k) hCΓ0
    calc |whitePullbackMetricInv κ hκ hKc q x i j|
          * |christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|
        = |whitePullbackMetricInv κ hκ hKc q x i j|
          * (|christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x| * |x k|) := by ring
      _ ≤ Gb * (CΓ * rncRadialSq x) :=
          mul_le_mul (hgib i j) hbc
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hGb0
  have hT2 : |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
      * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
          (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
      * x k| ≤ (n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x)) := by
    calc |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
          * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
          * x k|
        ≤ ∑ i, |∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
            * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
            * x k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ((n : ℝ) ^ 2 * (Gb * (CΓ * rncRadialSq x))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc |∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                    (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                * x k|
              ≤ ∑ j, |∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                  * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                      (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                  * x k| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _j : Fin n, ((n : ℝ) * (Gb * (CΓ * rncRadialSq x))) := by
                refine Finset.sum_le_sum fun j _ => ?_
                calc |∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                      * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                          (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                      * x k|
                    ≤ ∑ k, |whitePullbackMetricInv κ hκ hKc q x i j
                        * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                            (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                        * x k| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ _k : Fin n, (Gb * (CΓ * rncRadialSq x)) :=
                      Finset.sum_le_sum fun k _ => hT2term i j k
                  _ = (n : ℝ) * (Gb * (CΓ * rncRadialSq x)) := by
                      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                        nsmul_eq_mul]
            _ = (n : ℝ) ^ 2 * (Gb * (CΓ * rncRadialSq x)) := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring
      _ = (n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- S1: the 1/τ coefficient
  have hS1 : |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))
      - 1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
          * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
              (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
          * x k)| ≤ cA * rncRadialSq x := by
    have hsplit : |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))
        - 1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
            * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
            * x k)|
        ≤ 1 / 2 * |∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1)|
          + 1 / 2 * |∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
              * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                  (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
              * x k| := by
      rw [sub_eq_add_neg]
      calc _ ≤ |1 / 2 * (∑ i, (whitePullbackMetricInv κ hκ hKc q x i i - 1))|
            + |-(1 / 2 * (∑ i, ∑ j, ∑ k, whitePullbackMetricInv κ hκ hKc q x i j
                * christoffel (fun w => whitePullbackMetric κ hκ hKc q w)
                    (fun w => whitePullbackMetricInv κ hκ hKc q w) k i j x
                * x k))| := abs_add_le _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_mul]; norm_num
    calc _ ≤ _ := hsplit
      _ ≤ 1 / 2 * ((n : ℝ) * (M₁ * rncRadialSq x))
          + 1 / 2 * ((n : ℝ) ^ 3 * (Gb * (CΓ * rncRadialSq x))) := by
          have h1 := mul_le_mul_of_nonneg_left hT1 (by norm_num : (0:ℝ) ≤ 1 / 2)
          have h2 := mul_le_mul_of_nonneg_left hT2 (by norm_num : (0:ℝ) ≤ 1 / 2)
          linarith
      _ = cA * rncRadialSq x := by rw [hcAdef]; ring
  -- S2: the 1/τ² coefficient
  have hS2 : |(-1) / 4 * (∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
      - (if i = j then (1 : ℝ) else 0)) * (x i * x j))| ≤ cB * rncRadialSq x ^ 2 := by
    rw [abs_mul]
    have hq14 : |(-1 : ℝ) / 4| = 1 / 4 := by norm_num
    rw [hq14]
    have hD : |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
        - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
        ≤ (n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x) := by
      calc |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
            - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
          ≤ ∑ i, |∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
              - (if i = j then (1 : ℝ) else 0)) * (x i * x j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ((n : ℝ) * (M₁ * rncRadialSq x * rncRadialSq x)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc |∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
                  - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
                ≤ ∑ j, |(whitePullbackMetricInv κ hκ hKc q x i j
                    - (if i = j then (1 : ℝ) else 0)) * (x i * x j)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _j : Fin n, (M₁ * rncRadialSq x * rncRadialSq x) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  rw [abs_mul]
                  exact mul_le_mul (hdev' i j) (hxij i j) (abs_nonneg _)
                    (mul_nonneg hM₁0 (rncRadialSq_nonneg x))
              _ = (n : ℝ) * (M₁ * rncRadialSq x * rncRadialSq x) := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc (1 : ℝ) / 4 * |∑ i, ∑ j, (whitePullbackMetricInv κ hκ hKc q x i j
          - (if i = j then (1 : ℝ) else 0)) * (x i * x j)|
        ≤ 1 / 4 * ((n : ℝ) ^ 2 * (M₁ * rncRadialSq x * rncRadialSq x)) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
      _ = cB * rncRadialSq x ^ 2 := by rw [hcBdef]; ring
  -- the width levers
  have hlev1' : rncRadialSq x / τ * gaussDdim τ x ≤ CL1 * gaussDdim (2 * τ) x :=
    hlev1 τ hτ x x (by rw [sub_zero, one_mul])
  have hlev2' : (rncRadialSq x / τ) ^ 2 * gaussDdim τ x ≤ CL2 * gaussDdim (2 * τ) x :=
    hlev2 τ hτ x x (by rw [sub_zero, one_mul])
  -- assemble
  exact normalform_abs_bound τ (gaussDdim τ x) (gaussDdim (2 * τ) x) _ _ (rncRadialSq x)
    cA cB CL1 CL2 hτ hG hcA0 hcB0 hS1 hS2 hlev1' hlev2'

/-! ### 5. Item (2): the chart→ambient Jacobian chain (landed piece) + the J4-624 scope. -/

/-- **The whitened chart Jacobian chain**: on the flow gate,
    `D(whiteExp_q) w = D(uniformFlowExp_q)(E_q w) ∘ E_q` — the first ingredient of the
    chart→ambient naturality weld.  ⚠ SCOPE (J4-624, NOT here): the naturality identity
    `Δ_{ĝ_q}(f ∘ whiteExp_q) = (Δ_{g^κ} f) ∘ whiteExp_q` via the banked
    `laplaceBeltrami_pullback_naturality_local` at `φ := whiteExp_q`, needing additionally
    (i) `IsUnit (fderiv ℝ (whiteExp_q) w)` (from this lemma + the banked
    `uniformFlowExp_common_nondeg_radius` + invertibility of `E_q` from
    `whiteVel_radialSq_ge`), (ii) the banked identification
    `whitePullbackMetric_eq_fderiv_pullback` (J4-622), and (iii) the entrywise two-sided
    inverse from the banked Neumann package `whitePullbackMetric_neumann`.  NOT `a₁ = R/6`. -/
theorem whiteExp_fderiv (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖whiteVel κ q w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) :
    fderiv ℝ (whiteExp κ hκ hKc q) w
      = (fderiv ℝ (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) (whiteVel κ q w)).comp
        (matToCLM (curvedWhitening κ q)) := by
  set F : Point n → Point n :=
    uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q with hF
  set E : Point n →L[ℝ] Point n := matToCLM (curvedWhitening κ q) with hE
  have hEfun : ∀ v : Point n, E v = whiteVel κ q v := by
    intro v; funext k
    rw [hE, matToCLM_apply]
    rfl
  have hcomp : whiteExp κ hκ hKc q = F ∘ ⇑E := by
    funext v
    rw [Function.comp_apply, hEfun v]
    rfl
  have hdiffF : DifferentiableAt ℝ F (E w) := by
    rw [hEfun w]
    exact (contDiffAt2_uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q hq (whiteVel κ q w) hw).differentiableAt (by norm_num)
  rw [hcomp, fderiv_comp w hdiffF E.differentiableAt, E.fderiv, hEfun w]

/-! ### 6. Item (3): the `√det` amplitude bookkeeping. -/

/-- **Two-sided determinant control on the fat ball** — explicit constants:
    `1 ≤ det g^κ(q) ≤ (1 − (κ/3)·n·r²)^{n−1}` for `q ∈ closedBall 0 r`, `κ ≤ 0`.  A ball-shaped
    corollary of the banked exact rank-one determinant (`curvedRNCMetric_det`).
    NOT `a₁ = R/6`. -/
theorem curvedRNC_det_bounds_on_ball (κ : ℝ) (hκ : κ ≤ 0) {r : ℝ} (q : Point n)
    (hq : q ∈ Metric.closedBall (0 : Point n) r) :
    1 ≤ Matrix.det (curvedRNCMetric κ q)
      ∧ Matrix.det (curvedRNCMetric κ q) ≤ (1 - κ / 3 * ((n : ℝ) * r ^ 2)) ^ (n - 1) :=
  ⟨curvedRNCMetric_det_ge_one κ hκ q,
    curvedRNCMetric_det_le κ hκ q ((n : ℝ) * r ^ 2) (rncRadialSq_le_of_mem_closedBall hq)⟩

/-- The `√det` version: `1 ≤ √det g^κ(q) ≤ √((1 − (κ/3)·n·r²)^{n−1})` on the fat ball. -/
theorem curvedRNC_sqrtDet_bounds_on_ball (κ : ℝ) (hκ : κ ≤ 0) {r : ℝ} (q : Point n)
    (hq : q ∈ Metric.closedBall (0 : Point n) r) :
    1 ≤ Real.sqrt (Matrix.det (curvedRNCMetric κ q))
      ∧ Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        ≤ Real.sqrt ((1 - κ / 3 * ((n : ℝ) * r ^ 2)) ^ (n - 1)) := by
  obtain ⟨h1, h2⟩ := curvedRNC_det_bounds_on_ball κ hκ q hq
  constructor
  · rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt h1
  · exact Real.sqrt_le_sqrt h2

/-- **The whitened witness Gaussian is two-sidedly flat-comparable on the fat ball**:
    `G_τ(w) ≤ whiteW_q(τ,w) ≤ √((1 − (κ/3)·n·r²)^{n−1}) · G_τ(w)` — the `√det` amplitude
    bookkeeping in witness form (via the exact phase transfer `whiteW_eq_det_mul_gaussDdim`).
    NOT `a₁ = R/6`. -/
theorem whiteW_flat_comparable_on_ball (κ : ℝ) (hκ : κ ≤ 0) {r : ℝ} (q : Point n)
    (hq : q ∈ Metric.closedBall (0 : Point n) r) (τ : ℝ) (hτ : 0 < τ) (w : Point n) :
    gaussDdim τ w ≤ whiteW κ q τ w
      ∧ whiteW κ q τ w
        ≤ Real.sqrt ((1 - κ / 3 * ((n : ℝ) * r ^ 2)) ^ (n - 1)) * gaussDdim τ w := by
  obtain ⟨h1, h2⟩ := curvedRNC_sqrtDet_bounds_on_ball κ hκ q hq
  have hG : 0 < gaussDdim τ w := gaussDdim_pos τ hτ w
  rw [whiteW_eq_det_mul_gaussDdim κ hκ q τ w]
  constructor
  · calc gaussDdim τ w = 1 * gaussDdim τ w := (one_mul _).symm
      _ ≤ Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ w :=
        mul_le_mul_of_nonneg_right h1 hG.le
  · exact mul_le_mul_of_nonneg_right h2 hG.le

/-- **★ The amplitude-carrying off-diagonal bound** — the ★ bound for the kernel
    `√det g^κ(q) · (flat phase G)`, i.e. the whitened witness Gaussian `whiteW` written in the
    chart velocity (`whiteW_eq_det_mul_gaussDdim`): the `√det` prefactor is paid by the fat-ball
    determinant bound (item 3), giving one uniform constant over `K ⊆ closedBall 0 R`.
    NOT `a₁ = R/6`. -/
theorem whiteChart_heatOp_offdiag_bound_amp (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ x : Point n, ‖x‖ < r₀ →
      |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * flatPhaseModel t x y)
        τ x (0 : Point n)|
      ≤ C * gaussDdim (2 * τ) x := by
  obtain ⟨r₀, hr₀0, C, hC0, hmain⟩ := whiteChart_heatOp_offdiag_bound κ hκ hKc
  refine ⟨r₀, hr₀0, Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) * C,
    mul_nonneg (Real.sqrt_nonneg _) hC0, ?_⟩
  intro q hq τ hτ x hx
  set c : ℝ := Real.sqrt (Matrix.det (curvedRNCMetric κ q)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcle : c ≤ Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) :=
    (curvedRNC_sqrtDet_bounds_on_ball κ hκ q (hKb hq)).2
  -- pull the constant through the heat operator
  have hcont : ContDiff ℝ ⊤ (fun p => flatPhaseModel τ p (0 : Point n)) := by
    have hK2 : (fun p => flatPhaseModel τ p (0 : Point n)) = gaussDdim τ := by
      funext p
      simp only [flatPhaseModel]
      congr 1
      funext i
      simp
    rw [hK2]
    exact QIQTH.HeatParametrixOrder.gaussDdim_contDiff τ
  have hsplit : heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
      (fun w => whitePullbackMetricInv κ hκ hKc q w)
      (fun t x y => c * flatPhaseModel t x y) τ x (0 : Point n)
      = c * heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
          (fun w => whitePullbackMetricInv κ hκ hKc q w)
          (fun t x y => flatPhaseModel t x y) τ x (0 : Point n) := by
    simp only [heatOp]
    have hderiv : deriv (fun u => c * flatPhaseModel u x (0 : Point n)) τ
        = c * deriv (fun u => flatPhaseModel u x (0 : Point n)) τ :=
      deriv_const_mul_field c
    have hlap : laplaceBeltrami (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun p => c * flatPhaseModel τ p (0 : Point n)) x
        = c * laplaceBeltrami (fun w => whitePullbackMetric κ hκ hKc q w)
            (fun w => whitePullbackMetricInv κ hκ hKc q w)
            (fun p => flatPhaseModel τ p (0 : Point n)) x :=
      laplaceBeltrami_const_mul _ _ c _ x hcont
    rw [hderiv, hlap]
    ring
  rw [hsplit, abs_mul, abs_of_nonneg hc0]
  have hmain' := hmain q hq τ hτ x hx
  have hCG : 0 ≤ C * gaussDdim (2 * τ) x :=
    mul_nonneg hC0 (gaussDdim_pos (2 * τ) (by linarith) x).le
  calc c * |heatOp (fun w => whitePullbackMetric κ hκ hKc q w)
        (fun w => whitePullbackMetricInv κ hκ hKc q w)
        (fun t x y => flatPhaseModel t x y) τ x (0 : Point n)|
      ≤ c * (C * gaussDdim (2 * τ) x) := mul_le_mul_of_nonneg_left hmain' hc0
    _ ≤ Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) * (C * gaussDdim (2 * τ) x) :=
        mul_le_mul_of_nonneg_right hcle hCG
    _ = Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) * C * gaussDdim (2 * τ) x := by
        ring

/-! ### 7. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- **★ The witness gate**: at the genuinely curved fat witness (`n = 2`, `κ = −1`,
    `K = closedBall 0 2`), (i) the whitened chart pair SATISFIES the off-diagonal
    (hpkgBound)-shape bound; (ii) the AMBIENT flat-phase pair at the SAME witness provably
    admits NO such bound (the J4-621 formal pin); (iii) the whitening frame is genuinely
    non-identity there.  The whitened bound holds exactly where the as-built one provably fails,
    at a genuinely curved instantiation — neither statement vacuous.  NOT `a₁ = R/6`. -/
theorem whiteOffDiag_witness_gate :
    (∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ Metric.closedBall (0 : Point 2) 2, ∀ τ : ℝ, 0 < τ → ∀ x : Point 2, ‖x‖ < r₀ →
        |heatOp (fun w => whitePullbackMetric (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) q w)
          (fun w => whitePullbackMetricInv (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) q w)
          (fun t x y => flatPhaseModel t x y) τ x (0 : Point 2)|
        ≤ C * gaussDdim (2 * τ) x)
    ∧ (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ p q : Point 2,
        |heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
            (fun t x y => flatPhaseModel t x y) τ p q|
          ≤ C * gaussDdim (2 * τ) (fun i => p i - q i))
    ∧ whiteVel (-1 : ℝ) probeQ probeW 0 ≠ probeW 0 :=
  ⟨whiteChart_heatOp_offdiag_bound (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2),
    flatPhase_hpkgBound_fails_witness,
    whiteVel_nondegenerate⟩

end QIQTH.WhiteOffDiag

section AxiomChecks
open QIQTH.WhiteOffDiag
#print axioms QIQTH.WhiteOffDiag.normalform_abs_bound
#print axioms QIQTH.WhiteOffDiag.uniformFlow_fderiv_linear_uniform
#print axioms QIQTH.WhiteOffDiag.whitePullbackMetric_pd_linear_uniform
#print axioms QIQTH.WhiteOffDiag.whiteChart_christoffel_linear_uniform
#print axioms QIQTH.WhiteOffDiag.whiteChart_heatOp_offdiag_bound
#print axioms QIQTH.WhiteOffDiag.whiteExp_fderiv
#print axioms QIQTH.WhiteOffDiag.curvedRNC_det_bounds_on_ball
#print axioms QIQTH.WhiteOffDiag.curvedRNC_sqrtDet_bounds_on_ball
#print axioms QIQTH.WhiteOffDiag.whiteW_flat_comparable_on_ball
#print axioms QIQTH.WhiteOffDiag.whiteChart_heatOp_offdiag_bound_amp
#print axioms QIQTH.WhiteOffDiag.whiteOffDiag_witness_gate
end AxiomChecks
