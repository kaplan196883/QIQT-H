/-
  GaussTauTraceCancellationInnerBall — residue (ii) of the chart-CoV route: the
  CENTER-LOCALIZED (inner-ball-only Lipschitz) `∂_τ`-TRACE moment-cancellation bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick — the follow-on to J4-922's
  `gaussian_hessian_cancel_trace_on_superset` (which needs the weight `q` to be GLOBALLY Lipschitz).
  This brick RELAXES the global-Lipschitz hypothesis to a CENTER-Lipschitz bound on an INNER BALL
  only (`|q w − q 0| ≤ L·‖w‖` for `w ∈ ball 0 r`), keeping only global boundedness/measurability
  (both cheaply satisfiable by a junk extension).  This is exactly what is needed to feed a
  transformed chart weight `q(w) = A(V w)/|det f'(V w)|` that is Lipschitz only near the chart centre.

  ## WHAT THIS DOES — AND DOES NOT — UNBLOCK (gpt-5.6-sol audit, verbatim honest).
  Residue (ii) removes the global-Lipschitz obstruction FOR THE HESSIAN(-TRACE) TERM.  It does NOT by
  itself discharge `hGpow`/`hCross`.  After the banked CoV `chart_gaussian_change_variables_concrete`
  transports the census integrand, the concrete `∂_τ` representation (`gatedTauRepProd`) has TWO
  pieces: (1) the multiplier·Gaussian·amplitude piece — which THIS brick's cancellation kills to
  `O(τ^{−1/2})`, with the CORRECT paired weight `q₁(w) = A(Vw)·F(s,·)(Vw)/|det|`; and (2) the
  zeroth-order `Cfield`(=∂_τA)·Gaussian piece, whose transformed weight `q₂(w) = Cfield(Vw)·F/|det|`
  is `O(1)` in `τ` (bounded Gaussian mass) — harmless on a bounded time horizon `0 < u−s ≤ T`
  (`O(1) ≤ (√T)·(u−s)^{−1/2}`), but a separate obligation.  So the concrete discharge STILL requires:
  a bound + a center-Lipschitz estimate for the FULL paired weight `A·F/|det|` on the inner ball
  (τ-uniform), and bounded control of the `Cfield·F/|det|` term.  NOT done here.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS.
    • `hessTrace_abs_mul_norm_integral_le` — ★ THE NEW MOMENT.  The inner `‖·‖`-weighted absolute
        trace moment:  `∫_{z:Point n} |∑ᵢ((zᵢ)²/4τ² − 1/2τ)|·gaussDdim τ z·‖z‖ ≤ n²·(16√2+1)/√τ`.
        Route: the sup-norm domination `|zᵢ| ≤ ‖z‖` collapses `|∑ᵢ((zᵢ)²−2τ)/(4τ²)| ≤ n(‖z‖²+2τ)/(4τ²)`,
        so the integrand is `≤ n/(4τ²)·‖z‖³·G + n/(2τ)·‖z‖·G`; the banked `normPow_gauss_tau`
        (fed `oneD_absMoment3`/`oneD_absMoment1`) turns `∫‖z‖ᵏG` into `n·cₖ·(√τ)ᵏ`, and the τ-powers
        collapse to `τ^{−1/2}` with constant `n²·(16√2+1)` (matching the 1-D J4-919 constant).
        NO coordinate factorization needed.
    • `gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz` — ★★ THE CENTER-LOCALIZED BOUND.
        For `τ>0`, `r>0`, `q` measurable + globally bounded (`|q|≤M`) + CENTER-Lipschitz on the inner
        ball (`∀ w∈ball 0 r, |q w − q 0| ≤ L·‖w‖`), and ANY measurable `Ω ⊇ ball 0 r`,
          `|∫_{z∈Ω} (∑ᵢ((zᵢ)²/4τ² − 1/2τ))·gaussDdim τ z·q z|`
            `≤ L·(n²·(16√2+1))/√τ  +  3·n·M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)` .
        Route (Sol's recipe): `q = (q − q 0) + q 0`; the constant part `q 0` is bounded via J4-922's
        `gaussian_hessian_cancel_trace_on_superset` at the CONSTANT weight (`L=0`) → `n·M·tail`; the
        centred part `q − q 0` is split `Ω = ball 0 r ⊍ (Ω∖ball 0 r)` — on the inner ball the
        center-Lipschitz bound gives `L·(inner moment)`, off it (`⊆ {‖z‖≥r}`) the `2M`-cap + the
        per-coord tail (`hessCoord_abs_weighted_tail_le`) gives `2·n·M·tail`.
    • `..._hyp_satisfiable` — non-vacuity EXHIBITED at a genuine bounded, CENTER-Lipschitz-but-NOT-
        globally-Lipschitz weight `q z := sin(‖z‖²)` (`|q|≤1`; `|q w − q 0| = |sin‖w‖²| ≤ ‖w‖² ≤ ‖w‖`
        on `ball 0 1`; NOT globally Lipschitz), on a PROPER superset `Ω = ball 0 5 ⊋ ball 0 1`.  This
        witnesses that the relaxation has TEETH (the old global-Lipschitz theorem does NOT apply to it).

  ⚠  STILL NOT `a₁ = R/6`.  The concrete chart wiring (transformed-weight boundedness + inner-ball
  Lipschitz of `A·F/|det|` from the banked near-identity Jacobian + resolvent Lipschitz, and the
  `Cfield·F/|det|` `O(1)` term) is the downstream assembly, NOT done here.  No `sorry`, no new axioms,
  no `:= True`, no vacuous hypothesis, none equal to the conclusion, no existing file edited.
-/
import Mathlib
import QIQTH.GaussTauTraceCancellationLocalized
import QIQTH.RemainderIntegration
import QIQTH.GaussianMomentEnvelope

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- Local continuity of the flat Gaussian (re-derived to avoid a heavy import). -/
private theorem gaussDdim_cont_local (τ : ℝ) : Continuous (fun z : Point n => gaussDdim τ z) := by
  unfold gaussDdim
  exact continuous_finsetProd _ (fun k _ => (hk_continuous τ).comp (continuous_apply k))

/-- **★ `hessTrace_abs_mul_norm_integral_le` — the inner `‖·‖`-weighted ABSOLUTE trace moment.**
    `∫_{z:Point n} |∑ᵢ((zᵢ)²/4τ² − 1/2τ)|·gaussDdim τ z·‖z‖ ≤ n²·(16√2+1)/√τ`  (`τ > 0`).
    The `τ^{−1/2}` inner-ball payoff of residue (ii).  NOT `a₁ = R/6`. -/
theorem hessTrace_abs_mul_norm_integral_le (τ : ℝ) (hτ : 0 < τ) :
    (∫ z : Point n, |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖)
      ≤ (n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
  have hτ0 : τ ≠ 0 := hτ.ne'
  have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsτ2 : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  -- Integrable envelope pieces.
  have hI3 : Integrable (fun z : Point n => ‖z‖ ^ 3 * gaussDdim τ z) volume :=
    normPow_gauss_integrable 3 (by norm_num) τ hτ
  have hI1 : Integrable (fun z : Point n => ‖z‖ ^ 1 * gaussDdim τ z) volume :=
    normPow_gauss_integrable 1 (by norm_num) τ hτ
  -- The dominator `D`.
  set D : Point n → ℝ :=
    fun z => (n : ℝ) / (4 * τ ^ 2) * (‖z‖ ^ 3 * gaussDdim τ z)
              + (n : ℝ) / (2 * τ) * (‖z‖ ^ 1 * gaussDdim τ z) with hDdef
  have hDint : Integrable D volume := by
    rw [hDdef]; exact (hI3.const_mul _).add (hI1.const_mul _)
  -- The integrand.
  set I : Point n → ℝ :=
    fun z => |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖ with hIdef
  -- Pointwise domination `I ≤ D`.
  have hpt : ∀ z : Point n, I z ≤ D z := by
    intro z
    have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    -- per-coordinate abs bound
    have hper : ∀ i : Fin n,
        |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
      intro i
      have hzi : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
      have hzi_sq : (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
        nlinarith [hzi, abs_nonneg (z i), sq_abs (z i), norm_nonneg z]
      have heq : (z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ) = ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) := by
        field_simp; ring
      rw [heq, abs_div, abs_of_pos h4τ2]
      have hnum : |(z i) ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
        rw [abs_le]; constructor <;> nlinarith [hzi_sq, hτ, sq_nonneg (z i), norm_nonneg z]
      gcongr
    have hsum : |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
        ≤ (n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)) := by
      calc |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
          ≤ ∑ i, |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
        _ = (n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hfrac_nn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) :=
      div_nonneg (by positivity) (by positivity)
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)) :=
      mul_nonneg (by positivity) hfrac_nn
    calc I z = |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖ := rfl
      _ ≤ ((n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2))) * gaussDdim τ z * ‖z‖ := by
          apply mul_le_mul_of_nonneg_right _ hzn
          exact mul_le_mul_of_nonneg_right hsum hg
      _ = D z := by rw [hDdef]; field_simp; ring
  -- Integrability of `I` (dominated by `D`).
  have hImeas : AEStronglyMeasurable I volume := by
    rw [hIdef]
    refine (((Continuous.aestronglyMeasurable ?_).mul ?_).mul continuous_norm.aestronglyMeasurable)
    · exact (continuous_finsetSum _ (fun i _ =>
        (((continuous_apply i).pow 2).div_const _).sub continuous_const)).abs
    · exact (gaussDdim_cont_local τ).aestronglyMeasurable
  have hInn : ∀ z, 0 ≤ I z := by
    intro z; rw [hIdef]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg τ z)) (norm_nonneg z)
  have hIint : Integrable I volume :=
    hDint.mono' hImeas (ae_of_all _ (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hInn z)]; exact hpt z))
  -- Integrate the domination and collapse the τ-powers.
  have hM3 : (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z) ≤ (n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3 :=
    normPow_gauss_tau 3 (by norm_num) (64 * Real.sqrt 2 + 1) (by positivity) τ hτ (oneD_absMoment3 τ hτ)
  have hM1 : (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z) ≤ (n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1 :=
    normPow_gauss_tau 1 (by norm_num) (3 / 2) (by norm_num) τ hτ (oneD_absMoment1 τ hτ)
  have hM3nn : (0 : ℝ) ≤ ∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z :=
    integral_nonneg (fun z => mul_nonneg (by positivity) (gaussDdim_nonneg τ z))
  have hM1nn : (0 : ℝ) ≤ ∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z :=
    integral_nonneg (fun z => mul_nonneg (by positivity) (gaussDdim_nonneg τ z))
  have hDeq : (∫ z, D z)
      = (n : ℝ) / (4 * τ ^ 2) * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
        + (n : ℝ) / (2 * τ) * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z) := by
    rw [hDdef, integral_add (hI3.const_mul _) (hI1.const_mul _), integral_const_mul, integral_const_mul]
  have hInt_le : (∫ z, I z) ≤ (∫ z, D z) := integral_mono hIint hDint hpt
  -- Final arithmetic.
  have hkey : (∫ z, D z) ≤ (n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1) / Real.sqrt τ := by
    rw [hDeq]
    have hc3 : (0 : ℝ) ≤ (n : ℝ) / (4 * τ ^ 2) := by positivity
    have hc1 : (0 : ℝ) ≤ (n : ℝ) / (2 * τ) := by positivity
    have hb : (n : ℝ) / (4 * τ ^ 2) * (∫ z : Point n, ‖z‖ ^ 3 * gaussDdim τ z)
              + (n : ℝ) / (2 * τ) * (∫ z : Point n, ‖z‖ ^ 1 * gaussDdim τ z)
            ≤ (n : ℝ) / (4 * τ ^ 2) * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt τ) ^ 3)
              + (n : ℝ) / (2 * τ) * ((n : ℝ) * (3 / 2) * (Real.sqrt τ) ^ 1) := by
      gcongr
    refine hb.trans (le_of_eq ?_)
    -- rewrite the τ-denominators in terms of `√τ` (do NOT touch the `√τ` factors), then clear.
    have hsne : Real.sqrt τ ≠ 0 := hsτ.ne'
    have e1 : (4 : ℝ) * τ ^ 2 = 4 * (Real.sqrt τ) ^ 2 * (Real.sqrt τ) ^ 2 := by rw [hsτ2]; ring
    have e2 : (2 : ℝ) * τ = 2 * (Real.sqrt τ) ^ 2 := by rw [hsτ2]
    rw [e1, e2]
    field_simp
    ring
  exact hInt_le.trans hkey

/-- **★★ `gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz` — THE CENTER-LOCALIZED BOUND.**
    For `τ>0`, `r>0`, `q` measurable + globally bounded (`|q|≤M`) + CENTER-Lipschitz on the inner ball
    (`∀ w∈ball 0 r, |q w − q 0| ≤ L·‖w‖`), and ANY measurable `Ω ⊇ ball 0 r`,
      `|∫_{z∈Ω} (∑ᵢ((zᵢ)²/4τ² − 1/2τ))·gaussDdim τ z·q z|`
          `≤ L·(n²·(16√2+1))/√τ  +  3·n·M·(√2)ⁿ·e^{−r²/8τ}·(2n+1)/(2τ)` .
    The global-Lipschitz hypothesis of `gaussian_hessian_cancel_trace_on_superset` is RELAXED to
    center-Lipschitz on `ball 0 r` (keeping global boundedness/measurability).  NOT `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz
    (τ r : ℝ) (hτ : 0 < τ) (hr : 0 < r) (q : Point n → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hqmeas : AEStronglyMeasurable q volume) (M : ℝ) (hM : ∀ z, |q z| ≤ M)
    (hcl : ∀ z ∈ Metric.ball (0 : Point n) r, |q z - q 0| ≤ L * ‖z‖)
    (Ω : Set (Point n)) (hΩ : MeasurableSet Ω) (hball : Metric.ball (0 : Point n) r ⊆ Ω) :
    |∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z|
      ≤ L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ
        + 3 * (n : ℝ) * M * (Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ))
            * ((2 * (n : ℝ) + 1) / (2 * τ))) := by
  set Tail : ℝ := Real.sqrt 2 ^ n * Real.exp (-(r ^ 2) / (8 * τ)) * ((2 * (n : ℝ) + 1) / (2 * τ))
    with hTaildef
  set q0 : ℝ := q 0 with hq0def
  have hM0 : |q0| ≤ M := hM 0
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  set A : Set (Point n) := Metric.ball (0 : Point n) r with hAdef
  -- Multiplier and per-coordinate summands (for integrability, mirroring J4-922).
  set g : Fin n → Point n → ℝ :=
    fun i z => ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q z with hgdef
  set gc : Fin n → Point n → ℝ :=
    fun i z => ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * q0 with hgcdef
  have hgint : ∀ i, Integrable (g i) volume := fun i => by
    rw [hgdef]; exact hess_coord_gaussDdim_q_integrable τ hτ i q hqmeas M hM
  have hgcint : ∀ i, Integrable (gc i) volume := fun i => by
    rw [hgcdef]
    exact hess_coord_gaussDdim_q_integrable τ hτ i (fun _ => q0) aestronglyMeasurable_const |q0|
      (fun z => le_refl _)
  -- The three named integrands.
  set Fq : Point n → ℝ :=
    fun z => (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z with hFqdef
  set Fc : Point n → ℝ :=
    fun z => (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q0 with hFcdef
  set Fd : Point n → ℝ :=
    fun z => (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * (q z - q0) with hFddef
  -- `Fq = ∑ g i`, `Fc = ∑ gc i`.
  have hcoord : ∀ (w : Point n → ℝ) (z : Point n),
      (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * (w z)
        = ∑ i, (((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (w z)) := by
    intro w z
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hc : (z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ) = ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) := by
      field_simp; ring
    rw [hc]
  have hFqeq : Fq = fun z => ∑ i, g i z := by
    funext z; rw [hFqdef, hgdef]; exact hcoord q z
  have hFceq : Fc = fun z => ∑ i, gc i z := by
    funext z; rw [hFcdef, hgcdef]; exact hcoord (fun _ => q0) z
  have hFqint : Integrable Fq volume := by rw [hFqeq]; exact integrable_finsetSum _ (fun i _ => hgint i)
  have hFcint : Integrable Fc volume := by rw [hFceq]; exact integrable_finsetSum _ (fun i _ => hgcint i)
  have hFdint : Integrable Fd volume := by
    have hEq : Fd = fun z => Fq z - Fc z := by
      funext z; rw [hFddef, hFqdef, hFcdef]; ring
    rw [hEq]; exact hFqint.sub hFcint
  -- `Fq = Fd + Fc` pointwise.
  have hFqsplit : Fq = fun z => Fd z + Fc z := by
    funext z; rw [hFqdef, hFddef, hFcdef]; ring
  -- Restriction integrabilities.
  have hAmeas : MeasurableSet A := measurableSet_ball
  have hdiffmeas : MeasurableSet (Ω \ A) := hΩ.diff hAmeas
  -- ═══ TERM Fc: constant weight `q0` → `n · M · Tail` via J4-922's superset theorem. ═══
  have hbound_c : |∫ z in Ω, Fc z| ≤ (n : ℝ) * M * Tail := by
    have h := gaussian_hessian_cancel_trace_on_superset τ r hτ hr (fun _ => q0)
      0 (le_refl 0) (fun z w => by simp) aestronglyMeasurable_const M (fun _ => hM0)
      Ω hΩ hball
    rw [← hTaildef] at h
    -- the const-weight integrand is defeq to `Fc`.
    calc |∫ z in Ω, Fc z|
        ≤ 0 * (15 / 2 * (n : ℝ) ^ 2) / Real.sqrt τ + (n : ℝ) * (M * Tail) := h
      _ = (n : ℝ) * M * Tail := by ring
  -- ═══ TERM Fd: split `Ω = A ⊍ (Ω∖A)`. ═══
  have hAsubΩ : A ⊆ Ω := hball
  have hunion : Ω = A ∪ (Ω \ A) := (Set.union_diff_cancel hAsubΩ).symm
  have hdisj : Disjoint A (Ω \ A) := by
    rw [Set.disjoint_left]; intro x hxA hxd; exact hxd.2 hxA
  have hFdsplit : (∫ z in Ω, Fd z) = (∫ z in A, Fd z) + (∫ z in (Ω \ A), Fd z) := by
    have hu := setIntegral_union (f := Fd) (μ := volume) hdisj hdiffmeas
      hFdint.integrableOn hFdint.integrableOn
    rw [Set.union_diff_cancel hAsubΩ] at hu
    exact hu
  -- ── inner ball bound: `≤ L · (inner moment)`.
  have hInnerMoment := hessTrace_abs_mul_norm_integral_le (n := n) τ hτ
  have hbound_A : |∫ z in A, Fd z| ≤ L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ := by
    -- `|∫_A Fd| ≤ ∫_A |Fd| ≤ ∫_A L·(|∑|·G·‖z‖) ≤ L·∫_ℝⁿ |∑|·G·‖z‖`.
    have hIeint : Integrable
        (fun z : Point n => |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) volume := by
      have hmeas : AEStronglyMeasurable
          (fun z : Point n => |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) volume := by
        refine (((Continuous.aestronglyMeasurable ?_).mul ?_).mul continuous_norm.aestronglyMeasurable)
        · exact (continuous_finsetSum _ (fun i _ =>
            (((continuous_apply i).pow 2).div_const _).sub continuous_const)).abs
        · exact (gaussDdim_cont_local τ).aestronglyMeasurable
      -- integrable via the same dominator as in the moment lemma; reuse integrability through `mono'`.
      have hI3 : Integrable (fun z : Point n => ‖z‖ ^ 3 * gaussDdim τ z) volume :=
        normPow_gauss_integrable 3 (by norm_num) τ hτ
      have hI1 : Integrable (fun z : Point n => ‖z‖ ^ 1 * gaussDdim τ z) volume :=
        normPow_gauss_integrable 1 (by norm_num) τ hτ
      have hDint : Integrable
          (fun z : Point n => (n : ℝ) / (4 * τ ^ 2) * (‖z‖ ^ 3 * gaussDdim τ z)
            + (n : ℝ) / (2 * τ) * (‖z‖ ^ 1 * gaussDdim τ z)) volume :=
        (hI3.const_mul _).add (hI1.const_mul _)
      refine hDint.mono' hmeas (ae_of_all _ (fun z => ?_))
      have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
      have hzn : 0 ≤ ‖z‖ := norm_nonneg z
      have h4τ2 : (0 : ℝ) < 4 * τ ^ 2 := by positivity
      have hval : 0 ≤ |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) hg) hzn
      rw [Real.norm_eq_abs, abs_of_nonneg hval]
      -- pointwise domination (same as moment lemma).
      have hper : ∀ i : Fin n,
          |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := by
        intro i
        have hzi : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
        have hzi_sq : (z i) ^ 2 ≤ ‖z‖ ^ 2 := by
          nlinarith [hzi, abs_nonneg (z i), sq_abs (z i), norm_nonneg z]
        have heq : (z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ) = ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) := by
          field_simp; ring
        rw [heq, abs_div, abs_of_pos h4τ2]
        have hnum : |(z i) ^ 2 - 2 * τ| ≤ ‖z‖ ^ 2 + 2 * τ := by
          rw [abs_le]; constructor <;> nlinarith [hzi_sq, hτ, sq_nonneg (z i), norm_nonneg z]
        gcongr
      have hsum : |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
          ≤ (n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)) := by
        calc |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
            ≤ ∑ i, |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
          _ = (n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hfrac_nn : (0 : ℝ) ≤ (‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2) :=
        div_nonneg (by positivity) (by positivity)
      calc |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖
          ≤ ((n : ℝ) * ((‖z‖ ^ 2 + 2 * τ) / (4 * τ ^ 2))) * gaussDdim τ z * ‖z‖ := by
            apply mul_le_mul_of_nonneg_right _ hzn
            exact mul_le_mul_of_nonneg_right hsum hg
        _ = (n : ℝ) / (4 * τ ^ 2) * (‖z‖ ^ 3 * gaussDdim τ z)
              + (n : ℝ) / (2 * τ) * (‖z‖ ^ 1 * gaussDdim τ z) := by field_simp; ring
    -- Now the chain.
    have hstep1 : |∫ z in A, Fd z| ≤ ∫ z in A, |Fd z| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict A) (f := Fd)
    have hpt_A : ∀ z ∈ A, |Fd z|
        ≤ L * (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) := by
      intro z hz
      have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
      have hql : |q z - q0| ≤ L * ‖z‖ := by rw [hq0def]; exact hcl z hz
      rw [hFddef]
      calc |(∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * (q z - q0)|
          = |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * |q z - q0| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hg]
        _ ≤ |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * (L * ‖z‖) := by
            apply mul_le_mul_of_nonneg_left hql
            exact mul_nonneg (abs_nonneg _) hg
        _ = L * (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) := by ring
    have hstep2 : (∫ z in A, |Fd z|)
        ≤ ∫ z in A, L * (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) := by
      refine setIntegral_mono_on hFdint.abs.integrableOn (hIeint.const_mul L).integrableOn hAmeas hpt_A
    have hstep3 : (∫ z in A, L * (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖))
        = L * ∫ z in A, (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) :=
      integral_const_mul _ _
    have hstep4 : (∫ z in A, (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖))
        ≤ ∫ z : Point n, (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) := by
      refine setIntegral_le_integral hIeint (ae_of_all _ (fun z => ?_))
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (gaussDdim_nonneg τ z)) (norm_nonneg z)
    calc |∫ z in A, Fd z|
        ≤ ∫ z in A, |Fd z| := hstep1
      _ ≤ L * ∫ z in A, (|∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * ‖z‖) := by
          rw [← hstep3]; exact hstep2
      _ ≤ L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1) / Real.sqrt τ) :=
          mul_le_mul_of_nonneg_left (hstep4.trans hInnerMoment) hL
      _ = L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ := by ring
  -- ── outer bound: `Ω∖A ⊆ {r ≤ ‖z‖}`, `2M`-cap + per-coord tail.
  have hcompl_sub : (Ω \ A) ⊆ {z : Point n | r ≤ ‖z‖} := by
    intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    exact hz.2 (by rw [hAdef]; exact mem_ball_zero_iff.mpr h)
  have hRHSint : ∀ i, Integrable
      (fun z : Point n => 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)|) volume :=
    fun i => (((hess_coord_gaussDdim_q_integrable τ hτ i (fun _ => (1 : ℝ)) aestronglyMeasurable_const 1
      (fun _ => abs_one.le)).abs).const_mul (2 * M))
  have hbound_OA : |∫ z in (Ω \ A), Fd z| ≤ 2 * (n : ℝ) * M * Tail := by
    have hstep1 : |∫ z in (Ω \ A), Fd z| ≤ ∫ z in (Ω \ A), |Fd z| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ω \ A)) (f := Fd)
    -- pointwise `|Fd| ≤ ∑ i, 2M·|hessCoord i · G · 1|`.
    have hpt_OA : ∀ z ∈ (Ω \ A), |Fd z|
        ≤ ∑ i, 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| := by
      intro z _
      have hg : 0 ≤ gaussDdim τ z := gaussDdim_nonneg τ z
      have hq2M : |q z - q0| ≤ 2 * M := by
        have htri : |q z - q0| ≤ |q z| + |q0| := by
          calc |q z - q0| = |q z + (-q0)| := by rw [sub_eq_add_neg]
            _ ≤ |q z| + |(-q0)| := abs_add_le _ _
            _ = |q z| + |q0| := by rw [abs_neg]
        calc |q z - q0| ≤ |q z| + |q0| := htri
          _ ≤ M + M := add_le_add (hM z) hM0
          _ = 2 * M := by ring
      -- per-coordinate: `|hm_i|·G = |hessCoord_i · G · 1|`.
      have hcoord_eq : ∀ i : Fin n,
          |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| * gaussDdim τ z
            = |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| := by
        intro i
        have heq : (z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ) = ((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) := by
          field_simp; ring
        rw [heq, mul_one, abs_mul, abs_of_nonneg hg]
      rw [hFddef]
      have habs : |(∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * (q z - q0)|
          = |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * |q z - q0| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hg]
      rw [habs]
      have hsumG_nn : 0 ≤ |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z :=
        mul_nonneg (abs_nonneg _) hg
      calc |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * |q z - q0|
          ≤ |∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * gaussDdim τ z * (2 * M) :=
            mul_le_mul_of_nonneg_left hq2M hsumG_nn
        _ ≤ (∑ i, |(z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)|) * gaussDdim τ z * (2 * M) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hg
        _ = ∑ i, 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| := by
            rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hcoord_eq i]; ring
    have hstep2 : (∫ z in (Ω \ A), |Fd z|)
        ≤ ∫ z in (Ω \ A), ∑ i, 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| :=
      setIntegral_mono_on hFdint.abs.integrableOn
        (integrable_finsetSum _ (fun i _ => hRHSint i)).integrableOn hdiffmeas hpt_OA
    have hstep3 : (∫ z in (Ω \ A), ∑ i, 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)|)
        = ∑ i, ∫ z in (Ω \ A), 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| :=
      integral_finsetSum _ (fun i _ => (hRHSint i).integrableOn)
    have hstep4 : (∑ i, ∫ z in (Ω \ A), 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)|)
        ≤ ∑ _i : Fin n, 2 * M * Tail := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [integral_const_mul]
      have hcb := hessCoord_abs_weighted_tail_le τ r hτ hr.le i (fun _ => (1 : ℝ))
        aestronglyMeasurable_const 1 (fun _ => abs_one.le) (Ω \ A) hdiffmeas hcompl_sub
      rw [one_mul, ← hTaildef] at hcb
      exact mul_le_mul_of_nonneg_left hcb (by positivity)
    calc |∫ z in (Ω \ A), Fd z|
        ≤ ∫ z in (Ω \ A), |Fd z| := hstep1
      _ ≤ ∑ i, ∫ z in (Ω \ A), 2 * M * |((z i) ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (1 : ℝ)| :=
          hstep2.trans (le_of_eq hstep3)
      _ ≤ ∑ _i : Fin n, 2 * M * Tail := hstep4
      _ = 2 * (n : ℝ) * M * Tail := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- ═══ combine. ═══
  have hFq_goal : (∫ z in Ω, (∑ i, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * gaussDdim τ z * q z)
      = ∫ z in Ω, Fq z := rfl
  rw [hFq_goal]
  have hΩsplit : (∫ z in Ω, Fq z) = (∫ z in Ω, Fd z) + (∫ z in Ω, Fc z) := by
    rw [hFqsplit]
    exact integral_add hFdint.integrableOn hFcint.integrableOn
  calc |∫ z in Ω, Fq z|
      = |(∫ z in Ω, Fd z) + (∫ z in Ω, Fc z)| := by rw [hΩsplit]
    _ ≤ |∫ z in Ω, Fd z| + |∫ z in Ω, Fc z| := abs_add_le _ _
    _ ≤ (|∫ z in A, Fd z| + |∫ z in (Ω \ A), Fd z|) + |∫ z in Ω, Fc z| := by
        gcongr
        rw [hFdsplit]; exact abs_add_le _ _
    _ ≤ (L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + 2 * (n : ℝ) * M * Tail)
          + (n : ℝ) * M * Tail :=
        add_le_add (add_le_add hbound_A hbound_OA) hbound_c
    _ = L * ((n : ℝ) ^ 2 * (16 * Real.sqrt 2 + 1)) / Real.sqrt τ + 3 * (n : ℝ) * M * Tail := by ring

/-- **Non-vacuity witness.**  The hypothesis bundle is jointly satisfiable at a genuine bounded,
    CENTER-Lipschitz-but-NOT-globally-Lipschitz weight `q z := sin(‖z‖²)` (`|q|≤1`; on `ball 0 1`,
    `|q z − q 0| = |sin‖z‖²| ≤ ‖z‖² ≤ ‖z‖`, so center-Lipschitz `L=1`; globally the modulus grows so
    it is NOT globally Lipschitz), on a PROPER superset `Ω = ball 0 5 ⊋ ball 0 1` (`r = 1`).  This
    exhibits that the relaxation has TEETH: `gaussian_hessian_cancel_trace_on_superset` does NOT apply
    to `q`.  NOT `a₁ = R/6`. -/
theorem gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz_hyp_satisfiable :
    ∃ (r : ℝ) (q : Point n → ℝ) (L M : ℝ) (Ω : Set (Point n)),
      0 < r ∧ 0 ≤ L ∧ AEStronglyMeasurable q (volume : Measure (Point n)) ∧ (∀ z, |q z| ≤ M) ∧
        (∀ z ∈ Metric.ball (0 : Point n) r, |q z - q 0| ≤ L * ‖z‖) ∧
        MeasurableSet Ω ∧ Metric.ball (0 : Point n) r ⊆ Ω := by
  refine ⟨1, fun z => Real.sin (‖z‖ ^ 2), 1, 1, Metric.ball (0 : Point n) 5,
    one_pos, zero_le_one, ?_, ?_, ?_, measurableSet_ball, ?_⟩
  · exact (Real.continuous_sin.comp ((continuous_norm.pow 2))).aestronglyMeasurable
  · intro z; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  · intro z hz
    have hz1 : ‖z‖ < 1 := by rw [← dist_zero_right]; exact Metric.mem_ball.mp hz
    have hzn : 0 ≤ ‖z‖ := norm_nonneg z
    have h0 : (Real.sin (‖(0 : Point n)‖ ^ 2)) = 0 := by simp
    have hsinabs : |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := by
      rcases eq_or_ne (‖z‖ ^ 2) 0 with h | h
      · rw [h]; simp
      · exact (Real.abs_sin_lt_abs h).le
    show |Real.sin (‖z‖ ^ 2) - Real.sin (‖(0 : Point n)‖ ^ 2)| ≤ 1 * ‖z‖
    rw [h0, sub_zero, one_mul]
    calc |Real.sin (‖z‖ ^ 2)| ≤ |‖z‖ ^ 2| := hsinabs
      _ = ‖z‖ ^ 2 := abs_of_nonneg (by positivity)
      _ ≤ ‖z‖ := by nlinarith [hz1, hzn]
  · exact Metric.ball_subset_ball (by norm_num)

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms hessTrace_abs_mul_norm_integral_le
#print axioms gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz
#print axioms gaussian_hessian_cancel_trace_on_superset_of_center_lipschitz_hyp_satisfiable
end AxiomChecks
