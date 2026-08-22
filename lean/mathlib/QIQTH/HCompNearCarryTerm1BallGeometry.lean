/-
  HCompNearCarryTerm1BallGeometry — J4-1020: the `linMult` ball-tail analogue (G2 companion for
  J4-1019's leftover linear piece) PLUS the r3/r4 "does `S'` contain a ball?" geometric reconciliation,
  toward wiring `HCompNearCarryTerm1LipschitzCancellation`'s (J4-1019) full-space G1 payoff onto `nb`'s
  actual bounded post-CoV domain `S'` (`HCompNearCarryKPrimeBaseFieldCoV.lean`, J4-1010).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM.  J4-1019's honesty firewall names two precise remaining gaps toward domain-
  restricting its full-space `hsMixed`-weighted Lipschitz bound onto `nb`'s domain: (a) a `linMult`
  analogue of J4-1018's `heatHessMult_ball_tail_le` ball-tail bound (NOT built in J4-1019); (b) whether
  `S'` (an OPAQUE `IsOpen S' ∧ x ∈ S'` set produced by `BaseSlotM1M4Assembly`'s IFT construction, NOT
  literally a `Metric.ball`) genuinely CONTAINS a concrete ball — the r3/r4 residuals of
  `HCompNearCarryKPrimeBaseFieldCoV.lean` (J4-1010).

  THIS FILE addresses BOTH, as two DECOUPLED bricks:

  ### Brick A — `linMult_ball_tail_le` (the G2 companion for `linMult`).
  Exact analogue of `HeatHessMultBallTail.heatHessMult_ball_tail_le`, now for `linMult` (J4-1019):
  `integral_add_compl` splits `linMult`'s exact-zero full-space integral
  (`integral_linMult_eq_zero`, J4-1019) into the ball region and its complement; the complement piece
  is bounded via the pointwise majorant `abs_linMult_le` (J4-1019) and the ALREADY-BANKED
  `normPow_gaussDdim_tail_le` at `k = 1` (fed the ALREADY-BANKED `oneD_absMoment1`, `ck = 3/2`) — the
  SAME route as J4-1018's `k = 0, 2` composition, one degree simpler since `linMult` is LINEAR (not
  quadratic) in `v`.

  Sympy-verified FIRST (`docs/qg_roadmap/rnc_sympy/hcomp_linmult_ball_tail_check.py`): (1) the composed
  constant from `normPow_gaussDdim_tail_le` at `k=1, ck=3/2` algebraically simplifies to a clean closed
  form; (2) the tail factor `exp(-R²/(8τ))` beats every polynomial power of `τ` as `τ → 0⁺` for FIXED
  `R > 0` (same structure as J4-1018's check (b), re-confirmed for the `1/√τ` prefactor); (3) the
  worst-case sliver integral over `τ ∈ (0,ε)` is `o(√ε)` as `ε → 0⁺` — genuinely negligible, matching
  J4-1018's check (c) pattern.

  ### Brick B — the r3/r4 geometric reconciliation: `S'` ALWAYS contains a ball, for free.
  `Point n := Fin n → ℝ` carries the Pi/SUP norm (`‖v‖ = sup_k |v k|`), while `rncRadialSq v := ∑ (v
  k)²` (`RadialDistance.lean`) is the EUCLIDEAN norm SQUARED — a genuinely DIFFERENT norm, flagged
  explicitly in J4-1018's own firewall ("Euclidean `rncRadialSq`, NOT the `Point n` Pi/sup norm").
  `norm_sq_le_rncRadialSq` bridges them: `‖v‖² ≤ rncRadialSq v` (each coordinate's square is `≤` the
  sum of ALL coordinates' squares, via `Finset.single_le_sum`, then `pi_norm_le_iff_of_nonneg` lifts
  the coordinatewise bound to the sup norm). Combined with the ELEMENTARY fact that ANY `IsOpen S'`
  with `x ∈ S'` contains SOME metric ball (`Metric.isOpen_iff`, a Mathlib one-liner — genuinely free,
  no construction needed), this gives `S'_ball_complement_subset_rncRadialSq_tail`: for ANY `IsOpen S'`
  with `x ∈ S'`, `∃ ρ > 0, S'ᶜ ⊆ {v | ρ² ≤ rncRadialSq (v - x)}` — i.e. the r3/r4 "does `S'` contain a
  ball?" question resolves UNCONDITIONALLY (every open set containing a point trivially does), and the
  Euclidean-vs-sup norm mismatch does NOT block reconciling `S'ᶜ` with the `rncRadialSq`-threshold tail
  region J4-1018/this file's ball-tail bounds are stated on.

  Consulted Sol (`gpt-5.6-sol`, high, 2026-08-23) BEFORE Lean with this exact plan: GO for Brick A + B,
  confirmed Brick B is non-circular (openness + `Metric.isOpen_iff` + the norm bridge genuinely suffice,
  no hidden gap), flagged the `n = 0` edge case in the Pi-norm lemma (robustly handled — `Fin 0 → ℝ` is
  a single point, all bounds trivially hold) and, CRITICALLY, that Brick A+B alone do NOT yet give the
  FULL domain-restricted `Amp`-weighted payoff: J4-1018/J4-1019's tail bounds are on the RAW
  `heatHessMult`/`linMult` (no `Amp` weight), while `nb`'s actual integrand needs the `Amp`-WEIGHTED
  version; and Brick B's ball is centred at the CoV base point `x`, while `heatHessMult_ball_tail_le`/
  `linMult_ball_tail_le`'s tail region is centred at `0` in the (already chart-relative) integration
  variable — reconciling the TWO requires either (i) verifying the actual `nb` integration variable is
  ALREADY `0`-centred at `x` (plausible from the CoV's own construction, `V x = 0`-type normalization,
  but NOT verified here) or (ii) a translated version of the tail bounds. NEITHER attempted in this
  file. Sol: "state Brick B as geometric infrastructure, not yet full analytic resolution."

  ## WHAT LANDS.
    • `linMult_ball_tail_le` — ★ Brick A, the `linMult` analogue of `heatHessMult_ball_tail_le`.
    • `norm_sq_le_rncRadialSq` — the Pi/sup-norm vs Euclidean-`rncRadialSq` bridge.
    • `isOpen_mem_ball_subset` — the elementary "open set containing a point contains a ball" fact
      (restated in this file's `Metric.ball`/`ρ > 0` language for direct downstream use).
    • `S'_ball_complement_subset_rncRadialSq_tail` — ★★ Brick B's PAYOFF: `IsOpen S' → x ∈ S' → ∃ ρ >
      0, S'ᶜ ⊆ {v | ρ² ≤ rncRadialSq (v - x)}`, resolving r3/r4's "does `S'` contain a ball" question
      unconditionally.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It does
  NOT compose Brick A/B with `HCompNearCarryTerm1LipschitzCancellation`'s (J4-1019) `Amp`-weighted G1
  payoff — that FULL domain-restricted composition (the "domain-restricted payoff" step of this
  dispatch's original task) is EXPLICITLY NOT attempted here: it needs (I) an `Amp`-weighted tail bound
  (raw `heatHessMult`/`linMult` tail bounds are insufficient once multiplied by a Lipschitz-but-
  unbounded `Amp`), and (II) reconciling Brick B's `x`-centred ball with the `0`-centred tail-bound
  convention (whether `nb`'s actual chart-relative integration variable is already `0`-centred at `x`
  is UNVERIFIED here). Does NOT discharge `nb`, `hCConv`, or any part of `hcomp`; does NOT address
  `Bfac`'s OTHER 3 terms (only term1/`hsMixed` infrastructure is touched); the far-carry `fb` remains
  SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypothesis, none equal to the conclusion (Brick A is a genuine new quantitative estimate; Brick B is
  a genuine new geometric bridge fact, neither a restatement of an existing banked theorem), no
  existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatHessMultBallTailBound
import QIQTH.HCompNearCarryTerm1LipschitzCancellation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation
open scoped Topology BigOperators

namespace QIQTH.HCompNearCarryTerm1BallGeometry

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### Brick A — the `linMult` ball-tail bound (G2 companion for `linMult`).
    ############################################################################### -/

/-- **★★★ `linMult_ball_tail_le` — Brick A, THE `linMult` G2 PAYOFF.**  For `τ > 0`, `R ≥ 0`, and
    `Q : Point n`, the ball-restricted `linMult` integral (the "tail" `∫_{Sᶜ} linMult` of the
    full-space exact cancellation `integral_linMult_eq_zero`, J4-1019, on the region `rncRadialSq v <
    R²`) is bounded EXPONENTIALLY SMALL in `R²/τ`:
        `|∫_{rncRadialSq v < R²} linMult τ Q v| ≤ exp(−R²/(8τ))·(√2)ⁿ·(n‖Q‖/(2τ))·(n·(3/2)·√2·√τ)`.
    Same route as `heatHessMult_ball_tail_le` (`integral_add_compl` + pointwise majorant
    `abs_linMult_le` + `normPow_gaussDdim_tail_le`), one degree simpler (`k = 1` only, via the
    ALREADY-BANKED `oneD_absMoment1`, `ck = 3/2`, vs `heatHessMult`'s `k = 0, 2`).  NOT `a₁ = R/6` — a
    DECOUPLED tail estimate for a FIXED radial threshold `R`, not yet wired to `Amp` or to `S'`. -/
theorem linMult_ball_tail_le (τ : ℝ) (hτ : 0 < τ) (R : ℝ) (Q : Point n) :
    |∫ v : Point n in {v | rncRadialSq v < R ^ 2}, linMult τ Q v|
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * ‖Q‖ / (2 * τ)) * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * Real.sqrt τ) := by
  set S : Set (Point n) := {v | R ^ 2 ≤ rncRadialSq v} with hSdef
  have hSmeas : MeasurableSet S := tailSet_measurableSet R
  have hScompl : Sᶜ = {v : Point n | rncRadialSq v < R ^ 2} := by
    ext v; simp [hSdef, not_le]
  have hL_int : Integrable (fun v : Point n => linMult τ Q v) volume := linMult_integrable τ hτ Q
  have hsplit := integral_add_compl hSmeas hL_int
  rw [hScompl] at hsplit
  have hfull0 : ∫ v : Point n, linMult τ Q v = 0 := integral_linMult_eq_zero τ hτ Q
  rw [hfull0] at hsplit
  have hball_eq_negS : ∫ v : Point n in {v | rncRadialSq v < R ^ 2}, linMult τ Q v
      = -(∫ v : Point n in S, linMult τ Q v) := by linarith [hsplit]
  rw [hball_eq_negS, abs_neg]
  have hL_int_S : Integrable (fun v : Point n => linMult τ Q v) (volume.restrict S) :=
    hL_int.restrict
  have hstep1 : |∫ v : Point n in S, linMult τ Q v|
      ≤ ∫ v : Point n in S, |linMult τ Q v| := by
    have h := norm_integral_le_integral_norm (μ := (volume.restrict S))
      (fun v : Point n => linMult τ Q v)
    simpa only [Real.norm_eq_abs] using h
  refine hstep1.trans ?_
  have hmaj_int : IntegrableOn (fun v : Point n =>
      ((n : ℝ) * ‖Q‖ / (2 * τ)) * (‖v‖ ^ 1 * gaussDdim τ v)) S volume := by
    have h1 : Integrable (fun v : Point n => ‖v‖ ^ 1 * gaussDdim τ v) volume :=
      normPow_gauss_integrable 1 (by norm_num) τ hτ
    exact (h1.const_mul _).integrableOn
  have hstep2 : ∫ v : Point n in S, |linMult τ Q v|
      ≤ ∫ v : Point n in S, ((n : ℝ) * ‖Q‖ / (2 * τ)) * (‖v‖ ^ 1 * gaussDdim τ v) := by
    refine setIntegral_mono_on (hL_int.abs.integrableOn) hmaj_int hSmeas (fun v _ => ?_)
    have hb := abs_linMult_le τ hτ Q v
    calc |linMult τ Q v| ≤ ((n : ℝ) * ‖Q‖ / (2 * τ)) * ‖v‖ * gaussDdim τ v := hb
      _ = ((n : ℝ) * ‖Q‖ / (2 * τ)) * (‖v‖ ^ 1 * gaussDdim τ v) := by ring
  refine hstep2.trans ?_
  have hCoefnn : 0 ≤ (n : ℝ) * ‖Q‖ / (2 * τ) := by positivity
  have hconst_pull : ∫ v : Point n in S, ((n : ℝ) * ‖Q‖ / (2 * τ)) * (‖v‖ ^ 1 * gaussDdim τ v)
      = ((n : ℝ) * ‖Q‖ / (2 * τ)) * (∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v) := by
    rw [← integral_const_mul]
  rw [hconst_pull]
  have hk1 : ∫ v : Point n in S, ‖v‖ ^ 1 * gaussDdim τ v
      ≤ Real.exp (-(R ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n
          * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1) :=
    normPow_gaussDdim_tail_le 1 (by norm_num) τ hτ R (3 / 2) (by norm_num)
      (by simpa using oneD_absMoment1 (2 * τ) (by positivity))
  refine (mul_le_mul_of_nonneg_left hk1 hCoefnn).trans_eq ?_
  ring

/-! ###############################################################################
    ### Brick B — r3/r4: `S'` always contains a ball, for free.
    ############################################################################### -/

/-- **`norm_sq_le_rncRadialSq` — the Pi/sup-norm vs Euclidean-`rncRadialSq` bridge.**  `‖v‖² ≤
    rncRadialSq v`: each coordinate's square is `≤` the sum of ALL coordinates' squares
    (`Finset.single_le_sum`), then `pi_norm_le_iff_of_nonneg` lifts the coordinatewise bound `|v k| ≤
    √(rncRadialSq v)` to the sup norm `‖v‖`.  Handles `n = 0` trivially (`Fin 0 → ℝ` is a single point,
    `‖v‖ = 0 = rncRadialSq v`). -/
theorem norm_sq_le_rncRadialSq (v : Point n) : ‖v‖ ^ 2 ≤ rncRadialSq v := by
  have hrnn : 0 ≤ rncRadialSq v := by
    rw [rncRadialSq]; exact Finset.sum_nonneg (fun k _ => sq_nonneg (v k))
  have hsqrtnn : 0 ≤ Real.sqrt (rncRadialSq v) := Real.sqrt_nonneg _
  have hle : ‖v‖ ≤ Real.sqrt (rncRadialSq v) := by
    rw [pi_norm_le_iff_of_nonneg hsqrtnn]
    intro k
    rw [Real.norm_eq_abs, Real.le_sqrt (abs_nonneg _) hrnn]
    have hcoord : (v k) ^ 2 ≤ rncRadialSq v := by
      rw [rncRadialSq]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ k)
    calc |v k| ^ 2 = (v k) ^ 2 := sq_abs (v k)
      _ ≤ rncRadialSq v := hcoord
  calc ‖v‖ ^ 2 ≤ (Real.sqrt (rncRadialSq v)) ^ 2 := by
        have hvnn : 0 ≤ ‖v‖ := norm_nonneg v
        nlinarith [hle, hvnn, hsqrtnn]
    _ = rncRadialSq v := Real.sq_sqrt hrnn

/-- **`isOpen_mem_ball_subset` — the elementary "open set containing a point contains a ball" fact.**
    Restated in `Metric.ball`/`ρ > 0` language for direct downstream use (`Metric.isOpen_iff`). -/
theorem isOpen_mem_ball_subset {S' : Set (Point n)} (hopen : IsOpen S') {x : Point n} (hx : x ∈ S') :
    ∃ ρ > (0 : ℝ), Metric.ball x ρ ⊆ S' :=
  Metric.isOpen_iff.mp hopen x hx

/-- **★★ `S'_ball_complement_subset_rncRadialSq_tail` — Brick B's PAYOFF, resolving r3/r4.**  For ANY
    `IsOpen S'` with `x ∈ S'` (matching `HCompNearCarryKPrimeBaseFieldCoV`'s / `BaseSlotM1M4Assembly`'s
    OPAQUE IFT-produced domain, no further structure assumed):
        `∃ ρ > 0, S'ᶜ ⊆ {v | ρ² ≤ rncRadialSq (v − x)}`.
    I.e. the r3/r4 "does `S'` contain a concrete ball?" question resolves UNCONDITIONALLY — every open
    set containing a point trivially contains SOME metric ball (`isOpen_mem_ball_subset`), and the
    Pi/sup-vs-Euclidean norm mismatch (`norm_sq_le_rncRadialSq`) does not block reconciling the
    resulting ball's complement with the `rncRadialSq`-threshold tail region `heatHessMult_ball_tail_le`
    / `linMult_ball_tail_le` are stated on.  NOT `a₁ = R/6` — geometric infrastructure ONLY: this does
    NOT yet reconcile the `x`-centring here with the `0`-centred convention of the tail bounds (a
    SEPARATE, still-open translation step), nor does it touch `Amp`-weighting. -/
theorem S'_ball_complement_subset_rncRadialSq_tail {S' : Set (Point n)} (hopen : IsOpen S')
    {x : Point n} (hx : x ∈ S') :
    ∃ ρ > (0 : ℝ), S'ᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq (v - x)} := by
  obtain ⟨ρ, hρpos, hballsub⟩ := isOpen_mem_ball_subset hopen hx
  refine ⟨ρ, hρpos, ?_⟩
  intro v hv
  by_contra hcon
  have hlt : rncRadialSq (v - x) < ρ ^ 2 := not_le.mp hcon
  apply hv
  apply hballsub
  rw [Metric.mem_ball]
  have hdist : dist v x = ‖v - x‖ := by
    rw [dist_eq_norm]
  rw [hdist]
  have hsqle : ‖v - x‖ ^ 2 ≤ rncRadialSq (v - x) := norm_sq_le_rncRadialSq (v - x)
  have hnvnn : 0 ≤ ‖v - x‖ := norm_nonneg _
  have hρnn : 0 ≤ ρ := hρpos.le
  nlinarith [hsqle, hlt, hnvnn, hρnn]

end QIQTH.HCompNearCarryTerm1BallGeometry

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1BallGeometry
#print axioms linMult_ball_tail_le
#print axioms norm_sq_le_rncRadialSq
#print axioms isOpen_mem_ball_subset
#print axioms S'_ball_complement_subset_rncRadialSq_tail
end AxiomChecks
