/-
  HCompNearCarryTerm1DomainRestrictedSliverWindowBound — J4-1072: completes J4-1071's frontier item 3
  composition for `Bfac`'s FOURTH and last remaining summand, `T1` (`hsMixed·A`) — composing
  `HCompNearCarryTerm1DomainRestrictedBound`'s (J4-1023) `W''S'`-domain-restricted, fixed-`τ` bound with
  the outer-`s`-sliver-window integration technique, closing the SAME gap J4-1071 closed for
  LEFTOVER/T2/T3.  Sol (`gpt-5.6-sol`, high, 2026-08-23) GO-confirmed the exact 4-branch composition plan
  below before Lean construction.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE 4-BRANCH TRACE (confirmed by tracing J4-1023's `HCompNearCarryTerm1DomainRestrictedBound.lean`
  literally, BEFORE any Lean here).  T1's domain-restricted fixed-`τ` bound
  (`hsMixed_gaussDdim_mul_amp_domain_restricted_bound`) has shape
      FullSpaceG1(τ) + TailCorrection(τ),      TailCorrection(τ) := heatHessMultTail(τ) + linMultTail(τ)
  via the SAME triangle-inequality split `hsMixed_amp_subset_tail_le` used internally by J4-1023 itself
  (`|hsMixed tail| ≤ |heatHessMult tail| + |linMult tail|`).  `FullSpaceG1(τ) = C1/√τ + C2` is the
  ALREADY-composed shape from J4-1065 (`hsMixed_gaussDdim_mul_amp_lipschitz_bound`, unaffected by domain
  restriction).  The two tail pieces split into FOUR monomial branches total:
    • `heatHessMultTail(τ)` (from `heatHessMult_amp_subset_tail_le`'s RHS bracket) — an `|Amp0|`-branch
      of order `τ^{-1}` (`(1/(4τ²))·(n·2·(√2)²·τ) + 1/(2τ) = (2n+1)/(2τ)`) and an `L`-branch of order
      `τ^{-1/2}` (`(1/(4τ²))·(n·(64√2+1)·(√2)³·τ^{3/2}) + (1/(2τ))·(n·(3/2)·√2·√τ)`), each multiplied by
      `exp(-ρ²/8τ)`.  NEITHER branch matches `grTerm_tail_le_of_sliver`'s (J4-1071) shape — this file's
      NEW lemma `heatHessMult_tail_le_of_sliver` is required.
    • `linMultTail(τ)` (from `linMult_amp_subset_tail_le`'s RHS) — ALGEBRAICALLY IDENTICAL to
      `grTerm_tail_le_of_sliver`'s LHS (same `Q`/`Amp0`/`L` structure, `τ^{-1/2}` and `τ^0` branches
      after the `1/(2τ)` prefactor is absorbed) — REUSED VERBATIM, no new lemma.
  So the "4 branches (heatHessMult ⊕ linMult)" flagged in J4-1071's docstring are: heatHessMult's
  `Amp0`-branch (`τ^{-1}`), heatHessMult's `L`-branch (`τ^{-1/2}`), linMult's `Amp0`-branch (`τ^{-1/2}`),
  linMult's `L`-branch (`τ^0`) — TWO handled by a NEW lemma here, TWO reused from J4-1071.

  ## THE FIX (SAME technique as J4-1071, one power worse but still dominated).  Quadratic exponential
  domination `exp(-(ρ²/8)/τ) ≤ 256·exp(-2)·τ²/ρ⁴` (`exp_neg_div_le_quadratic`, J4-1071) turns
  `exp(-ρ²/8τ)·τ^{-1}` into `O(τ)` (→0) and `exp(-ρ²/8τ)·τ^{-1/2}` into `O(τ^{3/2})` (→0) — BOTH strictly
  weaker singularities than the `τ^{-2}` the quadratic bound was built to dominate, so the SAME lemma
  suffices with no strengthening.  Sol GO-confirmed this exact algebra (τ^{-1}→O(τ), τ^{-1/2}→O(τ^{3/2}))
  before Lean, flagging it as "a half-power more singular than the corresponding grTerm branches [but]
  that does not affect the argument."

  ## THE COMPOSITION.  After folding BOTH tail pieces into a single τ-INDEPENDENT `TailBound(ε)`
  (bounded on `(0,ε]` by monotonicity `τ ≤ ε`/`τ·√τ ≤ ε·√ε`, Sol-confirmed the standard step), the WHOLE
  domain-restricted bound at fixed `τ ∈ (0,ε]` is `FullSpaceG1(τ) + TailBound(ε) = C1/√τ + (C2 +
  TailBound(ε))` — EXACTLY `pointwise_bound_sliver_window_inv_sqrt`'s (J4-1065) accepted `C1/√τ + C2'`
  shape, with `C2' := C2 + TailBound(ε)` (an `ε`-dependent but `τ`/`s`-independent constant, valid since
  the same `S'`/`ρ` witnesses are reused for every `τ` in the sliver — J4-1023's own capstone already
  guarantees this: its witnesses `S',ρ` do not depend on `τ`).  NO new generic window lemma needed.

  ## WHAT LANDS.
    • `heatHessMult_tail_le_of_sliver` — ★★ the NEW quadratic-domination bound for `heatHessMult`'s tail
      (the two branches `grTerm_tail_le_of_sliver` does not cover).
    • `hsMixed_domain_restricted_sliver_window_bound` — ★★★★★ THE T1 CAPSTONE, completing J4-1069's
      frontier item 3 for ALL FOUR of `Bfac`'s summands: `∃ S' ρ, IsOpen S' ∧ q₀∈S' ∧ 0<ρ ∧
      |∫ s in (t-ε)..t, ∫_{W''S'} G_{t-s}·(hsMixed·Amp)| ≤ 2·C1·√ε + C2'·ε = O(√ε)` — MEETING (not
      beating) `hcomp`'s required rate, matching T1's full-space-only rate from J4-1065.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  With this
  file, J4-1069's frontier item 3 (outer-`s`-integration ⊕ `W''S'`-domain-restriction composition) is
  CLOSED for ALL FOUR of `Bfac`'s summands (LEFTOVER/T2/T3 via J4-1071, T1 here) — but this does NOT
  close item 1 (the literal `∂ⱼA`/`∂ᵢA`/`∂ⱼ∂ᵢA` globalization and `Bfac(V w)/|det(fderiv W (V w))|`
  composed-regularity gap, flagged unchanged by J4-1023/J4-1071, UNCHANGED here too — `Amp`/`L` remain
  ABSTRACT, not the literal chart-composed amplitude), does NOT discharge `hxmem` (the shared upstream
  architectural wall gating ALL FOUR `Bfac` summands equally, UNCHANGED), does NOT sum the four terms'
  bounds into a single combined `Bfac` estimate (a separate triangle-inequality assembly, NOT attempted
  here), does NOT discharge `hfac`'s literal carry over `S'` (residuals r1/r2 of
  `HCompNearCarryKPrimeBaseFieldCoV`, UNCHANGED), and does NOT discharge `nb`, `hCConv`, or any part of
  `hcomp`.  The far-carry `fb` remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous/unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  Non-vacuity: every theorem's hypotheses are satisfiable by concrete test data (e.g.
  `Amp := 0`/`L := 0`/`PI := 0`/`PJ := 0`/`Q := 0`), and no theorem's hypothesis set is equal to its
  conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1DomainRestrictedBound
import QIQTH.HCompNearCarryTerm1SliverWindowBound
import QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.HeatHessMoment
open QIQTH.HeatHessMultBallTail QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.ExpMap
open QIQTH.HCompNearCarryTerm1AmpWeightedTail QIQTH.HCompNearCarryTerm1BallGeometry
open QIQTH.HerrHminGeneralQ0GeneralK QIQTH.BaseSlotM1M4ImageOpen
open QIQTH.HCompNearCarryTerm1DomainRestrictedBound
open QIQTH.HCompNearCarryTerm1SliverWindowBound
open QIQTH.HCompNearCarryBfacSliverWindowDomainRestricted
open scoped Topology BigOperators Interval

namespace QIQTH.HCompNearCarryTerm1DomainRestrictedSliverWindowBound

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### PART 1 — the NEW quadratic-domination bound for `heatHessMult`'s tail.
    ############################################################################### -/

/-- **★★ `heatHessMult_tail_le_of_sliver`** — for `τ ∈ (0,ε]`, `heatHessMult`'s complement-tail
    correction (from `heatHessMult_amp_subset_tail_le`, J4-1023) is bounded by a `τ`-INDEPENDENT
    constant, via `exp_neg_div_le_quadratic` (J4-1071) dominating its `τ^{-1}` (`Amp0`-branch) and
    `τ^{-1/2}` (`L`-branch) singularities — one power worse than `grTerm_tail_le_of_sliver`'s branches,
    still dominated by the SAME quadratic bound (Sol GO-confirmed). -/
theorem heatHessMult_tail_le_of_sliver (ρ ε τ : ℝ) (hρ : 0 < ρ) (hε : 0 < ε) (hτ : 0 < τ)
    (hτε : τ ≤ ε) (PI PJ : Point n) (Amp0 L : ℝ) (hAmp0 : 0 ≤ Amp0) (hL : 0 ≤ L) :
    Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
        * (Amp0 * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
              + (1 / (2 * τ)))
            + L * ((1 / (4 * τ ^ 2))
                  * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
                + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)))
      ≤ 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
          * (Amp0 * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
              + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                    + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε))) := by
  set c : ℝ := ρ ^ 2 / 8 with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hτne : τ ≠ 0 := hτ.ne'
  have hcform : -(ρ ^ 2) / (8 * τ) = -(c / τ) := by rw [hcdef]; ring
  have hexp0 : Real.exp (-(ρ ^ 2) / (8 * τ)) ≤ 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 := by
    rw [hcform]; exact exp_neg_div_le_quadratic c τ hc hτ
  have hcsq : 4 * Real.exp (-2) * τ ^ 2 / c ^ 2 = 256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4 := by
    rw [hcdef]; field_simp; ring
  have hexp : Real.exp (-(ρ ^ 2) / (8 * τ)) ≤ 256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4 := by
    rw [← hcsq]; exact hexp0
  set Br : ℝ := Amp0 * ((1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * (Real.sqrt τ) ^ 2)
        + (1 / (2 * τ)))
      + L * ((1 / (4 * τ ^ 2))
            * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * (Real.sqrt τ) ^ 3)
          + (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * (Real.sqrt 2) ^ 1 * (Real.sqrt τ) ^ 1)) with hBrdef
  have hBrnn : 0 ≤ Br := by
    rw [hBrdef]
    have hsnn : ∀ k : ℕ, (0:ℝ) ≤ (Real.sqrt τ) ^ k := fun k => pow_nonneg (Real.sqrt_nonneg _) k
    positivity
  have hCconn : 0 ≤ (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) := by positivity
  have hstep1 : Real.exp (-(ρ ^ 2) / (8 * τ)) * ((Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br)
      ≤ (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4)
          * ((Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br) :=
    mul_le_mul_of_nonneg_right hexp (by positivity)
  have hτsq : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
  have hτcube : (Real.sqrt τ) ^ 3 = τ * Real.sqrt τ := by
    have h32 : (Real.sqrt τ) ^ 3 = (Real.sqrt τ) ^ 2 * Real.sqrt τ := by ring
    rw [h32, hτsq]
  have hτone : (Real.sqrt τ) ^ 1 = Real.sqrt τ := pow_one _
  have hτ2Br : τ ^ 2 * Br
      = Amp0 * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * τ + τ / 2)
          + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (τ * Real.sqrt τ)
                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (τ * Real.sqrt τ)) := by
    rw [hBrdef, hτsq, hτcube, hτone]
    field_simp
  have hrw : (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4)
      * ((Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br)
      = 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
          * (τ ^ 2 * Br) := by ring
  have hsqrtτε : Real.sqrt τ ≤ Real.sqrt ε := Real.sqrt_le_sqrt hτε
  have hsqrtτnn : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg _
  have hb1 : τ * Real.sqrt τ ≤ ε * Real.sqrt ε := mul_le_mul hτε hsqrtτε hsqrtτnn hε.le
  have hstep3 : τ ^ 2 * Br
      ≤ Amp0 * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
          + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε)) := by
    rw [hτ2Br]
    have e1 : ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * τ ≤ ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε :=
      mul_le_mul_of_nonneg_left hτε (by positivity)
    have e2 : τ / 2 ≤ ε / 2 := by linarith
    have e3 : (((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (τ * Real.sqrt τ)
        ≤ (((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε) :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have e4 : (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (τ * Real.sqrt τ)
        ≤ (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε) :=
      mul_le_mul_of_nonneg_left hb1 (by positivity)
    have hA := add_le_add e1 e2
    have hLb := add_le_add e3 e4
    have := add_le_add (mul_le_mul_of_nonneg_left hA hAmp0) (mul_le_mul_of_nonneg_left hLb hL)
    linarith [this]
  calc Real.exp (-(ρ ^ 2) / (8 * τ)) * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br
      = Real.exp (-(ρ ^ 2) / (8 * τ)) * ((Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br) := by
        ring
    _ ≤ (256 * Real.exp (-2) * τ ^ 2 / ρ ^ 4)
          * ((Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖) * Br) := hstep1
    _ = 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
          * (τ ^ 2 * Br) := hrw
    _ ≤ 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
          * (Amp0 * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
              + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                    + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε))) := by
        gcongr

/-! ###############################################################################
    ### PART 2 — the T1 capstone: composing `FullSpaceG1(τ) = C1/√τ + C2` with the folded tail bound
    ### via `pointwise_bound_sliver_window_inv_sqrt` (J4-1065).
    ############################################################################### -/

/-- **★★★★★ `hsMixed_domain_restricted_sliver_window_bound` — THE T1 CAPSTONE, completing J4-1069's
    frontier item 3 for ALL FOUR `Bfac` summands.**  For the base-slot CoV map
    `W p := uniformInverseChart g gi hC hK p q₀` at `q₀ ∈ interior K`, chart-Jacobian jet fields
    `PI PJ Q`, and `Amp` Lipschitz-at-`0` (modulus `L ≥ 0`), the near carry's `T1`-type (`hsMixed`)
    contribution, RESTRICTED to `nb`'s ACTUAL post-CoV domain `W''S'` AND integrated over the ACTUAL
    shrinking `s`-sliver `(t-ε,t)`, is bounded by `2·C1·√ε + C2'·ε = O(√ε)` — MEETING (not beating)
    `hcomp`'s required rate, closing J4-1069's frontier item 3 for T1 (the last of `Bfac`'s four
    summands). Composes `hsMixed_gaussDdim_mul_amp_domain_restricted_bound`'s (J4-1023) internal
    machinery (inlined, SAME `S',ρ` reused for every `τ` in the sliver) with
    `heatHessMult_tail_le_of_sliver` (Part 1) and `grTerm_tail_le_of_sliver` (J4-1071, reused verbatim
    for the `linMult` tail branch) folded into `pointwise_bound_sliver_window_inv_sqrt`'s (J4-1065)
    `C2` slot. -/
theorem hsMixed_domain_restricted_sliver_window_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {q₀ : Point n} (hq₀ : q₀ ∈ interior K)
    (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    ∃ (S' : Set (Point n)) (ρ : ℝ), IsOpen S' ∧ q₀ ∈ S' ∧ 0 < ρ ∧
      |∫ s in (t - ε)..t, ∫ v : Point n in (fun p => uniformInverseChart g gi hC hK p q₀) '' S',
          gaussDdim (t - s) v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v)|
        ≤ 2 * (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
            + (((n : ℝ) ^ 2 * L * ‖Q‖)
                + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
                    * (|Amp 0| * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
                        + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4)
                                * (ε * Real.sqrt ε)
                              + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε)))
                + 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
                    * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
                        + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2))) * ε := by
  set W : Point n → Point n := fun p => uniformInverseChart g gi hC hK p q₀ with hWdef
  obtain ⟨S', V, hS'open, hq0S', hinj, hV, hfd, hJpos, hWSopen⟩ :=
    uniformInverseChart_baseSlot_M1M4_image_open_generalK g gi hC hK hq₀
  set U : Set (Point n) := W '' S' with hUdef
  have hq0K : q₀ ∈ K := interior_subset hq₀
  have hWq0 : W q₀ = 0 := uniformInverseChart_diag_zero_of_mem g gi hC hK hq0K
  have h0U : (0 : Point n) ∈ U := ⟨q₀, hq0S', hWq0⟩
  obtain ⟨ρ, hρpos, hρsub⟩ := S'_ball_complement_subset_rncRadialSq_tail hWSopen h0U
  have hρsub' : Uᶜ ⊆ {v : Point n | ρ ^ 2 ≤ rncRadialSq v} := by
    intro v hv
    have := hρsub hv
    simpa using this
  have hUmeas : MeasurableSet U := hWSopen.measurableSet
  have hUcmeas : MeasurableSet Uᶜ := hUmeas.compl
  set C1 : ℝ := L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) with hC1def
  set HHTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) ^ 2 * ‖PI‖ * ‖PJ‖)
      * (|Amp 0| * (((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 / 4) * ε + ε / 2)
          + L * ((((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3) / 4) * (ε * Real.sqrt ε)
                + (((n : ℝ) * (3 / 2) * Real.sqrt 2) / 2) * (ε * Real.sqrt ε))) with hHHTaildef
  set LMTail : ℝ := 256 * Real.exp (-2) / ρ ^ 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ‖Q‖ / 2)
      * (|Amp 0| * ((n : ℝ) * (3 / 2) * Real.sqrt 2 * ε * Real.sqrt ε)
          + L * ((n : ℝ) * 2 * (Real.sqrt 2) ^ 2 * ε ^ 2)) with hLMTaildef
  set C2' : ℝ := (n : ℝ) ^ 2 * L * ‖Q‖ + HHTail + LMTail with hC2'def
  have hC2'nn : 0 ≤ C2' := by rw [hC2'def, hHHTaildef, hLMTaildef]; positivity
  refine ⟨S', ρ, hS'open, hq0S', hρpos, ?_⟩
  apply pointwise_bound_sliver_window_inv_sqrt t ε C1 C2' hε
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (s - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (s - s))) * Amp v) = 0 := by
      intro v; rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]; simp [hn]
      rw [hG0, zero_mul]
    simp only [hz0, MeasureTheory.integral_zero]
    have hnn : (0:ℝ) ≤ C1 / Real.sqrt (s - s) + C2' := by
      rw [sub_self]; positivity
    simpa using hnn
  · set τ : ℝ := t - s with hτdef
    have hτ : 0 < τ := by rw [hτdef]; linarith
    have hτε : τ ≤ ε := by rw [hτdef]; linarith [hs.1]
    have hpt1 : ∀ v : Point n, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
      intro v
      have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
          * gaussDdim τ v
        = heatHessMult τ PI PJ v - linMult τ Q v := by
        simp only [heatHessMult, linMult]; ring
      calc gaussDdim τ v
          * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
          = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by
            ring
        _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
        _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
    have hInt : Integrable (fun v : Point n => gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)) volume := by
      have h1 := heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip
      have h2 := linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip
      exact (h1.sub h2).congr (ae_of_all _ (fun v => (hpt1 v).symm))
    have hsplit := integral_add_compl hUmeas hInt
    have hGfull := hsMixed_gaussDdim_mul_amp_lipschitz_bound τ hτ PI PJ Q Amp hAmp L hL hlip
    have hGtail0 := hsMixed_amp_subset_tail_le τ hτ ρ PI PJ Q Amp hAmp L hL hlip hUcmeas hρsub'
    have hHHtail := heatHessMult_amp_subset_tail_le τ hτ ρ PI PJ Amp hAmp L hL hlip hUcmeas hρsub'
    have hLtail := linMult_amp_subset_tail_le τ hτ ρ Q Amp hAmp L hL hlip hUcmeas hρsub'
    have hHHtail' := hHHtail.trans
      (heatHessMult_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε PI PJ (|Amp 0|) L (abs_nonneg _) hL)
    have hLtail' := hLtail.trans
      (grTerm_tail_le_of_sliver ρ ε τ hρpos hε hτ hτε Q (|Amp 0|) L (abs_nonneg _) hL)
    have hGtail : |∫ v : Point n in Uᶜ, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)| ≤ HHTail + LMTail :=
      hGtail0.trans (add_le_add hHHtail' hLtail')
    have hUeq : ∫ v : Point n in U, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = (∫ v : Point n, gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v))
          - ∫ v : Point n in Uᶜ, gaussDdim τ v
              * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                    - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v) := by
      linarith [hsplit]
    have habs : |∫ v : Point n in U, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
        ≤ |∫ v : Point n, gaussDdim τ v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
          + |∫ v : Point n in Uᶜ, gaussDdim τ v
              * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
                    - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)| := by
      rw [hUeq, sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
    have hfinal : |∫ v : Point n in U, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
        ≤ C1 / Real.sqrt τ + C2' := by
      refine habs.trans ?_
      have := add_le_add hGfull hGtail
      rw [hC1def, hC2'def]
      linarith [this]
    exact hfinal

end QIQTH.HCompNearCarryTerm1DomainRestrictedSliverWindowBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1DomainRestrictedSliverWindowBound
#print axioms heatHessMult_tail_le_of_sliver
#print axioms hsMixed_domain_restricted_sliver_window_bound
end AxiomChecks
