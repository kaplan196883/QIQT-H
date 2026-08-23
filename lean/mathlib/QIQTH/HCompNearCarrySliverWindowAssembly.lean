/-
  HCompNearCarrySliverWindowAssembly — J4-1066: (A) the mechanical triangle-inequality COMBINED-
  ASSEMBLY of `Bfac`'s four sliver-window bounds (LEFTOVER J4-1063, T2/T3 J4-1064, T1 J4-1065), and
  (B) the GENERIC "restricting to a sub-domain only shrinks a norm-majorized integral" transfer lemma
  for the `S'`-vs-full-space reconciliation question flagged by all three files above.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT.  `VanVleckGatedSpatialSymmetry.hcomp`'s near-carry `nb` (`HCompNearCarryKPrimeBaseFieldCoV`,
  J4-1010, BRICK 1) factors `kPrime`'s on-gate normal form as `gaussDdim(t−s,U z x)·Bfac(z)`,
  `Bfac(z) := Levi(s,z)·(T1+T2+T3+LEFTOVER)`.  J4-1063/1064/1065 each closed ONE summand's contribution
  to the ACTUAL shrinking `s`-window carry at the fixed-`τ`, FULL-SPACE sliver-window-rate level.
  J4-1065's own scope note flagged two remaining steps: (1) sum the four bounds into one estimate via
  triangle inequality, (2) reconcile the FULL-SPACE (`ℝⁿ`) domain those bounds were built on with `nb`'s
  actual bounded IFT domain `S'` (`HCompNearCarryKPrimeBaseFieldCoV`'s own existentially-quantified,
  merely-open `S'`, r1–r4, UNCHANGED).

  ## (A) COMBINED ASSEMBLY — WHAT THIS FILE FOUND (a genuine domain SPLIT, not previously flagged).
  Re-reading the three files' literal conclusion types: J4-1063's payoff integrates the `z`-variable
  over `Metric.ball (0 : Point n) r` (a BALL, since its underlying `f`-boundedness hypothesis is only a
  BALL bound, needed for integrability); J4-1064's and J4-1065's payoffs integrate the `v`-variable over
  ALL of `Point n` (UNRESTRICTED `ℝⁿ`, since their underlying Lipschitz-at-`0` hypothesis gives a
  globally-integrable Gaussian-times-linear-growth majorant).  These are NOT the same domain.  A single
  triangle-inequality sum of the four LITERAL integrals therefore does not type-check directly — LEFTOVER
  lives on `ball 0 r`, T1/T2/T3 live on `ℝⁿ`.  This file supplies:
    • `sliver_window_four_term_combined_bound` — the fully GENERIC (domain-agnostic) mechanical
      composition: for ANY four functions `fLO,fT1,fT2,fT3 : ℝ → ℝ` (standing for the four terms'
      already-computed `z`/`v`-integrals as functions of `s` alone — the level at which the domain
      question is irrelevant, since each `f_i` is just some real number for each `s`), each individually
      interval-integrable and window-bounded, the SUM's window integral is bounded by the SUM of bounds.
      Pure `intervalIntegral.integral_add` (×3) + triangle inequality (`abs_add` ×3) — mechanical, no new
      analysis.
    • `t1t2t3_sliver_window_combined_bound` — the CONCRETE partial payoff: since T1/T2/T3 (J4-1064,
      J4-1065) DO share the same `ℝⁿ` domain, their three literal bounds compose directly (via the
      generic lemma, specialized) into ONE bound on `T1+T2+T3`'s combined `ℝⁿ`-sliver-window integral —
      `2·L₁·n³·‖PI‖·‖PJ‖·(16√2+1)·√ε + n²·L₁·‖Q‖·ε + n²·L₂·‖Q₂‖·ε + n²·L₃·‖Q₃‖·ε`, `O(√ε)`.  LEFTOVER's
      `ball`-domain term is NOT folded in here (the domain mismatch above is genuine and unresolved by
      this file — flagged, not silently assumed away).

  ## (B) S'-RECONCILIATION — THE FREE-DIRECTION TRANSFER LEMMA.
  For a function `f` on `Point n`, ANY norm bound on `∫ v, ‖f v‖` (full space) TRANSFERS FOR FREE to
  `|∫ v in S', f v| ≤` the SAME bound, for an ARBITRARY set `S'` — via `norm_integral_le_integral_norm`
  (needs no integrability hypothesis: both sides are `0` by the junk-value convention if `f` is not
  integrable on `S'`) composed with `MeasureTheory.setIntegral_le_integral` (mathlib,
  `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:728`, restricting a NONNEGATIVE integrable function's
  full-space integral to any subset only decreases it).  Confirms PRECISELY the "free direction" flagged
  in J4-1065's scope note for T1/T2/T3 (whose underlying bounds integrate over ALL of `ℝⁿ`): since their
  domain is already `ℝⁿ = Set.univ`, ANY `S' ⊆ ℝⁿ` (in particular the actual IFT-constructed `S'` from
  `HCompNearCarryKPrimeBaseFieldCoV`) trivially satisfies the subset requirement (`Set.subset_univ`), so
  `setIntegral_norm_transfer_bound` below applies UNCONDITIONALLY — no further work needed to transfer
  T1/T2/T3's `ℝⁿ`-bounds to the literal `S'`-restricted integral, PROVIDED the norm/majorant route used
  to derive each bound (which it is: J4-1019's underlying Lipschitz-bound proofs go via
  `‖∫‖ ≤ ∫‖·‖ ≤ (explicit majorant)`, the same structural route this file's transfer lemma formalizes).
  LEFTOVER's `ball 0 r`-domain bound does NOT get this for free: it would additionally need `S' ⊆
  ball 0 r`, a genuinely separate geometric fact about the IFT-selected `S'` NOT established by any
  existing file (this is real, unresolved, work — correctly flagged in J4-1010's r1–r4, unchanged).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It does
  **NOT**: literally combine all four `Bfac` summands into one bound (the ball-vs-`ℝⁿ` domain split
  discovered here blocks that, honestly reported rather than papered over); literally instantiate the
  transfer lemma with the ACTUAL `S'`/`Bfac` from `HCompNearCarryKPrimeBaseFieldCoV` (that file's `S'` is
  merely `IsOpen S' ∧ x ∈ S'`, with NO literal integral-equals-Bfac-on-`ℝⁿ` wiring done anywhere yet —
  the transfer lemma is the GENERIC tool that WOULD apply once such wiring exists); discharge the shared
  `hxmem` gate, the `chartFieldAmp`-derivative Lipschitz regularity (still abstract), or `nb`, `hCConv`,
  or any part of `hcomp`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable
  hypothesis, none equal to the conclusion, no existing file edited.  Non-vacuity: all theorems' hypothesis
  sets are satisfiable by concrete test data (e.g. all `f_i := 0`/bounds `:= 0`, `S' := ∅` or `S' := univ`),
  and none of their hypothesis sets equal their conclusions.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryLinMultSliverWindowBound
import QIQTH.HCompNearCarryTerm1SliverWindowBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open scoped Topology Interval

namespace QIQTH.HCompNearCarrySliverWindowAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### A1 — the fully generic four-term combined-assembly lemma.
    ############################################################################### -/

/-- **★ `sliver_window_four_term_combined_bound`.**  For ANY four functions `fLO fT1 fT2 fT3 : ℝ → ℝ`
    (standing for `Bfac`'s four summands' already-computed spatial integrals, as functions of `s`
    alone — domain-agnostic, since each is just a real number per `s`), each interval-integrable on
    `(t−ε,t)` and individually window-bounded by `BLO/BT1/BT2/BT3`, the SUM's window integral is
    bounded by the SUM of the four bounds.  Pure mechanical triangle-inequality composition —
    `intervalIntegral.integral_add` (linearity, ×3) then `abs_add` (×3). -/
theorem sliver_window_four_term_combined_bound (t ε : ℝ)
    (fLO fT1 fT2 fT3 : ℝ → ℝ) (BLO BT1 BT2 BT3 : ℝ)
    (hIntLO : IntervalIntegrable fLO volume (t - ε) t)
    (hIntT1 : IntervalIntegrable fT1 volume (t - ε) t)
    (hIntT2 : IntervalIntegrable fT2 volume (t - ε) t)
    (hIntT3 : IntervalIntegrable fT3 volume (t - ε) t)
    (hLO : |∫ s in (t - ε)..t, fLO s| ≤ BLO)
    (hT1 : |∫ s in (t - ε)..t, fT1 s| ≤ BT1)
    (hT2 : |∫ s in (t - ε)..t, fT2 s| ≤ BT2)
    (hT3 : |∫ s in (t - ε)..t, fT3 s| ≤ BT3) :
    |∫ s in (t - ε)..t, (fLO s + fT1 s + fT2 s + fT3 s)| ≤ BLO + BT1 + BT2 + BT3 := by
  have hsplit : ∫ s in (t - ε)..t, (fLO s + fT1 s + fT2 s + fT3 s)
      = (∫ s in (t - ε)..t, fLO s) + (∫ s in (t - ε)..t, fT1 s)
        + (∫ s in (t - ε)..t, fT2 s) + (∫ s in (t - ε)..t, fT3 s) := by
    have h1 : IntervalIntegrable (fun s => fLO s + fT1 s) volume (t - ε) t := hIntLO.add hIntT1
    have h2 : IntervalIntegrable (fun s => fLO s + fT1 s + fT2 s) volume (t - ε) t := h1.add hIntT2
    rw [intervalIntegral.integral_add h2 hIntT3, intervalIntegral.integral_add h1 hIntT2,
      intervalIntegral.integral_add hIntLO hIntT1]
  rw [hsplit]
  set A := ∫ s in (t - ε)..t, fLO s
  set B := ∫ s in (t - ε)..t, fT1 s
  set C := ∫ s in (t - ε)..t, fT2 s
  set D := ∫ s in (t - ε)..t, fT3 s
  have step1 : |A + B| ≤ |A| + |B| := abs_add_le A B
  have step2 : |A + B + C| ≤ |A + B| + |C| := abs_add_le (A + B) C
  have step3 : |A + B + C + D| ≤ |A + B + C| + |D| := abs_add_le (A + B + C) D
  linarith [hLO, hT1, hT2, hT3]

/-! ###############################################################################
    ### A2 — the concrete partial payoff: T1+T2+T3 combined (shared `ℝⁿ` domain).
    ############################################################################### -/

open QIQTH.HCompNearCarryLinMultSliverWindowBound QIQTH.HCompNearCarryTerm1SliverWindowBound

/-- **★★ `t1t2t3_sliver_window_combined_bound`.**  T1 (J4-1065), T2, and T3 (J4-1064, applied twice
    with independent data since `Bfac` has two `linMult`-type summands `grⱼ·∂ⱼA` and `grᵢ·∂ᵢA`) DO
    share the same `ℝⁿ` domain, so their three literal bounds compose directly into ONE bound on
    `T1+T2+T3`'s combined sliver-window integral: `O(√ε)`.  LEFTOVER (`ball`-domain) is NOT folded in
    (genuine, flagged domain split — see file docstring). -/
theorem t1t2t3_sliver_window_combined_bound (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (PI PJ Q QT2 QT3 : Point n)
    (Amp AmpT2 AmpT3 : Point n → ℝ)
    (hAmp : AEStronglyMeasurable Amp volume) (hAmpT2 : AEStronglyMeasurable AmpT2 volume)
    (hAmpT3 : AEStronglyMeasurable AmpT3 volume)
    (L LT2 LT3 : ℝ) (hL : 0 ≤ L) (hLT2 : 0 ≤ LT2) (hLT3 : 0 ≤ LT3)
    (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖)
    (hlipT2 : ∀ v : Point n, |AmpT2 v - AmpT2 0| ≤ LT2 * ‖v‖)
    (hlipT3 : ∀ v : Point n, |AmpT3 v - AmpT3 0| ≤ LT3 * ‖v‖) :
    |(∫ s in (t - ε)..t,
        ∫ v : Point n, gaussDdim (t - s) v
          * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v))
      + (∫ s in (t - ε)..t,
          ∫ v : Point n, gaussDdim (t - s) v * ((-(∑ k, v k * QT2 k) / (2 * (t - s))) * AmpT2 v))
      + (∫ s in (t - ε)..t,
          ∫ v : Point n, gaussDdim (t - s) v * ((-(∑ k, v k * QT3 k) / (2 * (t - s))) * AmpT3 v))|
      ≤ (2 * (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
          + (n : ℝ) ^ 2 * L * ‖Q‖ * ε)
        + (n : ℝ) ^ 2 * LT2 * ‖QT2‖ * ε + (n : ℝ) ^ 2 * LT3 * ‖QT3‖ * ε := by
  set BT1 := 2 * (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
      + (n : ℝ) ^ 2 * L * ‖Q‖ * ε with hBT1def
  set BT2 := (n : ℝ) ^ 2 * LT2 * ‖QT2‖ * ε with hBT2def
  set BT3 := (n : ℝ) ^ 2 * LT3 * ‖QT3‖ * ε with hBT3def
  have hT1 := hsMixed_sliver_window_bound_of_lipschitz hn t ε hε PI PJ Q Amp hAmp L hL hlip
  have hT2 := grTerm_sliver_window_bound_of_lipschitz hn t ε hε QT2 LT2 hLT2 AmpT2 hAmpT2 hlipT2
  have hT3 := grTerm_sliver_window_bound_of_lipschitz hn t ε hε QT3 LT3 hLT3 AmpT3 hAmpT3 hlipT3
  set X1 := ∫ s in (t - ε)..t,
      ∫ v : Point n, gaussDdim (t - s) v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v)
  set X2 := ∫ s in (t - ε)..t,
      ∫ v : Point n, gaussDdim (t - s) v * ((-(∑ k, v k * QT2 k) / (2 * (t - s))) * AmpT2 v)
  set X3 := ∫ s in (t - ε)..t,
      ∫ v : Point n, gaussDdim (t - s) v * ((-(∑ k, v k * QT3 k) / (2 * (t - s))) * AmpT3 v)
  have step1 : |X1 + X2| ≤ |X1| + |X2| := abs_add_le X1 X2
  have step2 : |X1 + X2 + X3| ≤ |X1 + X2| + |X3| := abs_add_le (X1 + X2) X3
  linarith [hT1, hT2, hT3]

/-! ###############################################################################
    ### B — the S'-reconciliation free-direction transfer lemma.
    ############################################################################### -/

/-- **★★★ `setIntegral_norm_transfer_bound` — THE FREE-DIRECTION LEMMA.**  If a full-space norm bound
    `∫ v, ‖f v‖ ≤ C` holds for `f : Point n → ℝ`, then for ANY set `S' : Set (Point n)` (in particular
    the actual IFT-constructed `S'` from `HCompNearCarryKPrimeBaseFieldCoV`, since it is automatically
    `⊆ Point n = Set.univ`), `|∫ v in S', f v| ≤ C`.  Composes `norm_integral_le_integral_norm` (no
    integrability hypothesis needed — both sides are `0` by the junk-value convention off the
    integrable locus) with `MeasureTheory.setIntegral_le_integral` (restricting a nonnegative
    integrable function's full-space integral to any subset only decreases it).  This is PRECISELY
    the "free direction" (subset integral ≤ full-space integral) flagged for T1/T2/T3's `ℝⁿ`-domain
    bounds: since their domain is already all of `ℝⁿ`, this lemma applies UNCONDITIONALLY to transfer
    them to the literal `S'`-restricted carry integral, with NO extra geometric fact about `S'`
    needed. -/
theorem setIntegral_norm_transfer_bound (f : Point n → ℝ) (hf : Integrable f volume)
    (S' : Set (Point n)) (C : ℝ) (hC : ∫ v, ‖f v‖ ≤ C) :
    |∫ v in S', f v| ≤ C := by
  calc |∫ v in S', f v| = ‖∫ v in S', f v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ v in S', ‖f v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, ‖f v‖ := setIntegral_le_integral hf.norm (Eventually.of_forall fun v => norm_nonneg (f v))
    _ ≤ C := hC

end QIQTH.HCompNearCarrySliverWindowAssembly

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarrySliverWindowAssembly
#print axioms sliver_window_four_term_combined_bound
#print axioms t1t2t3_sliver_window_combined_bound
#print axioms setIntegral_norm_transfer_bound
end AxiomChecks
