/-
  HCompNearCarryLinMultSliverWindowBound — J4-1064: the window-shrinking rate mechanism (the SAME
  boundedness × window-length technique J4-1063 landed for the bare LEFTOVER term) applied to `Bfac`'s
  OTHER already-reduced summands — `linMult`-type terms 2/3 (`grⱼ·∂ⱼA`, `grᵢ·∂ᵢA`) — closing the
  outer `s`-integration gap the J4-106x survey found still open for them.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT.  `VanVleckGatedSpatialSymmetry.hcomp`'s near-carry `nb` (`HCompNearCarryKPrimeBaseFieldCoV`,
  J4-1010, BRICK 1) factors `kPrime`'s on-gate normal form as `gaussDdim(t−s, U z x) · Bfac(z)`,
  `Bfac(z) := Levi(s,z)·(T1 + T2 + T3 + LEFTOVER)` with (writing `τ := t−s`, `U := U(z,x)`):
    `T1 := (⟨U,PI⟩⟨U,PJ⟩/(4τ²) − (⟨PI,PJ⟩+⟨U,Q⟩)/(2τ))·A`,  `T2 := −⟨U,PJ⟩/(2τ)·∂ⱼA`,
    `T3 := −⟨U,PI⟩/(2τ)·∂ᵢA`,  `LEFTOVER := ∂ⱼ∂ᵢA`.
  J4-1063 (`HcompLeftoverSliverWindowBound`) closed LEFTOVER's contribution to the ACTUAL shrinking
  `s`-window carry via "bounded density × window length" = `O(ε) = o(√ε)`, and its own docstring
  explicitly flagged T1/T2/T3 as NOT re-litigated there.

  ## THE SURVEY (this session, BEFORE any new Lean).  A full read of the existing `Term1`/`linMult`
  family (16 files, J4-919 through J4-1047) found: (a) `HCompNearCarryBfacLinearTermsLinMultBridge`
  (J4-1041) ALREADY identifies `Bfac`'s `T2`/`T3` summands as EXACT signed instances of
  `HCompNearCarryTerm1LipschitzCancellation.linMult` (J4-1019) — pure `ring`, no new algebra
  (`grTerm_gaussian_mul_amp_eq_neg_linMult_mul_amp` + literal specializations); (b)
  `grTerm_gaussian_mul_amp_lipschitz_bound` (same file) ALREADY gives the FULL-SPACE, τ-INDEPENDENT
  fixed-`τ` bound `|∫ v, gaussDdim τ v · (grTerm · f v)| ≤ n²·L·‖Q‖` for `f` Lipschitz-at-0 (via
  `integral_linMult_mul_lipschitz`, J4-1019); (c) NONE of the 16 files composes this fixed-`τ` bound
  with an OUTER `s`-integral over a shrinking sliver `(t−ε,t)` — the window-integration step J4-1063
  performed for LEFTOVER was never done for T2/T3.  A companion `gpt-5.6-sol` consult (this session,
  BEFORE this file, on the T1/T2/T3 sympy rate check) independently confirmed the general STRUCTURE
  (Gaussian IBP moment-shift ⟹ the explicit `1/τ` prefactor cancels the moment's own `O(τ)` scaling,
  leaving a bounded density) — this file supplies the missing composition step using the
  ALREADY-BANKED fixed-`τ` bound directly (no new asymptotic/moment claim needed: `n²·L·‖Q‖` is
  ALREADY `τ`-independent, i.e. a stronger statement than "bounded near `τ=0`" — it is bounded for
  EVERY `τ>0`).

  ## WHAT LANDS.
    • `pointwise_bound_sliver_window` — the GENERIC window-shrinking rate lemma: for ANY function
      `h : ℝ → ℝ` bounded by `M` on the sliver `s ∈ (t−ε,t]`, `|∫ s in (t−ε)..t, h s| ≤ M·ε`.  A
      strict generalization of J4-1063's `leftover_sliver_window_bound` (that lemma's `h` was tied to
      the specific shape `s ↦ ∫ z, gaussDdim(t−s,z)·f z`; this one is shape-agnostic, letting it
      compose with `grTerm_gaussian_mul_amp_lipschitz_bound`'s bound directly without re-deriving the
      `intervalIntegral.norm_integral_le_of_norm_le_const` argument).
    • `grTerm_sliver_window_bound_of_lipschitz` — ★★★ THE PAYOFF: composing the generic window lemma
      with the ALREADY-BANKED `grTerm_gaussian_mul_amp_lipschitz_bound`, the near carry's `T2`/`T3`-type
      (`linMult`) contribution, integrated over the ACTUAL shrinking sliver `s ∈ (t−εₘ,t)`, is bounded
      by `n²·L·‖Q‖·εₘ = O(εₘ) = o(√εₘ)` — the SAME rate LEFTOVER achieved, strictly faster than the
      `O(√εₘ)` `hcomp` needs.  The `τ=0` boundary point (`s=t`) uses the SAME junk-value fact J4-1063
      used (`gaussDdim 0 v = 0`, so the integrand vanishes identically there — no case-split cost).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  ONLY the OUTER-window-integration gap for `Bfac`'s `T2`/`T3` (`linMult`-type) summands, reusing
  ALREADY-BANKED fixed-`τ`, FULL-SPACE (`ℝⁿ`, not the IFT domain `S'`) machinery from J4-1019/J4-1041.
  It does **NOT**: discharge `T1`'s own window-integration (the `heatHessMult`/quadratic piece, whose
  fixed-`τ` bound is `O(1/√τ)` not constant — genuinely separate follow-on work, NOT attempted here,
  since `∫₀^ε C/√τ dτ = O(√ε)` needs a DIFFERENT window lemma than the flat-`M` one built here);
  discharge LEFTOVER (already closed, J4-1063, untouched); reconcile the FULL-SPACE domain with `nb`'s
  actual bounded IFT domain `S'` (residuals r1–r4 of `HCompNearCarryKPrimeBaseFieldCoV`, UNCHANGED,
  untouched — same domain caveat every file in this family carries); discharge the shared `hxmem`
  upstream gate (`HCompNearCarryBfacLinearTermsLinMultBridge`'s own firewall, UNCHANGED); establish the
  literal `chartFieldAmp`-derivative's global Lipschitz regularity (the `L`/Lipschitz hypothesis is
  supplied ABSTRACTLY, exactly as every file in this family does); or discharge `nb`, `hCConv`, or any
  part of `hcomp`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable hypothesis, none
  equal to the conclusion, no existing file edited.  Non-vacuity: both theorems' hypotheses are
  satisfiable by concrete test data (e.g. `h := 0`/`M := 0`, `f := 0`/`L := 0`), and neither theorem's
  hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open QIQTH.HCompNearCarryTerm1LipschitzCancellation QIQTH.HCompNearCarryBfacLinearTermsLinMultBridge
open scoped Topology Interval

namespace QIQTH.HCompNearCarryLinMultSliverWindowBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### A — the GENERIC window-shrinking rate lemma (shape-agnostic).
    ############################################################################### -/

/-- **★ `pointwise_bound_sliver_window`.**  For ANY function `h : ℝ → ℝ` bounded by `M ≥ 0` on the
    HALF-OPEN sliver `s ∈ Ioc (t−ε) t`, the interval integral over the SAME shrinking window is bounded
    by `M · ε`.  A shape-agnostic generalization of J4-1063's `leftover_sliver_window_bound` — that
    lemma's hypothesis tied `h` to the specific form `s ↦ ∫ z, gaussDdim(t−s,z) · f z`; this one drops
    that restriction, letting it compose directly with ANY already-banked fixed-parameter bound (e.g.
    `grTerm_gaussian_mul_amp_lipschitz_bound`'s `τ`-independent estimate) without re-deriving the
    underlying `intervalIntegral.norm_integral_le_of_norm_le_const` argument. -/
theorem pointwise_bound_sliver_window (t ε M : ℝ) (hε : 0 < ε) (hM : 0 ≤ M)
    (h : ℝ → ℝ) (hbound : ∀ s ∈ Set.Ioc (t - ε) t, |h s| ≤ M) :
    |∫ s in (t - ε)..t, h s| ≤ M * ε := by
  have hab : t - ε ≤ t := by linarith
  have hIoc : Ι (t - ε) t = Set.Ioc (t - ε) t := uIoc_of_le hab
  have hbound' : ∀ s ∈ Ι (t - ε) t, ‖h s‖ ≤ M := by
    intro s hs
    rw [Real.norm_eq_abs]
    exact hbound s (hIoc ▸ hs)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound'
  have hdiff : |t - (t - ε)| = ε := by
    rw [show t - (t - ε) = ε by ring, abs_of_pos hε]
  rw [hdiff] at hnorm
  calc |∫ s in (t - ε)..t, h s| = ‖∫ s in (t - ε)..t, h s‖ := (Real.norm_eq_abs _).symm
    _ ≤ M * ε := hnorm

/-! ###############################################################################
    ### B — the payoff: `Bfac`'s `T2`/`T3` (`linMult`-type) sliver-window bound.
    ############################################################################### -/

/-- **★★★ `grTerm_sliver_window_bound_of_lipschitz` — THE PAYOFF.**  For `ε > 0`, `Q : Point n`,
    `L ≥ 0`, and `f : Point n → ℝ` Lipschitz-at-`0` with modulus `L` (`AEStronglyMeasurable`), the near
    carry's `T2`/`T3`-type (`linMult`) contribution, integrated over the ACTUAL shrinking sliver
    `s ∈ (t−ε,t)`, is bounded by `n²·L·‖Q‖·ε` — `O(ε) = o(√ε)`, the SAME rate LEFTOVER achieved
    (J4-1063), strictly faster than the `O(√ε)` rate `hcomp` needs.  Composes `pointwise_bound_sliver_
    window` (Part A) with the ALREADY-BANKED fixed-`τ` full-space bound
    `grTerm_gaussian_mul_amp_lipschitz_bound` (J4-1041/J4-1019).  The `τ = t−s = 0` boundary point
    (`s = t`) is handled by the junk value `gaussDdim 0 v = 0` (`heatKernel1D 0 x = (√0)⁻¹·exp(⋯) = 0`
    for `n ≠ 0`), making the whole integrand `0` there — no separate case in the hypothesis. -/
theorem grTerm_sliver_window_bound_of_lipschitz (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (Q : Point n) (L : ℝ) (hL : 0 ≤ L) (f : Point n → ℝ) (hf : AEStronglyMeasurable f volume)
    (hlip : ∀ v : Point n, |f v - f 0| ≤ L * ‖v‖) :
    |∫ s in (t - ε)..t,
        ∫ v : Point n, gaussDdim (t - s) v * ((-(∑ k, v k * Q k) / (2 * (t - s))) * f v)|
      ≤ (n : ℝ) ^ 2 * L * ‖Q‖ * ε := by
  apply pointwise_bound_sliver_window t ε ((n : ℝ) ^ 2 * L * ‖Q‖) hε
    (by positivity)
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · -- s = t : τ = t - s = 0, gaussDdim 0 v = 0 pointwise, so the integral is 0.
    subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v * ((-(∑ k, v k * Q k) / (2 * (s - s))) * f v) = 0 := by
      intro v; rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by
          rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]
        simp [hn]
      rw [hG0, zero_mul]
    simp only [hz0, MeasureTheory.integral_zero]
    simpa using mul_nonneg (mul_nonneg (by positivity) hL) (norm_nonneg Q)
  · exact grTerm_gaussian_mul_amp_lipschitz_bound (t - s) (by linarith) Q L hL f hf hlip

end QIQTH.HCompNearCarryLinMultSliverWindowBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryLinMultSliverWindowBound
#print axioms pointwise_bound_sliver_window
#print axioms grTerm_sliver_window_bound_of_lipschitz
end AxiomChecks
