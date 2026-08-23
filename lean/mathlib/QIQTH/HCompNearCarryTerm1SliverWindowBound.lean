/-
  HCompNearCarryTerm1SliverWindowBound — J4-1065: the window-shrinking rate mechanism (J4-1063's
  bare LEFTOVER, J4-1064's `linMult`-type T2/T3) applied to `Bfac`'s LAST remaining summand — `T1`
  (the `hsMixed·A` quadratic/mixed piece) — closing the outer `s`-integration gap for T1 at the
  fixed-`τ`, FULL-SPACE level, completing the four-way survey `{LEFTOVER, T1, T2, T3}` at that level.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT.  `VanVleckGatedSpatialSymmetry.hcomp`'s near-carry `nb` (`HCompNearCarryKPrimeBaseFieldCoV`,
  J4-1010, BRICK 1) factors `kPrime`'s on-gate normal form as `gaussDdim(t−s, U z x) · Bfac(z)`,
  `Bfac(z) := Levi(s,z)·(T1 + T2 + T3 + LEFTOVER)`.  J4-1063 closed LEFTOVER and J4-1064 closed T2/T3
  at the "bounded density × shrinking window" rate `O(ε) = o(√ε)`, both STRICTLY FASTER than `hcomp`'s
  required `O(√ε)`.  Both files explicitly flagged T1 as DIFFERENT: T1's already-banked fixed-`τ`
  full-space bound (`hsMixed_gaussDdim_mul_amp_lipschitz_bound`, J4-1019,
  `HCompNearCarryTerm1LipschitzCancellation.lean`) has the shape
      `|∫ v, G_τ(v)·(hsMixed·Amp v)| ≤ L·n³·‖PI‖·‖PJ‖·(16√2+1)/√τ + n²·L·‖Q‖`,
  i.e. `C1/√τ + C2` — NOT the flat/constant-in-`τ` shape T2/T3 had.  Window-integrating `C1/√τ + C2`
  over the shrinking sliver `τ ∈ (0,ε)` gives `∫₀^ε (C1/√τ + C2) dτ = 2·C1·√ε + C2·ε = O(√ε)` — this
  MEETS (does not beat) `hcomp`'s required rate exactly, the tightest of the four terms, and needs a
  genuinely different window lemma than J4-1063/J4-1064's flat-`M` one (that lemma's hypothesis was a
  UNIFORM bound on the whole sliver, which is false here — the bound blows up as `τ → 0`).

  ## SYMPY VERIFICATION (`docs/qg_roadmap/rnc_sympy/hcomp_term1_sliver_window_check.py`, BEFORE this
  Lean file): confirmed `∫₀^ε (C1/√τ + C2) dτ = 2·C1·√ε + C2·ε` exactly (symbolic `sympy.integrate`,
  zero residual against the closed form) — both terms present with the EXACT constants, no hidden
  log/divergence at the `τ → 0` endpoint (`1/√τ` is integrable there; the existing fixed-`τ` bound `C1`
  is itself `τ`-INDEPENDENT — a stronger fact than merely "bounded near 0" — so no additional
  near-endpoint blow-up of the constant `C1` itself needs to be tracked).

  ## MATHLIB ROUTE (confirmed via `gpt-5.6-sol`, high, before Lean construction; no ready-made
  "`∫ C/√x`" convenience lemma found — built from `integral_rpow` + `IntervalIntegrable.comp_sub_left`
  + `intervalIntegral.norm_integral_le_of_norm_le`, i.e. general power-function integral machinery, NOT
  a Gaussian-specific shortcut): `Real.sqrt x = x^(1/2:ℝ)` (`Real.sqrt_eq_rpow`, unconditional) lets the
  `1/√(t−s)` majorant be rewritten as `(t−s)^(-(1/2):ℝ)` for `s` in the sliver (`t−s ≥ 0`); reflection
  (`IntervalIntegrable.comp_sub_left` / `intervalIntegral.integral_comp_sub_left`) reduces the
  `s`-integral over `(t−ε,t)` to the STANDARD `x`-integral over `(0,ε)`; `integral_rpow` (with
  `-1 < -(1/2)`) evaluates that in closed form to `2√ε`; `intervalIntegral.norm_integral_le_of_norm_le`
  (the DOMINATION form, taking an interval-integrable majorant `g`, NOT the constant-bound form
  J4-1063/1064 used) supplies the domination step.  No `sorry`, no numerical approximation.

  ## WHAT LANDS.
    • `pointwise_bound_sliver_window_inv_sqrt` — the GENERIC `C1/√τ + C2`-type window-shrinking rate
      lemma: for `h : ℝ → ℝ` with `|h s| ≤ C1/√(t−s) + C2` pointwise on the sliver `s ∈ (t−ε,t]`,
      `|∫ s in (t−ε)..t, h s| ≤ 2·C1·√ε + C2·ε`.  Shape-agnostic (does not know about `hsMixed`,
      `heatHessMult`, or any chart datum) — a strict analogue of J4-1064's `pointwise_bound_sliver_
      window`, but for the genuinely different `C/√τ` integrand family, needed because T1's fixed-`τ`
      bound is not flat.
    • `hsMixed_sliver_window_bound_of_lipschitz` — ★★★ THE PAYOFF: composing the generic window lemma
      with the ALREADY-BANKED fixed-`τ` full-space bound `hsMixed_gaussDdim_mul_amp_lipschitz_bound`
      (J4-1019), `Bfac`'s `T1`-type (`hsMixed`) contribution, integrated over the ACTUAL shrinking
      sliver `s ∈ (t−ε,t)`, is bounded by `2·L·n³·‖PI‖·‖PJ‖·(16√2+1)·√ε + n²·L·‖Q‖·ε = O(√ε)` — MEETING
      (not beating) `hcomp`'s required rate.  The `τ = 0` boundary point (`s = t`) uses the SAME
      junk-value fact J4-1063/1064 used (`gaussDdim 0 v = 0`, so the integrand vanishes identically
      there — no case-split cost, and `C1/√0 = C1/0 = 0` matches by Lean's division-by-zero convention).

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It closes
  ONLY the OUTER-window-integration gap for `Bfac`'s `T1` (`hsMixed`-type) summand, reusing
  ALREADY-BANKED fixed-`τ`, FULL-SPACE (`ℝⁿ`, not the IFT domain `S'`) machinery from J4-1019.  With
  this file, ALL FOUR of `Bfac`'s summands (LEFTOVER J4-1063, T2/T3 J4-1064, T1 here) are closed at the
  FIXED-`τ`-FULL-SPACE sliver-window level — but this file does NOT: reconcile the FULL-SPACE domain
  with `nb`'s actual bounded IFT domain `S'` (residuals r1–r4 of `HCompNearCarryKPrimeBaseFieldCoV`,
  UNCHANGED, untouched — same domain caveat every file in this family carries); discharge the shared
  `hxmem` upstream gate (UNCHANGED); establish the literal `chartFieldAmp`-derivative's global Lipschitz
  regularity (the `L`/Lipschitz hypothesis is supplied ABSTRACTLY, exactly as every file in this family
  does); sum the four terms' bounds into a single combined `Bfac` sliver-window estimate (NOT attempted
  here — a genuinely separate composition step, since the four terms were bounded via different generic
  lemmas and need a `triangle-inequality`-style assembly, not automatic from this file alone); or
  discharge `nb`, `hCConv`, or any part of `hcomp`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`, no
  vacuous/unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  Non-vacuity:
  both theorems' hypotheses are satisfiable by concrete test data (e.g. `h := 0`/`C1 := 0`/`C2 := 0`,
  `Amp := 0`/`L := 0`), and neither theorem's hypothesis set is equal to its conclusion.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HCompNearCarryTerm1LipschitzCancellation

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open QIQTH.HCompNearCarryTerm1LipschitzCancellation
open scoped Topology Interval

namespace QIQTH.HCompNearCarryTerm1SliverWindowBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### A — the GENERIC `C1/√τ + C2`-type window-shrinking rate lemma.
    ############################################################################### -/

/-- **★ `pointwise_bound_sliver_window_inv_sqrt`.**  For ANY function `h : ℝ → ℝ` bounded by
    `C1/√(t−s) + C2` (`C1, C2 ≥ 0`) on the HALF-OPEN sliver `s ∈ Ioc (t−ε) t`, the interval integral
    over the SAME shrinking window is bounded by `2·C1·√ε + C2·ε`.  Sympy-verified
    (`docs/qg_roadmap/rnc_sympy/hcomp_term1_sliver_window_check.py`) BEFORE this Lean statement.  A
    genuinely different shape than J4-1064's `pointwise_bound_sliver_window` (flat `M`): here the
    majorant itself blows up as `s → t` (`τ = t−s → 0`), handled via `Real.sqrt_eq_rpow` +
    `integral_rpow` + reflection, not the constant-bound `norm_integral_le_of_norm_le_const`. -/
theorem pointwise_bound_sliver_window_inv_sqrt (t ε C1 C2 : ℝ) (hε : 0 < ε)
    (h : ℝ → ℝ) (hbound : ∀ s ∈ Set.Ioc (t - ε) t, |h s| ≤ C1 / Real.sqrt (t - s) + C2) :
    |∫ s in (t - ε)..t, h s| ≤ 2 * C1 * Real.sqrt ε + C2 * ε := by
  have hab : t - ε ≤ t := by linarith
  set g : ℝ → ℝ := fun s => C1 / Real.sqrt (t - s) + C2 with hgdef
  have hkey : ∀ s : ℝ, 0 ≤ t - s → C1 / Real.sqrt (t - s) = C1 * (t - s) ^ (-(1 / 2 : ℝ)) := by
    intro s hs'
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hs']
  -- integrability of the rpow piece via reflection
  have hrpow0ε : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 ε :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hrpowRefl : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume (t - ε) t := by
    have h1 := hrpow0ε.comp_sub_left t
    simpa using h1.symm
  have hgint : IntervalIntegrable g volume (t - ε) t := by
    have hcombine : IntervalIntegrable (fun s => C1 * (t - s) ^ (-(1 / 2 : ℝ)) + C2) volume (t - ε) t :=
      (hrpowRefl.const_mul C1).add intervalIntegrable_const
    apply hcombine.congr
    intro s hs
    have hs' : 0 ≤ t - s := by
      rw [uIoc_of_le hab] at hs
      linarith [hs.2]
    simp only [hgdef]
    rw [hkey s hs']
  have hnormbound : ∀ s ∈ Set.Ioc (t - ε) t, ‖h s‖ ≤ g s := by
    intro s hs; rw [Real.norm_eq_abs]; exact hbound s hs
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall (fun s hs => hnormbound s hs)) hgint
  have hval : ∫ s in (t - ε)..t, g s = 2 * C1 * Real.sqrt ε + C2 * ε := by
    have hsplit : ∫ s in (t - ε)..t, g s
        = (∫ s in (t - ε)..t, C1 * (t - s) ^ (-(1 / 2 : ℝ))) + ∫ _s in (t - ε)..t, C2 := by
      rw [← intervalIntegral.integral_add (hrpowRefl.const_mul C1) intervalIntegrable_const]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : 0 ≤ t - s := by
        rw [uIcc_of_le hab] at hs
        linarith [hs.2]
      simp only [hgdef]
      rw [hkey s hs']
    rw [hsplit]
    have hpiece1 : ∫ s in (t - ε)..t, C1 * (t - s) ^ (-(1 / 2 : ℝ)) = 2 * C1 * Real.sqrt ε := by
      rw [intervalIntegral.integral_const_mul]
      have hrefl : ∫ s in (t - ε)..t, (t - s) ^ (-(1 / 2 : ℝ))
          = ∫ x in (0 : ℝ)..ε, x ^ (-(1 / 2 : ℝ)) := by
        have hh := intervalIntegral.integral_comp_sub_left (a := t - ε) (b := t)
          (f := fun x : ℝ => x ^ (-(1 / 2 : ℝ))) t
        simpa using hh
      rw [hrefl, integral_rpow (Or.inl (by norm_num))]
      have hexp : (-(1 / 2 : ℝ) + 1) = 1 / 2 := by norm_num
      rw [hexp, Real.zero_rpow (by norm_num)]
      rw [Real.sqrt_eq_rpow]
      ring
    have hpiece2 : ∫ _s in (t - ε)..t, C2 = C2 * ε := by
      rw [intervalIntegral.integral_const]
      have heq : t - (t - ε) = ε := by ring
      rw [heq]; ring
    rw [hpiece1, hpiece2]
  rw [hval] at hnorm
  calc |∫ s in (t - ε)..t, h s| = ‖∫ s in (t - ε)..t, h s‖ := (Real.norm_eq_abs _).symm
    _ ≤ 2 * C1 * Real.sqrt ε + C2 * ε := hnorm

/-! ###############################################################################
    ### B — the payoff: `Bfac`'s `T1` (`hsMixed`-type) sliver-window bound.
    ############################################################################### -/

/-- **★★★ `hsMixed_sliver_window_bound_of_lipschitz` — THE PAYOFF.**  For `ε > 0`, chart-Jacobian
    jet fields `PI PJ Q : Point n`, and an amplitude weight `Amp` Lipschitz-at-`0` with modulus
    `L ≥ 0` (`AEStronglyMeasurable`), the near carry's `T1`-type (`hsMixed`) contribution, integrated
    over the ACTUAL shrinking sliver `s ∈ (t−ε,t)`, is bounded by
    `2·L·n³·‖PI‖·‖PJ‖·(16√2+1)·√ε + n²·L·‖Q‖·ε` — `O(√ε)`, MEETING (not beating) the rate `hcomp`
    needs.  Composes `pointwise_bound_sliver_window_inv_sqrt` (Part A) with the ALREADY-BANKED
    fixed-`τ` full-space bound `hsMixed_gaussDdim_mul_amp_lipschitz_bound` (J4-1019).  The `τ = t−s = 0`
    boundary point (`s = t`) is handled by the junk value `gaussDdim 0 v = 0`, making the whole
    integrand `0` there — no separate case in the hypothesis. -/
theorem hsMixed_sliver_window_bound_of_lipschitz (hn : n ≠ 0) (t ε : ℝ) (hε : 0 < ε)
    (PI PJ Q : Point n) (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    |∫ s in (t - ε)..t,
        ∫ v : Point n, gaussDdim (t - s) v
          * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (t - s) ^ 2)
                - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (t - s))) * Amp v)|
      ≤ 2 * (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) * Real.sqrt ε
          + (n : ℝ) ^ 2 * L * ‖Q‖ * ε := by
  apply pointwise_bound_sliver_window_inv_sqrt t ε
    (L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1)) ((n : ℝ) ^ 2 * L * ‖Q‖) hε
  intro s hs
  rcases eq_or_lt_of_le hs.2 with heq | hlt
  · -- s = t : τ = t - s = 0, gaussDdim 0 v = 0 pointwise, so the integral is 0.
    subst heq
    have hz0 : ∀ v : Point n,
        gaussDdim (s - s) v
            * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * (s - s) ^ 2)
                  - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * (s - s))) * Amp v) = 0 := by
      intro v; rw [sub_self]
      have hG0 : gaussDdim (0 : ℝ) v = 0 := by
        simp only [gaussDdim, heatKernel1D]
        have hsqrt0 : Real.sqrt (4 * Real.pi * (0 : ℝ)) = 0 := by
          rw [mul_zero, Real.sqrt_zero]
        rw [hsqrt0]
        simp [hn]
      rw [hG0, zero_mul]
    simp only [hz0, MeasureTheory.integral_zero]
    have hnn : (0:ℝ) ≤ (n : ℝ) ^ 2 * L * ‖Q‖ := by positivity
    simpa using hnn
  · exact hsMixed_gaussDdim_mul_amp_lipschitz_bound (t - s) (by linarith) PI PJ Q Amp hAmp L hL hlip

end QIQTH.HCompNearCarryTerm1SliverWindowBound

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1SliverWindowBound
#print axioms pointwise_bound_sliver_window_inv_sqrt
#print axioms hsMixed_sliver_window_bound_of_lipschitz
end AxiomChecks
