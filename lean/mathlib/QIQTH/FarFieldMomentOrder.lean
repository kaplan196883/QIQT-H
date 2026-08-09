/-
  FarFieldMomentOrder — J4-491: the EXPLICIT O(1/τ) far-field moment-order bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  No `sorry` (header prose excepted),
  no `:= True`, no new axioms, no vacuous / unsatisfiable hypothesis, no result equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  std-3 only.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE OBJECT.  `FarFieldDecay.farField_decay_bound` (J4-457) discharges the off-collar comparison
  integral by the finite Gaussian-moment dominator
      `‖∫_{far} f‖ ≤ ∫_z farFieldDom τ M1F M2F Mqc z`,
      `farFieldDom z = M1F·(1/(2τ))·(‖z‖·G_τ) + M2F·G_τ + Mqc·(1/(4τ²))·((‖z‖²+2τ)·G_τ)`.
  The τ→0⁺ DECAY ORDER of that dominator (its per-term scaling — the DOMAIN/TAIL GATE verdict) is only
  recorded in PROSE there: gradient `O(τ^{-1/2})`, mass `O(1)`, Hessian `O(τ^{-1})`.  This file turns
  that prose into a THEOREM by COMPUTING the integral to an explicit closed form:

      ★  `∫_z farFieldDom τ M1F M2F Mqc z  ≤  M1F·(3n/4)/√τ  +  M2F  +  Mqc·(n+1)/(2τ)`,

  each summand's τ-order manifest — the third (Hessian) term is the honest DOMINANT `O(1/τ)`.

  ## THE ROUTE (all banked bricks; NO new analysis).
    • Linearity: `farFieldDom = c₁·(‖z‖·G) + c₂·(‖z‖²·G) + (M2F + 2τ·c₂)·G` (a pure `ring` regroup),
      `c₁ = M1F/(2τ) ≥ 0`, `c₂ = Mqc/(4τ²) ≥ 0`; integrate term-by-term via `integral_add` /
      `integral_const_mul` (each piece integrable by `normPow_gauss_integrable` / `gaussDdim_integrable`).
    • Moments (the banked width-τ envelope `normPow_gauss_tau`, fed `oneD_absMoment1`/`oneD_absMoment2`):
        `∫ ‖z‖·G_τ  ≤  n·(3/2)·√τ`,      `∫ ‖z‖²·G_τ  ≤  n·2·τ`,      `∫ G_τ = 1` (`gaussDdim_integral_eq_one`).
    • Arithmetic: `c₁·(n·(3/2)·√τ) = M1F·(3n/4)/√τ` (uses `√τ·√τ = τ`), `c₂·(n·2·τ) = Mqc·n/(2τ)`,
      `(M2F + 2τ·c₂)·1 = M2F + Mqc/(2τ)`; sum `= M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)`.

  ## THE GATE (satisfiability — checked BEFORE building).  The dominator constants `M1F,M2F,Mqc ≥ 0`
  are the SAME satisfiable global amplitude sups `FarFieldDecay.farField_decay_bound` already carries
  (genuine `∀ z` sups of `|A1amp·F|`, `|A2amp·F|`, `|chartAmp·F|`); the moment bounds are BANKED and TRUE;
  no false pointwise inequality, no divergent width, no single-coordinate envelope masquerading as a full
  contraction.  The `√τ`-in-denominator terms are HONEST (`τ^{-1/2} < τ^{-1}` as `τ→0⁺`), so the whole
  dominator is genuinely `O(1/τ)` and REACHABLE.

  ⚠ HONEST DISTANCE.  These `M1F/M2F/Mqc` are the OFF-collar (global) sups, NOT the (I1)-closed ON-collar
  constants `M₀/M₁/M₂` of `C2AggregatorPhase6.collarSupConstants_of_reach` (J4-490): off `K` the witness
  term VANISHES, so the far field is a pure Gaussian remainder controlled by these global sups, DISJOINT
  from the collar constants which control the on-collar leg.  This brick nails the far-field τ-order;
  it does NOT reduce the far field to (I1).  ⚠ NOT `a₁ = R/6`; `a₁ = R/6` remains CONDITIONAL.
-/
import QIQTH.FarFieldDecay

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ResidueBound QIQTH.FarFieldDecay
open scoped BigOperators

namespace QIQTH.FarFieldMomentOrder

variable {n : ℕ}

set_option maxHeartbeats 1200000

/-! ###############################################################################
    ### ★ THE EXPLICIT O(1/τ) FAR-FIELD MOMENT-ORDER BOUND.
    ############################################################################### -/

/-- **★★★ `farFieldDom_integral_le` — the EXPLICIT O(1/τ) far-field moment order.**  The far-field
    Gaussian-moment dominator of `FarFieldDecay.farFieldDom` (the honest off-collar comparison bound of
    `farField_decay_bound`) integrates to an explicit closed form with each summand's τ-order manifest:
      `∫_z farFieldDom τ M1F M2F Mqc z  ≤  M1F·(3n/4)/√τ  +  M2F  +  Mqc·(n+1)/(2τ)`.
    The third (Hessian) term `Mqc·(n+1)/(2τ)` is the honest DOMINANT `O(1/τ)`; the gradient term is
    `O(τ^{-1/2})`, the mass term `O(1)` — turning the DOMAIN/TAIL GATE prose verdict of J4-457 into a
    theorem.  Route: linearity (`integral_add`/`integral_const_mul`) + the banked width-τ moments
    `normPow_gauss_tau` (`∫‖z‖G ≤ n·(3/2)√τ`, `∫‖z‖²G ≤ n·2τ`) + `gaussDdim_integral_eq_one`
    (`∫ G = 1`).  ⚠ NOT `a₁ = R/6`. -/
theorem farFieldDom_integral_le (τ M1F M2F Mqc : ℝ) (hτ : 0 < τ)
    (hM1F : 0 ≤ M1F) (hM2F : 0 ≤ M2F) (hMqc : 0 ≤ Mqc) :
    ∫ z : Point n, farFieldDom τ M1F M2F Mqc z
      ≤ M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ) := by
  -- integrability of the three moment pieces.
  have hI1 : Integrable (fun z : Point n => ‖z‖ * gaussDdim τ z) volume := by
    have h := normPow_gauss_integrable (n := n) 1 (by norm_num) τ hτ
    simpa [pow_one] using h
  have hI2 : Integrable (fun z : Point n => ‖z‖ ^ 2 * gaussDdim τ z) volume :=
    normPow_gauss_integrable (n := n) 2 (by norm_num) τ hτ
  have hI0 : Integrable (fun z : Point n => gaussDdim τ z) volume := gaussDdim_integrable τ hτ
  -- nonnegativity of the two `‖z‖`-carrying coefficients.
  have hc1 : (0 : ℝ) ≤ M1F * (1 / (2 * τ)) := mul_nonneg hM1F (by positivity)
  have hc2 : (0 : ℝ) ≤ Mqc * (1 / (4 * τ ^ 2)) := mul_nonneg hMqc (by positivity)
  -- the banked width-τ moments.
  have hm1 : ∫ z : Point n, ‖z‖ * gaussDdim τ z ≤ (n : ℝ) * (3 / 2) * Real.sqrt τ := by
    have h := normPow_gauss_tau (n := n) 1 (by norm_num) (3 / 2) (by norm_num) τ hτ
      (oneD_absMoment1 τ hτ)
    simpa [pow_one] using h
  have hm2 : ∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z ≤ (n : ℝ) * 2 * τ := by
    have h := normPow_gauss_tau (n := n) 2 (by norm_num) 2 (by norm_num) τ hτ
      (oneD_absMoment2 τ hτ)
    rwa [Real.sq_sqrt hτ.le] at h
  -- the final closed-form arithmetic (`√τ·√τ = τ`).
  have key : M1F * (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * Real.sqrt τ)
        + Mqc * (1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * τ)
        + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * 1
      = M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ) := by
    have hsq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ.le
    have hsne : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
    set s := Real.sqrt τ with hsdef
    rw [← hsq]
    field_simp
    ring
  -- the integral splits by linearity (term-mode `integral_add`, robust against HOU).
  have hlin : ∫ z : Point n, farFieldDom τ M1F M2F Mqc z
      = M1F * (1 / (2 * τ)) * (∫ z : Point n, ‖z‖ * gaussDdim τ z)
          + Mqc * (1 / (4 * τ ^ 2)) * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z)
          + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * (∫ z : Point n, gaussDdim τ z) :=
    calc ∫ z : Point n, farFieldDom τ M1F M2F Mqc z
        = ∫ z : Point n,
            (M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z)
              + Mqc * (1 / (4 * τ ^ 2)) * (‖z‖ ^ 2 * gaussDdim τ z))
            + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * gaussDdim τ z := by
          refine integral_congr_ae (ae_of_all _ (fun z => ?_))
          simp only [farFieldDom]; ring
      _ = (∫ z : Point n,
              M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z)
                + Mqc * (1 / (4 * τ ^ 2)) * (‖z‖ ^ 2 * gaussDdim τ z))
            + ∫ z : Point n, (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * gaussDdim τ z :=
          integral_add
            ((hI1.const_mul (M1F * (1 / (2 * τ)))).add
              (hI2.const_mul (Mqc * (1 / (4 * τ ^ 2)))))
            (hI0.const_mul (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))))
      _ = ((∫ z : Point n, M1F * (1 / (2 * τ)) * (‖z‖ * gaussDdim τ z))
              + ∫ z : Point n, Mqc * (1 / (4 * τ ^ 2)) * (‖z‖ ^ 2 * gaussDdim τ z))
            + ∫ z : Point n, (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * gaussDdim τ z := by
          rw [integral_add (hI1.const_mul (M1F * (1 / (2 * τ))))
            (hI2.const_mul (Mqc * (1 / (4 * τ ^ 2))))]
      _ = M1F * (1 / (2 * τ)) * (∫ z : Point n, ‖z‖ * gaussDdim τ z)
            + Mqc * (1 / (4 * τ ^ 2)) * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z)
            + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * (∫ z : Point n, gaussDdim τ z) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
  calc ∫ z : Point n, farFieldDom τ M1F M2F Mqc z
      = M1F * (1 / (2 * τ)) * (∫ z : Point n, ‖z‖ * gaussDdim τ z)
          + Mqc * (1 / (4 * τ ^ 2)) * (∫ z : Point n, ‖z‖ ^ 2 * gaussDdim τ z)
          + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * (∫ z : Point n, gaussDdim τ z) := hlin
    _ ≤ M1F * (1 / (2 * τ)) * ((n : ℝ) * (3 / 2) * Real.sqrt τ)
          + Mqc * (1 / (4 * τ ^ 2)) * ((n : ℝ) * 2 * τ)
          + (M2F + 2 * τ * (Mqc * (1 / (4 * τ ^ 2)))) * 1 := by
        rw [gaussDdim_integral_eq_one τ hτ]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hm1 hc1)
          (mul_le_mul_of_nonneg_left hm2 hc2)) le_rfl
    _ = M1F * (n : ℝ) * 3 / 4 / Real.sqrt τ + M2F + Mqc * ((n : ℝ) + 1) / (2 * τ) := key

end QIQTH.FarFieldMomentOrder

/-! ###############################################################################
    ## J4-491 LEDGER — the explicit O(1/τ) far-field moment order.
    ###############################################################################

  WHAT LANDS.  `farFieldDom_integral_le` computes `FarFieldDecay.farFieldDom`'s full-space integral to
  the explicit closed form `M1F·(3n/4)/√τ + M2F + Mqc·(n+1)/(2τ)`, exhibiting the far-field decay order
  term-by-term: gradient `O(τ^{-1/2})`, mass `O(1)`, Hessian `O(τ^{-1})` (DOMINANT).  This turns the
  DOMAIN/TAIL GATE prose verdict of J4-457 (`FarFieldDecay`) into a proved bound — the `∫ farFieldDom`
  carry that `hcomp_final4` / `slotInstantiation_phase10` thread through is now an explicit `O(1/τ)`.

  THE GATE (satisfiability).  REACHABLE.  `M1F/M2F/Mqc ≥ 0` are the same satisfiable global sups
  `farField_decay_bound` already carries; the moments are banked and true; no false pointwise inequality.

  DON'T-UNDERCREDIT.  The heavy lifting was ALREADY BANKED and reused verbatim: the moment envelope
  `HeatResidualBound.normPow_gauss_tau` (fed `oneD_absMoment1`/`oneD_absMoment2`), the mass identity
  `gaussDdim_integral_eq_one`, the per-piece integrability `normPow_gauss_integrable`/`gaussDdim_integrable`.
  The `FarFieldDecay.farFieldDom` dominator itself is J4-457.  This brick is a THIN integrate-and-simplify
  adapter (linearity + three banked moments + `ring`), NOT a re-derivation.

  HONEST DISTANCE.  These are the OFF-collar (global) sups, NOT the (I1)-closed ON-collar constants
  `M₀/M₁/M₂` of `C2AggregatorPhase6.collarSupConstants_of_reach` (J4-490): off `K` the witness term
  vanishes, so the far field is a pure Gaussian remainder controlled by the global sups — DISJOINT from
  the collar constants which control the on-collar leg.  The far field is now τ-order-CONTROLLED (explicit
  `O(1/τ)`), but NOT reduced to (I1).

  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack; this brick only
  makes the far-field moment order explicit.
-/

section AxiomChecks
open QIQTH.FarFieldMomentOrder
#print axioms farFieldDom_integral_le
end AxiomChecks
