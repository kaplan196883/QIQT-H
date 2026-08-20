/-
  HpardiffZTimeDerivReduction — J4-912: the census `hpardiff` binder (the companion parametric
  `HasDerivAt` for the frozen convolution's TIME parameter `c`) reduced to the named INNER `z`-level
  differentiation family, via the banked engine `HeatResidualBound.heatConvInner_hasDerivAt`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE reduction brick.  It supplies the previously-DATA-still `hpardiff`
  census binder — the differentiation-under-the-`z`-integral parametric `HasDerivAt` shared by the
  `hDuhamel` and `hDConv` legs — GIVEN the named inner `z`-level differentiation family (a per-`(s,c)`
  local `z`-integrable dominator, the `z`-slice measurabilities, and the genuine `z`-POINTWISE TIME
  `HasDerivAt` of the witness field).  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis (satisfiability EXHIBITED below), none equal to (or trivially
  yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## STRUCTURAL CLARIFICATION (gpt-5.6-sol high, confirmed against source).
  `hpardiff` is a SIBLING of the J4-911 `boundD`/`hbound_d` triple, NOT a consumer of it.  All six
  binders `{hFmeas_d, hFint_d, hF'meas_d, boundD/hbdd_d/hbound_d, hpardiff}` are the hypotheses of ONE
  DOWNSTREAM application of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the
  OUTER `s`-integral (parameter `c = u`): there `boundD/hbdd_d/hbound_d` play the outer `s`-level
  dominator (`bound`/`bound_integrable`/`h_bound`) and `hpardiff` plays the `h_diff` slot (the
  pointwise-in-`s` inner `HasDerivAt` in `c`).  A bound on `‖∫ z, …‖` cannot justify differentiating
  that `z`-integral; so `hpardiff` must be proved from a strictly LOWER-level differentiation — the
  INNER `z`-integral engine.

  ## THE ENGINE (banked).  `HeatResidualBound.heatConvInner_hasDerivAt` (`HeatConvRegularity.lean`) is
  the `t`-differentiation-under-the-`z`-integral (`.2` of `hasDerivAt_integral_of_dominated_loc_of_
  deriv_le`).  Fired at `A := Wit`, `dAu τ x z := deriv (fun r => Wit r x z) τ`, `B := F`, `x = y = 0`,
  `u₀ := c`, it yields EXACTLY the `hpardiff` per-`(s,c)` instance
      `HasDerivAt (fun c => ∫ z, Wit (c−s) 0 z · F s z 0)`
      `           (∫ z, deriv (fun r => Wit r 0 z) (c−s) · F s z 0) c`.

  ## THE CARRIED RESIDUE (honest, NOT discharged here).  The `z`-POINTWISE TIME `HasDerivAt` family
  `∀ᵐ z, ∀ c' ∈ V, HasDerivAt (fun c' => Wit (c'−s) 0 z · F s z 0) (…) c'` is the genuine geometric
  input — the DIFFERENTIABILITY sibling of the J4-911 crude-envelope BOUND `hAcrude`.
  `GatedTauDerivRep` banks only the deriv-EQUALITY representative (conditional on a carried amplitude
  `HasDerivAt hgate`), NOT the differentiability itself.  The local `z`-integrable dominator is
  constructible from the SAME `hAcrude`/`hFdom` envelopes as J4-911's `Dz` (`gaussDdim_pair_integrable`);
  the `z`-slice measurabilities are the F2-pile `z`-analogues.  This brick performs the ENGINE wiring
  (opaque `hpardiff` ⟹ named `z`-level family), mirroring J4-911's reduction of `boundD` to `hAcrude`.

  ⚠  STILL NOT `a₁ = R/6`.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import QIQTH.HeatConvRegularity
import QIQTH.ConvApproximants

open MeasureTheory Filter Set
open QIQTH.Curvature
open QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.HpardiffZTimeDeriv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ J4-912 — `hpardiff_of_zTimeDeriv`.**  THE `hpardiff` CENSUS BINDER, REDUCED.  Produces the
    VERBATIM generic-`(A,F)` `hpardiff` member — the parametric `HasDerivAt` in the TIME parameter `c`
    the C3ε outer-Leibniz application consumes — from the named INNER `z`-level differentiation family
    `hZ` (a per-`(m,u,s,c)` local neighborhood `V ∋ c` with a `z`-integrable dominator `Dz`, the base
    and derivative `z`-slice measurabilities/integrability, the `z`-pointwise dominator, and the genuine
    `z`-pointwise TIME `HasDerivAt` of the integrand) plus the global `z`-slice measurability `hAmeas`,
    fired through the banked engine `HeatResidualBound.heatConvInner_hasDerivAt` per `(s,c)`.

    Sol-recommended local-existential form (`∃ V ∈ 𝓝 c`) with the AE quantifier INNERMOST
    (`∀ᵐ z, ∀ c' ∈ V`, never the illegal `∀ c', ∀ᵐ z`).  NONE of the hypotheses is the conclusion: `hZ`
    supplies the `z`-POINTWISE (pre-integration) `HasDerivAt`, and the engine (Mathlib dominated
    differentiation) lifts it to the `z`-INTEGRAL `HasDerivAt`.  ⚠ NOT `a₁ = R/6`. -/
theorem hpardiff_of_zTimeDeriv
    (A F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (nb : ℕ → ℝ → Set ℝ)
    (hAmeas : ∀ (s u' : ℝ),
      AEStronglyMeasurable (fun z => A (u' - s) 0 z * F s z 0) volume)
    (hZ : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
        ∃ V ∈ 𝓝 c, ∃ Dz : Point n → ℝ,
          Integrable Dz volume ∧
          Integrable (fun z => A (c - s) 0 z * F s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => deriv (fun r => A r 0 z) (c - s) * F s z 0) volume ∧
          (∀ᵐ z ∂volume, ∀ c' ∈ V,
            ‖deriv (fun r => A r 0 z) (c' - s) * F s z 0‖ ≤ Dz z) ∧
          (∀ᵐ z ∂volume, ∀ c' ∈ V,
            HasDerivAt (fun c' => A (c' - s) 0 z * F s z 0)
              (deriv (fun r => A r 0 z) (c' - s) * F s z 0) c')) :
    ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
      HasDerivAt (fun c => ∫ z, A (c - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => A r 0 z) (c - s) * F s z 0) c := by
  intro m u hu
  filter_upwards [hZ m u hu] with s hs
  intro hsmem c hc
  obtain ⟨V, hV, Dz, hDz_int, hFint, hF'meas, hbound, hdiff⟩ := hs hsmem c hc
  exact heatConvInner_hasDerivAt A (fun τ x z => deriv (fun r => A r x z) τ) F s c
    (0 : Point n) (0 : Point n) V hV (hAmeas s) hFint hF'meas Dz hDz_int hbound hdiff

/-- **Non-vacuity witness.**  The full hypothesis bundle of `hpardiff_of_zTimeDeriv` is jointly
    satisfiable (`A ≡ 0`, `F ≡ 0`, `U = univ`, `nb = fun _ _ => univ`), so the reduction is NOT
    vacuously true — no J4-548-style unsatisfiable-antecedent trap. -/
theorem hpardiff_of_zTimeDeriv_hyp_satisfiable :
    ∃ (A F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (nb : ℕ → ℝ → Set ℝ),
      (∀ (s u' : ℝ), AEStronglyMeasurable (fun z => A (u' - s) 0 z * F s z 0) volume) ∧
      (∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ c ∈ nb m u,
        ∃ V ∈ 𝓝 c, ∃ Dz : Point n → ℝ,
          Integrable Dz volume ∧
          Integrable (fun z => A (c - s) 0 z * F s z 0) volume ∧
          AEStronglyMeasurable
            (fun z => deriv (fun r => A r 0 z) (c - s) * F s z 0) volume ∧
          (∀ᵐ z ∂volume, ∀ c' ∈ V,
            ‖deriv (fun r => A r 0 z) (c' - s) * F s z 0‖ ≤ Dz z) ∧
          (∀ᵐ z ∂volume, ∀ c' ∈ V,
            HasDerivAt (fun c' => A (c' - s) 0 z * F s z 0)
              (deriv (fun r => A r 0 z) (c' - s) * F s z 0) c')) := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, Set.univ, fun _ _ => Set.univ, ?_, ?_⟩
  · intro s u'
    simp only [mul_zero]
    exact aestronglyMeasurable_const
  · intro m u _hu
    refine Filter.Eventually.of_forall (fun s _hsmem c _hc => ?_)
    refine ⟨Set.univ, Filter.univ_mem, (fun _ => 0), integrable_zero _ _ _, ?_, ?_, ?_, ?_⟩
    · simp only [mul_zero]; exact integrable_zero _ _ _
    · simp only [mul_zero]; exact aestronglyMeasurable_const
    · refine Filter.Eventually.of_forall (fun z c' _ => ?_)
      simp
    · refine Filter.Eventually.of_forall (fun z c' _ => ?_)
      simp only [mul_zero]
      exact hasDerivAt_const c' (0 : ℝ)

end QIQTH.HpardiffZTimeDeriv

section AxiomChecks
open QIQTH.HpardiffZTimeDeriv
#print axioms hpardiff_of_zTimeDeriv
#print axioms hpardiff_of_zTimeDeriv_hyp_satisfiable
end AxiomChecks
