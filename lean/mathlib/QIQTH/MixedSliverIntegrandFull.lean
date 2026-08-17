/-
  MixedSliverIntegrandFull — J4-808: the seven mixed-sliver integrabilities discharged from PURELY
  PRIMITIVE on-gate data — the composition of the J4-806 on-gate integrability engines
  (`MixedSliverIntegrandMeas.integrable_*_onGate`) with the J4-807 on-gate measurability suppliers
  (`MixedSliverIntegrandMeasSupply.hmeas_*_onGate`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the final
  wiring of the seven mixed-sliver integrand integrabilities carried by
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed`.  J4-804 discharged the SUPPORT leg, J4-806
  reduced the measurability and bound legs to ON-GATE form, and J4-807 SUPPLIED the on-gate
  measurability leg from primitive factor measurability.  This file COMPOSES 806+807, so each of the
  seven `Integrable … volume` conclusions now follows from:
      { measurable gate `S`, finite gate, off-gate amplitude vanishing,
        vector on-gate measurability of `V/Pi/Pj/Q`, scalar on-gate measurability of `A0`/`F`,
        on-gate sup-bound `M` } —
  every one a PRIMITIVE geometric or on-gate regularity fact with a named supplier (the chart-reach
  continuity route for `V/Pi/Pj/Q`, `gaussDdim_cont` for the two Gaussian factors, the N1 `hEmeas` for
  the Levi field `F`, the amplitude sup-bounds J4-793 for the on-gate bound).  This is EXACTLY the shape
  `witness_sliver2_xuniform_mixed` consumes for each of `hIntE1`/`hIntPlain`/`hIntRem`/`hInt0`/`hInt1i`/
  `hInt1j`/`hInt2` — validated byte-for-byte by the fact that the composition typechecks.

  ── WHAT LANDS (all std-3; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `integrable_hIntE1_full` / `integrable_hIntPlain_full` / `integrable_hIntRem_full`
      / `integrable_hInt0_full` / `integrable_hInt1i_full` / `integrable_hInt1j_full`
      / `integrable_hInt2_full` — the seven integrabilities from primitive on-gate data.

  Every hypothesis is satisfiable and non-vacuous (`V=Pi=Pj=Q=0`, `A0=F=0` on `S`, `M=0` gives the
  constant-0 integrand, trivially integrable; any continuous gated data on a bounded gate is a genuine
  witness), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverIntegrandMeasSupply

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.MixedSliverAssembly QIQTH.HeatResidualBound
open QIQTH.MixedSliverIntegrands QIQTH.MixedSliverIntegrandMeas
open QIQTH.MixedSliverIntegrandMeasSupply
open scoped BigOperators ENNReal

namespace QIQTH.MixedSliverIntegrandFull

variable {n : ℕ}

/-- **★★ `integrable_hIntE1_full`.**  The `hIntE1` integrand is integrable from primitive on-gate data:
    finite measurable gate + off-gate amplitude vanishing + on-gate vector/scalar measurability of the
    factors + on-gate sup-bound.  NOT `a₁ = R/6`. -/
theorem integrable_hIntE1_full
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |(gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume :=
  integrable_hIntE1_onGate V Pi Pj Q A0 F u s x S hS hSfin hAsupp
    (hmeas_hIntE1_onGate V Pi Pj Q A0 F u s x S hV hPi hPj hQ hA0 hF) M hM hon

/-- **★★ `integrable_hIntPlain_full`.**  The `hIntPlain` integrand, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hIntPlain_full
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume :=
  integrable_hIntPlain_onGate V Pi Pj Q A0 F u s x S hS hSfin hAsupp
    (hmeas_hIntPlain_onGate V Pi Pj Q A0 F u s x S hV hPi hPj hQ hA0 hF) M hM hon

/-- **★★ `integrable_hIntRem_full`.**  The `hIntRem` integrand, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hIntRem_full
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i j : Fin n) (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
            - (z i * z j) / (4 * (u - s) ^ 2))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
              - (z i * z j) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) volume :=
  integrable_hIntRem_onGate V Pi Pj Q A0 F i j u s x S hS hSfin hAsupp
    (hmeas_hIntRem_onGate V Pi Pj Q A0 F i j u s x S hV hPi hPj hQ hA0 hF) M hM hon

/-- **★★ `integrable_hInt0_full`.**  `mTerm0 V Pi Pj Q A0 (u−s) z · F`, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt0_full
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm0 V Pi Pj Q A0 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume :=
  integrable_hInt0_onGate V Pi Pj Q A0 F u s x S hS hSfin hAsupp
    (hmeas_hInt0_onGate V Pi Pj Q A0 F u s x S hV hPi hPj hQ hA0 hF) M hM hon

/-- **★★ `integrable_hInt1i_full`.**  `mTerm1 V Pj A1i (u−s) z · F`, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt1i_full
    (V Pj : Point n → Point n) (A1i : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1i (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hA1i : AEStronglyMeasurable (fun z : Point n => A1i (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pj A1i (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) volume :=
  integrable_hInt1i_onGate V Pj A1i F u s x S hS hSfin hAsupp
    (hmeas_hInt1i_onGate V Pj A1i F u s x S hV hPj hA1i hF) M hM hon

/-- **★★ `integrable_hInt1j_full`.**  `mTerm1 V Pi A1j (u−s) z · F`, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt1j_full
    (V Pi : Point n → Point n) (A1j : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1j (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hA1j : AEStronglyMeasurable (fun z : Point n => A1j (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pi A1j (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) volume :=
  integrable_hInt1j_onGate V Pi A1j F u s x S hS hSfin hAsupp
    (hmeas_hInt1j_onGate V Pi A1j F u s x S hV hPi hA1j hF) M hM hon

/-- **★★ `integrable_hInt2_full`.**  `sTerm2 V A2 (u−s) z · F`, from primitive on-gate data.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt2_full
    (V : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A2 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hA2 : AEStronglyMeasurable (fun z : Point n => A2 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : AEStronglyMeasurable (fun z : Point n => F s z x)
      ((volume : Measure (Point n)).restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |sTerm2 V A2 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) volume :=
  integrable_hInt2_onGate V A2 F u s x S hS hSfin hAsupp
    (hmeas_hInt2_onGate V A2 F u s x S hV hA2 hF) M hM hon

end QIQTH.MixedSliverIntegrandFull

/-! ## Axiom checks — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverIntegrandFull
#print axioms integrable_hIntE1_full
#print axioms integrable_hIntPlain_full
#print axioms integrable_hIntRem_full
#print axioms integrable_hInt0_full
#print axioms integrable_hInt1i_full
#print axioms integrable_hInt1j_full
#print axioms integrable_hInt2_full
end AxiomChecks
