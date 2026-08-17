/-
  SliverIntegrandXUniform — J4-815: the x-UNIFORM CO-INSTANTIATION of the sliver-integrand
  integrabilities.  Both the mixed (`MixedSliverXUniform.witness_sliver2_xuniform_mixed`) and the
  diagonal (`XUniformSliverFull.witness_sliver2_xuniform`) sliver rate theorems carry their per-slice
  integrand integrabilities in the `∀ x, ∀ s ∈ Ioo (u−ε) u, Integrable … volume` shape.  J4-808
  (`MixedSliverIntegrandFull.integrable_*_full`) and J4-812 (`DiagSliverIntegrands.integrable_*_onGate`)
  discharged each of these to on-gate data, but ONLY at a FIXED, GENERIC field point `x` and slice `s`.
  This file performs the missing CO-INSTANTIATION: it packages the on-gate input data quantified over
  `(x, s)` and produces the exact `∀ x, ∀ s ∈ Ioo (u−ε) u, Integrable …` conclusions the two sliver
  theorems consume.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  QUANTIFIER-WIRING step: the per-`(x,s)` engines already work for GENERIC `(x,s)`, so the uniform
  statement is obtained by `intro x s hs` and applying the engine.  The only genuinely `(x,s)`-dependent
  inputs are:
    • the amplitude off-gate vanishing `hAsupp` (depends on `s` through `u−s`);
    • the Levi-field on-gate measurability `hF` (depends on `x` and `s`);
    • the on-gate sup-bound `M`/`hon` (depends on `x` and `s`, carried as a per-`(x,s)` `∃ M`).
  The gate `S`, its finiteness/measurability, and the geometric factor measurabilities of `V/Pi/Pj/Q`
  (resp. `Y/P`) are field- and slice-INDEPENDENT, supplied ONCE.  This is EXACTLY the co-instantiation
  the residue of J4-811/J4-814 identified.

  ── WHAT LANDS (all std-3; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    MIXED (the seven `witness_sliver2_xuniform_mixed` slots):
      * `uniform_hIntE1_mixed` / `uniform_hIntPlain_mixed` / `uniform_hIntRem_mixed`
        / `uniform_hInt0_mixed` / `uniform_hInt1i_mixed` / `uniform_hInt1j_mixed` / `uniform_hInt2_mixed`.
    DIAGONAL (the five `witness_sliver2_xuniform` slots):
      * `uniform_hIntT1_diag` / `uniform_hIntT2_diag` / `uniform_hIntT3_diag`
        / `uniform_hInt1_diag` / `uniform_hInt2_diag`.

  Every hypothesis is satisfiable and non-vacuous (`V=Pi=Pj=Q=0`, `A0=A1i=A1j=A2=F=0` on `S`, per-`(x,s)`
  `M=0` gives the constant-0 integrand, trivially integrable; any continuous gated data on a bounded gate
  is a genuine witness), and none equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverIntegrandFull
import QIQTH.DiagSliverIntegrands

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.MixedSliverAssembly QIQTH.HeatResidualBound
open QIQTH.MixedSliverIntegrandFull QIQTH.DiagSliverIntegrands
open scoped BigOperators ENNReal

namespace QIQTH.SliverIntegrandXUniform

variable {n : ℕ}

/-! ###############################################################################
    ★★ MIXED — the seven `witness_sliver2_xuniform_mixed` integrability slots, x-uniform.
    ############################################################################### -/

/-- **★★ `uniform_hIntE1_mixed`.**  The `hIntE1` slot of `witness_sliver2_xuniform_mixed`, co-instantiated
    to `∀ x, ∀ s ∈ Ioo (u−ε) u, Integrable …` from `(x,s)`-quantified on-gate data.  NOT `a₁ = R/6`. -/
theorem uniform_hIntE1_mixed
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |(gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntE1_full V Pi Pj Q A0 F u s x S hS hSfin (hAsupp s hs)
    hV hPi hPj hQ (hA0 s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hIntPlain_mixed`.**  The `hIntPlain` slot, x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hIntPlain_mixed
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntPlain_full V Pi Pj Q A0 F u s x S hS hSfin (hAsupp s hs)
    hV hPi hPj hQ (hA0 s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hIntRem_mixed`.**  The `hIntRem` slot (parity moment `zᵢ zⱼ`), x-uniform.
    NOT `a₁ = R/6`. -/
theorem uniform_hIntRem_mixed
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i j : Fin n) (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
            - (z i * z j) / (4 * (u - s) ^ 2))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
              - (z i * z j) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntRem_full V Pi Pj Q A0 F i j u s x S hS hSfin (hAsupp s hs)
    hV hPi hPj hQ (hA0 s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hInt0_mixed`.**  The `hInt0` slot (`mTerm0 V Pi Pj Q A0 · F`), x-uniform.
    NOT `a₁ = R/6`. -/
theorem uniform_hInt0_mixed
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hQ : AEStronglyMeasurable Q ((volume : Measure (Point n)).restrict S))
    (hA0 : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A0 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |mTerm0 V Pi Pj Q A0 (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt0_full V Pi Pj Q A0 F u s x S hS hSfin (hAsupp s hs)
    hV hPi hPj hQ (hA0 s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hInt1i_mixed`.**  The `hInt1i` slot (`mTerm1 V Pj A1i · F`), x-uniform.
    NOT `a₁ = R/6`. -/
theorem uniform_hInt1i_mixed
    (V Pj : Point n → Point n) (A1i : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A1i (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPj : AEStronglyMeasurable Pj ((volume : Measure (Point n)).restrict S))
    (hA1i : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A1i (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |mTerm1 V Pj A1i (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt1i_full V Pj A1i F u s x S hS hSfin (hAsupp s hs)
    hV hPj (hA1i s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hInt1j_mixed`.**  The `hInt1j` slot (`mTerm1 V Pi A1j · F`), x-uniform.
    NOT `a₁ = R/6`. -/
theorem uniform_hInt1j_mixed
    (V Pi : Point n → Point n) (A1j : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A1j (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hPi : AEStronglyMeasurable Pi ((volume : Measure (Point n)).restrict S))
    (hA1j : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A1j (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |mTerm1 V Pi A1j (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt1j_full V Pi A1j F u s x S hS hSfin (hAsupp s hs)
    hV hPi (hA1j s hs) (hF x s hs) M hM hon

/-- **★★ `uniform_hInt2_mixed`.**  The `hInt2` slot (`sTerm2 V A2 · F`), x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hInt2_mixed
    (V : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A2 (u - s) z = 0)
    (hV : AEStronglyMeasurable V ((volume : Measure (Point n)).restrict S))
    (hA2 : ∀ s ∈ Set.Ioo (u - ε) u, AEStronglyMeasurable (fun z : Point n => A2 (u - s) z)
      ((volume : Measure (Point n)).restrict S))
    (hF : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => F s z x) ((volume : Measure (Point n)).restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |sTerm2 V A2 (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt2_full V A2 F u s x S hS hSfin (hAsupp s hs)
    hV (hA2 s hs) (hF x s hs) M hM hon

/-! ###############################################################################
    ★★ DIAGONAL — the five `witness_sliver2_xuniform` integrability slots, x-uniform.
    The diagonal on-gate engines (`DiagSliverIntegrands.integrable_*_onGate`) consume the COMPOSED
    on-gate measurability directly, so it is carried here as the `(x,s)`-quantified `hmeas`.
    ############################################################################### -/

/-- **★★ `uniform_hIntT1_diag`.**  The `hIntT1` slot of `witness_sliver2_xuniform` (E1 Gaussian-
    replacement Hessian bracket), x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hIntT1_diag
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |(gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
        * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        (gaussDdim (u - s) (Y z) - gaussDdim (u - s) z)
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntT1_onGate Y P Q A0 F u s x S hS hSfin (hAsupp s hs) (hmeas x s hs) M hM hon

/-- **★★ `uniform_hIntT2_diag`.**  The `hIntT2` slot (plain-Gaussian bracket minus the mass moment),
    x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hIntT2_diag
    (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
            - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
            - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, Y z k * P z k) ^ 2 / (4 * (u - s) ^ 2)
              - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * (u - s))
              - ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntT2_onGate Y P Q A0 F i u s x S hS hSfin (hAsupp s hs) (hmeas x s hs) M hM hon

/-- **★★ `uniform_hIntT3_diag`.**  The `hIntT3` slot (isolated mass moment), x-uniform.
    NOT `a₁ = R/6`. -/
theorem uniform_hIntT3_diag
    (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n =>
        ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
        * (A0 (u - s) z * F s z x)| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n =>
        ((z i) ^ 2 - 2 * (u - s)) / (4 * (u - s) ^ 2) * gaussDdim (u - s) z
          * (A0 (u - s) z * F s z x)) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hIntT3_onGate A0 F i u s x S hS hSfin (hAsupp s hs) (hmeas x s hs) M hM hon

/-- **★★ `uniform_hInt1_diag`.**  The `hInt1` slot (`sTerm1 Y P A1 · F`), x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hInt1_diag
    (Y P : Point n → Point n) (A1 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A1 (u - s) z = 0)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => sTerm1 Y P A1 (u - s) z * F s z x) (volume.restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |sTerm1 Y P A1 (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => sTerm1 Y P A1 (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt1_onGate Y P A1 F u s x S hS hSfin (hAsupp s hs) (hmeas x s hs) M hM hon

/-- **★★ `uniform_hInt2_diag`.**  The `hInt2` slot (`sTerm2 Y A2 · F`), x-uniform.  NOT `a₁ = R/6`. -/
theorem uniform_hInt2_diag
    (Y : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u ε : ℝ)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z ∉ S, A2 (u - s) z = 0)
    (hmeas : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      AEStronglyMeasurable (fun z : Point n => sTerm2 Y A2 (u - s) z * F s z x) (volume.restrict S))
    (hbnd : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ S, |sTerm2 Y A2 (u - s) z * F s z x| ≤ M) :
    ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
      Integrable (fun z : Point n => sTerm2 Y A2 (u - s) z * F s z x) volume := by
  intro x s hs
  obtain ⟨M, hM, hon⟩ := hbnd x s hs
  exact integrable_hInt2_onGate Y A2 F u s x S hS hSfin (hAsupp s hs) (hmeas x s hs) M hM hon

end QIQTH.SliverIntegrandXUniform

/-! ## Axiom checks — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SliverIntegrandXUniform
#print axioms uniform_hIntE1_mixed
#print axioms uniform_hIntPlain_mixed
#print axioms uniform_hIntRem_mixed
#print axioms uniform_hInt0_mixed
#print axioms uniform_hInt1i_mixed
#print axioms uniform_hInt1j_mixed
#print axioms uniform_hInt2_mixed
#print axioms uniform_hIntT1_diag
#print axioms uniform_hIntT2_diag
#print axioms uniform_hIntT3_diag
#print axioms uniform_hInt1_diag
#print axioms uniform_hInt2_diag
end AxiomChecks
