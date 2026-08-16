/-
  MixedSliverIntegrands — J4-803: the SEVEN integrability hypotheses of
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` WIRED through the gate-compact-support engine
  `MixedSliverQLipInt.integrable_of_finiteSupport_bounded` (J4-800).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is item (d) of
  the mixed-sliver chart-surface residue (J4-800/801/802): the seven per-slice integrabilities
  `hIntE1`/`hIntPlain`/`hIntRem`/`hInt0`/`hInt1i`/`hInt1j`/`hInt2` were "engine exists, concrete
  instantiation per-integrand unwired."  This file WIRES each of the seven concrete integrand SHAPES
  through the engine.

  ## THE STRUCTURAL FACT.  Every one of the seven integrands has the relevant AMPLITUDE as a literal
  multiplicative factor:
    • `hIntE1`/`hIntPlain`/`hIntRem` carry the factor `(A0 (u−s) z · F s z x)`;
    • `hInt0`  = `mTerm0 V Pi Pj Q A0 (u−s) z · F s z x`  (`mTerm0` ends in `· A0 τ z`);
    • `hInt1i` = `mTerm1 V Pj A1i (u−s) z · F s z x`       (`mTerm1` ends in `· A1 τ z`);
    • `hInt1j` = `mTerm1 V Pi A1j (u−s) z · F s z x`;
    • `hInt2`  = `sTerm2 V A2 (u−s) z · F s z x`           (`sTerm2` ends in `· A2 τ z`).
  In the concrete mixed normal form (`witnessMixed_hNormalForm_full`) the amplitudes are the **`S`-GATED**
  chart amplitudes `gateAmp S z₀ (…)` (J4-793), which VANISH off the gate set `S z₀`.  Hence each integrand
  VANISHES off the (finite-measure) gate, which is precisely the `hsupp` input of the engine.  The
  remaining two engine inputs — AE-strong-measurability and a global sup-bound — are carried; the
  sup-bound is REDUCED to an ON-GATE bound (off-gate the integrand is `0`, mirroring
  `MixedSliverAmpBounds.gateAmp_abs_le_onGate`) via `global_bound_of_onGate`.

  ── WHAT LANDS (all abstract; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `global_bound_of_onGate` — global sup-bound from an on-gate bound + off-gate vanishing.
    * `integrable_hIntE1` / `integrable_hIntPlain` / `integrable_hIntRem`
    * `integrable_hInt0` / `integrable_hInt1i` / `integrable_hInt1j` / `integrable_hInt2`
      — the seven per-slice integrabilities in the EXACT integrand shapes of
      `witness_sliver2_xuniform_mixed`, each reduced to {amplitude-vanishes-off-gate, finite gate,
      AE-measurable, on-gate bound}.

  Every hypothesis is satisfiable and non-vacuous (`A ≡ 0`, `S = ∅`, `M = 0`, `F ≡ 0` gives integrand `0`,
  trivially integrable; any bounded gated amplitude on a bounded gate is a genuine witness), and none
  equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverQLipInt
import QIQTH.MixedSliverAssembly

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.MixedSliverAssembly QIQTH.HeatResidualBound
open QIQTH.MixedSliverQLipInt
open scoped BigOperators ENNReal

namespace QIQTH.MixedSliverIntegrands

variable {n : ℕ}

/-! ############################################################################
    ### The on-gate → global sup-bound reduction (mirror of `gateAmp_abs_le_onGate`).
    ############################################################################ -/

/-- **★ `global_bound_of_onGate`.**  A function `h` that VANISHES off a set `S` and is bounded by
    `M ≥ 0` **on** `S` is bounded by `M` **globally**.  Off `S` it is `0` (`|0| = 0 ≤ M`); on `S` it is
    the hypothesis.  This is the exact reduction that turns the ON-GATE sup-bounds of the seven
    mixed-sliver integrands into the GLOBAL sup-bound the engine `integrable_of_finiteSupport_bounded`
    demands (mirror of `MixedSliverAmpBounds.gateAmp_abs_le_onGate`).  NOT `a₁ = R/6`. -/
theorem global_bound_of_onGate {X : Type*} (h : X → ℝ) (S : Set X) (M : ℝ) (hM : 0 ≤ M)
    (hsupp : ∀ z ∉ S, h z = 0) (hon : ∀ z ∈ S, |h z| ≤ M) :
    ∀ z, |h z| ≤ M := by
  intro z
  by_cases hz : z ∈ S
  · exact hon z hz
  · rw [hsupp z hz, abs_zero]; exact hM

/-! ############################################################################
    ### The seven concrete integrand integrabilities.
    ############################################################################ -/

/-- **★★ `integrable_hIntE1` — the `hIntE1` integrand.**  The mixed-Hessian chart-Gaussian residue
    integrand `(G_{u−s}(V z) − G_{u−s}(z))·[bracket]·(A0(u−s) z · F s z x)`, in the EXACT shape carried by
    `witness_sliver2_xuniform_mixed`, is integrable — it vanishes off the finite-measure gate `S` (where
    `A0(u−s) = 0`), is AE-measurable, and is bounded (on-gate bound lifted to global).  NOT `a₁ = R/6`. -/
theorem integrable_hIntE1
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |(gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
      * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
          - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hIntPlain` — the `hIntPlain` integrand.**  `G_{u−s}(z)·[bracket]·(A0(u−s) z · F s z x)`,
    the plain-Gaussian residue term, in the EXACT shape of `witness_sliver2_xuniform_mixed`.
    NOT `a₁ = R/6`. -/
theorem integrable_hIntPlain
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |gaussDdim (u - s) z
        * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
            - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
        * (A0 (u - s) z * F s z x)| ≤ M) :
    Integrable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, gaussDdim (u - s) z
      * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
          - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hIntRem` — the `hIntRem` integrand.**  The remainder term
    `G_{u−s}(z)·[bracket − z_i z_j/4(u−s)²]·(A0(u−s) z · F s z x)`, in the EXACT shape of
    `witness_sliver2_xuniform_mixed` (carrying the extra `−(z i · z j)/(4(u−s)²)` subtraction).
    NOT `a₁ = R/6`. -/
theorem integrable_hIntRem
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i j : Fin n) (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
              - (z i * z j) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) volume)
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
          * (A0 (u - s) z * F s z x)) volume := by
  have hsupp : ∀ z ∉ S, gaussDdim (u - s) z
      * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
          - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
          - (z i * z j) / (4 * (u - s) ^ 2))
      * (A0 (u - s) z * F s z x) = 0 := by
    intro z hz; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hInt0` — the `hInt0` integrand.**  `mTerm0 V Pi Pj Q A0 (u−s) z · F s z x`, in the
    EXACT shape of `witness_sliver2_xuniform_mixed`.  `mTerm0` ends in the factor `· A0 τ z`, so it
    vanishes off the gate where `A0(u−s) = 0`.  NOT `a₁ = R/6`. -/
theorem integrable_hInt0
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm0 V Pi Pj Q A0 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm0 V Pi Pj Q A0 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm0]; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hInt1i` — the `hInt1i` integrand.**  `mTerm1 V Pj A1i (u−s) z · F s z x`, in the
    EXACT shape of `witness_sliver2_xuniform_mixed`.  `mTerm1` ends in `· A1 τ z`.  NOT `a₁ = R/6`. -/
theorem integrable_hInt1i
    (V Pj : Point n → Point n) (A1i : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1i (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pj A1i (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm1 V Pj A1i (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm1]; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hInt1j` — the `hInt1j` integrand.**  `mTerm1 V Pi A1j (u−s) z · F s z x`, in the
    EXACT shape of `witness_sliver2_xuniform_mixed`.  NOT `a₁ = R/6`. -/
theorem integrable_hInt1j
    (V Pi : Point n → Point n) (A1j : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1j (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pi A1j (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm1 V Pi A1j (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm1]; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

/-- **★★ `integrable_hInt2` — the `hInt2` integrand.**  `sTerm2 V A2 (u−s) z · F s z x`, in the EXACT
    shape of `witness_sliver2_xuniform_mixed`.  `sTerm2` ends in `· A2 τ z`.  NOT `a₁ = R/6`. -/
theorem integrable_hInt2
    (V : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A2 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) volume)
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |sTerm2 V A2 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, sTerm2 V A2 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [sTerm2]; rw [hAsupp z hz]; ring
  exact integrable_of_finiteSupport_bounded _ S hS hSfin hsupp hmeas M
    (global_bound_of_onGate _ S M hM hsupp hon)

end QIQTH.MixedSliverIntegrands

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverIntegrands
#print axioms global_bound_of_onGate
#print axioms integrable_hIntE1
#print axioms integrable_hIntPlain
#print axioms integrable_hIntRem
#print axioms integrable_hInt0
#print axioms integrable_hInt1i
#print axioms integrable_hInt1j
#print axioms integrable_hInt2
end AxiomChecks
