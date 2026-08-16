/-
  MixedSliverIntegrandMeas — J4-806: the MEASURABILITY analog of `MixedSliverIntegrands.global_bound_of_onGate`
  (J4-804).  Reduces the AE-strong-measurability leg of each of the SEVEN mixed-sliver integrabilities
  (`hIntE1`/`hIntPlain`/`hIntRem`/`hInt0`/`hInt1i`/`hInt1j`/`hInt2`) from a GLOBAL
  `AEStronglyMeasurable … volume` to an ON-GATE `AEStronglyMeasurable … (volume.restrict S)`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the exact
  measurability-side twin of J4-804: J4-804 discharged the SUPPORT leg uniformly and reduced the BOUND
  leg to an ON-GATE bound (`global_bound_of_onGate`), but left the AE-strong-measurability leg as a
  GLOBAL `volume` carry.  This file supplies the missing structural reduction of THAT leg.

  ## WHY THE REDUCTION IS GENUINE PROGRESS (not a relabelling).
  The GLOBAL measurability `AEStronglyMeasurable (fun z => uniformInverseChart … z p) volume` of the raw
  chart pullback has NO SUPPLIER — the `Classical.choose`-opacity of `uniformInverseChart` is the
  campaign's single remaining "opaque-chart wall" (commit `3a1eaa99`).  But the ON-GATE (`volume.restrict`
  over the compact reach set) measurability of the SAME pullback IS supplied, from geometry alone, by the
  chart-reach CONTINUITY route `ChartGeneralPContinuity.hVmapMeasK_at_p_of_geom` (via
  `ContinuousOn.aestronglyMeasurable`).  So converting the seven integrands' `hmeas` legs from the
  unsupplied global form to the supplied on-gate form moves them PAST the opaque wall for the geometry
  factors; the residue becomes on-gate continuity of `gaussDdim`/`gateAmp` (available) plus the Levi-kernel
  `F` measurability (available downstream from `hEmeas`).

  ## THE STRUCTURAL FACT (mirror of J4-804).  Every one of the seven integrands VANISHES off the
  finite-measure gate `S` (the gated amplitude is a literal multiplicative factor, `= 0` off `S`).  A
  function that vanishes off a MEASURABLE set `S` equals `S.indicator` of itself, so its global
  AE-strong-measurability is EQUIVALENT (`aestronglyMeasurable_indicator_iff`) to the restricted
  `volume.restrict S` measurability.  `aesm_global_of_onGate` formalizes this; `integrable_of_onGate`
  packages it with the J4-804 bound reduction and the J4-800 engine into a single "purely on-gate"
  integrability engine; the seven `integrable_*_onGate` restate the exact witness integrand shapes with
  the `hmeas` leg in on-gate form.

  ── WHAT LANDS (all abstract; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `aesm_global_of_onGate`     — global AE-strong-measurability from on-gate (restrict) + off-gate vanishing.
    * `integrable_of_onGate`      — the consolidated "purely on-gate" integrability engine.
    * `integrable_hIntE1_onGate` / `integrable_hIntPlain_onGate` / `integrable_hIntRem_onGate`
    * `integrable_hInt0_onGate` / `integrable_hInt1i_onGate` / `integrable_hInt1j_onGate`
      / `integrable_hInt2_onGate`
      — the seven per-slice integrabilities in the EXACT integrand shapes of
      `witness_sliver2_xuniform_mixed`, each reduced to {amplitude-vanishes-off-gate, finite gate,
      ON-GATE AE-measurable, ON-GATE bound}.

  Every hypothesis is satisfiable and non-vacuous (`A ≡ 0`, `S = ∅`, `F ≡ 0` gives integrand `0`,
  trivially integrable; any continuous gated integrand on a bounded gate is a genuine witness), and none
  equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverIntegrands

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.MixedSliverAssembly QIQTH.HeatResidualBound
open QIQTH.MixedSliverQLipInt QIQTH.MixedSliverIntegrands
open scoped BigOperators ENNReal

namespace QIQTH.MixedSliverIntegrandMeas

variable {n : ℕ}

/-! ############################################################################
    ### The on-gate → global AE-strong-measurability reduction (measurability twin of
    ###   `MixedSliverIntegrands.global_bound_of_onGate`).
    ############################################################################ -/

/-- **★ `aesm_global_of_onGate`.**  A function `h` that VANISHES off a MEASURABLE set `S` and is
    AE-strongly-measurable **on** `S` (`μ.restrict S`) is AE-strongly-measurable **globally** (on `μ`).
    Off `S` it is `0`, so `h = S.indicator h` pointwise, and
    `aestronglyMeasurable_indicator_iff` turns the restricted measurability into the global one.  This is
    the exact reduction that turns the ON-GATE (compact-reach, chart-CONTINUOUS) measurability of the
    seven mixed-sliver integrands into the GLOBAL `volume` measurability the engine
    `integrable_of_finiteSupport_bounded` demands (measurability twin of
    `MixedSliverIntegrands.global_bound_of_onGate`).  NOT `a₁ = R/6`. -/
theorem aesm_global_of_onGate {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (h : X → ℝ) (S : Set X) (hS : MeasurableSet S)
    (hsupp : ∀ z ∉ S, h z = 0)
    (hon : AEStronglyMeasurable h (μ.restrict S)) :
    AEStronglyMeasurable h μ := by
  have hind : S.indicator h = h := by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hsupp z hz]
  have hindmeas : AEStronglyMeasurable (S.indicator h) μ :=
    (aestronglyMeasurable_indicator_iff hS).mpr hon
  rwa [hind] at hindmeas

/-! ############################################################################
    ### The consolidated "purely on-gate" integrability engine.
    ############################################################################ -/

/-- **★★ `integrable_of_onGate`.**  The J4-800 gate-compact-support engine
    (`integrable_of_finiteSupport_bounded`) with BOTH the measurability leg (via
    `aesm_global_of_onGate`) and the bound leg (via `MixedSliverIntegrands.global_bound_of_onGate`)
    reduced to purely ON-GATE data.  A function `h` that vanishes off a finite-measure MEASURABLE gate
    `S`, is AE-strongly-measurable ON `S`, and is bounded by `M ≥ 0` ON `S`, is integrable on `μ`.  This
    is the maximally-reduced form of the seven mixed-sliver integrabilities: every input is either
    geometric (finite gate, off-gate vanishing) or ON-GATE regularity (measurable + bounded on the
    compact reach set, both chart-continuity-supplied).  NOT `a₁ = R/6`. -/
theorem integrable_of_onGate {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (h : X → ℝ) (S : Set X) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hsupp : ∀ z ∉ S, h z = 0)
    (hon_meas : AEStronglyMeasurable h (μ.restrict S))
    (M : ℝ) (hM : 0 ≤ M) (hon_bnd : ∀ z ∈ S, |h z| ≤ M) :
    Integrable h μ :=
  integrable_of_finiteSupport_bounded h S hS hSfin hsupp
    (aesm_global_of_onGate h S hS hsupp hon_meas) M
    (global_bound_of_onGate h S M hM hsupp hon_bnd)

/-! ############################################################################
    ### The seven concrete integrand integrabilities — ON-GATE measurability form.
    ############################################################################ -/

/-- **★★ `integrable_hIntE1_onGate`.**  The `hIntE1` integrand, in the EXACT shape carried by
    `witness_sliver2_xuniform_mixed`, is integrable from purely on-gate data (measurable + bounded ON the
    finite gate `S`, where the amplitude `A0(u−s)` lives).  NOT `a₁ = R/6`. -/
theorem integrable_hIntE1_onGate
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
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
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hIntPlain_onGate`.**  The `hIntPlain` integrand, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hIntPlain_onGate
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
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
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hIntRem_onGate`.**  The `hIntRem` integrand (with the extra `−(z i·z j)/(4(u−s)²)`
    subtraction), on-gate measurability form.  NOT `a₁ = R/6`. -/
theorem integrable_hIntRem_onGate
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i j : Fin n) (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable (fun z : Point n =>
        gaussDdim (u - s) z
          * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
              - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
              - (z i * z j) / (4 * (u - s) ^ 2))
          * (A0 (u - s) z * F s z x)) (volume.restrict S))
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
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt0_onGate`.**  `mTerm0 V Pi Pj Q A0 (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt0_onGate
    (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A0 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm0 V Pi Pj Q A0 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm0 V Pi Pj Q A0 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm0]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt1i_onGate`.**  `mTerm1 V Pj A1i (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt1i_onGate
    (V Pj : Point n → Point n) (A1i : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1i (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pj A1i (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pj A1i (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm1 V Pj A1i (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm1]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt1j_onGate`.**  `mTerm1 V Pi A1j (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt1j_onGate
    (V Pi : Point n → Point n) (A1j : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A1j (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |mTerm1 V Pi A1j (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => mTerm1 V Pi A1j (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, mTerm1 V Pi A1j (u - s) z * F s z x = 0 := by
    intro z hz; simp only [mTerm1]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

/-- **★★ `integrable_hInt2_onGate`.**  `sTerm2 V A2 (u−s) z · F s z x`, on-gate measurability form.
    NOT `a₁ = R/6`. -/
theorem integrable_hInt2_onGate
    (V : Point n → Point n) (A2 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (u s : ℝ) (x : Point n)
    (S : Set (Point n)) (hS : MeasurableSet S) (hSfin : volume S < ∞)
    (hAsupp : ∀ z ∉ S, A2 (u - s) z = 0)
    (hmeas : AEStronglyMeasurable
        (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) (volume.restrict S))
    (M : ℝ) (hM : 0 ≤ M)
    (hon : ∀ z ∈ S, |sTerm2 V A2 (u - s) z * F s z x| ≤ M) :
    Integrable (fun z : Point n => sTerm2 V A2 (u - s) z * F s z x) volume := by
  have hsupp : ∀ z ∉ S, sTerm2 V A2 (u - s) z * F s z x = 0 := by
    intro z hz; simp only [sTerm2]; rw [hAsupp z hz]; ring
  exact integrable_of_onGate _ S hS hSfin hsupp hmeas M hM hon

end QIQTH.MixedSliverIntegrandMeas

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverIntegrandMeas
#print axioms aesm_global_of_onGate
#print axioms integrable_of_onGate
#print axioms integrable_hIntE1_onGate
#print axioms integrable_hIntPlain_onGate
#print axioms integrable_hIntRem_onGate
#print axioms integrable_hInt0_onGate
#print axioms integrable_hInt1i_onGate
#print axioms integrable_hInt1j_onGate
#print axioms integrable_hInt2_onGate
end AxiomChecks
