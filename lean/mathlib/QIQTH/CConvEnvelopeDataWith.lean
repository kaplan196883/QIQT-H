/-
  CConvEnvelopeDataWith — J4-1181: dispatch 3 of the RESUMED witness-unification sub-campaign
  (`docs/qg_roadmap/WITNESS_UNIFICATION_PLAN.md`), Phase 1, D4 — the chart-and-amplitude-and-witness
  -parametric fork of `CConvFacade.CConvEnvelopeData`, following the standard three-layer
  `XWith`/`X`/`X'` discipline established by the chart-parametric rebuild campaign (J4-1156 onward)
  and continued by `CConvChartGateDataWith` (J4-1179, D2) / `CConvDerivativeDataWith` (J4-1180, D3).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes a `: Prop` DATA BUNDLE (never a conclusion) over an abstract chart `W`, an abstract
  chart-field amplitude `AMP`, and an abstract gated witness `GW`, then instantiates it twice: once at
  the OLD concrete values (bridged back to the existing `CConvEnvelopeData` via a two-way `Iff`, not
  `rfl`, since these are distinct `structure` declarations — every field-level equality involved IS
  `rfl`/definitional) and once at the NEW primed values `uniformInverseChart'`/`chartFieldAmp'`/
  `vanVleckGatedWitness'`. No `sorry`, no new axioms, no `:= True`, no vacuous/unsatisfiable
  hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SCOPE CORRECTION (honest, found by this dispatch's own direct read of `CConvEnvelopeData`,
  `CConvFacade.lean:150-182`, BEFORE writing any Lean — per D2's own "recheck, don't trust the plan's
  literal field count" lesson, and D3's confirmation that the count is SOMETIMES exactly right).

  `WITNESS_UNIFICATION_PLAN.md`'s Phase 1 D4 entry describes forking "`hC2fam`/`hGateData` (naming
  `vanVleckGatedWitness`/`uniformInverseChart`/`chartFieldAmp` directly)" — TWO fields.  Direct re-read
  of the structure's FOUR fields finds this undercounts by one, the SAME class of undercount D2 found
  (and flagged as "NOT a STOP trigger — the same known fork point, more completely counted"):
    • `hcoef` — `0 ≤ Bs * Ba + Bd`, no chart/witness/amplitude token — witness-FREE, kept fixed;
    • `hC2fam` — calls `vanVleckGatedWitness g gi hC hK S a b (t - s) x' z` directly — hardwired;
    • `hGateData` — calls `uniformInverseChart g gi hC hK z ...` (twice) AND
      `chartFieldAmp g gi hC hK a b (t - s) z` (three times: the abs bound, the `pd`, the `PdiffAt`
      leg) directly — hardwired;
    • `hGateData'` — the `∀ᵐ s → ∀ᶠ x` order-swapped TWIN of `hGateData`, with the IDENTICAL chart and
      amplitude tokens — ALSO hardwired, but omitted from the plan's literal "`hC2fam`/`hGateData`"
      list. This is NOT a new obstruction: `hGateData'` is structurally identical to `hGateData` (same
      body, only the `∀ᵐ`/`∀ᶠ` binder order differs), so forking it is the same mechanical
      substitution, done below alongside `hGateData`.
  So 3 of 4 fields are hardwired (`hC2fam`, `hGateData`, `hGateData'`), not 2 as literally stated.
  Per this dispatch's canary discipline (STOP on a genuine NEW obstruction, not on a more complete
  field count matching D2's precedent), this does not warrant halting.

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.CConvFacade
import QIQTH.ChartFieldAmpWith
import QIQTH.VanVleckGatedWitnessWith
import QIQTH.ThetaMeasurableEmbedding

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.OnGateFieldRegularity QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.ThetaMeasurableEmbedding
open QIQTH.CConvFacade
open scoped Topology

namespace QIQTH.CConvEnvelopeWith

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE CHART/AMPLITUDE/WITNESS-PARAMETRIC SIBLING — `CConvEnvelopeDataWith`.
    ############################################################################### -/

/-- **★★ `CConvEnvelopeDataWith` — the chart-and-amplitude-and-witness-parametric variant of
    `CConvFacade.CConvEnvelopeData`.**  Identical to the original bundle EXCEPT: `hC2fam` takes an
    abstract gated witness `GW : ℝ → Point n → Point n → ℝ` in place of the hardwired
    `vanVleckGatedWitness g gi hC hK S a b`; `hGateData`/`hGateData'` take an abstract chart
    `W : Point n → Point n → Point n` in place of `uniformInverseChart g gi hC hK` and an abstract
    chart-field amplitude `AMP : ℝ → Point n → Point n → ℝ` in place of
    `chartFieldAmp g gi hC hK a b`.  The chart/witness-FREE field `hcoef` is kept VERBATIM.  Pure
    `: Prop` data, never a conclusion.  NOT `a₁ = R/6`. -/
structure CConvEnvelopeDataWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ)
    (W : Point n → Point n → Point n)
    (AMP : ℝ → Point n → Point n → ℝ)
    (GW : ℝ → Point n → Point n → ℝ) : Prop where
  hcoef : 0 ≤ Bs * Ba + Bd
  hC2fam : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
      ContDiffAt ℝ 2 (fun x' => GW (t - s) x' z) x₀
  hGateData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∉ K ∨
        (∃ Pval : Fin n → ℝ,
          z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
          (∀ k, HasDerivAt
            (fun r : ℝ => W z (Function.update x i r) k) (Pval k)
            (x i)) ∧
          PdiffAt (AMP (t - s) z) i x ∧
          |(-(∑ k, W z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
          |AMP (t - s) z x| ≤ Ba ∧
          |pd (AMP (t - s) z) i x| ≤ Bd ∧
          (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z x))
  hGateData' : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
        z ∉ K ∨
        (∃ Pval : Fin n → ℝ,
          z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
          (∀ k, HasDerivAt
            (fun r : ℝ => W z (Function.update x i r) k) (Pval k)
            (x i)) ∧
          PdiffAt (AMP (t - s) z) i x ∧
          |(-(∑ k, W z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
          |AMP (t - s) z x| ≤ Ba ∧
          |pd (AMP (t - s) z) i x| ≤ Bd ∧
          (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (W z x))

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGE — old-chart/old-amplitude/old-witness instantiation
    ### recovers `CConvEnvelopeData` exactly.
    ############################################################################### -/

/-- **★ `envelopeDataWith_iff_old` — the compatibility bridge.**  Instantiating the generic
    `CConvEnvelopeDataWith` at the OLD concrete chart `uniformInverseChart g gi hC hK`, the OLD
    concrete amplitude `chartFieldAmp g gi hC hK a b`, and the OLD concrete gated witness
    `vanVleckGatedWitness g gi hC hK S a b` is `Iff`-equivalent to the EXISTING `CConvEnvelopeData` —
    every field's TYPE is definitionally identical after substitution, so the equivalence is a plain
    field-by-field constructor map, closing by `exact`/projection alone. NOT `a₁ = R/6`. -/
theorem envelopeDataWith_iff_old (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) :
    CConvEnvelopeDataWith g gi hC hK S a b t u Bs Ba Bd
        (uniformInverseChart g gi hC hK) (chartFieldAmp g gi hC hK a b)
        (vanVleckGatedWitness g gi hC hK S a b)
      ↔ CConvEnvelopeData g gi hC hK S a b t u Bs Ba Bd := by
  constructor
  · intro h
    exact
      { hcoef := h.hcoef
        hC2fam := h.hC2fam
        hGateData := h.hGateData
        hGateData' := h.hGateData' }
  · intro h
    exact
      { hcoef := h.hcoef
        hC2fam := h.hC2fam
        hGateData := h.hGateData
        hGateData' := h.hGateData' }

/-! ###############################################################################
    ### THE NEW-CHART/NEW-AMPLITUDE/NEW-WITNESS INSTANTIATION — `CConvEnvelopeData'`.
    ############################################################################### -/

/-- **`CConvEnvelopeData'` — the NEW-chart/NEW-amplitude/NEW-witness instantiation.**
    `CConvEnvelopeDataWith` at `W := uniformInverseChart' g gi hC hK c`,
    `AMP := chartFieldAmp' g gi hC hK a b c`, `GW := vanVleckGatedWitness' g gi hC hK S a b c`, for a
    fixed tube radius `c` — the primed analogue of `CConvEnvelopeData`, threading Campaign 1's
    jointly-measurable chart, primed amplitude, and primed gated witness throughout every
    chart/amplitude/witness-mentioning field. NOT globally `Iff`-equivalent to the old
    `CConvEnvelopeData` (the two charts agree only on a bounded tube image; no such claim is made or
    needed here). NOT `a₁ = R/6`. -/
def CConvEnvelopeData' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (Bs Ba Bd : ℝ) (c : ℝ) : Prop :=
  CConvEnvelopeDataWith g gi hC hK S a b t u Bs Ba Bd
    (uniformInverseChart' g gi hC hK c) (chartFieldAmp' g gi hC hK a b c)
    (vanVleckGatedWitness' g gi hC hK S a b c)

end QIQTH.CConvEnvelopeWith

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvEnvelopeWith
#print axioms envelopeDataWith_iff_old
end AxiomChecks
