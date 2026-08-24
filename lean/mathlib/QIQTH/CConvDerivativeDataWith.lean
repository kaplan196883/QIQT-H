/-
  CConvDerivativeDataWith — J4-1180: dispatch 2 of the RESUMED witness-unification sub-campaign
  (`docs/qg_roadmap/WITNESS_UNIFICATION_PLAN.md`), Phase 1, D3 — the witness-derivative-parametric
  fork of `CConvFacade.CConvDerivativeData`, following the standard three-layer `XWith`/`X`/`X'`
  discipline established by the chart-parametric rebuild campaign (J4-1156 onward) and continued by
  `CConvChartGateDataWith` (J4-1179, D2).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It
  genericizes a `: Prop` DATA BUNDLE (never a conclusion) over an abstract witness-field-derivative
  `WD`, then instantiates it twice: once at the OLD concrete value (bridged back to the existing
  `CConvDerivativeData` via a two-way `Iff`, not `rfl`, since these are distinct `structure`
  declarations — every field-level equality involved IS `rfl`/definitional) and once at the NEW
  primed value `witnessFieldDeriv'`. No `sorry`, no new axioms, no `:= True`, no
  vacuous/unsatisfiable hypotheses, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## SCOPE CHECK (honest, done by this dispatch's own direct read of `CConvDerivativeData`,
  `CConvFacade.lean:130-144`, BEFORE writing any Lean — per the lesson of D2's own undercount).

  `WITNESS_UNIFICATION_PLAN.md`'s Phase 1 D3 entry describes forking "only `hDmeas`/`hDrep` (the
  fields naming `witnessFieldDeriv`)".  Direct re-read of the structure's THREE fields confirms this
  is EXACTLY RIGHT, with no undercount (unlike D2's chart-gate bundle, which had 5 hardwired fields
  against a stated 2):
    • `hDmeas` — calls `witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2` directly;
    • `hlin` — mentions only the GENERIC kernels `H`/`Fconv`/`D` (already abstract parameters of the
      structure itself, not `witnessFieldDeriv`) — no witness token at all;
    • `hDrep` — calls `witnessFieldDeriv g gi hC hK S a b i (t - s) x z` directly inside the
      defining integral.
  So exactly 2 of 3 fields are hardwired, matching the plan's count precisely.  `hlin` is kept FIXED
  verbatim below (mirroring `hSliceData`'s `Continuous` leg in `CConvChartGateDataWith`, the "kept
  fixed, not witness-shaped" precedent).

  NOT `a₁ = R/6`.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.
-/
import QIQTH.CConvFacade
import QIQTH.WitnessFieldDerivWith

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.OnGateFieldRegularity QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel
open QIQTH.CConvFacade
open scoped Topology

namespace QIQTH.CConvDerivativeWith

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE WITNESS-DERIVATIVE-PARAMETRIC SIBLING — `CConvDerivativeDataWith`.
    ############################################################################### -/

/-- **★★ `CConvDerivativeDataWith` — the witness-derivative-parametric variant of
    `CConvFacade.CConvDerivativeData`.**  Identical to the original bundle EXCEPT: the two fields that
    mention `witnessFieldDeriv` directly (`hDmeas`, `hDrep`) take an abstract witness-field-derivative
    `WD : Fin n → ℝ → Point n → Point n → ℝ` in place of the hardwired
    `witnessFieldDeriv g gi hC hK S a b`.  The witness-FREE field `hlin` (about the generic kernels
    `H`/`Fconv`/`D` only) is kept VERBATIM.  Pure `: Prop` data, never a conclusion.  NOT
    `a₁ = R/6`. -/
structure CConvDerivativeDataWith (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (WD : Fin n → ℝ → Point n → Point n → ℝ) : Prop where
  hDmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      Measurable (fun p : ℝ × Point n => WD i (t - p.1) x p.2)
  hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv H Fconv t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i)
  hDrep : ∀ x ∈ u,
      D x = ∑ i : Fin n,
        (∫ s in (0:ℝ)..t, ∫ z, WD i (t - s) x z * F s z
          ∂(volume : Measure (Point n))) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)

/-! ###############################################################################
    ### ★ THE COMPATIBILITY BRIDGE — old-derivative instantiation recovers
    ### `CConvDerivativeData` exactly.
    ############################################################################### -/

/-- **★ `derivativeDataWith_iff_old` — the compatibility bridge.**  Instantiating the generic
    `CConvDerivativeDataWith` at the OLD concrete witness derivative
    `witnessFieldDeriv g gi hC hK S a b` is `Iff`-equivalent to the EXISTING `CConvDerivativeData` —
    every field's TYPE is definitionally identical after substitution, so the equivalence is a plain
    field-by-field constructor map, closing by `exact`/projection alone. NOT `a₁ = R/6`. -/
theorem derivativeDataWith_iff_old (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ)) :
    CConvDerivativeDataWith g gi hC hK S a b t u F H Fconv D
        (witnessFieldDeriv g gi hC hK S a b)
      ↔ CConvDerivativeData g gi hC hK S a b t u F H Fconv D := by
  constructor
  · intro h
    exact { hDmeas := h.hDmeas, hlin := h.hlin, hDrep := h.hDrep }
  · intro h
    exact { hDmeas := h.hDmeas, hlin := h.hlin, hDrep := h.hDrep }

/-! ###############################################################################
    ### THE NEW-DERIVATIVE INSTANTIATION — `CConvDerivativeData'`.
    ############################################################################### -/

/-- **`CConvDerivativeData'` — the NEW-derivative instantiation.**  `CConvDerivativeDataWith` at
    `WD := witnessFieldDeriv' g gi hC hK S a b c`, for a fixed tube radius `c` — the primed analogue
    of `CConvDerivativeData`, threading Campaign 1's primed field-derivative throughout every
    witness-mentioning field.  NOT globally `Iff`-equivalent to the old `CConvDerivativeData` (the two
    derivatives agree only on a bounded tube image; no such claim is made or needed here). NOT
    `a₁ = R/6`. -/
def CConvDerivativeData' (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ)) (c : ℝ) : Prop :=
  CConvDerivativeDataWith g gi hC hK S a b t u F H Fconv D
    (witnessFieldDeriv' g gi hC hK S a b c)

end QIQTH.CConvDerivativeWith

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CConvDerivativeWith
#print axioms derivativeDataWith_iff_old
end AxiomChecks
