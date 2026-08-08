/-
  AuditPromotions — J4-418 (Part A): the two audit promotions requested by J4-417's VERDICT block.

  J4-417 (`JointInstantiabilityAudit.lean`) left two findings at INSPECTION level:
    • FINDING 3 (parenthetical) — the threaded Duhamel core's V1 per-`u` census binder group is the
      VERBATIM input shape of `PerUCensusTuple.hPd2conv_perU_fired`;
    • FINDING 4 — the moment-wall `hGpow` trio has the `∃ Cpair` chosen BEFORE the `(m, s)` binders
      (the correct `∃C ∀(m,s)` order — NOT the flipped `∀(m,s) ∃C` quantifier trap).
  This file PROMOTES both to machine-checked, mirroring `JointInstantiabilityAudit.audit_coreSlots_shape`.

  ⚠  HONESTY FIREWALL.  NEITHER lemma is `a₁ = R/6`, nor does this file discharge any analytic content.
  `audit_perU_shape` is a shape/witness-coherence certificate (it typechecks IFF the carrier's V1 binder
  group is verbatim the fired census tuple's input, and its output is verbatim the `hPd2conv` binder the
  core consumes).  `audit_hGpow_quantifier_order` is a projection of the banked `hGpow_covered` whose
  STATEMENT makes the `∃Cpair ∀(m,s)` order explicit.  No `sorry`, no `:= True`, no new axioms; std-3.
-/
import QIQTH.MomentWallCoverage
import QIQTH.PerUCensusTuple

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.LeviSeries QIQTH.ExpMap QIQTH.HeatKernelA1
open QIQTH.MomentWallCoverage QIQTH.PerUCensusTuple
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.AuditPromotions

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### A1 — `audit_perU_shape` : the V1 per-`u` census binder group = fired-tuple input.
    ############################################################################### -/

/-- **A1 — `audit_perU_shape`.**  THE V1 PER-`u` CENSUS SHAPE AUDIT (promotes J4-417 FINDING 3's
    parenthetical to machine-checked).  The hypothesis list is COPIED VERBATIM from the V1 per-`u` census
    binder group of `MomentWallCoverage.truncatedDuhamelCore_threaded_v3` (equivalently
    `TerminalCoverage.hPd2conv_threaded`): the field-neighbourhood data `nb`/`hnb_open`/`hnb0`, the
    positivity `hUpos`, the seven-leg linewise provider `hProv`, the bulk/limit fderivs
    `fderivBulk`/`gderiv`/`C₀`/`C₁`/`C₂`, the integrability `hGint`, the analytic sliver carries
    `hbulkderiv`/`hsliver`/`hcont`, and the frozen germ-link `hfrozen_pd1`.  The conclusion is COPIED
    VERBATIM from the `hPd2conv` binder that `GpowClosure.memLapFull_from_gpow_chain` /
    `truncatedDuhamelCore_threaded_v3` consumes.  The proof is the single application
    `PerUCensusTuple.hPd2conv_perU_fired`, so it COMPILES IFF the carrier's V1 binder group is verbatim
    the fired census tuple's input AND the fired output is verbatim the core's `hPd2conv` binder — the
    exact `id`-transport shape audit mirroring `audit_coreSlots_shape`.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_perU_shape (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    (hGint : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hfrozen_pd1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        (fun y => pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y)
          =ᶠ[𝓝 (0 : Point n)]
          QIQTH.FrozenGermInternal.fbulkInt g gi hChr hK S a b u i m) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.PerUCensusTuple.hPd2conv_perU_fired g gi hChr hK S a b U hUpos nb hnb_open hnb0 hProv
    fderivBulk gderiv C₀ C₁ C₂ hGint hbulkderiv hsliver hcont hfrozen_pd1

/-! ###############################################################################
    ### A2 — `audit_hGpow_quantifier_order` : `∃Cpair` fixed BEFORE `(m, s)`.
    ############################################################################### -/

/-- **A2 — `audit_hGpow_quantifier_order`.**  THE MOMENT-WALL QUANTIFIER-ORDER AUDIT (promotes J4-417
    FINDING 4 to machine-checked).  A PROJECTION of the banked `MomentWallCoverage.hGpow_covered` whose
    STATEMENT makes the quantifier order explicit: `∃ Cpair : ℝ, ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
    ∀ s ∈ uIoc …, |∫ …| ≤ Cpair · (u−s)^{−1/2}` — i.e. the single `Cpair` is bound BEFORE the `(m, s)`
    binders (the `m`-uniformity the historical `∀(m,s)∃C` trap would have flipped).  The proof `obtain`s
    the `(Cpair, hCpair, hGpow)` triple from `hGpow_covered` and re-packages `⟨Cpair, hGpow⟩`, dropping
    only the `0 ≤ Cpair` conjunct — so its compilation certifies the banked bundle really does supply the
    `m`-uniform (pre-`m,s`) `Cpair`.  ⚠ NOT `a₁ = R/6`. -/
theorem audit_hGpow_quantifier_order (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (τc Lc Bcomp Q Sconst : ℝ)
    (hLc : 0 ≤ Lc) (hBcomp : 0 ≤ Bcomp) (hQ : 0 ≤ Q) (hSconst : 0 ≤ Sconst)
    (hslot : ∀ (i : Fin n) (τ s : ℝ), 0 < τ → τ ≤ τc →
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i τ z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ (2 * Lc * (15 / 2 * (n : ℝ)) + Bcomp + Q) * τ ^ (-(1 : ℝ) / 2) + Sconst)
    (hcap : ∀ (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u, u - s ≤ τc)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0) :
    ∃ Cpair : ℝ,
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨Cpair, _, hGpow⟩ :=
    QIQTH.MomentWallCoverage.hGpow_covered g gi hChr hK S a b U τc Lc Bcomp Q Sconst
      hLc hBcomp hQ hSconst hslot hcap hEndpoint
  exact ⟨Cpair, hGpow⟩

end QIQTH.AuditPromotions

/-! ## Axiom checks — every public audit lemma is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.AuditPromotions
#print axioms audit_perU_shape
#print axioms audit_hGpow_quantifier_order
end AxiomChecks
