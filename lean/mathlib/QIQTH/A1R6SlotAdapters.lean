/-
  A1R6SlotAdapters — J4-339: v3-export bricks 2 + 3 + 4.  The adapters feeding the pre-∃ core
  `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS` (J4-338): the `htr` re-export (brick 2), the
  `Da`-limit gate thread (brick 3), and the shallow slot package `A1R6GateSlots` (brick 4).  ONE step of
  the `a₁ = R/6` heat-kernel campaign.

  ⚠ HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Everything
  here is a CONDITIONAL re-export / adapter: the `htr` binder still rests on the labelled gauge input
  `hGauss` (via `NCRiemannTwoJet.htr_from_hGauss`); the `Da`-limit still rests on the entire labelled
  census of `GlobalRawBoundFacade.hDaLimLU_from_labelled` (four labelled inputs `hGauss/hraw/hD2Hexpand/
  hPd2conv` + the analytic piles); the three per-gate analytic slots (`hDuhamel/hDConv/hCConv`) are still
  carried antecedents with their FULL honest hypothesis piles.  `a₁ = R/6` stays CONDITIONAL.  Brick 5
  (`a1_R6_from_labelled`) will bundle these piles behind the four labelled inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## FEED-SHAPE VERDICTS (read off the banked producers).

  ── (L2, brick 2) `htr_adapter`.  The core's `htr` binder is
       `htr : ∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0) = -(2/3) * Ric cc d`
     with `Ric : Fin n → Fin n → ℝ` an ABSTRACT parameter.  `NCRiemannTwoJet.htr_from_hGauss` concludes
     the SAME identity per-component at the CONCRETE curvature `Ric := ricci g gi · · 0`.  So the core's
     `Ric` is instantiated at `fun c d => ricci g gi c d 0` and `htr_adapter` supplies the `∀`-form
     verbatim.  Direct re-export.

  ── (L3, brick 3) `daLim_for_slots` — THE GATE MATCH.  `GlobalRawBoundFacade.hDaLimLU_from_labelled`
     takes `S` as a GENERIC parameter and concludes `DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK
     S a b) (leviSeries (heatOp g gi (vanVleckGatedWitness …))) U`.  Instantiating `S := constGate g gi
     hChr hK c` gives the `DaLimLUGoal` at the LITERAL constant-radius gate.  `DaLimLUGoal` is the abbrev
       `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
         (fun u => laplaceBeltrami g gi (fun x => heatConv H F u x 0) 0 + heatConv (heatOp g gi H) F u 0 0) atTop U`
     which is EXACTLY the `hDaLimLU` antecedent that `HDConvGateThreading.hDConv_W1free` consumes (and, in
     the same abbrev shape, what `truncatedDuhamelCore_AT_GATE` consumes for the Duhamel core).  So the
     thread is DIRECT — `daLim_for_slots` certifies the defeq (abbrev-unfold) shape match with NO adapter
     and NO re-derivation of the ~60-binder labelled census (brick 5 calls `hDaLimLU_from_labelled`
     directly at `S := constGate`).

  ── (L4, brick 4) `A1R6GateSlots`.  A shallow `Prop` structure with the three slot fields at the literal
     gate — VERBATIM the core's `hDuhamel/hDConv/hCConv` binders.  `a1_R6_slots_AT_GATE` produces it from
     the three banked slot producers:
       • `hDuhamel` field  ← `HDuhamelExportRethread.hDuhamelSlot_AT_GATE` (from a `TruncatedDuhamelCore`);
       • `hDConv`   field  ← `HDConvGateThreading.hDConv_W1free` (its W1-free census + the `Da`-limit L3
                             input `hDaLimLU : DaLimLUGoal …` + the boundary loc-unif `hbdryLU`);
       • `hCConv`   field  ← `CConvV2Facade.hCConvSlot_AT_GATE_v2` (the open-nbhd + linewise-`HasDerivAt`
                             family + the L2 sliver census).
     The `H`/`F` of the Duhamel + DConv legs are pinned to the concrete witness / Levi source by two
     defining equations `hHeq`/`hFeq` (satisfiable by `rfl`), discharged by `subst` so the fields match
     the structure syntactically.  Every carried hypothesis pile is enumerated honestly — the slot
     censuses are LONG, which is expected; brick 5 bundles them.  NONE of the hypotheses is the
     conclusion.  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NCRiemannTwoJet
import QIQTH.GlobalRawBoundFacade
import QIQTH.HDuhamelExportRethread
import QIQTH.HDConvGateThreading
import QIQTH.CConvV2Facade
import QIQTH.A1R6CoreAtGate

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HEmeasRecon QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami
open QIQTH.CConvV2DerivRep QIQTH.TruncatedDuhamelData QIQTH.DaLimLUWallRecon
open QIQTH.NCRiemannTwoJet QIQTH.GlobalRawBoundFacade QIQTH.HDuhamelExportRethread
open QIQTH.HDConvGateThreading QIQTH.CConvV2Facade QIQTH.A1R6CoreAtGate
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6SlotAdapters

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (L2 — brick 2) `htr_adapter` — the core's `htr` binder at `Ric := ricci g gi · · 0`.
    ############################################################################### -/

/-- **★★ (L2) `htr_adapter`.**  The core `wide_a1_R6_core_AT_CONSTRADIUS`'s `htr` binder shape
    `∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0) = -(2/3) * Ric cc d`, at the concrete
    Ricci instantiation `Ric := fun cc d => ricci g gi cc d 0`, re-exported verbatim from
    `NCRiemannTwoJet.htr_from_hGauss`.  The whole R3 Ricci-source coefficient still rests on the labelled
    gauge input `hGauss`.  ⚠ NOT `a₁ = R/6`. -/
theorem htr_adapter (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    ∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0)
      = -(2 / 3) * ricci g gi cc d 0 :=
  fun cc d => htr_from_hGauss g gi hg hgsymm hgiC hgi0 hdg0 hGauss cc d

/-! ###############################################################################
    ### (L3 — brick 3) `daLim_for_slots` — the `Da`-limit gate thread (direct, no adapter).
    ############################################################################### -/

/-- **★★ (L3) `daLim_for_slots`.**  THE `Da`-LIMIT GATE THREAD.  Given the `DaLimLUGoal` at the literal
    constant-radius gate — i.e. exactly what `GlobalRawBoundFacade.hDaLimLU_from_labelled` produces at
    `S := constGate g gi hChr hK c` — this certifies (by abbrev-unfold defeq) that it IS the raw
    `hDaLimLU` antecedent consumed by `HDConvGateThreading.hDConv_W1free` (the loc-unif `DaTrunc`-limit).
    The thread is DIRECT: NO adapter, NO re-derivation of the labelled `hDaLimLU_from_labelled` census.
    ⚠ NOT `a₁ = R/6`. -/
theorem daLim_for_slots (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b : ℝ) (U : Set ℝ)
    (hDa : DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) U) :
    TendstoLocallyUniformlyOn
      (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) m u)
      (fun u => laplaceBeltrami g gi
          (fun x => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u x 0) 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) u 0 0)
      atTop U :=
  hDa

/-! ###############################################################################
    ### (L4 — brick 4) `A1R6GateSlots` — the shallow slot package at the literal gate.
    ############################################################################### -/

/-- **★★★ (L4) `A1R6GateSlots`.**  The shallow `Prop` package of the three per-gate analytic slots at the
    literal constant-radius gate `constGate g gi hChr hK c`, VERBATIM the core
    `wide_a1_R6_core_AT_CONSTRADIUS`'s `hDuhamel`/`hDConv`/`hCConv` antecedents.  A carrier structure
    only — every field is a CONDITIONAL analytic slot; ⚠ NOT `a₁ = R/6`. -/
structure A1R6GateSlots (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t : ℝ) : Prop where
  /-- the `hDuhamel` slot at the literal gate. -/
  hDuhamel : heatOp g gi (fun u p q =>
        heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
          u p q) t 0 0
      = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0
        + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
            t 0 0
  /-- the `hDConv` slot at the literal gate. -/
  hDConv : DifferentiableAt ℝ
      (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        u 0 0) t
  /-- the `hCConv` slot at the literal gate. -/
  hCConv : ContDiffAt ℝ 2
      (fun p => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
        t p 0)
      (0 : Point n)

/-- **★★★ (L4) `a1_R6_slots_AT_GATE`.**  Builds the shallow slot package `A1R6GateSlots` at the literal
    constant-radius gate from the three banked slot producers.  The `hDuhamel` field is fed by
    `HDuhamelExportRethread.hDuhamelSlot_AT_GATE` from a `TruncatedDuhamelCore`; the `hDConv` field by
    `HDConvGateThreading.hDConv_W1free` from its W1-free census (the `Da`-limit L3 input `hDaLimLU`
    = `DaLimLUGoal …`, plus the boundary loc-unif `hbdryLU`); the `hCConv` field by
    `CConvV2Facade.hCConvSlot_AT_GATE_v2` from the open-nbhd + linewise-`HasDerivAt` family + the L2
    sliver census.  `H`/`F` are pinned to the concrete witness / Levi source by `hHeq`/`hFeq`
    (satisfiable by `rfl`) and discharged by `subst`.  Each field is closed by ONE explicit application
    of an already-banked producer.  Every carried pile is honest and satisfiable; NONE of the hypotheses
    is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_slots_AT_GATE (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c a b t T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    -- ── the abstracted witness / Levi source, pinned by defining equations (satisfiable by `rfl`):
    (H F : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
    (hFeq : F = leviSeries (heatOp g gi H))
    -- ── the `hDuhamel` leg: a truncated-Duhamel core at the gate (banked FULL census producer):
    (core : TruncatedDuhamelCore g gi H t)
    -- ── the `hDConv` leg: the W1-free census of `hDConv_W1free` (abstract in `H F`):
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |H τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, H τ p q = 0)
    (C_L : ℝ) (hC_L : 0 ≤ C_L)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, H (u - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ cc : ℝ, 0 < cc ∧ ∀ u ∈ U, cc ≤ u)
    (hInnerCont : ∀ u ∈ U,
        ContinuousOn (fun s => ∫ z, H (u - s) 0 z * F s z 0) (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ aa, AEStronglyMeasurable
      (fun s => ∫ z, H (aa - s) 0 z * F s z 0) (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, H (u - s) 0 z * F s z 0) volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => H r 0 z) (u - s) * F s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ aa ∈ nb m u,
      ‖∫ z, deriv (fun r => H r 0 z) (aa - s) * F s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ aa ∈ nb m u,
      HasDerivAt (fun aa => ∫ z, H (aa - s) 0 z * F s z 0)
        (∫ z, deriv (fun r => H r 0 z) (aa - s) * F s z 0) aa)
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen H F (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen H F (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen H F u (u - epsSeq m + k) 0 0
          + heatConvFrozen H F u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    (hDaLimLU : DaLimLUGoal g gi H F U)
    (hbdryLU : QIQTH.LocUnifDerivConv.hbdryLUTarget H F U)
    -- ── the `hCConv` leg: the facade-v2 census of `hCConvSlot_AT_GATE_v2` (concrete at the gate):
    (uSet : Set (Point n)) (hu_open : IsOpen uSet) (hu0 : (0 : Point n) ∈ uSet)
    (hlin : ∀ x ∈ uSet, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t
          (Function.update x i w) 0)
        ((Dmap g gi hChr hK (constGate g gi hChr hK c) a b
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t x)
          (Pi.single i (1 : ℝ))) (x i))
    (sSet : Set (Point n)) (hsOpen : IsOpen sSet) (hsnhds : sSet ∈ 𝓝 (0 : Point n))
    (fbulk : Fin n → ℕ → Point n → ℝ)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (bb : Fin n → ℕ → ℝ) (hb : ∀ i, Filter.Tendsto (bb i) atTop (𝓝 (0 : ℝ)))
    (hbulkderiv : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, HasFDerivAt (fbulk i m) (fderivBulk i m x) x)
    (hbulk_tendsto : ∀ i : Fin n, ∀ x ∈ sSet, Filter.Tendsto (fun m => fbulk i m x) atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z,
          witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) s z 0
          ∂(volume : Measure (Point n)))))
    (hsliver : ∀ i : Fin n, ∀ m : ℕ, ∀ x ∈ sSet, dist (fderivBulk i m x) (gderiv i x) ≤ bb i m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) sSet) :
    A1R6GateSlots g gi hChr hK c a b t := by
  subst hHeq
  subst hFeq
  refine ⟨?_, ?_, ?_⟩
  · -- the `hDuhamel` field, from the truncated-Duhamel core.
    exact hDuhamelSlot_AT_GATE g gi hChr hK (constGate g gi hChr hK c) a b t core
  · -- the `hDConv` field, from the W1-free census (`Da`-limit L3 input + boundary loc-unif).
    exact hDConv_W1free g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
      t T hT U hUopen htU hUpos hUT A₀ A₁ hA₀ hA₁ hAdom hAzero C_L hC_L hBdom hMeasFII
      hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff L hLnn hCross
      hDaLimLU hbdryLU
  · -- the `hCConv` field, from the facade-v2 sliver census.
    exact hCConvSlot_AT_GATE_v2 g gi hChr hK (constGate g gi hChr hK c) a b t
      uSet hu_open hu0 hlin sSet hsOpen hsnhds fbulk fderivBulk gderiv bb hb
      hbulkderiv hbulk_tendsto hsliver hcont

end QIQTH.A1R6SlotAdapters

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6SlotAdapters
#print axioms htr_adapter
#print axioms daLim_for_slots
#print axioms a1_R6_slots_AT_GATE
end AxiomChecks
