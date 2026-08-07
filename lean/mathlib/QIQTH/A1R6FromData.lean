/-
  A1R6FromData — J4-410: Sol #18 final-assembly brick #3, THE PUBLIC CAPSTONE `a1_R6_from_data`.
  The one-line public wrap of the entire `a₁` heat-kernel final-assembly sequence: assemble the two
  banked bundles (`ConstGateAssembly.ConstGateAssemblyData` and `FinalA1Slots.FinalA1SlotsAtConstGate`)
  from the raw SEMANTIC inputs and hand both to `FinalA1Slots.FinalA1SlotsAtConstGate.fire`, yielding
  the a₁ two-jet at the ONE literal constant-radius gate `G₀ := constGate g gi hChr hK c` with the
  Ricci source `(∑ᵢ ricci g gi i i 0)/6` in the `O(t)` coefficient.  THE LAST BRICK of the final-assembly
  sequence of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠⚠⚠ HONESTY FIREWALL — THIS FILE IS **NOT** an unconditional `a₁ = R/6`. ⚠⚠⚠
  `a1_R6_from_data` is the maximally-UNCONDITIONAL **CONDITIONAL** theorem: it proves the a₁ two-jet
  ONLY on the explicit semantic hypotheses in its signature.  Nothing here proves anything new about
  `R/6` — it is pure final assembly.  The capstone merely:
    (1) builds `ConstGateAssemblyData` via `constGate_assembly_data_from_data` (J4-408) from the
        affine on-gate carry `hgate`, the v4 measurability carriers, and the honest
        `hpkgBound`/`hmemS0`/`hopenS0` carries;
    (2) builds `FinalA1SlotsAtConstGate` via `finalA1Slots_from_data` (J4-409) from the ONE semantic
        slot package `A1R6GateSlots` and the single labelled gauge carry `hGauss`;
    (3) hands both to the banked firing lemma `FinalA1SlotsAtConstGate.fire`, which applies the core
        `A1R6CoreAtGate.wide_a1_R6_core_AT_CONSTRADIUS` and re-exports its CONDITIONAL two-jet.
  Every hypothesis is satisfiable and NONE of them is the conclusion; no `sorry`, no `admit`, no
  `:= True`, no new axiom (`std-3` only).  `a₁ = R/6` stays CONDITIONAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SIGNATURE AUDIT (Sol #18 — group inputs semantically, expose NOTHING beyond the four groups).
    (A) base geometry / gauge binders — `t, ht, hn, g, gi, hChr, hK, hK0, hg, hgsymm, hgiC, hgpos, hg0,
        hgi, hΓ, hdg0, hsrc, a, b, c, C, ha, hab, hbc, hCnn` (the standard constant-radius geometry
        binders shared by the core, plus the gauge-symmetry `hgsymm` the `htr_adapter` needs; the SINGLE
        `hgi` binder serves both `.fire`'s `hgi` and `finalA1Slots_from_data`'s `hgi0` — they are the
        SAME statement `∀ i j, gi 0 i j = if i = j then 1 else 0`);
    (B) the `ConstGateAssemblyData` semantic carries — `P₀, P₁, hP₀, hP₁, hgate` (the affine on-gate
        width-4/3 quadratic carry), `hKSmeas, hcarTau, hcarField, hcarField2, hgiMeas, hchrMeas` (the v4
        measurability carriers), `hpkgBound, hmemS0, hopenS0` (the honest package/gate-centre carries);
    (C) the ONE slot package — `slots : A1R6GateSlots g gi hChr hK c a b t` (internally the Duhamel
        census + the W1-free census + the L2 sliver census, bundled by `a1_R6_slots_AT_GATE`);
    (D) the single gauge carry — `hGauss` (derived in-bank via `hGauss_pullback_concrete` etc.,
        absorbable later).
  ⚠ NO legacy `hraw`.  NO retired-hgate-shape (the AFFINE `hgate` carry IS allowed — it is the honest
     post-repair shape).  NO `a`/`b`/`S` existential witnesses beyond the explicit `constGate` gate
     parameters `(a, b, c)`.  NO unrestricted `AmplitudeDerivativeData`.  NO raw `hD2Hexpand`/`hPd2conv`.
     `hGauss` IS allowed (per the J4-409 shape).
  ⚠ STILL CONDITIONAL — NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FinalA1Slots

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromData

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (C1) THE PUBLIC CAPSTONE — `a1_R6_from_data`.
    ############################################################################### -/

/-- **★★★★★ J4-410 — `a1_R6_from_data`.**  THE PUBLIC CAPSTONE of the `a₁` heat-kernel final-assembly
    sequence.  From the raw SEMANTIC inputs, grouped into exactly four semantic groups — (A) the base
    geometry/gauge binders, (B) the `ConstGateAssemblyData` carries, (C) the ONE `A1R6GateSlots` slot
    package, (D) the single `hGauss` gauge carry — it assembles both banked bundles
    (`constGate_assembly_data_from_data` J4-408 and `finalA1Slots_from_data` J4-409) and hands them to
    the banked firing lemma `FinalA1SlotsAtConstGate.fire`, yielding the a₁ two-jet at the ONE literal
    constant-radius gate `G₀ := constGate g gi hChr hK c` with the Ricci source `(∑ᵢ ricci g gi i i 0)/6`
    in the `O(t)` coefficient.  A ONE-LINE apply-wrapper — pure final assembly, adds nothing analytic.
    Every hypothesis is satisfiable; NONE is the conclusion.

    ⚠ THE FINAL HONEST SUMMARY.  `a1_R6_from_data` is the maximally-unconditional **CONDITIONAL** a₁
    two-jet, NOT an unconditional `a₁ = R/6`.  What it proves: at the literal constant-radius gate the
    true heat kernel's on-diagonal two-jet has the `1 + ((∑ᵢ ricci g gi i i 0)/6)·t + O(t²)` shape, on
    the explicit semantic hypotheses of its signature.  What remains genuinely CONDITIONAL:
      (a) the `A1R6GateSlots` censuses — the Duhamel (~90-binder) census, the W1-free census, and the L2
          sliver census — each satisfiable and largely fired by the F-pile bricks, but still binder-shaped;
      (b) the `ConstGateAssemblyData` carries — the affine `hgate` (DERIVABLE via the J4-368..380 arc's
          `hEdom_from_geometry` at the ∃-gate, carried explicit-gate here); the v4 measurability
          carriers; and `hpkgBound`/`hmemS0`/`hopenS0` (satisfiable via `constRadius_package_and_S1`,
          whose own ∃-witnesses do not defeq-match a caller-chosen literal gate);
      (c) `hGauss` — DERIVED in-bank (`hGauss_pullback_concrete` etc.), absorbable later;
      (d) THE DEEP CONDITIONALITY NEVER CLAIMED CLOSED — the convergence-trio content living inside the
          Duhamel census, and hence the `a₁ = R/6` statement itself, remains CONDITIONAL.
    ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders:
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    -- ── (B) the `ConstGateAssemblyData` semantic carries:
    -- the affine on-gate width-4/3 quadratic carry `hgate`:
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁)
    (hgate : ∀ τ : ℝ, 0 < τ → ∀ q : Point n, q ∈ K → ∀ p : Point n,
        p ∈ closure (constGate g gi hChr hK c q) →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (P₀ + P₁ * τ) * (((rncRadialSq (p - q) / τ) ^ 2 + rncRadialSq (p - q) / τ + 1)
                  * gaussDdim (4 / 3 * τ) (p - q)))
    -- the v4 measurability carriers:
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ i j : Fin n, ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- the honest package / gate-centre carries:
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    -- ── (C) the ONE semantic slot package (Duhamel + W1-free + L2 censuses bundled):
    (slots : A1R6GateSlots g gi hChr hK c a b t)
    -- ── (D) the single labelled gauge carry (derived in-bank, absorbable later):
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) :=
  FinalA1SlotsAtConstGate.fire g gi t ht hn hChr hK hK0
    hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    (constGate_assembly_data_from_data hn g gi hChr hK c a b C
      P₀ P₁ hP₀ hP₁ hgate hKSmeas hcarTau hcarField hcarField2 hgiMeas hchrMeas
      hpkgBound hmemS0 hopenS0)
    (finalA1Slots_from_data g gi hChr hK c a b t slots
      hg hgsymm hgiC hgi hdg0 hGauss)

end QIQTH.A1R6FromData

/-! ###############################################################################
    ### (C2) THE FINAL AUDITS — `#print axioms` for the capstone (must be `std-3`).
    #############################################################################

    SIGNATURE AUDIT (forbidden-name check on the `a1_R6_from_data` binders above):
      • NO legacy `hraw`                       — ✓ absent;
      • NO retired-hgate-shape                 — ✓ only the AFFINE `hgate` (width-4/3 quadratic) appears,
                                                 which is the honest post-repair shape (allowed);
      • NO `a`/`b`/`S` existential witnesses    — ✓ only the explicit `constGate` gate parameters
        beyond the explicit gate parameters      `(a, b, c)` appear; no floating `∃ a b, ∃ S` gate;
      • NO unrestricted `AmplitudeDerivativeData` — ✓ absent;
      • NO raw `hD2Hexpand` / `hPd2conv`         — ✓ absent;
      • `hGauss` allowed (per the J4-409 shape)  — ✓ present as the single gauge carry (group D).
    -/
section AxiomChecks
open QIQTH.A1R6FromData
#print axioms a1_R6_from_data
end AxiomChecks
