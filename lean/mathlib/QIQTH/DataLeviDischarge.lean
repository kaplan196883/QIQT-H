/-
  DataLeviDischarge — J4-385: the `dataLevi` census-pile (iv) discharge.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  surviving LABELLED census carries.  This file discharges ONE census pile — the source-envelope bundle
  `dataLevi : LeviSeriesLocalData (heatOp g gi (vanVleckGatedWitness …)) C T` (census step (iv) of
  `CensusGeometryThread.hDaLimLU_from_geometry_census` / `GlobalRawBoundFacade.hDaLimLU_from_labelled`) —
  from banked machinery + exactly TWO honest carries.  NO `sorry` (header prose excepted), NO new axioms,
  NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the
  conclusion, NO existing file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE `LeviSeriesLocalData E C T` FIELD INVENTORY (SUPPLIER MAP) at the concrete residual
     `E := heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)`.

  The whole package is built ONCE by the banked generic builder
  `LeviSeriesLocalData.leviSeriesLocalData_of_windowBound`, which turns FOUR inputs on `E`
    (A) `hEbnd`   — the width-2 one-step Gaussian bound on the `(0,T]` window;
    (B) `hEzero`  — nonpositive-time vanishing;
    (C) `hEmeas`  — base joint strong measurability of `E`;
    (D) `hglobal` — the every-ceiling (`∀ T'>0`) width-2 bound family;
  into ALL EIGHT structure fields (`hC`, `hT`, `hEmeas`, `htermMeas`, `hmajor`, `hmajorSum`, `hInt`,
  `hFmeas`, `hFenv`) via the width-2 Volterra machinery + the two generic `tsum` lemmas.  So the field →
  supplier map collapses to the input → supplier map:

    field           supplier (inside the banked builder)
    ─────────────   ──────────────────────────────────────────────────────────────────────────────────
    hC / hT         arithmetic (`0 ≤ C·(1+T)`, `0 < T`)                                       [banked]
    hEmeas          = input (C)                                                               [CARRY 2]
    htermMeas       `iterE_joint_stronglyMeasurable` (from hEmeas)                            [banked]
    hmajor          `iterConvW_bound_le` (from hEbnd + hInt)                                  [banked]
    hmajorSum       `scaledIterKernelW_summable`                                              [banked]
    hInt            `iterConvIntegrableW_of_locally_bound_baseMeas` (from hEzero+hEmeas+hglobal)[banked]
    hFmeas          `leviSeries_stronglyMeasurable_of_termwise` (from the majorant summ.)     [banked]
    hFenv           `leviSeries_dominatedW_le` (from hEbnd + hInt)                            [banked]

  ── THE FOUR BUILDER INPUTS AT THE CONCRETE GATE (input → supplier) ─────────────────────────────────
    (A) hEbnd    ← the `t' := T` slice of the carried ALL-`t` width-2 bound `hpkgBound`.       [CARRY 1]
    (B) hEzero   ← `DataPileWitnessAudit.hEzeroE_concrete g gi hChr hK S a b hn`               [BANKED,
                    the geometry-derived nonpositive-time vanishing of the gated residual (needs 1≤n)].
    (C) hEmeas   ← `HEmeasBorelAudit.tripleHEmeas g gi (vanVleckGatedWitness …)` (DEFEQ to the field).[CARRY 2]
    (D) hglobal  ← the full `∀ T'` family of `hpkgBound` (`CT := C·(1+T')`).                    [CARRY 1]

  ── THE TWO HONEST CARRIES (genuinely-missing, satisfiable, never the conclusion) ──────────────────
    • `hpkgBound` — the ALL-`t` width-2 residual Gaussian bound
        `∀ t' τ p q, 0<τ→τ≤t' → |heatOp g gi (vanVleckGatedWitness …) τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`.
      SHAPE: the residual-domination that the ENTIRE campaign hinges on (the `hEboundW` wall).
      SATISFIABILITY: the constant-radius package `constRadius_package_and_S1` (J4-316) delivers exactly
      this at its literal gate; at a GENERAL geometry-chosen gate it is the surviving labelled input
      (the W3 gate-compatibility residue — see `FixedGateSourceProviders` header).
      DISCHARGE ROUTE: brick-5 fixed-gate re-run of `gatedWitnessN1_hEboundW_le_vanVleck_final`.
    • `hEmeas` (`tripleHEmeas …`) — the base joint strong measurability of the residual `E`.
      SHAPE: `StronglyMeasurable (fun q : ℝ×Point n×Point n => heatOp g gi (vanVleckGatedWitness …) q.1 q.2.1 q.2.2)`.
      SATISFIABILITY: banked at fixed gates by `GatedRepSFix.tripleHEmeas_concrete_v4`; at the general
      geometry-chosen gate it is the honest S1 carry.
      DISCHARGE ROUTE: the S1 Borel-measurability chain (chart joint measurability).

  ── `hBcont` (pile-(v) joint continuity of `leviSeries` on the strip) — DOES NOT fall out here.
     `LeviSeriesLocalData` provides only MEASURABILITY + a Gaussian ENVELOPE, never CONTINUITY, so the
     Levi-strip joint-continuity carry is untouched by this machinery.  Reported, not landed.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.LeviSeriesLocalData
import QIQTH.DataPileWitnessAudit
import QIQTH.HEmeasBorelAudit

open MeasureTheory Filter Topology
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.LeviSeriesLocalData QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit
open scoped Interval

namespace QIQTH.DataLeviDischarge

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### THE DISCHARGE — census pile (iv), `dataLevi`, from banked machinery + 2 carries.
    ############################################################################### -/

/-- **★★★ `dataLevi_from_geometry` — J4-385.**  The census pile-(iv) source-envelope bundle
    `LeviSeriesLocalData (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (C·(1+T)) T`, assembled
    from banked machinery + exactly TWO honest carries.

    ── BANKED (derived here, none carried) ───────────────────────────────────────────────────────────
      • `hEzero` (nonpositive-time vanishing) ← `hEzeroE_concrete` (geometry, needs `1 ≤ n`);
      • ALL EIGHT `LeviSeriesLocalData` structure fields ← `leviSeriesLocalData_of_windowBound`
        (width-2 Volterra machinery + the two generic `tsum` lemmas).
    ── CARRIED (genuinely missing, satisfiable, never the conclusion) ─────────────────────────────────
      • `hpkgBound` — the ALL-`t` width-2 residual Gaussian bound (feeds BOTH `hEbnd` at `t'=T` and the
        `hglobal` family `CT := C·(1+T')`); the campaign's `hEboundW` residual-domination wall;
      • `hEmeas` (`tripleHEmeas …`, DEFEQ the field shape) — the base joint strong measurability (S1).
    NOT `a₁ = R/6`. -/
theorem dataLevi_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C T : ℝ) (hCnn : 0 ≤ C) (hT : 0 < T) (hn : 1 ≤ n)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (hpkgBound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (C * (1 + T)) T := by
  have hCt : (0 : ℝ) ≤ C * (1 + T) := mul_nonneg hCnn (by linarith)
  exact leviSeriesLocalData_of_windowBound
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (C * (1 + T)) T hCt hT
    (fun τ p q hτ hτT => hpkgBound T τ p q hτ hτT)
    (hEzeroE_concrete g gi hChr hK S a b hn)
    hEmeas
    (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hCnn (by linarith),
      fun τ p q hτ hτT' => hpkgBound T' τ p q hτ hτT'⟩)

/-- **★ `dataLevi_exists_from_geometry` — J4-385, the census-facing `∃ C` shape.**  Repackages
    `dataLevi_from_geometry` into the `∃ C, LeviSeriesLocalData (heatOp g gi (vanVleckGatedWitness …)) C T`
    form the census step (iv) consumes (`CensusGeometryThread`/`GlobalRawBoundFacade` take the model
    constant `C` as a bound `∀`-variable).  The witnessing constant is `C·(1+T)`.  Same two honest
    carries.  NOT `a₁ = R/6`. -/
theorem dataLevi_exists_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C T : ℝ) (hCnn : 0 ≤ C) (hT : 0 < T) (hn : 1 ≤ n)
    (hEmeas : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b))
    (hpkgBound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∃ C' : ℝ, LeviSeriesLocalData
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) C' T :=
  ⟨C * (1 + T),
   dataLevi_from_geometry g gi hChr hK S a b C T hCnn hT hn hEmeas hpkgBound⟩

end QIQTH.DataLeviDischarge

/-! ## Axiom check — both public decls are `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.DataLeviDischarge
#print axioms dataLevi_from_geometry
#print axioms dataLevi_exists_from_geometry
end AxiomChecks
