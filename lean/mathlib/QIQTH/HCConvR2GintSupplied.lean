/-
  HCConvR2GintSupplied — R2 carry-audit follow-on to J4-793/795: DISCHARGE the `hGintFull` member of
  the `hCConv` facade's R2 (non-geometric per-slice) residue onto a BANKED supplier.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  It does NOT close `hCConv`.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT.  After J4-793 the open `hCConv` facade census (of `hCConvSlot_bulkderivClosed`,
  `HCConvTractableCarriesClosed.lean`) is `{hlin, hsliver, hcont}` (geometric / sliver) PLUS the
  R2 residue of per-slice NON-geometric analytic carries:
      • `hGintFull` — interval-integrability of the pairing `s`-profile
          `s ↦ ∫ z, witnessFieldDeriv … i (t−s) x z · leviSeries … s z 0` on `[0, t]`;
      • `bulkCensusSlice` / `bulkCensusAtx` — the `fderivBulkInt_hasFDerivAt` per-slice census
          (integrability / measurability / domination / first-order `hd`), incl. the `kPrime` legs.

  This brick discharges the FIRST R2 member, `hGintFull`, onto the BANKED
  `HGintCutoff.hGint_at_witness` (J4-444), specialised at `U := {t}`.  `hGint_at_witness` splits the
  full `[0,t]` integrability into the DISCHARGED non-singular bulk `[0, t−εₘ]` (banked capped-ceiling
  engine) ⊕ the honest endpoint-sliver carry `hSliver`, re-assembled by `IntervalIntegrable.trans`.
  So `hGintFull` reduces to the named, strictly-lower-level, per-slice carries
      `{hFzero, hWFDdomCapped, hFdomEvery, hGintMeas, hSliver}`
  — the `witnessFieldDeriv` capped Gaussian envelope (`hWFDdomCapped`, the FIRST-jet chart-data
  subset), the `leviSeries` Gaussian envelope (`hFdomEvery`), the `s`-profile measurability
  (`hGintMeas`), and the integrable endpoint singularity (`hSliver`).  NONE is the joint-second-order
  geometric frontier; NONE equals `a₁ = R/6`.

  ## WHAT LANDS (ns `QIQTH.HCConvR2GintSupplied`).
    • `hGintFull_supplied` — ★  the EXACT `hGintFull` binder of `hCConvSlot_bulkderivClosed`
      (`∀ i x, IntervalIntegrable (fun s ↦ ∫ z, witnessFieldDeriv … i (t−s) x z · leviSeries … s z 0)
       volume 0 t`), discharged from `HGintCutoff.hGint_at_witness` at `U := {t}` from the five named
      per-slice carries above.  NOT `a₁ = R/6`.

  Every hypothesis is satisfiable, non-vacuous, and strictly lower-level than the conclusion.
  NOT `a₁ = R/6`; `hCConv` NOT closed.
-/
import Mathlib
import QIQTH.HGintCutoff

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.HeatDuhamel QIQTH.CConvFacade
open QIQTH.TrueHeatKernel QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade
open scoped Topology BigOperators Interval ContDiff

namespace QIQTH.HCConvR2GintSupplied

variable {n : ℕ}

/-- **★ `hGintFull_supplied`.**  The EXACT `hGintFull` R2 carry of
    `HCConvTractableCarriesClosed.hCConvSlot_bulkderivClosed` — the interval-integrability on `[0, t]`
    of the field-derivative pairing `s`-profile, per `i`, `x` — DISCHARGED from the banked
    `HGintCutoff.hGint_at_witness` specialised at `U := {t}`.  The five carries
    `{hFzero, hWFDdomCapped, hFdomEvery, hGintMeas, hSliver}` are the named, strictly-lower-level,
    per-slice analytic inputs (Gaussian envelopes of `witnessFieldDeriv`/`leviSeries`, `s`-profile
    measurability, and the integrable endpoint singularity).  NONE is the joint-second-order geometric
    frontier.  NOT `a₁ = R/6`. -/
theorem hGintFull_supplied (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hChr hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (t - epsSeq m))))
    (hSliver : ∀ (i : Fin n) (x : Point n), ∃ m : ℕ, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume (t - epsSeq m) t) :
    ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t := by
  intro i x
  have h := QIQTH.HGintCutoff.hGint_at_witness g gi hChr hK S a b ({t} : Set ℝ)
    hFzero hWFDdomCapped hFdomEvery
    (fun u hu i x m => by
      rw [Set.mem_singleton_iff] at hu; subst hu; exact hGintMeas i x m)
    (fun u hu i x => by
      rw [Set.mem_singleton_iff] at hu; subst hu; exact hSliver i x)
  exact h t (Set.mem_singleton t) i x

end QIQTH.HCConvR2GintSupplied

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCConvR2GintSupplied
#print axioms hGintFull_supplied
end AxiomChecks
