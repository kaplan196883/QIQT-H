/-
  WhiteHInnerCont — J4-688 (downstream item (a), whitened instantiation): the WHITENED-witness
  instantiation of the width/witness-generic `hInnerCont` builder
  `CurvedA1HContDomGen.hInnerCont_of_dominations_generic`, fed on the B-slot by the just-landed
  FULL-MATRIX whitened Levi domination `WhiteHBdomAllRows.white_hBdom_discharged` (width
  `lam = whiteLam`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── CONTEXT.  `white_hBdom_discharged` (J4-687) supplies, for EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)`,
     a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2` such that — MODULO exactly ONE
     labelled input (the whitened-defect S1 joint measurability `tripleHEmeas`) — the FULL whitened
     signed Levi-series obeys `|leviSeries (whiteDefectKernel …) s z y| ≤ C_L·G_{lam·s}(z−y)` on
     `(0,1]`, for ALL `z y`.  This is exactly the `∀ (z,y)` B-slot the generic builder consumes, at
     width `lam` (NOT the pinned width `2`), at the WHITENED witness (NOT `vanVleckGatedWitness`).

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_hInnerCont_of_dominations` — ★★ the WHITENED re-base.  For EVERY `κ ≤ 0`, compact
      `K ⊆ B̄(0,R)`, there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2` such
      that, MODULO {the whitened-defect S1 measurability `tripleHEmeas`, a whitened-witness VALUE
      Gaussian domination `hWdom` at ANY positive width `wA` with affine amplitude, the interior
      slice measurability `hmeas`, the a.e.-`z` interior time continuity `hcont`}, the interior-time
      continuity of the WHITENED inner pairing
          `s ↦ ∫ z, whiteGatedWitness κ … (u−s) 0 z · leviSeries (whiteDefectKernel κ …) s z 0`
      holds on `Ioo 0 u`, for every `u ∈ U ⊆ (·,1]`.  The B-slot width-`lam` Levi domination is
      DISCHARGED INTERNALLY from `white_hBdom_discharged` (given the S1 input); it is composed with
      the carried whitened value domination through the generic builder.  ⚠ HONEST width `lam =
      whiteLam`; NO `lam ≤ 8` used.
    • `white_hInnerCont_witness_gate` — the cp466 non-vacuity certificate (`n = 2`, `κ = −1`,
      `K = closedBall 0 2`): the ∃-package produces a FAT gate (`0 ∈ S 0`, open) with `0 < a < b`
      and `lam ≥ 2`, so the re-base is not `∅`-degenerate.

  ── HONEST RESIDUAL.  This is the WHITENED-witness re-base of the builder (downstream item (a)),
     width `lam`.  Feeding it fully still owes: (b) the whitened-defect S1 measurability
     `tripleHEmeas` (the ONE labelled input threaded through `white_hBdom_discharged`); (b′) the
     whitened-witness VALUE Gaussian domination `hWdom` (NOT banked in this exact affine/width shape
     — carried here as an explicit hypothesis); (b″) the interior slice measurability / a.e.-`z`
     continuity carries `{hmeas, hcont}`; (c) the prior `K1TransportBudget` / capstone
     co-instantiation piles.  `a₁ = R/6` established non-vacuously ONLY for the FLAT tower.

  ⚠ HONEST FIREWALL.  Builder re-base ONLY — NOT `a₁ = R/6`; the `R/6` value is a labelled carrier,
  untouched.  DERIVED from the PROVED generic builder + the PROVED whitened all-rows Levi domination.
  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis,
  no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1HContDomGen
import QIQTH.WhiteHBdomAllRows

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.WhiteGated QIQTH.WhiteBridge
open scoped Topology

namespace QIQTH.WhiteHInnerCont

variable {n : ℕ}

/-- **★★ `white_hInnerCont_of_dominations` — THE WHITENED-WITNESS RE-BASE.**  The whitened
    instantiation of `CurvedA1HContDomGen.hInnerCont_of_dominations_generic`: for EVERY `κ ≤ 0`,
    compact `K ⊆ B̄(0,R)`, there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2`
    such that, MODULO {the whitened-defect S1 measurability `tripleHEmeas`, a whitened-witness VALUE
    Gaussian domination `hWdom` at ANY positive width `wA`, the interior slice measurability `hmeas`,
    the a.e.-`z` interior time continuity `hcont`}, the interior-time continuity of the WHITENED
    inner pairing `s ↦ ∫ z, whiteGatedWitness … (u−s) 0 z · leviSeries (whiteDefectKernel …) s z 0`
    holds on `Ioo 0 u`, for every `u ∈ U ⊆ (·,1]`.  The B-slot width-`lam` Levi domination is
    discharged internally from `WhiteHBdomAllRows.white_hBdom_discharged` (given the S1 input).
    ⚠ HONEST width `lam = whiteLam`; NO `lam ≤ 8`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_of_dominations (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1)
    (wA Cpre A₀ A₁ : ℝ) (hwA : 0 < wA) (hCpre : 0 ≤ Cpre) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
            (whiteGatedWitness κ hκ hKc S a b) →
          (∀ τ, 0 < τ → ∀ p q : Point n,
              |whiteGatedWitness κ hκ hKc S a b τ p q|
                ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q)) →
          (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
              AEStronglyMeasurable
                (fun z => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                  * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
                (volume : Measure (Point n))) →
          (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
              ContinuousAt
                (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                  * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0) s₀) →
          ∀ u ∈ U, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, hBimpl⟩ :=
    QIQTH.WhiteHBdomAllRows.white_hBdom_discharged κ hκ hKc R hKb
  refine ⟨S, a, b, ha, hab, hgate, lam, hlam2, fun hEmeas hWdom hmeas hcont => ?_⟩
  obtain ⟨C_L, hC_L, hBdom⟩ := hBimpl hEmeas
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S a b) (leviSeries (whiteDefectKernel κ hκ hKc S a b))
    1 U hU1 wA lam hwA hlam0 Cpre A₀ A₁ C_L hCpre hA₀ hA₁ hC_L
    hWdom (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_hInnerCont_of_dominations` produces a FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b` and `lam ≥ 2` — the antecedent chain up to the labelled inputs is genuinely
    satisfiable, not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_hInnerCont_of_dominations (n := 2) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
      (U := (∅ : Set ℝ)) (by simp) (wA := 1) (Cpre := 0) (A₀ := 0) (A₁ := 0)
      (by norm_num) le_rfl le_rfl le_rfl
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

end QIQTH.WhiteHInnerCont

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteHInnerCont

#print axioms white_hInnerCont_of_dominations
#print axioms white_hInnerCont_witness_gate

end AxiomChecks
