/-
  HD1Concrete — J4-406 (Sol #17 F2): the CONCRETE `hD1` census discharge via the HD1SliverRoute.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL.  This file only INSTANTIATES the already-banked uniform-limit-of-derivatives
  skeleton (`XUniformSliverFull.hD1_from_data` / `HD1SliverRoute.hD1_bulk_sliver_reduction` /
  `HD1ConcreteWiring.hD1_reduction`) at the CONCRETE van-Vleck gated witness pair, discharging the
  census members that are algorithmically dischargeable and carrying the genuine analytic ones
  explicitly.  No `sorry`, no new axioms, no `:= True`, no vacuous hypothesis, no hypothesis equal to
  the conclusion.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE TARGET.  `CConvV2DerivRep.hD1_conditional`'s `hD1` slot: `ContDiffAt ℝ 1 (Dmap … Fconv t) 0`,
  the `C¹`-regularity of the heat-convolution derivative representative at `0`, at the concrete pair
    `W := vanVleckGatedWitness g gi hC hK S a b`,  `Fconv := leviSeries (heatOp g gi W)`,
  the same pair the D-pile bricks (`FrozenGermInternal.fbulkInt`, `W2Finish.w2_hQ1`, the sliver
  tranches) already anchor.

  ## THE H1 CENSUS MAP.  `hD1_from_data` / `hD1_conditional` take an 11-member census; at the concrete
  pair each maps to a banked supplier or an honest analytic carry:
    • `sSet, hsOpen, hsnhds`  — DISCHARGED here: `sSet := Set.univ`, `isOpen_univ` / `univ_mem`
      (`sSet_concrete_isOpen`, `sSet_concrete_mem_nhds`).
    • `fbulk`                 — SUPPLIED: `FrozenGermInternal.fbulkInt g gi hC hK S a b t i m`
      (the banked concrete truncated `∫₀^{t−εₘ}` primitive).
    • `gfull` (= `gcoef`)     — DEFINITIONAL: the Dmap coefficient `∫₀ᵗ∫z witnessFieldDeriv i (t−s) x z
      · leviSeries … s z 0` (= `hbulk_tendsto`'s limit, = `Dmap … x (Pi.single i 1)`).
    • `b`, `hb`               — DISCHARGED here (`hb_concrete`): the vanishing sliver rate
      `(C₀+C₁)·2√εₘ + C₂·εₘ → 0`, via `HD1ConcreteWiring.sliver_bound_tendsto_zero`
      ∘ `MovingFBoundaryLim.tendsto_comp_epsSeq` (`εₘ → 0⁺`).
    • `hbulk_tendsto`         — DISCHARGED here (`hbulk_tendsto_concrete`): `fbulkInt … m x → gcoef x`,
      via `HD1ConcreteWiring.bulk_tendsto_of_primitive` ∘ `tendsto_comp_epsSeq`, on the honest
      integrability carry `hGint` (`fbulkInt … m x` is DEFINITIONALLY `∫₀^{t−εₘ} Gₓ`).
    • `hbulkderiv`            — CARRY: the BULK order-2 differentiation
      `HasFDerivAt (fbulkInt … m) (fderivBulk i m x) x` (supplied SHAPE-wise by
      `HD1SliverRoute.gcoef_bulk_hasFDerivAt`; its dominated bundle is the analytic carry).
    • `hsliver`              — CARRY: the `O(√ε)` `x`-uniform sliver dist-bound
      `dist (fderivBulk i m x) (gderiv i x) ≤ bb i m` (from `witness_sliver2_xuniform` /
      the `DaLimEasyTranche` `√ε` tranche).
    • `hcont`               — CARRY: the order-2 field continuity `ContinuousOn (gderiv i) univ`
      (supplied SHAPE-wise by `HD1ConcreteWiring.gderiv_continuousAt`; its cancellation `hsbound` is
      the analytic carry).
    • `fderivBulk`, `gderiv` — CARRY: the order-2 derivative fields (data).

  ── Pd2ConvPerU correspondence.  `Pd2ConvPerU.hPd2conv_perU`'s per-`u` census block is the SAME
  `{sSet, gcoef, gderiv, fbulk, fderivBulk, bb, hb, hbulkderiv, hbulk_tendsto, hsliver}` family; this
  file's discharges (`hb`, `hbulk_tendsto`, the nbhd pair) are exactly the `u`-slice of that census's
  algorithmically-dischargeable members, with `fbulk := fbulkInt …` and `gcoef` the Dmap coefficient —
  i.e. this is the `hD1`-facing slice of the same census, not a mirror.

  ## WHAT LANDS (ns `QIQTH.HD1Concrete`).
    • `sSet_concrete_isOpen` / `sSet_concrete_mem_nhds` — the nbhd members.
    • `hb_concrete`           — ★ the vanishing sliver-rate member `hb`.
    • `hbulk_tendsto_concrete`— ★ the bulk pointwise-convergence member `hbulk_tendsto`.
    • `hD1_concrete`          — ★★ THE FIRED `hD1`: `ContDiffAt ℝ 1 (Dmap … (leviSeries …) t) 0` from
      `hD1_conditional` at the concrete pair, with `hb`/`hbulk_tendsto`/nbhd DISCHARGED internally and
      the three analytic carries (`hbulkderiv`/`hsliver`/`hcont`) + `hGint` bound taken as hypotheses.

  Every hypothesis is satisfiable, non-vacuous (the width-2 Gaussian model of the sliver bricks
  satisfies the whole census), and never equal to the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvV2DerivRep
import QIQTH.FrozenGermInternal
import QIQTH.HD1ConcreteWiring
import QIQTH.MovingFBoundaryLim

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open scoped Topology Interval ContDiff BigOperators

namespace QIQTH.HD1Concrete

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### M0 — the field neighbourhood members (`hsOpen` / `hsnhds`), at `sSet := univ`.
    ############################################################################### -/

/-- **M0a — `sSet_concrete_isOpen`.**  The concrete field neighbourhood `sSet := Set.univ` is open;
    the `hsOpen` census slot.  NOT `a₁ = R/6`. -/
theorem sSet_concrete_isOpen : IsOpen (Set.univ : Set (Point n)) := isOpen_univ

/-- **M0b — `sSet_concrete_mem_nhds`.**  The concrete field neighbourhood `sSet := Set.univ` is a
    neighbourhood of `0`; the `hsnhds` census slot.  NOT `a₁ = R/6`. -/
theorem sSet_concrete_mem_nhds : (Set.univ : Set (Point n)) ∈ 𝓝 (0 : Point n) := univ_mem

/-! ###############################################################################
    ### M1 — the vanishing sliver-rate member `hb`.
    ############################################################################### -/

/-- **★ M1 — `hb_concrete`.**  The `hb` census slot at the concrete `ε`-sequence: the sliver
    right-hand side `(C₀+C₁)·2√εₘ + C₂·εₘ` tends to `0` along `m → ∞`.  This is the banked
    `HD1ConcreteWiring.sliver_bound_tendsto_zero` (a `𝓝[>]0`-limit in the scale) composed with
    `MovingFBoundaryLim.tendsto_comp_epsSeq` (`εₘ → 0⁺`).  It is EXACTLY the `hb : Tendsto b l (𝓝 0)`
    slot `XUniformSliverFull.hD1_from_data` consumes.  NOT `a₁ = R/6`. -/
theorem hb_concrete (C₀ C₁ C₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => (C₀ + C₁) * (2 * Real.sqrt (epsSeq m)) + C₂ * epsSeq m)
      Filter.atTop (𝓝 (0 : ℝ)) :=
  QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq
    (QIQTH.HD1ConcreteWiring.sliver_bound_tendsto_zero C₀ C₁ C₂)

/-! ###############################################################################
    ### M2 — the bulk pointwise-convergence member `hbulk_tendsto`.
    ############################################################################### -/

/-- **★ M2 — `hbulk_tendsto_concrete`.**  The `hbulk_tendsto` census slot at the concrete pair: the
    BULK truncated primitive `fbulkInt … t i m x = ∫₀^{t−εₘ} ∫z witnessFieldDeriv i (t−s) x z
    · leviSeries … s z 0` converges, as `m → ∞`, to the full Dmap coefficient
    `∫₀ᵗ ∫z witnessFieldDeriv i (t−s) x z · leviSeries … s z 0` (= `hD1_conditional`'s limit).
    Via `HD1ConcreteWiring.bulk_tendsto_of_primitive` (endpoint primitive-continuity, `ε → 0⁺`)
    composed with `MovingFBoundaryLim.tendsto_comp_epsSeq` (`εₘ → 0⁺`); `fbulkInt … t i m x` is
    DEFINITIONALLY the truncated `s`-integral.  Honest carry: `hGint`, the interval-integrability of
    the `s`-profile (the gcoef integrand) — a genuine, non-conclusion input.  NOT `a₁ = R/6`. -/
theorem hbulk_tendsto_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (ht : 0 < t) (x : Point n)
    (hGint : IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t) :
    Filter.Tendsto (fun m : ℕ => QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b t i m x)
      Filter.atTop
      (𝓝 (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))) := by
  have h := QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq
    (QIQTH.HD1ConcreteWiring.bulk_tendsto_of_primitive
      (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
          ∂(volume : Measure (Point n)))
      t ht hGint)
  -- `fbulkInt … t i m x` unfolds definitionally to `∫₀^{t−εₘ} Gₓ`.
  simpa only [QIQTH.FrozenGermInternal.fbulkInt] using h

/-! ###############################################################################
    ### H3 — the FIRED concrete `hD1` from `hD1_conditional`.
    ############################################################################### -/

/-- **★★ H3 — `hD1_concrete`.**  THE fired `hD1` at the concrete van-Vleck gated pair: the L2
    regularity slot `ContDiffAt ℝ 1 (Dmap … (leviSeries …) t) 0` obtained from
    `CConvV2DerivRep.hD1_conditional` with the algorithmically-dischargeable census members supplied
    internally by this file —
      • `sSet := Set.univ`, `hsOpen`/`hsnhds` (`sSet_concrete_isOpen` / `sSet_concrete_mem_nhds`),
      • `fbulk := fbulkInt …`, `bb := (C₀+C₁)·2√εₘ + C₂·εₘ`, `hb := hb_concrete`,
      • `hbulk_tendsto := hbulk_tendsto_concrete` (on the `hGint` integrability carry),
    — and the three genuine analytic carries kept explicit:
      • `hbulkderiv` — the bulk order-2 differentiation of `fbulkInt …`,
      • `hsliver`    — the `O(√ε)` `x`-uniform sliver dist-bound,
      • `hcont`      — the order-2 field continuity.
    This closes the `hD1` slot at the concrete pair DOWN to those three carries + the integrability
    bound, discharging every other census member.  It does NOT prove `a₁ = R/6`.  NOT `a₁ = R/6`. -/
theorem hD1_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t)
    (fderivBulk : Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : Fin n → ℝ)
    (hGint : ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 t)
    (hbulkderiv : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b t i m)
          (fderivBulk i m x) x)
    (hsliver : ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk i m x) (gderiv i x)
          ≤ (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (hcont : ∀ i : Fin n, ContinuousOn (gderiv i) (Set.univ : Set (Point n))) :
    ContDiffAt ℝ 1
      (QIQTH.CConvV2DerivRep.Dmap g gi hC hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t) (0 : Point n) :=
  QIQTH.CConvV2DerivRep.hD1_conditional g gi hC hK S a b
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) t
    (Set.univ) sSet_concrete_isOpen sSet_concrete_mem_nhds
    (fun i m => QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b t i m)
    fderivBulk gderiv
    (fun i m => (C₀ i + C₁ i) * (2 * Real.sqrt (epsSeq m)) + C₂ i * epsSeq m)
    (fun i => hb_concrete (C₀ i) (C₁ i) (C₂ i))
    hbulkderiv
    (fun i x _hx => hbulk_tendsto_concrete g gi hC hK S a b i t ht x (hGint i x))
    hsliver hcont

end QIQTH.HD1Concrete

section AxiomChecks
open QIQTH.HD1Concrete
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms sSet_concrete_isOpen
#print axioms sSet_concrete_mem_nhds
#print axioms hb_concrete
#print axioms hbulk_tendsto_concrete
#print axioms hD1_concrete
end AxiomChecks
