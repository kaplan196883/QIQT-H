/-
  CappedAdom2Audit — J4-391: Sol consult #16 bricks 1–3.  The CAPPED second-derivative family
  (`hAdom2_capped_of_crude`), the exact `hII` pairing-leg adapters, and THE DECISIVE `memLapFull`
  interface audit (`memLapFull_from_pairing_dominations`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PURE INTERFACE AUDIT: it (a) restates the banked crude `τ⁻¹` second-derivative bound in its only valid
  consequence — the lower-capped `(C/ε)·gaussDdim` form, (b) shows the LOW-adjacency pairing leg
  (`MemAdjLo`) can be discharged from that capped form (per-`m` constant — the honest `∀m∃CA2(ε_m)`
  side of the quantifier trap), and (c) audits `memLapFull`, REDUCING the false uncapped whole-time
  `hAdom2` carry to {capped-Lo family} ∪ {the labelled `MemAdjHi` matched-sliver residual}.  No `sorry`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed.
  `a₁ = R/6` remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE VERDICT (recorded here for the DAG bookkeeping — Sol consult #16, wall A).

  Wall A = the census `hAdom2` binder
      `∀ i τ, 0 < τ → τ ≤ T → ∀ z, |witnessSecondXDeriv … i τ z| ≤ CA2·gaussDdim (wA2·τ) (0−z)`,
  with a SINGLE `τ`-uniform constant `CA2` (quantified OUTSIDE `∀ m`) — is GENERALLY FALSE (the `τ⁻¹`
  blow-up at `z = 0` of a heat-kernel second derivative is intrinsic; no fixed `CA2` bounds it down to
  `τ → 0`).  The ONLY valid consequence of the banked crude bound `C·τ⁻¹·gaussDdim (wA2·τ)` is the
  lower-capped form `(C·ε⁻¹)·gaussDdim (wA2·τ)` on `[ε, T]` (`hAdom2_capped_of_crude`, brick 1, a thin
  specialization of `EveryCeilingFamilies.gaussDdim_crude_to_capped` to `witnessSecondXDeriv`).

  CONSUMER MAP (brick 2 audit).  `hAdom2` is consumed by
  `GlobalRawBoundFacade.integrability_from_dominations`, which threads it into BOTH
  `DaLimEasyTranche.hII_lo_concrete` (⟹ `MemAdjLo`, the `[0, u−ε_m]` leg) and `.hII_hi_concrete`
  (⟹ `MemAdjHi`, the `[u−ε_m, u]` leg) via the generic engine `pairing_intervalIntegrable`.  On that
  engine the first factor is evaluated at `τ = u − s`:
    •  LO leg `[0, u−ε_m]`:  `s ∈ (0, u−ε_m]` ⟹ `τ = u − s ∈ [ε_m, u)` — BOUNDED BELOW by `ε_m`.  The
       CAPPED form (per-`m` constant `C/ε_m`) SUFFICES, routed through
       `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped`.  ⟹ `hII_lo_from_capped` (brick 2,
       LANDED) — the uncapped whole-time `hAdom2` is NOT needed for `MemAdjLo`.
    •  HI leg `[u−ε_m, u]`:  `s ∈ (u−ε_m, u)` ⟹ `τ = u − s ∈ (0, ε_m)` — NOT bounded below (`τ → 0`).
       `pairing_intervalIntegrable` genuinely evaluates the domination at `τ → 0`; the capped form
       FAILS, and `pairing_intervalIntegrable_lowerCapped` is INAPPLICABLE (its `β ≤ u − ε_m` cap is
       violated by the right endpoint `β = u`).  The crude `τ⁻¹` bank does not rescue integrability
       either — `∫₀^{ε_m} τ⁻¹ dτ = +∞`.  So `MemAdjHi` is NOT dischargeable from any pointwise
       second-derivative Gaussian domination.

  HI-LEG USAGE (the split verdict).  `MemAdjHi` (`hII_hi`) flows through
  `GlobalRawBoundFacade.memLapFull_from_labelled` → `FrozenLaplaceSliver.hLapFull_of_pd2conv` →
  `InterchangeThreading.hLapFull_of_lims`, where it is used at EXACTLY ONE place —
  `intervalIntegral.integral_add_adjacent_intervals (hII_lo m i) (hII_hi m i)` — i.e. purely to justify
  the additivity split `∫₀ᵘ = ∫₀^{u−ε_m} + ∫_{u−ε_m}^u`.  The SIZE of the `[u−ε_m, u]` sliver piece is
  then controlled NOT by absolute domination but by the matched-sliver bound `hbnd` (the √ε
  Leibniz–Gaussian `hD2Hexpand` cancellation) via `hSliver`/`hBlim → 0`.  Thus `MemAdjHi`'s only role is
  its INTEGRABILITY (a prerequisite for the additivity lemma), which must be supplied by the
  matched-sliver / moment-aware route, NOT by the (false) uncapped `hAdom2`.

  BRICK 3 VERDICT — wall A is NOT eliminated by pure interface weakening; it is REDUCED.
  `memLapFull_from_pairing_dominations` produces the full `MemLapFull` census binder from
  {the CAPPED-Lo family (brick 1/2) + gauge + `hInter` + the √ε sliver bundle + `hPd2conv`} PLUS the
  LABELLED RESIDUAL `hII_hi : MemAdjHi` — and NO uncapped whole-time `hAdom2` appears anywhere.  The
  irreducible residue is exactly `MemAdjHi` (the Hi-leg integrability), the honest target of the
  moment-aware `WideSliverBoundary` / matched-sliver-integrability campaign.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.DaLimLUWallRecon QIQTH.LeviSeriesLocalData
open QIQTH.DaLimCensusRecon QIQTH.DaLimEasyTranche QIQTH.DaLimHardTranche QIQTH.FrozenLaplaceSliver
open QIQTH.DaLimLUConcreteDischarge QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open QIQTH.EveryCeilingFamilies QIQTH.ESLegWidening QIQTH.GlobalRawBoundFacade
open scoped Interval Topology BigOperators

namespace QIQTH.CappedAdom2Audit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### BRICK 1 — the capped second-derivative family from the crude `τ⁻¹` bank.
    ############################################################################### -/

/-- **★ BRICK 1 — `hAdom2_capped_of_crude`.**  THE ONLY VALID CONSEQUENCE of the banked crude
    second-derivative envelope.  A crude `C·τ⁻¹·gaussDdim (wA2·τ) (0−z)` bound on `witnessSecondXDeriv`
    (whose `τ⁻¹` prefactor blows up as `τ → 0` — the intrinsic wall) restricted to the lower-capped range
    `[ε, T]` becomes the GENUINE Gaussian bound `(C·ε⁻¹)·gaussDdim (wA2·τ) (0−z)`.  The width `wA2` is
    UNCHANGED (no width-monotonicity algebra).  Thin per-`i` specialization of
    `EveryCeilingFamilies.gaussDdim_crude_to_capped` to `A := fun τ _ z => witnessSecondXDeriv … i τ z`.
    ⚠ This does NOT establish the uncapped whole-time `hAdom2` (which is FALSE); it is the capped
    substitute.  NOT `a₁ = R/6`. -/
theorem hAdom2_capped_of_crude (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T εₘ Ccrude wA2 : ℝ) (hεₘ : 0 < εₘ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z)) :
    ∀ (i : Fin n) (τ : ℝ), εₘ ≤ τ → τ ≤ T → ∀ z : Point n,
      |witnessSecondXDeriv g gi hChr hK S a b i τ z|
        ≤ (Ccrude * εₘ⁻¹) * gaussDdim (wA2 * τ) (0 - z) := by
  intro i
  exact QIQTH.EveryCeilingFamilies.gaussDdim_crude_to_capped
    (fun τ _ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    T εₘ Ccrude wA2 hεₘ hCcrude (fun τ hτ0 hτT z => hcrude i τ hτ0 hτT z)

/-- **★ BRICK 1′ — `hAdom2_capped_family_of_crude`.**  The per-`m` capped family: for every ceiling
    index `m` the capped bound at `ε_m := epsSeq m > 0`, with the per-`m` constant `C·(epsSeq m)⁻¹`.
    This EXHIBITS the honest `∀ m ∃ CA2(ε_m)` (GOOD) side of the quantifier trap — the constant is
    chosen AFTER `m`, never a single `τ`-uniform `CA2`.  NOT `a₁ = R/6`. -/
theorem hAdom2_capped_family_of_crude (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T Ccrude wA2 : ℝ) (hCcrude : 0 ≤ Ccrude)
    (hcrude : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z|
          ≤ Ccrude * τ⁻¹ * gaussDdim (wA2 * τ) (0 - z)) :
    ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
      |witnessSecondXDeriv g gi hChr hK S a b i τ z|
        ≤ (Ccrude * (epsSeq m)⁻¹) * gaussDdim (wA2 * τ) (0 - z) :=
  fun m => hAdom2_capped_of_crude g gi hChr hK S a b T (epsSeq m) Ccrude wA2
    (epsSeq_pos m) hCcrude hcrude

/-! ###############################################################################
    ### BRICK 2 — the exact `hII` pairing-leg adapters.  LO LANDS; HI is the residual.
    ############################################################################### -/

/-- **★ BRICK 2 (Lo) — `hII_lo_from_capped`.**  THE ADAPTER THAT LANDS.  The low-adjacency
    interval-integrability `MemAdjLo` (the `[0, u−ε_m]` leg) from the PER-`m` CAPPED second-derivative
    family — NO uncapped whole-time `hAdom2`.  On `[0, u−ε_m]` the first factor is evaluated at
    `τ = u − s ∈ [ε_m, u)` (bounded below by `ε_m`), so the capped bound (with the per-`m` constant
    `CA2c m`) is EXACTLY what `pairing_intervalIntegrable_lowerCapped` needs (both strip endpoints
    `≤ u − ε_m`).  The degenerate case `u − ε_m ≤ 0` (source vanishes) is
    `ESLegWidening.intervalIntegrable_of_deg`.  This is the honest `∀m∃CA2(ε_m)` discharge — the
    constant may depend on `m`, and `MemAdjLo` is a per-`m` statement, so per-`m` constants are fine.
    NOT `a₁ = R/6`. -/
theorem hII_lo_from_capped (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (E : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries E s z 0| ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n, leviSeries E s z 0 = 0)
    (hmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * leviSeries E s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    MemAdjLo (leviSeries E) U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  intro m i u hu
  have hεpos := epsSeq_pos m
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact QIQTH.ESLegWidening.intervalIntegrable_of_deg
      (fun τ _ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) (leviSeries E)
      u (u - epsSeq m) hdeg hFzero
  · exact QIQTH.EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped
      (fun τ _ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) (leviSeries E)
      u u (epsSeq m) wA2 (CA2c m) wF CF (hUpos u hu) le_rfl hεpos hwA2 (hCA2c m) hwF hCF
      (fun τ hlo hhi z => hAdom2cap m i τ hlo (le_trans hhi (hUT u hu)) z)
      (fun s hs hsu z => hFdom s hs (le_trans hsu (hUT u hu)) z) hFzero
      0 (u - epsSeq m) (by linarith) le_rfl (hmeas m i u hu)

/-! ###############################################################################
    ### BRICK 3 — THE DECISIVE `memLapFull` INTERFACE AUDIT.
    ############################################################################### -/

/-- **★★★ BRICK 3 — `memLapFull_from_pairing_dominations`.**  THE DECISIVE AUDIT (Sol consult #16,
    wall A).  The full `MemLapFull` census binder at the endgame gate
    `H_G := vanVleckGatedWitness …`, `E := heatOp g gi H_G`, `F := leviSeries E`,
    `pdpdH := witnessSecondXDeriv …`, derived from
      •  the PER-`m` CAPPED second-derivative family `hAdom2cap` (brick 1/2) — the LO adjacency leg is
         built INTERNALLY via `hII_lo_from_capped`;  **NO uncapped whole-time `hAdom2` appears**;
      •  the gauge (`hgi`/`hΓ`), the frozen-side interchange `hInter`, the √ε sliver bundle
         (`D0`/`D1`/`hbnd` — the matched-sliver amplitude), and `hPd2conv`;
      •  ★ the LABELLED RESIDUAL `hII_hi : MemAdjHi` — the Hi adjacency leg (`[u−ε_m, u]`, `τ = u−s → 0`)
         is NOT dischargeable from any pointwise second-derivative Gaussian domination (capped OR the
         false uncapped `hAdom2`; `∫₀^{ε_m} τ⁻¹ = +∞`), so it is CARRIED as the moment-aware /
         matched-sliver-integrability residual.
    ⟹ **WALL A IS REDUCED, NOT ELIMINATED**:  the false uncapped whole-time `hAdom2` carry is replaced
    by {the capped-Lo family} ∪ {the labelled `MemAdjHi` residual}, and this `MemLapFull` assembly
    COMPILES without ever asserting the uncapped bound.  The irreducible residue is exactly `MemAdjHi`
    (Hi-leg integrability), the honest target of the moment-aware `WideSliverBoundary` campaign.
    Route: `hII_lo_from_capped` ⟹ `hII_lo`; then `GlobalRawBoundFacade.memLapFull_from_labelled`.
    Every hypothesis is SATISFIABLE and NON-VACUOUS; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem memLapFull_from_pairing_dominations (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (T wA2 wF CF : ℝ) (CA2c : ℕ → ℝ)
    (hwA2 : 0 < wA2) (hCA2c : ∀ m, 0 ≤ CA2c m) (hwF : 0 < wF) (hCF : 0 ≤ CF)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    (hInter : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- (Lo leg) the PER-`m` CAPPED second-derivative family — NO uncapped whole-time `hAdom2`:
    (hAdom2cap : ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessSecondXDeriv g gi hChr hK S a b i τ z| ≤ CA2c m * gaussDdim (wA2 * τ) (0 - z))
    (hFdom : ∀ s : ℝ, 0 < s → s ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim (wF * s) z)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0 = 0)
    (hmeas2Lo : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (Hi leg) ★ THE MATCHED-SLIVER RESIDUAL — NOT from any pointwise 2nd-derivative domination:
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    -- the √ε sliver amplitude bundle:
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    -- the labelled atomic interchange carrier:
    (hPd2conv : ∀ u ∈ U, ∀ i : Fin n,
        Tendsto
          (fun m => pd (fun y => pd (fun x => heatConvFrozen
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u
              (u - epsSeq m) x 0) i y) i 0)
          atTop (𝓝 (pd (fun y => pd (fun x => heatConv
              (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u x 0) i y) i 0))) :
    MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
      (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) := by
  -- (Lo leg) build `MemAdjLo` from the CAPPED family — the uncapped `hAdom2` is never used.
  have hII_lo := hII_lo_from_capped g gi hChr hK S a b
    (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) U T wA2 wF CF CA2c
    hwA2 hCA2c hwF hCF hUpos hUT hAdom2cap hFdom hFzero hmeas2Lo
  -- assemble via the banked facade capstone, with `hII_hi` carried as the labelled residual.
  exact QIQTH.GlobalRawBoundFacade.memLapFull_from_labelled g gi
    (vanVleckGatedWitness g gi hChr hK S a b)
    (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U
    (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    hgi hΓ hInter hII_lo hII_hi D0 D1 hD0 hD1 hbnd hPd2conv

end QIQTH.CappedAdom2Audit

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CappedAdom2Audit.hAdom2_capped_of_crude
#print axioms QIQTH.CappedAdom2Audit.hAdom2_capped_family_of_crude
#print axioms QIQTH.CappedAdom2Audit.hII_lo_from_capped
#print axioms QIQTH.CappedAdom2Audit.memLapFull_from_pairing_dominations
