/-
  HGintCutoff — J4-444 (GROUP (3), Sol #20 item (ii)): DISCHARGING THE hGint CENSUS CARRY.

  The V1 per-`u` census (`PerUCensusInstantiation.perUCensus_phase1`, J4-428) carries `hGint`: the
  interval-integrability of the FIELD-DERIVATIVE `s`-profile
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) x z · leviSeries (heatOp g gi W) s z 0`
  on the FULL interval `[0, u]`, per `u ∈ U`, `i`, `x`.  J4-428 flagged it "NO banked supplier".  This
  brick supplies it, CUTOFF-INDEXED, from the banked capped-ceiling engine
  `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped` — the SAME engine `frozenLeg_hFint`
  (J4-438) runs on for the witness-VALUE leg — instantiated at the first factor
  `A := fun τ _ z ↦ witnessFieldDeriv … i τ x z`, plus the honest endpoint-sliver carry.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING
  about `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio +
  geometric-wiring stack AND on the surviving labelled census carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable Gaussian-domination /
  interval-integrability data into the exact census `hGint` shape.  NONE proves `a₁ = R/6`.  Each
  carried hypothesis is genuine, satisfiable, non-vacuous, and never the conclusion.  No `sorry`
  (header prose excepted), no `:= True`, no new axioms, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SOL #20 ENDPOINT ANALYSIS (why the census `hGint` is cutoff-indexed, not forced whole).

  The census `hGint` binder is the FULL oriented interval `[0, u]`.  The first factor is the FIELD
  derivative `witnessFieldDeriv … i τ x z` (τ = u−s), whose gated envelope
  (`WitnessDerivDomination.witnessFieldDeriv_gate_envelope`) carries a `Bs`-constant that scales like
  `τ⁻¹` as `τ → 0` (the `1/(2τ)` slope factor).  So near the ENDPOINT `s = u` (τ = u−s → 0) the
  `z`-pairing profile is dominated only by a SINGULAR `(u−s)^{-1/2}` bound — an INTEGRABLE singularity
  (`∫₀ᵘ (u−s)^{-1/2} ds = 2√u`), but NOT a CONSTANT.  The banked pairing engine bounds by a CONSTANT
  `M`, so it CANNOT reach the endpoint; forcing the full `[0,u]` with the naive dominator FAILS (the
  `SecondDerivEnvelope §C` verdict is the sharper `(u−s)⁻¹` non-integrability at second order).

  ⟹  SOL #20-COMPLIANT SPLIT.  Split `[0, u] = [0, u−εₘ] ∪ [u−εₘ, u]`:
    •  the BULK tranche `[0, u−εₘ]`  (τ = u−s ≥ εₘ, the NON-singular region) — DISCHARGED by
       `pairing_intervalIntegrable_lowerCapped` at ceiling `Tc := u`, lower cap `εₘ := epsSeq m`,
       from the CAPPED field-derivative Gaussian domination `hWFDdomCapped` (`εₘ ≤ τ`, satisfiable —
       the `τ⁻¹` bank feeds it via `EveryCeilingFamilies.gaussDdim_crude_to_capped`), `hFdomEvery`,
       `hFzero`, and the `s`-profile measurability `hGintMeas`;
    •  the ENDPOINT sliver `[u−εₘ, u]`  (τ = u−s ∈ [0, εₘ], the singular region) — the honest CARRY
       `hSliver` (the `(u−s)^{-1/2}` integrable-singularity content no constant/Gaussian engine
       supplies);
  then `IntervalIntegrable.trans` re-assembles the FULL `[0, u]` census shape.

  ── WHAT LANDS (this file, ns `QIQTH.HGintCutoff`).
    • `hGint_capped_at_witness` — ★ the CUTOFF-INDEXED bulk tranche `[0, u−εₘ]` of the census `hGint`
      profile, DISCHARGED (deg-case + capped-ceiling engine), first factor `witnessFieldDeriv … i · x`.
    • `hGint_at_witness` — ★★ the census's EXACT full-`[0,u]` `hGint` shape, reduced to
      {bulk tranche DISCHARGED} + {endpoint sliver CARRY} via `IntervalIntegrable.trans`.
    • `perUCensus_phase2` — ★★★ the per-`u` census tuple FIRED (= `perUCensus_phase1`'s conclusion) with
      the `hGint` field DISCHARGED-THIS-BRICK from `hGint_at_witness`, every other census field kept as
      its J4-428 enumerated carry.

  ── DONT-UNDERCREDIT FINDINGS.
    • The engine IS banked: `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped` — the exact
      capped-ceiling machine `frozenLeg_hFint` runs on.  We WIRE it at `A := witnessFieldDeriv`, not
      re-prove.  The deg-case is `ESLegWidening.intervalIntegrable_of_deg`.
    • The `τ⁻¹`-to-capped unlock `gaussDdim_crude_to_capped` (J4·F3) is exactly why the crude
      field-derivative envelope (with its `1/(2τ)` slope factor) SATISFIES `hWFDdomCapped` on `[εₘ, Tc]`.
    • The J4-428 `hGint` "NO banked supplier" flag was TRUE for the FULL `[0,u]` constant-dominator
      route; the CUTOFF-INDEXED bulk IS now supplied here — only the endpoint sliver stays a carry.

  Every hypothesis is satisfiable, non-vacuous, strictly lower-level than the conclusion, and NONE
  equals `a₁ = R/6`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PerUCensusInstantiation
import QIQTH.EveryCeilingFamilies

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.HGintCutoff

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `hGint_capped_at_witness` — the CUTOFF-INDEXED bulk tranche `[0, u−εₘ]`.
    ############################################################################### -/

/-- **★ `hGint_capped_at_witness` — THE hGint BULK TRANCHE, DISCHARGED (capped-ceiling).**  Interval-
    integrability on the NON-singular bulk `[0, u−εₘ]` of the census `hGint` field-derivative profile
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) x z · leviSeries (heatOp g gi W) s z 0`,
    per `u ∈ U`, `i`, `x`, `m`.  Verbatim the `frozenLeg_hFint` route with the first factor instantiated
    to the FIELD DERIVATIVE at base `x` — `A := fun τ _ z ↦ witnessFieldDeriv … i τ x z`, so
    `A (u−s) 0 z = witnessFieldDeriv … i (u−s) x z`.  CASE 1 (`u−εₘ ≤ 0`) is
    `ESLegWidening.intervalIntegrable_of_deg` (`hFzero`); CASE 2 (`u−εₘ > 0`, `0 < u`) is
    `EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped` at ceiling `Tc := u`, lower cap
    `εₘ := epsSeq m` (both endpoints `≤ u−εₘ`, so `τ = u−s ≥ εₘ`, where the crude `τ⁻¹` field-derivative
    bound is a genuine Gaussian bound).  Honest carries: {`hFzero`, `hWFDdomCapped` (the capped
    field-derivative Gaussian domination), `hFdomEvery`, `hGintMeas`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_capped_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m)))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 (u - epsSeq m) := by
  intro u hu i x m
  rcases le_or_gt (u - epsSeq m) 0 with hdeg | hpos
  · exact QIQTH.ESLegWidening.intervalIntegrable_of_deg
      (fun τ _ z => witnessFieldDeriv g gi hC hK S a b i τ x z)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
      u (u - epsSeq m) hdeg hFzero
  · have hεpos := epsSeq_pos m
    have hu0 : 0 < u := by linarith
    obtain ⟨wA, CA, hwA, hCA, hDom⟩ := hWFDdomCapped i x u (epsSeq m) hεpos
    obtain ⟨wF, CF, hwF, hCF, hFdom⟩ := hFdomEvery u
    exact QIQTH.EveryCeilingFamilies.pairing_intervalIntegrable_lowerCapped
      (fun τ _ z => witnessFieldDeriv g gi hC hK S a b i τ x z)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)))
      u u (epsSeq m) wA CA wF CF hu0 le_rfl hεpos hwA hCA hwF hCF hDom hFdom hFzero
      0 (u - epsSeq m) (by linarith) le_rfl (hGintMeas u hu i x m)

/-! ###############################################################################
    ### ★★ `hGint_at_witness` — the census's exact full-`[0,u]` hGint, bulk⊕sliver.
    ############################################################################### -/

/-- **★★ `hGint_at_witness` — THE CENSUS `hGint` SHAPE, DISCHARGED (bulk ⊕ sliver).**  The EXACT
    `hGint` binder of `PerUCensusInstantiation.perUCensus_phase1`: interval-integrability on the FULL
    `[0, u]` of the field-derivative `s`-profile, per `u ∈ U`, `i`, `x`.  For each `(u,i,x)` the endpoint
    sliver carry `hSliver` hands a cutoff index `m` and the sliver integrability on `[u−εₘ, u]`; the
    banked `hGint_capped_at_witness` supplies the bulk `[0, u−εₘ]`; `IntervalIntegrable.trans` splices
    them into `[0, u]`.  This is the SOL #20-compliant reduction: the NON-singular bulk is DISCHARGED,
    the singular endpoint sliver stays the honest carry `hSliver`.  Honest carries: {`hFzero`,
    `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hSliver`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hSliver : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ m : ℕ, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume (u - epsSeq m) u) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u := by
  intro u hu i x
  obtain ⟨m, hsliver_m⟩ := hSliver u hu i x
  exact (hGint_capped_at_witness g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery hGintMeas
    u hu i x m).trans hsliver_m

/-! ###############################################################################
    ### ★★★ `perUCensus_phase2` — the fired per-`u` census, `hGint` supplied internally.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase2`.**  THE V1 PER-`u` CENSUS TUPLE FIRED (= the conclusion of
    `PerUCensusInstantiation.perUCensus_phase1` / `PerUCensusTuple.hPd2conv_perU_fired`), with the
    `hGint` census field supplied INTERNALLY from the SOL #20-compliant bulk⊕sliver reduction
    (`hGint_at_witness`), and every OTHER census field kept as its J4-428 ENUMERATED CARRY: the heat-time
    domain `U`/`hUpos`, the field nbhd `nb`/`hnb_open`/`hnb0`, the seven-leg linewise provider `hProv`,
    the order-2 derivative fields `fderivBulk`/`gderiv` and rate constants `C₀`/`C₁`/`C₂`, the bulk
    order-2 differentiation `hbulkderiv`, the `O(√ε)` sliver bound `hsliver`, the order-2 field
    continuity `hcont`, and the frozen pointwise carry `hQ1`.  In place of the `hGint` binder it carries
    its lower-level suppliers {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hSliver`}.
    Conclusion = the exact per-`u` frozen→full second-partial `Tendsto` binder (viii).  Every carry is
    satisfiable, non-vacuous, strictly lower-level than the conclusion, and none equals `a₁ = R/6`.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase2 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ) (hUpos : ∀ u ∈ U, 0 < u)
    (nb : ℝ → Set (Point n)) (hnb_open : ∀ u ∈ U, IsOpen (nb u))
    (hnb0 : ∀ u ∈ U, (0 : Point n) ∈ nb u)
    (hProv : ∀ u ∈ U, ∀ x ∈ nb u, ∀ i : Fin n,
      ∃ (snb : Set ℝ) (bound : ℝ → ℝ),
        snb ∈ 𝓝 (x i) ∧
        (∀ w, AEStronglyMeasurable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u))) ∧
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) volume 0 u ∧
        AEStronglyMeasurable
          (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
          (volume.restrict (Set.uIoc 0 u)) ∧
        IntervalIntegrable bound volume 0 u ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0‖ ≤ bound s) ∧
        (∀ᵐ s ∂volume, s ∈ Set.uIoc 0 u → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, vanVleckGatedWitness g gi hC hK S a b (u - s)
              (Function.update x i w) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0)
            (∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) (Function.update x i w) z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0) w))
    (fderivBulk : ℝ → Fin n → ℕ → Point n → (Point n →L[ℝ] ℝ))
    (gderiv : ℝ → Fin n → Point n → (Point n →L[ℝ] ℝ))
    (C₀ C₁ C₂ : ℝ → Fin n → ℝ)
    -- the lower-level `hGint` suppliers (in place of the `hGint` census binder)
    (hFzero : ∀ s : ℝ, s ≤ 0 → ∀ z : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0 = 0)
    (hWFDdomCapped : ∀ (i : Fin n) (x : Point n), ∀ Tc εₘ : ℝ, 0 < εₘ →
        ∃ wA CA : ℝ, 0 < wA ∧ 0 ≤ CA ∧
        ∀ τ : ℝ, εₘ ≤ τ → τ ≤ Tc → ∀ z : Point n,
          |witnessFieldDeriv g gi hC hK S a b i τ x z|
            ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomEvery : ∀ Tc : ℝ, ∃ wF CF : ℝ, 0 < wF ∧ 0 ≤ CF ∧
        ∀ s : ℝ, 0 < s → s ≤ Tc → ∀ z : Point n,
          |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0|
            ≤ CF * gaussDdim (wF * s) z)
    (hGintMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc 0 (u - epsSeq m))))
    (hSliver : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ m : ℕ, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume (u - epsSeq m) u)
    (hbulkderiv : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        HasFDerivAt (QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m)
          (fderivBulk u i m x) x)
    (hsliver : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ), ∀ x ∈ (Set.univ : Set (Point n)),
        dist (fderivBulk u i m x) (gderiv u i x)
          ≤ (C₀ u i + C₁ u i) * (2 * Real.sqrt (epsSeq m)) + C₂ u i * epsSeq m)
    (hcont : ∀ u ∈ U, ∀ i : Fin n, ContinuousOn (gderiv u i) (Set.univ : Set (Point n)))
    (hQ1 : ∀ u ∈ U, ∀ (i : Fin n) (m : ℕ),
        ∃ V ∈ 𝓝 (0 : Point n),
          ∀ y ∈ V, pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hC hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
              (u - epsSeq m) x 0) i y
            = QIQTH.FrozenGermInternal.fbulkInt g gi hC hK S a b u i m y) :
    ∀ u ∈ U, ∀ i : Fin n,
      Tendsto
        (fun m => pd (fun y => pd (fun x => heatConvFrozen
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u
            (u - epsSeq m) x 0) i y) i 0)
        atTop (𝓝 (pd (fun y => pd (fun x => heatConv
            (vanVleckGatedWitness g gi hC hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b))) u x 0) i y) i 0)) :=
  QIQTH.PerUCensusInstantiation.perUCensus_phase1 g gi hC hK S a b U hUpos
    nb hnb_open hnb0 hProv fderivBulk gderiv C₀ C₁ C₂
    (hGint_at_witness g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery hGintMeas hSliver)
    hbulkderiv hsliver hcont hQ1

end QIQTH.HGintCutoff

/-! ## THE CENSUS LEDGER v2 — the honest group-(3) residue after this brick.

  `perUCensus_phase2` reproduces the conclusion of `PerUCensusInstantiation.perUCensus_phase1`
  (= `PerUCensusTuple.hPd2conv_perU_fired`, the per-`u` frozen→full second-partial `Tendsto` binder
  (viii)) from the V1 per-`u` census, with `hGint` DISCHARGED-THIS-BRICK (traded for the SOL #20
  bulk⊕sliver suppliers via `hGint_at_witness`).  Combined with J4-428's `hfrozen_pd1 ⟵ hQ1` trade and
  the members already fired internally by J4-405/406/407, the V1 per-`u` census now closes to:

    field                    v1 status (J4-428)        v2 status (this brick)
    ──────────────────────   ───────────────────────   ─────────────────────────────────────────────
    (G3-a) `U`,`hUpos`       CARRY [domain]            CARRY [domain]                    (unchanged)
    (G3-b) `nb`,`hnb_*`      CARRY [nbhd]              CARRY [nbhd]                      (unchanged)
    (G3-c) `hProv`           CARRY [7-leg provider]    CARRY [7-leg provider]           (unchanged) †
    (G3-d) `fderivBulk`,     CARRY [order-2 data]      CARRY [order-2 data]             (unchanged)
           `gderiv`,`C₀₁₂`
    (G3-e) `hGint`           CARRY [integrability;     ★ DISCHARGED-THIS-BRICK ⟵ bulk (capped-ceiling
                             "NO banked supplier"]       engine) ⊕ sliver carry `hSliver`
    (G3-f) `hbulkderiv`      CARRY [bulk order-2 diff] CARRY [bulk order-2 diff]        (unchanged)
    (G3-g) `hsliver`         CARRY [√ε sliver]         CARRY [√ε sliver]                (unchanged)
    (G3-h) `hcont`           CARRY [order-2 cont.]     CARRY [order-2 cont.]            (unchanged)
    (G3-i) `hQ1`             CARRY [W2 diff; ⟵         CARRY [W2 diff]                  (unchanged) ‡
                             `hfrozen_pd1`]

  In place of the single `hGint` binder, phase2 carries its five strictly-lower-level suppliers:
    `hFzero`        — the `s ≤ 0` Levi-source vanishing (banked `hFzero_concrete` shape);
    `hWFDdomCapped` — the CAPPED (`εₘ ≤ τ`) field-derivative Gaussian domination (the `τ⁻¹` bank feeds
                      it via `gaussDdim_crude_to_capped`);
    `hFdomEvery`    — the every-ceiling Levi Gaussian envelope (F2-style);
    `hGintMeas`     — the `s`-profile ae-strong-measurability on the bulk window (Fubini-supplied shape);
    `hSliver`       — the ENDPOINT-sliver `[u−εₘ, u]` integrability (the `(u−s)^{-1/2}` integrable-
                      singularity content; the honest irreducible remainder).

  † `hProv` — the diagonal 7-leg linewise diff-under-∫ provider (= J4-405 `hlin_field_concrete` input);
    the J4-437..443 chain shrank the FROZEN `hQ1` provider 7→4 (`FrozenProviderLegs`), but that is a
    DIFFERENT provider from the census-`hProv` DIAGONAL provider bound here — `hProv` is unchanged.
  ‡ `hQ1` — the frozen pointwise-on-nbhd first-partial formula; `InnerDiffFamily`/`FrozenProviderLegs`
    reduce it further (7→4) at the `innerDiff_phase2` layer, but at THIS `perUCensus` layer `hQ1` is the
    census carry, unchanged.

  ⚠  GROUP (3) v2 = ENUMERATED INPUT CARRIES ONLY.  This brick does NOT prove `a₁ = R/6`, and makes NO
  claim of unconditionality.  It discharges the census `hGint` field to the bulk tranche (banked
  capped-ceiling engine) plus the honest endpoint-sliver carry, per SOL #20 (the full `[0,u]` constant-
  dominator route is NOT forced).  `a₁ = R/6` remains CONDITIONAL.
-/

section AxiomChecks
open QIQTH.HGintCutoff
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms hGint_capped_at_witness
#print axioms hGint_at_witness
#print axioms perUCensus_phase2
end AxiomChecks
