/-
  SliverSingularEngine — J4-445 (GROUP (3), Sol #20 item (ii)): DISCHARGING THE hGint ENDPOINT SLIVER.

  J4-444 (`QIQTH.HGintCutoff`) reduced the V1 per-`u` census `hGint` (interval-integrability of the
  FIELD-DERIVATIVE `s`-profile
      `s ↦ ∫ z, witnessFieldDeriv … i (u−s) x z · leviSeries (heatOp g gi W) s z 0`
  on the FULL `[0, u]`) to a SOL #20-compliant bulk⊕sliver split: the NON-singular bulk `[0, u−εₘ]`
  DISCHARGED by the banked capped-ceiling pairing engine, and the ENDPOINT sliver `[u−εₘ, u]` carried
  as `hSliver` — the `(u−s)^{-1/2}` INTEGRABLE-SINGULARITY content that no constant/Gaussian engine can
  reach.  THIS brick discharges that `hSliver` carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SLIVER SINGULAR ENGINE (why the endpoint sliver IS integrable, not a wall).

  Near the ENDPOINT `s = u` (τ = u−s → 0) the field-derivative envelope carries a `1/(2τ)` slope
  factor — the naive dominator scales like `τ⁻¹`, which is NON-integrable
  (`SecondDerivEnvelope.order2_naive_dominator_not_intervalIntegrable`).  BUT the `1/(2τ)` numerator
  is an ODD coordinate factor `∑ₖ (…)·zₖ`, and integrating it against the Gaussian produces the
  coordinate FIRST MOMENT `∫ |zₖ|·Gτ ≤ (3/2)√τ` (`HeatResidualBound.absCoord_gaussDdim_integral_le`,
  the J4-422 machinery) — a √τ GAIN.  The net count is
      `τ⁻¹ · √τ = (√τ)⁻¹ = τ^{-1/2}`   (`HeatResidualBound.inv_sqrt_eq_rpow`),
  the INTEGRABLE sliver rate (`∫₀ᵉ τ^{-1/2} = 2√ε`, `HeatResidualBound.sliver_rpow`).  This is EXACTLY
  the risk-gate power-count (`SliverRiskGate.riskGate_powercount`): a quantity `Q` bounded by
  `C·τ⁻¹·|rem|` with `|rem| ≤ B·√τ` is majorised by `(C·B)·τ^{-1/2}`.

  ⟹  ENGINE.  (1) `sliverProfile_dom` turns the risk-gate FACTORISATION of the pairing profile
      (the `C·τ⁻¹·|rem|` leading factor from the amplitude sups + Levi Gaussian, and the coordinate-
      moment remainder `|rem| ≤ B·√τ`) into the pointwise `(u−s)^{-1/2}` domination (via the banked
      `riskGate_powercount`).  (2) `sliverProfile_intervalIntegrable` dominates the profile by the
      SINGULAR-but-INTEGRABLE `(u−s)^{-1/2}` weight (`HeatResidualBound.rpow_sub_intervalIntegrable`)
      via `IntervalIntegrable.mono'`, a.e. on the sliver interior (`s = u` is a null endpoint —
      never forced).  Together they discharge the exact J4-444 `hSliver` shape.

  One brick of the `a₁ = R/6` heat-kernel campaign.  It is **NOT** `a₁ = R/6`, and proves NOTHING
  about `R/6`.  `a₁ = R/6` remains CONDITIONAL on the whole `hDuhamel` / convergence-trio +
  geometric-wiring stack AND on the surviving labelled census carries threaded here.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  Every theorem here re-threads BANKED, satisfiable Gaussian-domination /
  coordinate-moment / interval-integrability data into the exact census `hGint` shape.  NONE proves
  `a₁ = R/6`.  Each carried hypothesis is genuine, satisfiable, non-vacuous, and never the conclusion.
  No `sorry` (header prose excepted), no `:= True`, no new axioms, no existing file edited.

  ── WHAT LANDS (this file, ns `QIQTH.SliverSingularEngine`).
    • `sliverProfile_dom` — ★ the pointwise `(u−s)^{-1/2}` domination of the profile, from the
      risk-gate factorisation carries (amplitude/Levi leading factor + coordinate-moment remainder).
    • `sliverProfile_intervalIntegrable` — ★ THE ENGINE: profile dominated a.e. by `K·(u−s)^{-1/2}`
      on the sliver `⟹` interval-integrable there (`mono'` against the singular integrable weight).
    • `hSliver_discharged` — ★★ the EXACT J4-444 `hSliver` shape, DISCHARGED, from {`hProfFac`,
      `hProfMeas`} (the factorisation + sliver measurability carries).
    • `hGint_full_at_witness` — ★★ the census `hGint` FULLY discharged (bulk ⊕ sliver both supplied):
      `[0, u]` interval-integrability from lower-level carries only, `hSliver` gone.
    • `perUCensus_phase3` — ★★★ the fired per-`u` census with `hGint` supplied INTERNALLY (bulk engine
      ⊕ sliver engine), every OTHER census field kept as its J4-428 enumerated carry.

  Every hypothesis is satisfiable, non-vacuous, strictly lower-level than the conclusion, and NONE
  equals `a₁ = R/6`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HGintCutoff
import QIQTH.SliverRiskGate
import QIQTH.SliverEstimates

open MeasureTheory Filter Finset Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.FlatHeatEquation
open QIQTH.CConvV2DerivRep QIQTH.CConvV2Facade QIQTH.Pd2ConvDissolution
open scoped Topology Interval BigOperators ContDiff

namespace QIQTH.SliverSingularEngine

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ `sliverProfile_dom` — the pointwise `(u−s)^{-1/2}` domination.
    ############################################################################### -/

/-- **★ `sliverProfile_dom` — THE POINTWISE `(u−s)^{-1/2}` DOMINATION.**  The risk-gate power-count at
    the shrinking width `τ = u − s`: a profile `f` whose value at `s < u` factors as
    `|f s| ≤ C·(u−s)⁻¹·|rem s|` (the `1/(2τ)` slope × the amplitude/Levi Gaussian bound) with the
    coordinate-moment remainder `|rem s| ≤ B·√(u−s)` (the `∫|zₖ|·Gτ ≤ (3/2)√τ` first moment) is
    majorised by the INTEGRABLE rate `(C·B)·(u−s)^{-1/2}`.  A thin, generic wiring of the banked
    `SliverRiskGate.riskGate_powercount` at `Q := f s`, `u := u−s`.  Honest carries: {`hC`, `hfac`,
    `hrem`} — each a genuine, satisfiable factorisation fact, none the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem sliverProfile_dom (f : ℝ → ℝ) (u C B : ℝ) (hC : 0 ≤ C) (rem : ℝ → ℝ)
    (hfac : ∀ s, s < u → |f s| ≤ C * (u - s)⁻¹ * |rem s|)
    (hrem : ∀ s, s < u → |rem s| ≤ B * Real.sqrt (u - s)) :
    ∀ s, s < u → |f s| ≤ (C * B) * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs
  exact QIQTH.SliverRiskGate.riskGate_powercount (u - s) C B (rem s) (f s)
    (by linarith) hC (hrem s hs) (hfac s hs)

/-! ###############################################################################
    ### ★ `sliverProfile_intervalIntegrable` — THE ENGINE (mono' vs the singular weight).
    ############################################################################### -/

/-- **★ `sliverProfile_intervalIntegrable` — THE SLIVER SINGULAR ENGINE.**  A profile `f` that is
    a.e.-strongly-measurable on the sliver window `Ι (u−εₘ) u` and dominated a.e. (`s ≠ u`, the null
    endpoint) by the SINGULAR-but-INTEGRABLE weight `K·(u−s)^{-1/2}` is INTERVAL-INTEGRABLE on
    `[u−εₘ, u]`.  Via `IntervalIntegrable.mono'` (through `intervalIntegrable_iff` + `Integrable.mono'`)
    against `HeatResidualBound.rpow_sub_intervalIntegrable` — the `∫₀ᵉ τ^{-1/2} = 2√ε` integrable
    singularity.  The endpoint `s = u` is a.e.-excluded (`HeatResidualBound.ae_ne_point`), never forced
    to a value.  `K` is m-FREE (only the interval endpoint `εₘ` carries `m`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliverProfile_intervalIntegrable (f : ℝ → ℝ) (u εₘ K : ℝ) (hεₘ : 0 ≤ εₘ)
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Set.uIoc (u - εₘ) u)))
    (hdom : ∀ s ∈ Set.uIoc (u - εₘ) u, s ≠ u →
        |f s| ≤ K * (u - s) ^ (-(1 : ℝ) / 2)) :
    IntervalIntegrable f volume (u - εₘ) u := by
  have hdomII : IntervalIntegrable (fun s => K * (u - s) ^ (-(1 : ℝ) / 2)) volume (u - εₘ) u :=
    (QIQTH.HeatResidualBound.rpow_sub_intervalIntegrable u εₘ hεₘ).const_mul K
  have hdomInt : Integrable (fun s => K * (u - s) ^ (-(1 : ℝ) / 2))
      ((volume : Measure ℝ).restrict (Set.uIoc (u - εₘ) u)) :=
    (intervalIntegrable_iff).mp hdomII
  refine (intervalIntegrable_iff).mpr (Integrable.mono' hdomInt hmeas ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (QIQTH.HeatResidualBound.ae_ne_point u)] with s hsmem hsne
  rw [Real.norm_eq_abs]
  exact hdom s hsmem hsne

/-! ###############################################################################
    ### ★★ `hSliver_discharged` — the exact J4-444 hSliver shape, DISCHARGED.
    ############################################################################### -/

/-- **★★ `hSliver_discharged` — THE ENDPOINT SLIVER CARRY, DISCHARGED.**  The EXACT `hSliver` binder of
    `HGintCutoff.hGint_at_witness`: for each `(u,i,x)` an index `m` and interval-integrability of the
    field-derivative `s`-profile on the endpoint sliver `[u−εₘ, u]`.  Supplied at `m := 0` from the two
    lower-level carries: the risk-gate FACTORISATION `hProfFac` (`|profile| ≤ C·(u−s)⁻¹·|rem|` ∧
    `|rem| ≤ B·√(u−s)`) — fed through `sliverProfile_dom` to the `(u−s)^{-1/2}` domination — and the
    sliver-window measurability `hProfMeas`, fed to `sliverProfile_intervalIntegrable`.  Honest carries:
    {`hProfMeas`, `hProfFac`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hSliver_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (U : Set ℝ)
    (hProfMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hProfFac : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C B : ℝ, ∃ rem : ℝ → ℝ, 0 ≤ C ∧
        (∀ s, s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ C * (u - s)⁻¹ * |rem s|) ∧
        (∀ s, s < u → |rem s| ≤ B * Real.sqrt (u - s))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ m : ℕ, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume (u - epsSeq m) u := by
  intro u hu i x
  obtain ⟨C, B, rem, hC0, hfac, hrem⟩ := hProfFac u hu i x
  refine ⟨0, sliverProfile_intervalIntegrable
    (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        ∂(volume : Measure (Point n)))
    u (epsSeq 0) (C * B) (epsSeq_pos 0).le (hProfMeas u hu i x 0) ?_⟩
  intro s hsmem hsne
  have hub : s ∈ Set.Ioc (min (u - epsSeq 0) u) (max (u - epsSeq 0) u) := hsmem
  have hsu : s ≤ u := by
    have h2 := hub.2
    rwa [max_eq_right (by linarith [epsSeq_pos 0])] at h2
  have hlt : s < u := lt_of_le_of_ne hsu hsne
  exact sliverProfile_dom
    (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
        ∂(volume : Measure (Point n)))
    u C B hC0 rem hfac hrem s hlt

/-! ###############################################################################
    ### ★★ `hGint_full_at_witness` — the census hGint, FULLY discharged (bulk ⊕ sliver).
    ############################################################################### -/

/-- **★★ `hGint_full_at_witness` — THE CENSUS `hGint`, FULLY DISCHARGED.**  The EXACT `hGint` binder of
    `PerUCensusInstantiation.perUCensus_phase1`: interval-integrability on the FULL `[0, u]` of the
    field-derivative `s`-profile, per `u ∈ U`, `i`, `x`.  Now BOTH tranches are supplied internally: the
    NON-singular bulk `[0, u−εₘ]` by `HGintCutoff.hGint_at_witness`'s banked capped-ceiling engine, and
    the endpoint sliver `[u−εₘ, u]` by `hSliver_discharged` (this file).  The `hSliver` carry is GONE —
    replaced by its two strictly-lower-level suppliers {`hProfMeas`, `hProfFac`}.  Honest carries:
    {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hProfMeas`, `hProfFac`}.  ⚠ NOT `a₁ = R/6`. -/
theorem hGint_full_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hProfMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hProfFac : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C B : ℝ, ∃ rem : ℝ → ℝ, 0 ≤ C ∧
        (∀ s, s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ C * (u - s)⁻¹ * |rem s|) ∧
        (∀ s, s < u → |rem s| ≤ B * Real.sqrt (u - s))) :
    ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        volume 0 u :=
  QIQTH.HGintCutoff.hGint_at_witness g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery hGintMeas
    (hSliver_discharged g gi hC hK S a b U hProfMeas hProfFac)

/-! ###############################################################################
    ### ★★★ `perUCensus_phase3` — the fired per-`u` census, hGint FULLY internal.
    ############################################################################### -/

/-- **★★★ `perUCensus_phase3`.**  THE V1 PER-`u` CENSUS TUPLE FIRED (= the conclusion of
    `PerUCensusInstantiation.perUCensus_phase1` / `PerUCensusTuple.hPd2conv_perU_fired`), with the
    `hGint` census field supplied INTERNALLY, FULLY (both tranches), from `hGint_full_at_witness`: the
    banked capped-ceiling bulk engine ⊕ the sliver singular engine (this file).  In place of the single
    `hGint` binder — and of J4-444's `hSliver` carry — phase3 carries the strictly-lower-level suppliers
    {`hFzero`, `hWFDdomCapped`, `hFdomEvery`, `hGintMeas`, `hProfMeas`, `hProfFac`}.  Every OTHER census
    field is kept as its J4-428 ENUMERATED CARRY (domain `U`/`hUpos`, nbhd `nb`/`hnb_*`, provider
    `hProv`, order-2 data `fderivBulk`/`gderiv`/`C₀₁₂`, `hbulkderiv`, `hsliver`, `hcont`, `hQ1`).
    Conclusion = the exact per-`u` frozen→full second-partial `Tendsto` binder (viii).  Every carry is
    satisfiable, non-vacuous, strictly lower-level than the conclusion, and none equals `a₁ = R/6`.
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem perUCensus_phase3 (g gi : Point n → Fin n → Fin n → ℝ)
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
    -- the lower-level `hGint` suppliers (in place of the `hGint` census binder AND J4-444's `hSliver`)
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
    (hProfMeas : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∀ m : ℕ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
            ∂(volume : Measure (Point n)))
        ((volume : Measure ℝ).restrict (Set.uIoc (u - epsSeq m) u)))
    (hProfFac : ∀ u ∈ U, ∀ (i : Fin n) (x : Point n), ∃ C B : ℝ, ∃ rem : ℝ → ℝ, 0 ≤ C ∧
        (∀ s, s < u →
          |∫ z, witnessFieldDeriv g gi hC hK S a b i (u - s) x z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) s z 0
              ∂(volume : Measure (Point n))|
            ≤ C * (u - s)⁻¹ * |rem s|) ∧
        (∀ s, s < u → |rem s| ≤ B * Real.sqrt (u - s)))
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
    (hGint_full_at_witness g gi hC hK S a b U hFzero hWFDdomCapped hFdomEvery hGintMeas
      hProfMeas hProfFac)
    hbulkderiv hsliver hcont hQ1

end QIQTH.SliverSingularEngine

/-! ## THE CENSUS LEDGER v3 — the honest group-(3) residue after this brick.

  `perUCensus_phase3` reproduces the conclusion of `PerUCensusInstantiation.perUCensus_phase1`
  (= `PerUCensusTuple.hPd2conv_perU_fired`, the per-`u` frozen→full second-partial `Tendsto` binder
  (viii)) from the V1 per-`u` census, with `hGint` now FULLY DISCHARGED — BOTH the bulk (J4-444 capped-
  ceiling engine) AND the endpoint sliver (this brick's singular engine).  J4-444's `hSliver` carry is
  GONE.  The V1 per-`u` census now closes to:

    field                    v2 status (J4-444)         v3 status (this brick)
    ──────────────────────   ────────────────────────   ────────────────────────────────────────────
    (G3-a) `U`,`hUpos`       CARRY [domain]             CARRY [domain]                    (unchanged)
    (G3-b) `nb`,`hnb_*`      CARRY [nbhd]               CARRY [nbhd]                      (unchanged)
    (G3-c) `hProv`           CARRY [7-leg provider]     CARRY [7-leg provider]           (unchanged) †
    (G3-d) `fderivBulk`,     CARRY [order-2 data]       CARRY [order-2 data]             (unchanged)
           `gderiv`,`C₀₁₂`
    (G3-e) `hGint`           bulk DISCHARGED ⊕ `hSliver` ★★ FULLY DISCHARGED — bulk (capped-ceiling
                             CARRY                        engine) ⊕ sliver (singular engine); `hSliver`
                                                          GONE, traded for {`hProfMeas`,`hProfFac`}
    (G3-f) `hbulkderiv`      CARRY [bulk order-2 diff]  CARRY [bulk order-2 diff]        (unchanged)
    (G3-g) `hsliver`         CARRY [√ε sliver]          CARRY [√ε sliver]                (unchanged) ‡
    (G3-h) `hcont`           CARRY [order-2 cont.]      CARRY [order-2 cont.]            (unchanged)
    (G3-i) `hQ1`             CARRY [W2 diff]            CARRY [W2 diff]                  (unchanged)

  In place of the `hGint` binder — and of J4-444's `hSliver` — phase3 carries the strictly-lower-level
  suppliers:
    `hFzero`        — the `s ≤ 0` Levi-source vanishing (banked `hFzero_concrete` shape);
    `hWFDdomCapped` — the CAPPED (`εₘ ≤ τ`) field-derivative Gaussian domination (bulk engine);
    `hFdomEvery`    — the every-ceiling Levi Gaussian envelope (F2-style);
    `hGintMeas`     — the `s`-profile ae-strong-measurability on the BULK window `Ι 0 (u−εₘ)`;
    `hProfMeas`     — the `s`-profile ae-strong-measurability on the SLIVER window `Ι (u−εₘ) u` (NEW,
                      the sliver-side Fubini-supplied measurability shape);
    `hProfFac`      — the risk-gate FACTORISATION of the sliver profile: `|profile| ≤ C·(u−s)⁻¹·|rem|`
                      (the `1/(2τ)` slope × amplitude/Levi Gaussian) with `|rem| ≤ B·√(u−s)` (the
                      coordinate first moment `∫|zₖ|·Gτ ≤ (3/2)√τ`) — the banked-mechanism content that
                      the singular engine converts to the integrable `(u−s)^{-1/2}` rate (NEW).

  ── REMAINING GROUP-(3) RESIDUE (v3).  Enumerated INPUT carries only; NO `a₁ = R/6` claim:
      U/hUpos, nb/hnb_* ;  the DIAGONAL 7-leg `hProv` ;  order-2 data `fderivBulk`/`gderiv`/`C₀₁₂` ;
      `hbulkderiv` ;  the `√ε` sliver bound `hsliver` ;  `hcont` ;  `hQ1` (at the census layer — note
      the WITNESS-level frozen provider was shrunk 7→4 by `FrozenProviderLegs`, a DIFFERENT provider) ;
      and the `hGint` suppliers {`hFzero`,`hWFDdomCapped`,`hFdomEvery`,`hGintMeas`,`hProfMeas`,
      `hProfFac`}.  The single `hGint` integrability binder — the J4-428 "NO banked supplier" flag —
      is now FULLY discharged to lower-level satisfiable carries.

  † `hProv` — the diagonal 7-leg linewise diff-under-∫ provider (= J4-405 `hlin_field_concrete` input),
    a DIFFERENT provider from the frozen `hQ1` provider that `FrozenProviderLegs` shrank; unchanged.
  ‡ `hsliver` (census G3-g) — the `√ε` DISTANCE bound on the ORDER-2 fderiv sliver; DIFFERENT object
    from this brick's `hProfFac` (the first-field-derivative pairing profile integrability); unchanged.

  ⚠  GROUP (3) v3 = ENUMERATED INPUT CARRIES ONLY.  This brick does NOT prove `a₁ = R/6`, and makes NO
  claim of unconditionality.  It discharges the census `hGint` field FULLY (bulk engine ⊕ sliver
  singular engine), per SOL #20 — the endpoint sliver is now supplied, not carried.  `a₁ = R/6`
  remains CONDITIONAL on the whole convergence-trio + geometric-wiring stack and the surviving carries.
-/

section AxiomChecks
open QIQTH.SliverSingularEngine
-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms sliverProfile_dom
#print axioms sliverProfile_intervalIntegrable
#print axioms hSliver_discharged
#print axioms hGint_full_at_witness
#print axioms perUCensus_phase3
end AxiomChecks
