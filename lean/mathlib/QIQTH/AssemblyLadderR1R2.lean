/-
  AssemblyLadderR1R2 — J4-223: LADDER BRICKS R1 (+ R2 verdict).

  ════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a pure
  RE-PLUMBING brick on top of `GrandAssemblyRecon.a1_R6_assembled` (J4-222): it UNBUNDLES the
  `endpoint`/`inter` bundle binders of that capstone, building them INTERNALLY from deeper banked
  data, and records the honest SIZE VERDICT on the R2 interchange trio.  No new analysis.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R1 — `a1_R6_assembled_v2`.  DONE (builds; std-3).
     `a1_R6_assembled` with the two bundle binders
        `endpoint : EndpointData g gi Wit t C`   and   `inter : InterchangeData g gi Wit t`
     REPLACED by the deeper data those bundles are built from, via
        `TruncatedDuhamelData.endpointData_of_banked` / `.interchangeData_of_banked`.
     Each builder consumes {hEbound(∀τ>0), hEzero, hEmeas}; the three are supplied INTERNALLY:
       · `hEmeas` (SHARED by both builders) ← `ChartJetHessianMixed.tripleHEmeas_concrete` at the
         concrete gated witness — defeq to the `StronglyMeasurable` slot (build-checked in
         `GrandAssemblyRecon.tripleHEmeas_is_hEmeas_slot`, `Iff.rfl`).  Its own carries become the
         NEW binders: the measurable-supplier existentials `hcarTau`/`hcarField`/`hcarField2`, the
         `gi`/`christoffel` measurabilities `hgiMeas`/`hchrMeas`, `hn : 0 < n`, `hKmeasSet`.
         CONTINUITY-FREE.
       · `hEzero` ← the capstone's OWN `hEzeroE` (already a binder — SHARED, no new slot).
       · `hEbound` ← the NEW binder `hEboundFull` (the ∀τ>0, width-2 `baseKernelW` envelope).

     ⚠ THE τ-WINDOW MISMATCH (honest).  `EboundWiringHD1.hEboundW_from_geometry` delivers only the
       `τ ≤ t`-restricted envelope, but BOTH builders need the UNRESTRICTED `∀ τ, 0 < τ` form
       (`endpointData_of_banked.hIntegrable` runs `iterConvIntegrableW_of_bound_baseMeas` over ALL
       τ > 0; `interchangeData_of_banked` runs the Volterra DCT interchange over ALL τ > 0).  So the
       geometry provider CANNOT discharge these slots as-is (it is τ-window-weakened, J4-210).  The
       ∀τ>0 envelope is therefore CARRIED HONESTLY as `hEboundFull` — a satisfiable geometric DATA
       fact (the un-weakened sibling of `hEboundW_from_geometry`), NOT taken from that provider.

     ⚠ SIZE/DEPTH NOTE (honest; consistent with J4-222).  `a1_R6_assembled`'s header explicitly kept
       `endpoint`/`inter` BUNDLED because unbundling their `{hEbound(∀τ>0), hEzero, hEmeas}` ENLARGES
       the binder COUNT.  `a1_R6_assembled_v2` DOES enlarge the count (net +6 binders): it trades the
       two OPAQUE `: Prop` bundles for the measurable-supplier existentials + the ∀τ>0 envelope.  The
       value is DEPTH, not size: the surface is now all measurable-suppliers + DATA (dischargeable
       from smoothness in a later rung), with NO opaque `EndpointData`/`InterchangeData` Prop bundle
       remaining — which is exactly the ladder's stated target (`a1_R6_of_geometry`, all-concrete).
       If the project's optimisation target were minimal binder COUNT, R1 would itself be a
       size-rejection; under the all-concrete ladder target it is genuine progress.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## R2 — the interchange trio `{hInterchange, hLapFull, hEcomb}`.  SIZE-REJECTED (all three).
     Verdict: NO `a1_R6_assembled_v3` improves on v2 — every discharge ENLARGES the surface
     (the J4-211 size-rejection pattern).  Reason: there is NO banked `∀ u ∈ U` (resp. `∀ m u`)
     producer for the `Mem*` members; only FIXED-`u`/per-`(m,u)` builders exist, each carrying many
     deeper hypotheses that must be re-quantified over the window to rebuild the member.

       · `hInterchange : MemInterchange` (= `∀ m i, ∀ u ∈ U, pd(pd(frozen)) = ∫∫ pdpdH·F`) — 1 member.
         `SecondOrderInterchange.hInterchange_discharge` is FIXED-`u`, carrying ~14 hyps (the spatial
         2nd-derivative diff-under-∫∫ engine: `hpdpdH, V, hVopen, hV0, hQ1, snb, hsnb, hFmeas, hFint,
         hF'meas, bound, hbdd, hbound, hdiff`), NONE reusable from the capstone's DaTrunc time-deriv
         engine.  ∀u∈U re-quantification ⟹ ~14 new families.  1 → ~14.  REJECT.

       · `hLapFull : MemLapFull` (= `∀ u ∈ U, Δ_g(H*F) = ∑ᵢ ∫₀ᵘ ∫ pdpdH·F`) — 1 member.
         `InterchangeThreading.hLapFull_of_lims` is FIXED-`u`; its `hgi`/`hΓ`/`pdpdH`/`hInterchange`/
         `hII_lo`/`hII_hi` carries ARE already capstone data (free), but `B`/`hSliver`/`hBlim` (the
         sliver bound) and — the genuine content — `hLHSlim` (the C²-limit `Δ_g(frozen)→Δ_g(H*F)`, an
         F2 derivative-of-limit fact) are NEW and must be `∀u∈U`.  1 → ~4 (incl. the hard `hLHSlim`).
         REJECT.

       · `hEcomb : MemECombine` (= `∀ m u, DaTrunc = LapTrunc + Etrunc`) — 1 member.
         `TruncatedDuhamel.hE_combination` is per-`(m,u)`, carrying `hDa, hLap, hLapZ, hEZ, hLapS, hES`
         (2 integral-form identities + 4 integrabilities).  ∀m,u re-quantification ⟹ ≥4 new families.
         1 → ≥4.  REJECT.

     Keeping the three `Mem*` members as capstone binders is the honest SMALLER surface — carried
     verbatim into `a1_R6_assembled_v2`.

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## POST-R1R2 LEAF ENUMERATION (the surface of `a1_R6_assembled_v2`, toward R3–R7).
     Relative to `a1_R6_assembled` (J4-222 §2), the DELTA is:
       REMOVED : `endpoint : EndpointData`, `inter : InterchangeData`   (2 opaque Prop bundles).
       ADDED   : `hn`, `hKmeasSet`, `hcarTau`, `hcarField`, `hcarField2`, `hgiMeas`, `hchrMeas`
                 (the tripleHEmeas measurable-supplier block — CONCRETE-DISCHARGEABLE from smoothness),
                 `hEboundFull` (∀τ>0 width-2 Gaussian envelope — DATA, the un-weakened
                 `hEboundW_from_geometry` sibling).
     UNCHANGED (still open toward the final `a1_R6_of_geometry`):
       GEOMETRY   g,gi,Ric,…,hgi,hΓ,hdg0,htr,hsrc                (RNC/Ricci input the theorem is ABOUT)
       CD/DATA    `core : TruncatedDuhamelCore`                  (R3: BoundaryAssembly + hDerivLU + daLim)
       CD         `hgD1 i`                                        (R5: XUniformSliverFull.hD1_from_data)
       CD         `hInterchange`/`hLapFull`/`hEcomb`             (R2 size-REJECTED — kept as members)
       DATA       the CConv facade scaffolding + bundles         (R4: hCConv_discharged_from_data)
       DATA       the whole hDConv analytic residue pile         (dominations/integrabilities/sliver…)
       DATA       `hEboundFull` (NEW), `hAdom`/`hEdom`/…          (R6: Gaussian-envelope banked bounds)
       CD         `hn`/`hKmeasSet`/`hcar*`/`hgiMeas`/`hchrMeas`  (NEW; R1½: discharge suppliers from
                                                                   smoothness of chart/amp jets)
     GENUINE-GAP: NONE at the a₁ = R/6 CONDITIONAL level (as in J4-222).

  ────────────────────────────────────────────────────────────────────────────────────────────────
  ## NEXT BRICK (R3, refined).  Discharge `core : TruncatedDuhamelCore` via
     `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim`, whose residue is the 3 pointwise limits
     {`hBoundaryLim`, `hDaLim`, `hDerivConv`}: `hDaLim` ← `ETailRateBound.hDaLimLU_from_data` composed
     with `daLimLU_reduces_to_pointwise` (`.tendsto_at htU`) — REUSING the exact hDaLimLU-data already
     carried by v2 (so `hDaLim` is FREE, net-neutral); `hBoundaryLim` ← BoundaryAssembly loc-unif →
     `.tendsto_at`; `hDerivConv` ← `hDerivLU_discharge` loc-unif → `.tendsto_at`.  Assess size: the
     `hDaLim` half is free (data already present); the boundary/deriv halves need their loc-unif
     carries — likely a net shrink IF BoundaryAssembly/hDerivLU reuse the capstone's DConv pile.

  NO `sorry`.  NO new axioms.  NO `:= True`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GrandAssemblyRecon
import QIQTH.ChartJetHessianMixed

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.TrueHeatKernel QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussianConvolution QIQTH.HeatParametrixAnsatz QIQTH.ResidueBound
open QIQTH.HeatKernelA1 QIQTH.LaplaceBeltrami
open QIQTH.HeatResidualBound
open QIQTH.CConvFacade QIQTH.LeviSeries
open QIQTH.CConvConcreteThreading
open QIQTH.HDConvThreading QIQTH.TruncatedDuhamelData
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound QIQTH.HD1CLMLift
open QIQTH.GrandAssemblyRecon QIQTH.ChartJetHessianMixed
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.AssemblyLadderR1R2

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★ R1 — `a1_R6_assembled_v2`: `endpoint`/`inter` bundles UNBUNDLED.
    ############################################################################### -/

/-- **★★★ J4-223 — `a1_R6_assembled_v2`.**  `GrandAssemblyRecon.a1_R6_assembled` with the two bundle
    binders `endpoint : EndpointData …` and `inter : InterchangeData …` REPLACED by the deeper banked
    data they are built from:
      · both bundles' shared `hEmeas` slot ← `ChartJetHessianMixed.tripleHEmeas_concrete` at the
        concrete gated witness (defeq to the `StronglyMeasurable` slot);
      · both bundles' `hEzero` slot ← the capstone's own `hEzeroE` (SHARED);
      · both bundles' `hEbound(∀τ>0)` slot ← the NEW carried envelope `hEboundFull` (honestly carried:
        `hEboundW_from_geometry` only supplies the τ≤t-weakened form, J4-210 — see header).
    Same conclusion as `a1_R6_assembled`; NO `EndpointData`/`InterchangeData` bundle in the surface.
    Pure composition — no new analysis.  NOT `a₁ = R/6`. -/
theorem a1_R6_assembled_v2 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    -- (i) RNC / Ricci geometric data (flat):
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- ★ R1 NEW: the `tripleHEmeas_concrete` measurable-supplier block (was `endpoint`/`inter` bundles).
    (hn : 0 < n) (hKmeasSet : MeasurableSet K)
    (hcarTau : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ S w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ k : Fin n, ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
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
            IsOpen (S w.2.2) ∧ w.2.1 ∈ S w.2.2 ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    (hEboundFull : ∀ τ p q, 0 < τ →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    -- core kept (R3), `hCH`:
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    -- (ii) the CConv `C²` facade bundles (v6, verbatim):
    (uu : Set (Point n)) (hu_open : IsOpen uu) (hu0 : (0 : Point n) ∈ uu)
    (Bs Ba Bd Cf : ℝ) (Dmap : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t uu)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (derivData : CConvDerivativeData g gi hChr hK S a b t uu
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      Dmap)
    (env : CConvEnvelopeData g gi hChr hK S a b t uu Bs Ba Bd)
    -- v7 route: per-coordinate SCALAR jets.
    (hgD1 : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n))) (0 : Point n))
    -- (v) the `hDConv` analytic residue block (v6 residue, verbatim — MINUS `DaLim`/`hDaLimLU`):
    (T : ℝ) (hT : 0 < T)
    (U : Set ℝ) (hUopen : IsOpen U) (htU : t ∈ U)
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (r₀ τ₀ : ℝ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀)
    (u₀ u₁ : Point n → ℝ)
    (hAnear : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z ∈ Metric.ball (0 : Point n) r₀,
        vanVleckGatedWitness g gi hChr hK S a b τ 0 z = gaussDdim τ z * (u₀ z + τ * u₁ z))
    (hu₀cont : ContinuousAt u₀ 0) (hu₀one : u₀ 0 = 1)
    (C₀ C₁ : ℝ) (hu₀bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₀ z| ≤ C₀)
    (hu₁bdd : ∀ z ∈ Metric.ball (0 : Point n) r₀, |u₁ z| ≤ C₁)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hAzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n, vanVleckGatedWitness g gi hChr hK S a b τ p q = 0)
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hBcont : ContinuousOn
        (fun x : ℝ × Point n =>
          leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
        (Set.Ioc 0 T ×ˢ Set.univ))
    (hAmeas : ∀ τ, AEStronglyMeasurable
        (fun z : Point n => vanVleckGatedWitness g gi hChr hK S a b τ 0 z) volume)
    (hBmeas : ∀ s, AEStronglyMeasurable
        (fun z : Point n => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        volume)
    (hu₀meas : AEStronglyMeasurable u₀ volume) (hu₁meas : AEStronglyMeasurable u₁ volume)
    (hMeasFII : ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    (hUfloor : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ U, c ≤ u)
    (hInnerCont : ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    (nb : ℕ → ℝ → Set ℝ) (hnb : ∀ (m : ℕ), ∀ u ∈ U, nb m u ∈ 𝓝 u)
    (hFmeas : ∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable
      (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
      (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (boundD : ℕ → ℝ → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ), ∀ u ∈ U, IntervalIntegrable (boundD m u) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      ‖∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖ ≤ boundD m u s)
    (hpardiff : ∀ (m : ℕ), ∀ u ∈ U, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ a' ∈ nb m u,
      HasDerivAt (fun a' => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (a' - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) a')
    (L : ℕ → ℝ → ℝ) (hLnn : ∀ (m : ℕ), ∀ u ∈ U, 0 ≤ L m u)
    (hCross : ∀ (m : ℕ), ∀ u ∈ U, ∀ h k : ℝ,
      |heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m + k) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) (u + h) (u - epsSeq m) 0 0
          - heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m + k) 0 0
          + heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u (u - epsSeq m) 0 0|
        ≤ L m u * (|h| * |k|))
    -- the `hDaLimLU_from_data` DATA carries (the WALL, turned into data) — R2 trio KEPT (size-rejected).
    (pdpdH : Fin n → ℝ → Point n → ℝ)
    (hInterchange : MemInterchange (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_lo : MemAdjLo (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (hII_hi : MemAdjHi (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) U pdpdH)
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1nn : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n), pdpdH i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hEzeroE : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0)
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n,
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) ) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- R1: the shared `hEmeas` slot from `tripleHEmeas_concrete` (defeq to `StronglyMeasurable …`).
  have hEmeas := QIQTH.ChartJetHessianMixed.tripleHEmeas_concrete hn g gi hChr hK S a b hKmeasSet
    hcarTau hcarField hcarField2 hgiMeas hchrMeas
  -- build the two bundles internally: `hEbound(∀τ>0) ← hEboundFull`, `hEzero ← hEzeroE`, `hEmeas`.
  have endpoint : EndpointData g gi (vanVleckGatedWitness g gi hChr hK S a b) t C :=
    endpointData_of_banked g gi (vanVleckGatedWitness g gi hChr hK S a b) t C
      hEboundFull hEzeroE hEmeas
  have inter : InterchangeData g gi (vanVleckGatedWitness g gi hChr hK S a b) t :=
    interchangeData_of_banked g gi (vanVleckGatedWitness g gi hChr hK S a b) t C hCnn
      hEboundFull hEzeroE hEmeas ht
  -- feed `a1_R6_assembled` with the internally-built bundles; everything else verbatim.
  exact QIQTH.GrandAssemblyRecon.a1_R6_assembled
    g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc endpoint core inter hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hgD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross
    pdpdH hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1nn hbnd
    E₀ E₁ hE₀ hE₁ hEdom hEzeroE hFzero hIlo hIhi hEcomb

end QIQTH.AssemblyLadderR1R2

section AxiomChecks
open QIQTH.AssemblyLadderR1R2
#print axioms a1_R6_assembled_v2
end AxiomChecks
