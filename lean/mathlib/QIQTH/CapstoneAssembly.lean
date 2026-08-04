/-
  CapstoneAssembly — J4-211 (Sol final plan Ph9): THE CAPSTONE ASSEMBLY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  ASSEMBLY brick: it COMPOSES the already-banked tower into a single capstone
  `a1_R6_of_geometry_and_frontier` whose hypothesis surface is STRICTLY SMALLER and SEMANTICALLY
  ORGANIZED relative to `HDConvThreading.a1_R6_of_residue_inf_v6`.  No new analysis, no re-proving of
  any analytic fact — only re-grouping the Levi/Duhamel interface into the `TruncatedDuhamelData`
  bundles and threading the rest verbatim.  Same conclusion as v6.

  ── WHAT v6 EXPOSES (checked against `HDConvThreading.a1_R6_of_residue_inf_v6`).
     v6 has the `hDConv` slot INTERNALIZED (it re-derives `hDConv` via `hDConv_from_banked` from the
     large near-diagonal / sliver / `hDaLimLU` analytic block).  So of the five Levi/Duhamel interface
     slots it exposes only FOUR directly —
         `hEboundW_le`, `hInt`, `hDuhamel`, `hInter`
     — plus the whole `hDConv` analytic residue block (`T … hDaLimLU`).  We therefore do NOT use the
     `BulkLimitData` bundle (its field IS `hDConv`); using it against v6 would DOUBLE-PROVIDE `hDConv`.

  ── THE COMPRESSION (choice made, documented).
     The four exposed Levi/Duhamel slots `{hEboundW_le, hInt, hDuhamel, hInter}` are re-grouped into
     the THREE `TruncatedDuhamelData` bundles (J4-210), instantiated at the concrete residual kernel
     `Wit := vanVleckGatedWitness g gi hChr hK S a b`:
         • `EndpointData      g gi Wit t C`  → `hEboundW_le` (`.hEbound`) + `hInt` (`.hIntegrable`);
         • `TruncatedDuhamelCore g gi Wit t` → `hDuhamel`    (`.hIdentity`);
         • `InterchangeData   g gi Wit t`    → `hInter`      (`.hSeries`).
     Each bundle field is DEFEQ to the corresponding v6 slot (structure projection at the concrete
     `Wit`), so the assembly is a pure projection.  NET: four flat slots collapse to three semantic
     bundle arguments — strictly fewer top-level hypotheses, and organized by meaning.

     ⋆ REJECTED — local-data threading of `hInt`/`hInter`.  `LeviSeriesLocalData.hInt_from_seriesData`
       and `InterchangeLocalRebase.hInter_from_local_data` COULD supply `hInt`/`hInter`, but each
       demands its own analytic residue (`hEbnd`/`hEzero`/`hEmeas`/`hglobal`, the `∀τ>0` global bound
       form) which is LARGER than the single bundle field it replaces AND is not delivered by the
       geometry provider (which only gives the `τ ≤ t` form).  Taking the bundles directly is strictly
       smaller, so we do NOT thread the local-data providers.  (No vacuity — this is a size choice.)

     ⋆ REJECTED — `hD1_from_data` threading of `hD1`.  `XUniformSliverFull.hD1_from_data` COULD supply
       `hD1`, but it takes twelve arguments (open set, nbhd, two kernel families, two limit fields, a
       vanishing bound, and four sliver/continuity carries) and proves `ContDiffAt` for a SCALAR field,
       not the CLM-valued `Dmap`.  Replacing the single slot `hD1 : ContDiffAt ℝ 1 Dmap 0` by that
       family would ENLARGE the surface and would not even type-match the CLM lift.  So `hD1` is kept
       as one clean slot.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★★  THE DEFINITIVE POST-ASSEMBLY ENUMERATION — the master residue list of
       `a1_R6_of_geometry_and_frontier`.  Tags:
         GEOMETRY = the RNC/Ricci normal-coordinate inputs the theorem is ABOUT (load-bearing, never
                    to be discharged);
         BANKED   = a banked provider EXISTS for this slot (named);
         DATA     = a satisfiable analytic fact (no single-shot provider re-plumbed here);
         WALL     = genuine hard heat-kernel content.

    (i) GEOMETRY / RNC-Ricci block (flat, small):
        g, gi, Ric, t, ht, C, hCnn, hChr, K, hK, S, a, b, ha, hab, hK0, hS0 ........... GEOMETRY
        hg, hg0, hgi, hΓ, hdg0 ........................................................ GEOMETRY (RNC gauge)
        htr .......................................................................... GEOMETRY (Ricci source, `Σ∂∂g = -(2/3)Ric`)
        hsrc ......................................................................... GEOMETRY (transport-coeff smoothness)

    (ii) CConv `C²`-facade bundles (banked provider `CConvFacade.hCConv_discharged_from_data`):
        uu, hu_open, hu0, Bs, Ba, Bd, Cf, Dmap ....................................... DATA (facade scaffolding)
        metric  : CConvMetricData ..................................................... DATA (metric smoothness/positivity)
        chart   : CConvChartGateData .................................................. DATA (chart/gate measurability family)
        source  : CConvSourceData ..................................................... DATA (source-term measurability/bound)
        derivData : CConvDerivativeData ............................................... DATA (derivative-representative bundle)
        env     : CConvEnvelopeData ................................................... DATA (envelope/regularity family)
        hCH .......................................................................... DATA (`ContDiffAt 2` of the witness at `t`)

    (iii) Levi/Duhamel interface — the THREE `TruncatedDuhamelData` bundles:
        endpoint : EndpointData g gi Wit t C .......................................... BANKED
                     (`.hEbound` ← `EboundWiringHD1.hEboundW_from_geometry`;
                      `.hIntegrable` ← `TruncatedDuhamelData.endpointData_of_banked`)
        core     : TruncatedDuhamelCore g gi Wit t .................................... BANKED
                     (`TruncatedDuhamelData.truncatedDuhamelCore_of_daLim`; residue = 3 truncation
                      limits, the last resting on the `hDaLimLU` WALL)
        inter    : InterchangeData g gi Wit t ......................................... BANKED
                     (`TruncatedDuhamelData.interchangeData_of_banked` — all DATA, no wall)

    (iv) the spatial `C¹` slot:
        hD1 : ContDiffAt ℝ 1 Dmap 0 .................................................. BANKED
                     (`XUniformSliverFull.hD1_from_data`; kept as ONE slot — see REJECTED note)

    (v) the `hDConv` analytic residue block (v6 residue, carried verbatim):
        T, hT, U, hUopen, htU, hUpos, hUT ............................................ DATA (window / nbhd)
        r₀, τ₀, hr₀, hτ₀, u₀, u₁, hAnear, hu₀cont, hu₀one, C₀, C₁, hu₀bdd, hu₁bdd .... DATA (near-diagonal parametrix)
        A₀, A₁, C_L, hA₀, hA₁, hC_L, hAdom, hAzero, hBdom ............................ DATA (Gaussian dominations)
        hBcont, hAmeas, hBmeas, hu₀meas, hu₁meas ..................................... DATA (continuity / measurability)
        hMeasFII ..................................................................... DATA (base `s`-measurability)
        hUfloor, hInnerCont .......................................................... DATA (floor + inner-continuity)
        nb, hnb, hFmeas, hFint, hF'meas, boundD, hbdd, hbound, hpardiff .............. DATA (C3ε under-∫ engine)
        L, hLnn, hCross .............................................................. DATA (cross-Lipschitz mixed-2nd-diff)
        DaLim ........................................................................ DATA (the limit field)
        hDaLimLU ..................................................................... WALL  ⟵ THE SOLE HARD CONTENT
                     (the locally-uniform truncated-`Da` limit → `Δ_g(H*F) + E*F`; L3/L4 sliver/
                      interchange family; the one irreducible heat-kernel input)

  VERDICT.  Exactly ONE WALL survives at capstone level: `hDaLimLU`.  Everything else is GEOMETRY
  (the RNC/Ricci gauge the theorem is about), a BANKED bundle (provider named), or satisfiable analytic
  DATA at the concrete gated van-Vleck witness.  None is vacuous, none is the conclusion.

  ── STRETCH (`a1_R6_of_geometry_and_walls`) — NOT SHIPPED, documented.  Discharging every BANKED
     bundle via its provider does NOT shrink the surface: `interchangeData_of_banked` /
     `endpointData_of_banked` each re-expose `{hEbound(∀τ>0), hEzero, hEmeas, …}` (the GLOBAL-`τ` bound
     form, NOT the geometry-provided `τ ≤ t` form), and `truncatedDuhamelCore_of_daLim` re-exposes the
     three truncation limits.  These inputs are LARGER than the bundle fields they replace and are not
     available from geometry without new analysis.  So the "walls-only" wrapper would ENLARGE, not
     shrink, the surface, and is rejected here per the mission's "do not force" clause.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HDConvThreading
import QIQTH.TruncatedDuhamelData
import QIQTH.CConvFacade

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
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CapstoneAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE CAPSTONE — `a1_R6_of_geometry_and_frontier`.
    ############################################################################### -/

/-- **★★★ J4-211 — `a1_R6_of_geometry_and_frontier`.**  The capstone assembly: EXACTLY the conclusion
    of `HDConvThreading.a1_R6_of_residue_inf_v6` (the `heatOp = 0` ∧ `trueHeatKernel`-diagonal
    expansion conjunction), with the four exposed Levi/Duhamel interface slots
    `{hEboundW_le, hInt, hDuhamel, hInter}` RE-GROUPED into the three `TruncatedDuhamelData` bundles
    `endpoint`/`core`/`inter` (instantiated at `Wit := vanVleckGatedWitness g gi hChr hK S a b`).  All
    other v6 carries — the RNC/Ricci geometry, the `CConv` `C²` facade bundles, the `hD1` spatial `C¹`
    slot, and the whole `hDConv` analytic residue block (`T … hDaLimLU`) — are threaded VERBATIM.
    Proved by pure composition: each bundle field is defeq to its v6 slot, so the four exposed slots are
    supplied by `endpoint.hEbound` / `endpoint.hIntegrable` / `core.hIdentity` / `inter.hSeries`.
    ⚠ STILL NOT `a₁ = R/6`; the sole surviving WALL is `hDaLimLU` (see the file-header enumeration). -/
theorem a1_R6_of_geometry_and_frontier (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
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
    -- (iii) Levi/Duhamel interface as the three `TruncatedDuhamelData` bundles:
    (endpoint : EndpointData g gi (vanVleckGatedWitness g gi hChr hK S a b) t C)
    (core : TruncatedDuhamelCore g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
    (inter : InterchangeData g gi (vanVleckGatedWitness g gi hChr hK S a b) t)
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
    -- (iv) the spatial `C¹` slot:
    (hD1 : ContDiffAt ℝ 1 Dmap (0 : Point n))
    -- (v) the `hDConv` analytic residue block (v6 residue, verbatim):
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
    (DaLim : ℝ → ℝ)
    (hDaLimLU : TendstoLocallyUniformlyOn
        (fun m u => DaTrunc (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) m u)
        DaLim atTop U) :
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
  -- Pure composition: the four exposed Levi/Duhamel slots come from the three bundles' fields
  -- (defeq at the concrete `Wit`); everything else threads verbatim into v6.
  refine a1_R6_of_residue_inf_v6 g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc ?_ ?_ ?_ ?_ hCH
    uu hu_open hu0 Bs Ba Bd Cf Dmap metric chart source derivData env hD1
    T hT U hUopen htU hUpos hUT r₀ τ₀ hr₀ hτ₀ u₀ u₁ hAnear hu₀cont hu₀one C₀ C₁ hu₀bdd hu₁bdd
    A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hAzero hBdom hBcont hAmeas hBmeas hu₀meas hu₁meas
    hMeasFII hUfloor hInnerCont nb hnb hFmeas hFint hF'meas boundD hbdd hbound hpardiff
    L hLnn hCross DaLim hDaLimLU
  · exact endpoint.hEbound
  · exact endpoint.hIntegrable
  · exact core.hIdentity
  · exact inter.hSeries

end QIQTH.CapstoneAssembly

section AxiomChecks
open QIQTH.CapstoneAssembly
#print axioms a1_R6_of_geometry_and_frontier
end AxiomChecks
