/-
  ECombinationDischarge — J4-386: THE E-COMBINATION CENSUS PILE (ix), z-INTEGRABILITY LEG.
  Discharging (as GENUINE reductions to the banked Gaussian dominations) the two z-integrability
  carries `hEZ` / `hLapZ` of the E-combination census pile exposed by
  `GlobalRawBoundFacade` / `CensusGeometryThread` (the (ix) block), plus the honest structural
  inventory of the remaining four carries (`hDa`, `hLap`, `hES`, `hLapS`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file discharges only the two CHEAP z-integrability legs of
  the (ix) E-combination pile — and even those only as REDUCTIONS to the banked Gaussian dominations
  (the heat-kernel domination `hAdomHeat`, the Levi envelope `hFdomW`, a laplaceBeltrami-slice
  domination) plus the two slice `AEStronglyMeasurable` facts.  NO `sorry` (header prose excepted), NO
  new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding)
  the conclusion, NO existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## PHASE-1 INVENTORY (the (ix) E-combination pile, at `W := vanVleckGatedWitness …`,
     `F := leviSeries (heatOp g gi W)`).

  •  `hDa`  — **REPRESENTATION theorem, NOT definitional.**  `DaTrunc H F m u` is DEFINED
     (`TruncatedDuhamel.DaTrunc`) as `deriv (fun a => heatConvFrozen H F a (u−ε_m) 0 0) u`; the census
     `hDa` body `= ∫ s in 0..(u−ε_m), ∫ z, ∂_r H(u−s) 0 z · F s z 0` is the OUTPUT of the W2
     differentiation-under-∫ representation `TruncatedDuhamel.hDa_trunc` / the threaded
     `InterchangeThreading.hDa_threaded` (T1a).  It therefore carries the genuine differentiation
     carriers (measurability, base/derivative integrability, a uniform integrable derivative bound, the
     pointwise `HasDerivAt` family) — it is NOT `rfl`.  ⟹ honest CARRY (banked reduction exists).

  •  `hLap` — **REPRESENTATION theorem, NOT definitional.**  `LapTrunc g gi H F m u` is DEFINED
     (`TruncatedDuhamel.LapTrunc`) as `laplaceBeltrami g gi (fun x => heatConvFrozen H F u (u−ε_m) x 0) 0`;
     the census `hLap` body is the OUTPUT of the DEFERRED second-order differentiation-under-∫
     `InterchangeThreading.hLap_threaded` (T1b) — RNC flat reduction (`lapTrunc_eq_sum_pdpd`) + the
     pd∘pd interchange + `laplaceBeltrami_at_rnc_center`.  NOT `rfl`.  ⟹ honest CARRY (banked reduction).

  •  `hEZ`  — **DISCHARGED here** (as a reduction).  See `hEZ_windowed`.
  •  `hLapZ` — **DISCHARGED here** (as a reduction).  See `hLapZ_from_dom`.

  •  `hES`  — the strip interval-integrability of `s ↦ ∫ z, heatOp(u−s) 0 z · F s z 0` on `0..(u−ε_m)`.
     SUPPLIER: `GlobalRawBoundFacade.integrability_from_dominations` produces exactly this shape (its
     `hIlo` leg, via the Gaussian-pairing engine `DaLimEasyTranche.hI*_concrete /
     pairing_intervalIntegrable`) — but for `u ∈ U` (windowed), whereas the census `hES` binder is
     stated `∀ u`.  ⟹ honest CARRY (banked windowed supplier; the `∀u`↔`∀u∈U` gap is a quantifier
     widening, out of scope for this z-leg brick).

  •  `hLapS` — same as `hES` with `laplaceBeltrami`-slice in place of `heatOp`; SUPPLIER is the
     `MemAdjLo`/`witnessSecondXDeriv` leg of `integrability_from_dominations` after the
     `laplaceBeltrami ↔ ∑ witnessSecondXDeriv` RNC identification (`laplaceBeltrami_at_rnc_center`).
     ⟹ honest CARRY.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE WORKHORSE.

  `integrable_of_two_gaussDom` — a PRODUCT of two `gaussDdim`-dominated (a.e.-measurable) real
  functions on `Point n` is `volume`-integrable, via `Integrable.mono'` against the (UNCONDITIONALLY
  integrable, `CConvV2GaussianPairing.gaussDdim_pair_integrable`) two-Gaussian product `CA·CF·G_A·G_B`.
  Both z-legs of the (ix) pile are one instantiation of this.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ConvApproximants
import QIQTH.LaplaceBeltrami
import QIQTH.ResidueBound
import QIQTH.TrueHeatKernel
import QIQTH.TruncatedDuhamel
import QIQTH.CConvV2GaussianPairing

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel
open QIQTH.ResidueBound QIQTH.HeatResidualBound QIQTH.CConvV2GaussianPairing
open scoped Topology

namespace QIQTH.ECombinationDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — THE WORKHORSE: product of two Gaussian-dominated functions is integrable.
    ############################################################################### -/

/-- **★ `integrable_of_two_gaussDom`.**  If `φ` is dominated by `CA·gaussDdim A (0−z)`, `ψ` by
    `CF·gaussDdim B z`, both a.e.-strongly-measurable and `0 ≤ CA`, `0 ≤ CF`, then the pointwise
    product `z ↦ φ z · ψ z` is `volume`-integrable on `Point n`.

    Route: `Integrable.mono'` against the dominator `z ↦ CA·CF·(gaussDdim A z · gaussDdim B z)`, itself
    integrable by `CConvV2GaussianPairing.gaussDdim_pair_integrable` (the two-Gaussian product is
    UNCONDITIONALLY integrable) scaled by the constant `CA·CF`.  The pointwise bound uses
    `‖φz·ψz‖ = |φz|·|ψz| ≤ (CA·gaussDdim A (0−z))·(CF·gaussDdim B z)` (`mul_le_mul` with the nonneg
    domination sides) then origin-evenness `gaussDdim_zero_sub` (`gaussDdim A (0−z) = gaussDdim A z`).
    Genuine hypotheses (the two dominations + measurabilities + constant signs); none is the
    conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem integrable_of_two_gaussDom (φ ψ : Point n → ℝ) (A B CA CF : ℝ)
    (hCA : 0 ≤ CA) (hCF : 0 ≤ CF)
    (hφmeas : AEStronglyMeasurable φ volume)
    (hψmeas : AEStronglyMeasurable ψ volume)
    (hφ : ∀ z, |φ z| ≤ CA * gaussDdim A (0 - z))
    (hψ : ∀ z, |ψ z| ≤ CF * gaussDdim B z) :
    Integrable (fun z => φ z * ψ z) volume := by
  have hg : Integrable (fun z : Point n => CA * CF * (gaussDdim A z * gaussDdim B z)) volume :=
    (gaussDdim_pair_integrable A B).const_mul (CA * CF)
  refine hg.mono' (hφmeas.mul hψmeas) (Filter.Eventually.of_forall (fun z => ?_))
  have hgA : 0 ≤ gaussDdim A (0 - z) := gaussDdim_nonneg _ _
  have hbound : |φ z| * |ψ z| ≤ (CA * gaussDdim A (0 - z)) * (CF * gaussDdim B z) :=
    mul_le_mul (hφ z) (hψ z) (abs_nonneg _) (mul_nonneg hCA hgA)
  calc ‖φ z * ψ z‖ = |φ z| * |ψ z| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ (CA * gaussDdim A (0 - z)) * (CF * gaussDdim B z) := hbound
    _ = CA * CF * (gaussDdim A z * gaussDdim B z) := by
        rw [gaussDdim_zero_sub]; ring

/-! ###############################################################################
    ### §2 — `hEZ`: the heat-operator × Levi z-integrability leg (reduced to `hAdomHeat`+`hFdomW`).
    ############################################################################### -/

/-- **★ `hEZ_windowed`.**  The census (ix) `hEZ` body AT a window pair `(u, s)` with
    `0 < s ≤ T` and `0 < u − s ≤ T`, reduced to the two banked Gaussian dominations:
    the heat-kernel domination `hAdomHeat` (width `wA`, `= hAdomHeat_from_hEdom`) and the Levi
    envelope `hFdomW` (width `wF`, `= source_from_leviData.hFdom`), plus the two slice
    `AEStronglyMeasurable` facts.  A single instantiation of `integrable_of_two_gaussDom` at
    `A := wA·(u−s)`, `B := wF·s`.  Genuine reduction; none is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem hEZ_windowed (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T wA CA wF CF u s : ℝ)
    (hCA : 0 ≤ CA) (hCF : 0 ≤ CF)
    (hs1 : 0 < s) (hs2 : s ≤ T) (hus1 : 0 < u - s) (hus2 : u - s ≤ T)
    (hAdomHeat : ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
          ≤ CA * gaussDdim (wA * τ) (0 - z))
    (hFdomW : ∀ s' : ℝ, 0 < s' → s' ≤ T → ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s' z 0|
          ≤ CF * gaussDdim (wF * s') z)
    (hHeatMeas : AEStronglyMeasurable
        (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z) volume)
    (hFmeas : AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) :
    Integrable
      (fun z => heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume :=
  integrable_of_two_gaussDom _ _ (wA * (u - s)) (wF * s) CA CF hCA hCF hHeatMeas hFmeas
    (hAdomHeat (u - s) hus1 hus2) (hFdomW s hs1 hs2)

/-! ###############################################################################
    ### §3 — `hLapZ`: the laplaceBeltrami-slice × Levi z-integrability leg.
    ############################################################################### -/

/-- **★ `hLapZ_from_dom`.**  The census (ix) `hLapZ` body AT `(u, s)`, reduced to a
    laplaceBeltrami-slice Gaussian domination `hLapDom` (width `A2`) and the Levi envelope `hFdom`
    (width `B`), plus the two slice `AEStronglyMeasurable` facts.  A single instantiation of
    `integrable_of_two_gaussDom` with `φ := laplaceBeltrami g gi (fun x => W (u−s) x z) 0`,
    `ψ := F s z 0`.  Genuine reduction.

    ▸  HONEST BRIDGE NOTE.  `hLapDom` is the laplaceBeltrami-slice analogue of the census (v)
       second-`x`-derivative domination `hAdom2` (on `witnessSecondXDeriv`); at the RNC centre
       `laplaceBeltrami g gi (fun x => W (u−s) x z) 0 = ∑ᵢ ∂ᵢ∂ᵢ (W (u−s) · z) 0`
       (`laplaceBeltrami_at_rnc_center`), so a clean `A2·gaussDdim` slice bound follows from a
       clean `hAdom2` — but `hAdom2` itself is an OPEN carry of the census (the banked
       second-derivative bound has the crude `τ⁻¹` shape, see `CensusDominations` (D3)).  `hLapDom`
       is therefore taken here as a satisfiable-shaped hypothesis, not manufactured.  ⚠ NOT `a₁ = R/6`. -/
theorem hLapZ_from_dom (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (A2 C2 B CF u s : ℝ)
    (hC2 : 0 ≤ C2) (hCF : 0 ≤ CF)
    (hLapDom : ∀ z : Point n,
        |laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0|
          ≤ C2 * gaussDdim A2 (0 - z))
    (hFdom : ∀ z : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ CF * gaussDdim B z)
    (hLapMeas : AEStronglyMeasurable
        (fun z => laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0) volume)
    (hFmeas : AEStronglyMeasurable
        (fun z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume) :
    Integrable
      (fun z => laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b (u - s) x z) 0
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) volume :=
  integrable_of_two_gaussDom _ _ A2 B C2 CF hC2 hCF hLapMeas hFmeas hLapDom hFdom

end QIQTH.ECombinationDischarge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.ECombinationDischarge.integrable_of_two_gaussDom
#print axioms QIQTH.ECombinationDischarge.hEZ_windowed
#print axioms QIQTH.ECombinationDischarge.hLapZ_from_dom
