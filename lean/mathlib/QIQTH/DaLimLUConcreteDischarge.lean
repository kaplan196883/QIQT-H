/-
  DaLimLUConcreteDischarge — J4-266: the `hDaLimLU` wall AT THE CONCRETE GATE — two of its
  `hDaLimLU_from_data` members (the W2 interchange member and the residual nonpositive-time vanishing)
  DISCHARGED for the concrete `N = 1` van-Vleck gated witness, the rest carried as honest DATA.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / concrete-gate-threading brick.  No `sorry` (header prose excepted), no new axioms, no
  `:= True`, no vacuous / unsatisfiable hypotheses, no hypothesis equal to (or trivially yielding) the
  conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT `hDaLimLU` IS AND WHAT IS DISCHARGED HERE.

  `hDaLimLU` is the locally-uniform `Da`-limit
      `TendstoLocallyUniformlyOn (fun m u => DaTrunc H F m u)
         (fun u => Δ_g (H*F)(u) + (E*F)(u)) atTop U`
  (the abbrev `DaLimLUWallRecon.DaLimLUGoal`), the sole hard residue of the `hDConv`/`hDuhamel` chain
  of the `a₁ = R/6` Duhamel-principle reduction.  J4-221 (`ETailRateBound.hDaLimLU_from_data`) reduced
  it ENTIRELY to DATA — the gauge, the second-`x`-partial kernel `pdpdH`, the interchange member
  `hInterchange` (= `MemInterchange`), the untruncated interchange `hLapFull` (= `MemLapFull`), the
  adjacency + strip interval-integrabilities, the `√ε` sliver amplitudes, the two Gaussian dominations,
  and the `E`-combination `hEcomb`.  NOTE `hDaLimLU_from_data` does NOT reference `hAnear` — the W1
  structural boundary wall (chart-image-vs-`z` Gaussian) lives only in the SEPARATE boundary pile feeding
  `hBoundaryLim`, NOT in the `Da`-limit; so discharging `hDaLimLU` at the concrete gate is FREE of W1.

  Here, at the concrete witness `H_G := vanVleckGatedWitness g gi hChr hK S a b` (with the concrete
  second-`x`-partial kernel `pdpdH := witnessSecondXDeriv g gi hChr hK S a b`), we discharge TWO of the
  `hDaLimLU_from_data` members INTERNALLY and carry the rest:

    • `hInterchange` (the W2 second-order differentiation-under-∫∫ member) — SUPPLIED by
      `SecondOrderInterchangeConcrete.witness_MemInterchange` (J4-256), the concrete W2 engine firing;
      this simultaneously FIXES `pdpdH := witnessSecondXDeriv` (the concrete second-`x`-partial kernel),
      trading the opaque member for its genuine differentiation-under-∫ sub-facts
      (`hQ1`/`hFmeas`/`hFint`/`hF'meas`/`bound`/`hbdd`/`hbound`/`hdiff`).
    • `hEzero` (the residual heat operator vanishing at nonpositive time) — SUPPLIED FROM GEOMETRY by
      `DataPileWitnessAudit.hEzeroE_concrete` (needs `1 ≤ n`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## HONEST DATA-GAP MAP for the REMAINING `hDaLimLU_from_data` members at the concrete gate.
  (verdict — provider / gap; NONE is the conclusion, all satisfiable analytic DATA about `H_G`):

    • gauge `hgi`/`hΓ`        — DATA (RNC normalization at the centre; geometric input).
    • `hInterchange`          — DISCHARGED HERE (concrete W2 engine, `witness_MemInterchange`).
    • `hEzero`                — DISCHARGED HERE (from geometry, `hEzeroE_concrete`).
    • `hLapFull` (`MemLapFull`)  — DATA.  Provider `InterchangeThreading.hLapFull_of_lims` is per-`u`,
                                 abstract in `H F`, and relocates content to its C²-limit carry `hLHSlim`
                                 (an F2 derivative-of-limit fact); no concrete-witness builder.
    • `hII_lo`/`hII_hi` (`MemAdj*`)  — DATA (interval-integrability of `pdpdH·F`; Gaussian-domination,
                                 routine but no concrete-witness builder banked).
    • `D0`/`D1`/`hbnd` (sliver)   — DATA, DISCHARGEABLE via `AmplitudePackage.amplitudePackage_sliver_-`
                                 `bound` once the `AmplitudeDerivativeData` bundle (`hD2Hexpand`, the
                                 Leibniz–Gaussian second-derivative identity at `pdpdH := witnessSecond-`
                                 `XDeriv`) is supplied — NOT built.
    • `hEdom` (residual width-3/2)  — DATA (the affine `|heatOp H_G|` bound; only consumed elsewhere).
    • `hFdom`/`hFzero` (source `F`)  — DATA (the Levi/source envelope + vanishing; `hFdom` = the landed
                                 `leviSeries_gatedWitnessN1_dominated` shape when `F := leviSeries …`).
    • `hIlo`/`hIhi` (strip)   — DATA (strip interval-integrability of the `E·F` inner pairing).
    • `hEcomb` (`MemECombine`)   — DATA/BANKED (`TruncatedDuhamel.hE_combination`, per `m u`).

  ## WHY THE PROVIDER-∃ EXPORT OF `hDuhamel`/`hDConv` IS NOT ATTEMPTED HERE.
  Exporting `hDuhamel` (resp. `hDConv`) through the residual provider `∃` (targets
  `hEboundW_wide_from_geometry_open_duh` / `wide_a1_R6_interface_discharged_v3`) requires the FULL
  `TruncatedDuhamelCore` (resp. the `hDConv` `DifferentiableAt`) at the provider-CHOSEN gate `S`.  Via
  `DerivConvDischarge.core_of_v2prime_data_FULL` (resp. `HDConvThreading.hDConv_from_banked`) that in
  turn requires the BOUNDARY pile — including `hAnear`, the W1 structural wall (`H_G` is Gaussian at the
  CHART IMAGE `W z 0`, not at `z`; the stated near-diagonal factorization holds only for a radially
  isometric chart, `DataPileWitnessAudit` W1) — whose satisfiability at a general provider-chosen gate is
  NOT established.  Carrying `hAnear` at the concrete gate would risk an unsatisfiable hypothesis, which
  the firewall forbids.  So the honest concrete-gate deliverable is the `hDaLimLU`-only reduction above;
  the `hDuhamel`/`hDConv` provider export stays blocked on W1 (boundary limit), NOT on `hDaLimLU`.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ETailRateBound
import QIQTH.SecondOrderInterchangeConcrete
import QIQTH.DataPileWitnessAudit

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound
open QIQTH.DaLimLUWallRecon QIQTH.ETailRateBound
open QIQTH.SecondOrderInterchangeConcrete QIQTH.DataPileWitnessAudit
open scoped Interval Topology BigOperators

namespace QIQTH.DaLimLUConcreteDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ★★★ `hDaLimLU_concrete` — the concrete-gate `Da`-limit with the W2 interchange
    ### member and the residual nonpositive-time vanishing discharged internally.
    ############################################################################### -/

/-- **★★★ J4-266 — `hDaLimLU_concrete`.**  The COMPLETE `hDaLimLU` conclusion (`DaLimLUGoal`, the
    loc-unif `Da`-limit consumed by the `hDConv`/`hDuhamel` chain) at the concrete `N = 1` van-Vleck
    gated witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, with the concrete second-`x`-partial
    kernel `pdpdH := witnessSecondXDeriv g gi hChr hK S a b`.

    TWO members of `ETailRateBound.hDaLimLU_from_data` are discharged INTERNALLY at the concrete gate:
      • `hInterchange` (the W2 second-order differentiation-under-∫∫ member) — from the concrete W2
        engine `SecondOrderInterchangeConcrete.witness_MemInterchange`, threaded here over the carried
        differentiation-under-∫ family (`hQ1`/`hFmeas`/`hFint`/`hF'meas`/`bound`/`hbdd`/`hbound`/`hdiff`)
        on the field-neighbourhood `V ∋ 0` and the derivative window `snb ∈ 𝓝 0`;
      • `hEzero` (residual heat operator vanishing at `τ ≤ 0`) — from `hEzeroE_concrete` (needs `1 ≤ n`).

    The remaining hypotheses are EXACTLY the residual DATA census (see the file header gap map): the RNC
    gauge, the untruncated interchange `hLapFull`, the adjacency + strip integrabilities, the `√ε` sliver
    amplitudes, the residual width-3/2 domination `hEdom`, the source domination/vanishing `hFdom`/
    `hFzero`, and the `E`-combination `hEcomb` — each a genuine satisfiable analytic fact about `H_G` /
    the source `F`, NONE the conclusion, none vacuous.  NOTE `hAnear` (W1) does NOT appear — the `Da`-limit
    is free of the boundary structural wall.  Pure composition otherwise.  NOT `a₁ = R/6`. -/
theorem hDaLimLU_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ) (hUopen : IsOpen U)
    (hn : 1 ≤ n)
    -- gauge (RNC normalization at the centre):
    (hgi : MemGaugeGi (n := n) gi) (hΓ : MemGaugeGamma (n := n) g gi)
    -- the W2 interchange member's differentiation-under-∫ family (produces `hInterchange`):
    (V : Set (Point n)) (hVopen : IsOpen V) (hV0 : (0 : Point n) ∈ V)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (0 : ℝ))
    (hQ1 : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ y ∈ V,
        pd (fun x => heatConvFrozen (vanVleckGatedWitness g gi hChr hK S a b) F u
            (u - epsSeq m) x 0) i y
          = ∫ s in (0)..(u - epsSeq m),
              ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) y z * F s z 0)
    (hFmeas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ w : ℝ, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
            (Function.update (0 : Point n) i w) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (hFint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, IntervalIntegrable
        (fun s => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        volume 0 (u - epsSeq m))
    (hF'meas : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s) (0 : Point n) z * F s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    (bnd : ℕ → Fin n → ℝ → ℝ)
    (hbdd : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        IntervalIntegrable (bnd m i) volume 0 (u - epsSeq m))
    (hbound : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          ‖∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0‖ ≤ bnd m i s)
    (hdiff : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ᵐ s ∂volume,
        s ∈ Set.uIoc 0 (u - epsSeq m) → ∀ w ∈ snb,
          HasDerivAt (fun w => ∫ z, witnessFieldDeriv g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0)
            (∫ z, witnessFieldDeriv2 g gi hChr hK S a b i (u - s)
              (Function.update (0 : Point n) i w) z * F s z 0) w)
    -- residual DATA members carried (see header gap map):
    (hLapFull : MemLapFull g gi (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_lo : MemAdjLo F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (hII_hi : MemAdjHi F U (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z))
    (D0 D1 : Fin n → ℝ) (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i)
    (hbnd : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hChr hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    (E₀ E₁ C_L aT : ℝ) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hC_L : 0 ≤ C_L) (haT : 0 < aT)
    (hUlb : ∀ u ∈ U, aT ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hEdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hFzero : ∀ s, s ≤ 0 → ∀ z y : Point n, F s z y = 0)
    (hIlo : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume 0 (u - epsSeq m))
    (hIhi : ∀ (m : ℕ), ∀ u ∈ U,
        IntervalIntegrable (fun s => ∫ (z : Point n),
            heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) (u - s) 0 z * F s z 0)
          volume (u - epsSeq m) u)
    (hEcomb : MemECombine g gi (vanVleckGatedWitness g gi hChr hK S a b) F) :
    DaLimLUGoal g gi (vanVleckGatedWitness g gi hChr hK S a b) F U := by
  -- ★ the W2 interchange member, DISCHARGED at the concrete gate (`pdpdH := witnessSecondXDeriv`).
  have hInterchange :
      MemInterchange (vanVleckGatedWitness g gi hChr hK S a b) F U
        (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z) :=
    witness_MemInterchange g gi hChr hK S a b F (0 : ℝ) U V hVopen hV0 snb hsnb
      hQ1 hFmeas hFint hF'meas bnd hbdd hbound hdiff
  -- ★ the residual nonpositive-time vanishing, DISCHARGED from geometry (`1 ≤ n`).
  have hEzero : ∀ τ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0 :=
    hEzeroE_concrete g gi hChr hK S a b hn
  -- thread into the DATA-reduced `Da`-limit.
  exact hDaLimLU_from_data g gi (vanVleckGatedWitness g gi hChr hK S a b) F T U hUopen
    hgi hΓ (fun i τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
    hInterchange hLapFull hII_lo hII_hi D0 D1 hD0 hD1 hbnd
    E₀ E₁ C_L aT hE₀ hE₁ hC_L haT hUlb hUT hEdom hEzero hFdom hFzero hIlo hIhi hEcomb

end QIQTH.DaLimLUConcreteDischarge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DaLimLUConcreteDischarge.hDaLimLU_concrete
