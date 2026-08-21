/-
  CensusIntegratedModuloG2 — the FULL INTEGRATION of the modulo-G2 `hballrate` (C1, J4-960) with its
  three SIBLING census premises `hF` / `hΦint` / `hSupp`, closing the reshaped any-`S` far-rate capstone
  `censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho` (J4-954) into the ρ-FREE `hCensusBound`
  MODULO the single G2 gate carry — and threading that all the way through the live `hCross`
  mixed-second-difference binder via `hcross_of_censusIntegral_bound` (J4-929).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ASSEMBLY brick: it composes ALREADY-banked bricks to remove the `hballrate` / `hF` / `hΦint` argument
  slots from the census capstone, leaving the closure conditional on {G2 gate `hS`; the width-2 Levi
  domination `hFdom` and s-uniform on-ball F-regularity `{hFb, hFl}` = the standard
  `{hDuhamel, hDConv, hCConv}`-family F-data; the small-gate carry `hSupp`; the standard F2
  measurability carriers `{hKSmeas, hcar, hFmeas}`; the benign positive-time window side `ε < u`}.  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypothesis,
  no existing banked file edited.

  ## THE ρ-ALIGNMENT (why the siblings hold at `hballrate_moduloG2`'s internally-chosen `ρ`).  The
  reshaped capstone (J4-954) binds `ρ, MF, Cpair, hF(ρ), hballrate(ρ)` INSIDE the `∀ D` binder, so the
  caller may pick `ρ := δ(D)` per-`D`.  `hballrate_moduloG2` (J4-960) internally chooses
  `ρ := δ = min (image-subdomain radius) (joint-gate radius)` and produces `(ρ, Cpair)` inhabiting the
  `hballrate(ρ)` slot MODULO G2.  The three siblings are all ρ-INDEPENDENT at that ρ:
    • `hF(ρ)` — `hF_of_leviWidth2Dom` (J4-952) proves the STRONGER all-`z` bound `|F s z 0| ≤ MF`
      (the off-ball `ρ ≤ ‖z‖` restriction is UNUSED slack), so `MF` is ρ-independent and the bound holds
      at ANY ρ, in particular `δ`;
    • `hΦint` — `censusPhi_integrable_of_amplitudeCarries` (J4-953) proves integrability over ALL of
      `ℝⁿ` (no `Metric.ball`), entirely ρ-free;
    • `hSupp` — the small-gate containment `∀ z ∈ K, 0 ∈ S z → ‖z‖ < D.r` is about `D.r`, ρ-free (kept as
      a genuine per-`D` carry — it is an UPPER gate containment, NOT implied by G2's lower one).
  So the three siblings align at `δ` with NO quantifier-order obstruction: the FULL `hCensusBound` closes
  modulo G2 + standard carriers.

  ## WHAT LANDS.
    • `censusBound_integrated_moduloG2` — ★★★ the ρ-FREE `hCensusBound` (∫ over all `ℝⁿ`, `C_far`
        existential) with `hballrate` / `hF` / `hΦint` ALL discharged; conditional on the carriers above.
    • `hcross_integrated_moduloG2` — ★★★ the FULL live `hCross` mixed-second-difference binder
        (`h, k > 0`) with `hballrate` / `hF` / `hΦint` discharged, conditional on the same carriers PLUS
        the J4-929 differentiation carries `{hFmeasG, four interval-integrabilities, hEnv, H_near,
        H_zero}` and the G2 gate `hS`.
    • non-vacuity `censusBound_integrated_moduloG2_carries_satisfiable` (the NEW carry bundle
        `{hS, hFb, hFl, hFdom, hεu, numeric}` jointly satisfiable at a GENUINELY non-`univ` gate with
        `F ≡ 0`) — the measurability/`hSupp` carriers are the standing carriers, unchanged.

  ## HONEST STATUS (blunt).  This CLOSES the `hballrate` / `hF` / `hΦint` argument slots of the census
  capstone MODULO G2 (`hS`) + the standard geometry / F-data / measurability carriers, and CERTIFIES the
  live `hCross` consumer accepts it.  It discharges NONE of `{hballrate, hDuhamel, hDConv, hCConv}` as a
  top-level τ-carry: the F-data carriers `{hFdom, hFb, hFl}` ARE the `{hDuhamel, hDConv, hCConv}`-family
  Levi objects (the amplitude / Gaussian-transport bookkeeping already acknowledged), and G2 (`hS`)
  remains an ungrounded gate carry.  `hDuhamel`/`hDConv` remain carried; `hCConv` unaffected.  `a₁ = R/6`
  remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}` (with G2 an additional census-side gate carry),
  UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusExistRhoRethread
import QIQTH.CensusHballrateModuloG2
import QIQTH.CensusFFactorSupDischarge
import QIQTH.CensusPhiIntegrabilityDischarge
import QIQTH.CensusAmplitudeSupDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.HeatResidualBound
open QIQTH.CensusAmpConcreteRegularity QIQTH.CensusTauDerivGateSplit
open QIQTH.CensusAmplitudeSupDischarge QIQTH.CensusAnySEnvelopeRethread
open QIQTH.CensusExistRhoRethread QIQTH.CensusHballrateModuloG2
open QIQTH.CensusFFactorSupDischarge QIQTH.CensusPhiIntegrabilityDischarge
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.CensusIntegratedModuloG2

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### §A — the ρ-FREE `hCensusBound`, `hballrate` / `hF` / `hΦint` discharged, MODULO G2.
    ############################################################################### -/

/-- **★★★ `censusBound_integrated_moduloG2` — the FULL far-rate `hCensusBound`, `hballrate` / `hF` /
    `hΦint` ALL discharged, MODULO the single G2 gate carry.**  For the concrete gated van-Vleck witness,
    given the standing geometry, the width-2 Levi domination `hFdom`, the s-uniform on-ball F-regularity
    `{hFb, hFl}`, the standard F2 measurability carriers `{hKSmeas, hcar, hFmeas}`, the benign
    positive-time window side `ε < u`, and the G2 gate carry `hS`, there is an amplitude radius `rAmp > 0`
    such that for EVERY small-radius gate record `D` (`D.r ≤ rAmp`) with the small-gate containment
    `hSupp`, there is a nonnegative far-rate constant `C_far` with, for EVERY `s ∈ Ioo (u−ε) u` and EVERY
    `a ∈ Icc u (u+h)`,
      `|∫ z, deriv (fun r => vanVleckGatedWitness … r 0 z) (a−s) · F s z 0| ≤ C_far · (u−s)^{−1/2}` .
    The internal `ρ := δ(D)` from `hballrate_moduloG2` aligns with the ρ-independent siblings `hF`, `hΦint`
    (and the ρ-free `hSupp`), closing the capstone's `hballrate` / `hF` / `hΦint` slots.  NOT `a₁ = R/6`. -/
theorem censusBound_integrated_moduloG2 (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ) (u ε h τ₀ : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀) (hεu : ε < u)
    -- G2 gate carry:
    (hS : ∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z})
    -- s-uniform on-ball F-regularity (for `hballrate`, the Levi output):
    (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w)
    -- width-2 Levi domination (for `hF` and `hΦint`):
    (C_L T : ℝ) (hC_L : 0 ≤ C_L) (huT : u ≤ T)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    -- standard F2 measurability carriers (for `hΦint`):
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK cutA cutB w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) volume) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
        ∃ C_far : ℝ, 0 ≤ C_far ∧
          ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
            |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
                * F s z 0|
              ≤ C_far * (u - s) ^ (-(1 : ℝ) / 2) := by
  classical
  -- the reshaped capstone (J4-954).
  obtain ⟨rAmp, hrAmp, hcapstone⟩ :=
    censusBound_of_geometry_gate_supp_F_ballRate_anyS_existRho hn g gi hC hK S cutA cutB
      h0Kmem hg hg0 hu F u ε h τ₀ hε hτ₀ hh hcap
  -- the amplitude sups (for the `hΦint` crude envelope).
  obtain ⟨rAmp', hrAmp', M, M', hM, hM', hampBnd, hcfBnd⟩ :=
    census_amplitude_supBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  refine ⟨min rAmp rAmp', lt_min hrAmp hrAmp', ?_⟩
  intro D hDr hSupp
  have hDr₁ : D.r ≤ rAmp := le_trans hDr (min_le_left _ _)
  have hDr₂ : D.r ≤ rAmp' := le_trans hDr (min_le_right _ _)
  -- ═══ discharge `hballrate` (C1) MODULO G2 — chooses ρ := δ(internal). ═══
  obtain ⟨ρ, Cpair, hρ, hCpair, hballrate⟩ :=
    hballrate_moduloG2 hn g gi hC hK S cutA cutB h0Kmem hg hg0 hu F u ε h τ₀
      hε hτ₀ hh hcap rF M_F L_F hrF hMF hLF hFb hFl hS
  -- ═══ discharge `hF(ρ)` — ρ-independent (off-ball slack unused). ═══
  obtain ⟨MF, hMF0, hF⟩ := hF_of_leviWidth2Dom F C_L T u ε ρ hC_L hFdom hεu huT
  -- ═══ discharge `hΦint` — ρ-free (∫ over all ℝⁿ). ═══
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M := by
    intro τ hτ hτ0 z _ hzr; exact hampBnd τ hτ hτ0 z (lt_of_lt_of_le hzr hDr₂)
  have hCfield : ∀ z ∈ K, ‖z‖ < D.r → |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M' := by
    intro z _ hzr; exact hcfBnd z (lt_of_lt_of_le hzr hDr₂)
  have hΦint := censusPhi_integrable_of_amplitudeCarries hn g gi hC hK S cutA cutB D τ₀ M M'
    hτ₀ hM hM' hAmp0 hCfield hSupp F hKSmeas hcar hFmeas u ε h T C_L hεu huT hh hcap hC_L hFdom
  -- ═══ apply the reshaped capstone at (ρ, MF, Cpair). ═══
  obtain ⟨lam', Cenv, hlam', hCenv, hAll⟩ :=
    hcapstone D hDr₁ ρ MF Cpair hρ hMF0 hCpair hSupp hF hΦint hballrate
  refine ⟨Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε, ?_, hAll⟩
  have h1 : 0 ≤ Cenv * Real.sqrt 2 ^ n * Real.sqrt ε :=
    mul_nonneg (mul_nonneg hCenv (by positivity)) (Real.sqrt_nonneg _)
  linarith

/-! ###############################################################################
    ### §B — the FULL live `hCross` binder, `hballrate` / `hF` / `hΦint` discharged, MODULO G2.
    ############################################################################### -/

/-- **★★★ `hcross_integrated_moduloG2` — the full live `hCross` mixed-second-difference binder, with
    `hballrate` / `hF` / `hΦint` ALL discharged, MODULO G2.**  Composes `censusBound_integrated_moduloG2`
    (§A) with the downstream consumer `hcross_of_censusIntegral_bound` (J4-929).  The caller supplies the
    standing geometry, the F-data carriers `{hFdom, hFb, hFl}`, the F2 measurability carriers
    `{hKSmeas, hcar, hFmeas}`, the positive-time window side `ε < u`, the G2 gate `hS`, and — per gate
    record `D` with `D.r ≤ rAmp` — the small-gate carry `hSupp` together with the J4-929 differentiation
    carries `{hFmeasG, four interval-integrabilities, hEnv, H_near, H_zero}`.  NOT `a₁ = R/6`. -/
theorem hcross_integrated_moduloG2 (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ) (u ε h k τ₀ M : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hh : 0 < h) (hk : 0 < k) (hMm : 0 ≤ M)
    (hcap : ε + h ≤ τ₀) (hεu : ε < u)
    (hS : ∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z})
    (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMF : 0 ≤ M_F) (hLF : 0 ≤ L_F)
    (hFb : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F)
    (hFl : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
      |F s z 0 - F s w 0| ≤ L_F * dist z w)
    (C_L T : ℝ) (hC_L : 0 ≤ C_L) (huT : u ≤ T)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hC hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hC hK cutA cutB w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hFmeas : ∀ s : ℝ, AEStronglyMeasurable (fun z => F s z 0) volume) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
        (∀ s u' : ℝ, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (u' - s) 0 z * F s z 0) volume) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            volume (u - ε) (u - ε + k) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
            volume (u - ε) (u - ε + k) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            volume 0 (u - ε) →
        IntervalIntegrable
          (fun s => ∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)
            volume 0 (u - ε) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          ∃ V ∈ 𝓝 a, ∃ Dz : Point n → ℝ,
            Integrable Dz volume ∧
            Integrable
              (fun z => vanVleckGatedWitness g gi hC hK S cutA cutB (a - s) 0 z * F s z 0) volume ∧
            AEStronglyMeasurable
              (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
                * F s z 0) volume ∧
            (∀ᵐ z ∂volume, ∀ a' ∈ V,
              ‖deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s) * F s z 0‖
                ≤ Dz z) ∧
            (∀ᵐ z ∂volume, ∀ a' ∈ V,
              HasDerivAt
                (fun a' => vanVleckGatedWitness g gi hC hK S cutA cutB (a' - s) 0 z * F s z 0)
                (deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a' - s)
                  * F s z 0) a')) →
        (∀ s ∈ Set.Icc u (u + h),
          |(∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
              - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0)| ≤ 2 * M) →
        (∀ s ∈ Set.Ioi (u + h),
          (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u + h - s) 0 z * F s z 0)
            - (∫ z, vanVleckGatedWitness g gi hC hK S cutA cutB (u - s) 0 z * F s z 0) = 0) →
        ∃ C_far : ℝ, 0 ≤ C_far ∧
          |heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε + k) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F (u + h) (u - ε) 0 0
              - heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε + k) 0 0
              + heatConvFrozen (vanVleckGatedWitness g gi hC hK S cutA cutB) F u (u - ε) 0 0|
            ≤ (2 * C_far / Real.sqrt ε + 2 * M / ε) * (|h| * |k|) := by
  obtain ⟨rAmp, hrAmp, hcensus⟩ :=
    censusBound_integrated_moduloG2 hn g gi hC hK S cutA cutB h0Kmem hg hg0 hu F u ε h τ₀
      hε hτ₀ hh.le hcap hεu hS rF M_F L_F hrF hMF hLF hFb hFl C_L T hC_L huT hFdom
      hKSmeas hcar hFmeas
  refine ⟨rAmp, hrAmp, ?_⟩
  intro D hDr hSupp hFmeasG hah_hi ha_hi hah_lo ha_lo hEnv H_near H_zero
  obtain ⟨C_far, hCf, hCensusBound⟩ := hcensus D hDr hSupp
  refine ⟨C_far, hCf, ?_⟩
  exact hcross_of_censusIntegral_bound g gi hC hK S cutA cutB F u ε h k C_far M
    hε hh hk hCf hMm hFmeasG hah_hi ha_hi hah_lo ha_lo hEnv hCensusBound H_near H_zero

/-! ###############################################################################
    ### §C — NON-VACUITY (TEETH).
    ############################################################################### -/

/-- **Non-vacuity (TEETH) of the NEW carry bundle.**  The carries this integration introduces on top of
    the standing geometry / measurability carriers — the G2 gate `hS`, the s-uniform on-ball F-regularity
    `{hFb, hFl}`, the width-2 Levi domination `hFdom`, the positive-time window side `ε < u`, and the
    numeric window — are JOINTLY satisfiable at a GENUINELY non-`univ` gate (`S z := ball z 1`, so
    `{z | 0 ∈ S z} = ball 0 1 ≠ univ`, witnessed by the constant-`2` point `0 ∉ ball (2·) 1`) with
    `F ≡ 0`, `M_F = L_F = C_L = 0`, window `u = 2, ε = 1, h = 0, τ₀ = 1, T = 2`.  Confirms the integration
    is NOT vacuously conditioned.  NOT `a₁ = R/6`. -/
theorem censusBound_integrated_moduloG2_carries_satisfiable (hn : 0 < n) :
    ∃ (S : Point n → Set (Point n)) (F : ℝ → Point n → Point n → ℝ)
      (u ε h τ₀ rF M_F L_F C_L T : ℝ),
      0 < ε ∧ 0 < τ₀ ∧ 0 ≤ h ∧ ε + h ≤ τ₀ ∧ ε < u ∧ 0 < rF ∧ 0 ≤ M_F ∧ 0 ≤ L_F ∧ 0 ≤ C_L ∧ u ≤ T ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F) ∧
      (∀ s ∈ Set.Ioo (u - ε) u, ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF →
        |F s z 0 - F s w 0| ≤ L_F * dist z w) ∧
      (∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) ∧
      (∃ rS : ℝ, 0 < rS ∧ Metric.ball (0 : Point n) rS ⊆ {z | (0 : Point n) ∈ S z}) ∧
      (∃ z : Point n, (0 : Point n) ∉ S z) := by
  classical
  refine ⟨fun z => Metric.ball z 1, fun _ _ _ => 0, 2, 1, 0, 1, 1, 0, 0, 0, 2,
    one_pos, one_pos, le_refl _, by norm_num, one_lt_two, one_pos, le_refl _, le_refl _, le_refl _,
    by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ z _; simp
  · intro s _ z w _ _; simp
  · intro s _ _ z y; simp
  · -- G2 for `S z := ball z 1`: `ball 0 1 ⊆ {z | 0 ∈ ball z 1}`.
    refine ⟨1, one_pos, fun z hz => ?_⟩
    rw [Set.mem_setOf_eq, Metric.mem_ball, dist_comm]
    exact Metric.mem_ball.mp hz
  · -- TEETH: the constant-`2` point has `0 ∉ ball (2·) 1`.
    refine ⟨fun _ => (2 : ℝ), ?_⟩
    rw [Metric.mem_ball, dist_comm, not_lt]
    have hcoord : ‖(2 : ℝ)‖ ≤ ‖(fun _ => (2 : ℝ) : Point n)‖ :=
      norm_le_pi_norm (fun _ => (2 : ℝ)) ⟨0, hn⟩
    rw [dist_zero_right]
    have h2 : ‖(2 : ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
    rw [h2] at hcoord; linarith

end QIQTH.CensusIntegratedModuloG2

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusIntegratedModuloG2
#print axioms censusBound_integrated_moduloG2
#print axioms hcross_integrated_moduloG2
#print axioms censusBound_integrated_moduloG2_carries_satisfiable
end AxiomChecks
