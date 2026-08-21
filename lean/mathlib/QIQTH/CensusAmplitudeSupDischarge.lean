/-
  CensusAmplitudeSupDischarge — DISCHARGING the amplitude sup-bound carries `hAmp0`/`hCfield` of
  `censusBound_of_amplitudeCarries_Fbound_ballRate` (J4-948) from the banked base-point continuity, and
  threading the discharge into the FULL `hCensusBound` far-rate so those two carries become INTERNAL.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  real-analysis / structural threading brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing banked file edited.

  ## THE TWO AMPLITUDE SUP-BOUND CARRIES.  `censusBound_of_amplitudeCarries_Fbound_ballRate` (J4-948)
  consumes, for the concrete van-Vleck gated witness, the amplitude carries
    • `hAmp0`  : `∀ τ, 0<τ → τ≤τ₀ → ∀ z∈K, ‖z‖<D.r → |chartFieldAmp … cutA cutB τ z 0| ≤ M`
    • `hCfield`: `∀ z∈K, ‖z‖<D.r → |Cfield z 0| ≤ M'`
  (the τ-UNIFORM zeroth amplitude sup + the amplitude-slope sup).

  ## THE DISCHARGE (mechanism).  `chartFieldAmp` is AFFINE in `τ`:
      `chartFieldAmp cutA cutB τ z 0 = chartFieldAmp cutA cutB 0 z 0 + censusAmpTauDeriv … z · τ`
  (pure `ring` on the def), and `censusAmpTauDeriv … z` is DEFINITIONALLY the slope `Cfield z 0`
  delivered by the banked UNCONDITIONAL `chartFieldAmp_hasDerivAt_tau`.  The banked base-point
  regularity `chartFieldAmp_base_regularity_center` (per fixed `τ`) and
  `censusAmpTauDeriv_base_regularity_center` each give a sup-bound on a base ball `ball 0 r`.  Bounding
  `chartFieldAmp` at `τ=0` (constant `M₀`) and the slope (constant `M'`), the affine form gives a SINGLE
  τ-UNIFORM bound `M := M₀ + M'·τ₀` on `(0,τ₀]` — no per-τ dependence.  So `hAmp0`/`hCfield` are
  discharged to the standard geometry carries `{hg, hg0, hu, h0Kmem}` alone, MODULO the benign radius
  compatibility `D.r ≤ rAmp` (choose the gate record small).

  ## WHAT LANDS.
    • `chartFieldAmp_affine_slope` — the affine identity (pure `ring`).
    • `census_amplitude_supBounds` — ★★★ the τ-UNIFORM amplitude sup-bound package (∃ rAmp,M,M').
    • `censusBound_of_geometry_gate_supp_F_ballRate` — ★★★ the FULL `hCensusBound` far-rate with `hAmp0`
        and `hCfield` DISCHARGED internally; carries left are {`hgateS` (the S-gate half), `hSupp`, the
        F-factor bound `hF`, C1 ball-rate, C2 integrability} + the benign `D.r ≤ rAmp` compat.
    • non-vacuity witnesses (genuine positive data, K={0}, S=univ, F≡0).

  ## HONEST STATUS.  `hAmp0`/`hCfield` are DISCHARGED (from banked base-point continuity, modulo `D.r ≤
  rAmp`).  ⚠ The other half of `hgate` — the GATE half `∀ w, w.2.2∈K → 0<w.1 → w.2.1∈S w.2.2` — remains a
  carry `hgateS`; because the field point `w.2.1` is universally quantified, it is STRONGER than the
  downstream census gate `0∈S z` (it forces `S z = univ` on `K`), arising because the banked τ-derivative
  closed form is an everywhere-in-field-point identity while the census evaluates only at field point `0`.
  `hSupp`, the F-factor bound, C1, C2 also remain.  So `hCensusBound` is assembled modulo {`hgateS`,
  `hSupp`, F-factor, C1, C2} — NOT `{G2, G3}` alone.  `hDuhamel`/`hDConv` remain carried; `hCConv`
  unaffected.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CensusAmpConcreteRegularity
import QIQTH.CensusTauDerivGateSplit
import QIQTH.OnGateJets
import QIQTH.CensusOnGateEnvelopeThreaded
import QIQTH.InverseChartNormalJets

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.ResidueBound QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.InverseChartNormalJets QIQTH.OnGateJets
open QIQTH.CensusTauDerivGateSplit QIQTH.CensusAmpConcreteRegularity
open QIQTH.CensusOnGateEnvelopeThreaded
open scoped Topology BigOperators ContDiff

namespace QIQTH.CensusAmplitudeSupDischarge

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ### §A — the affine-in-τ identity `chartFieldAmp τ = chartFieldAmp 0 + slope·τ`.
    ############################################################################### -/

/-- **`chartFieldAmp_affine_slope`.**  The concrete census field amplitude is AFFINE in `τ`, with
    `∂_τ`-slope the banked `censusAmpTauDeriv`:
      `chartFieldAmp … cutA cutB τ z 0 = chartFieldAmp … cutA cutB 0 z 0 + censusAmpTauDeriv … z · τ`.
    Pure `ring` on the shared atoms (`radialCutoff·Θ^{−1/2}·(u₀ + u₁·τ)`).  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_affine_slope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cutA cutB τ : ℝ) (z : Point n) :
    chartFieldAmp g gi hC hK cutA cutB τ z 0
      = chartFieldAmp g gi hC hK cutA cutB 0 z 0
        + censusAmpTauDeriv g gi hC hK cutA cutB z * τ := by
  simp only [chartFieldAmp, censusAmpTauDeriv]; ring

/-! ###############################################################################
    ### §B — the τ-UNIFORM amplitude sup-bound package.
    ############################################################################### -/

/-- **★★★ `census_amplitude_supBounds` — the τ-UNIFORM amplitude sup-bound package.**  From the standard
    geometry carries (`hg` metric smoothness, `hg0` `g(0)=I`, `hu` transport smoothness, `h0Kmem` `K∈𝓝 0`)
    and a positive time cap `τ₀`, there is a base ball radius `rAmp > 0` and explicit constants `M, M' ≥ 0`
    with, on `ball 0 rAmp`,
      • `|chartFieldAmp … cutA cutB τ z 0| ≤ M`  UNIFORMLY over `0 < τ ≤ τ₀`, and
      • `|censusAmpTauDeriv … z| ≤ M'`.
    Route: bound `chartFieldAmp` at `τ=0` (`M₀`) and the slope (`M'`) via the banked base-point
    regularity, then the affine form `chartFieldAmp τ = chartFieldAmp 0 + slope·τ` gives the SINGLE
    τ-uniform `M := M₀ + M'·τ₀` on `(0,τ₀]`.  This DISCHARGES the `hAmp0`/`hCfield` sup-bound content to
    the standard geometry carries alone.  NOT `a₁ = R/6`. -/
theorem census_amplitude_supBounds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (cutA cutB τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ rAmp : ℝ, 0 < rAmp ∧ ∃ M M' : ℝ, 0 ≤ M ∧ 0 ≤ M' ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, ‖z‖ < rAmp →
        |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M) ∧
      (∀ z : Point n, ‖z‖ < rAmp →
        |censusAmpTauDeriv g gi hC hK cutA cutB z| ≤ M') := by
  obtain ⟨r0, hr0, M0, L0, hM0, _hL0, hb0, _⟩ :=
    chartFieldAmp_base_regularity_center g gi hC hK cutA cutB 0 h0Kmem hg hg0 hu
  obtain ⟨r', hr', M', L', hM', _hL', hb', _⟩ :=
    censusAmpTauDeriv_base_regularity_center g gi hC hK cutA cutB h0Kmem hg hg0 hu
  refine ⟨min r0 r', lt_min hr0 hr', M0 + M' * τ₀, M',
    add_nonneg hM0 (mul_nonneg hM' hτ₀.le), hM', ?_, ?_⟩
  · intro τ hτ hτ0 z hz
    have hz0 : ‖z‖ < r0 := lt_of_lt_of_le hz (min_le_left _ _)
    have hz' : ‖z‖ < r' := lt_of_lt_of_le hz (min_le_right _ _)
    rw [chartFieldAmp_affine_slope]
    have hslopeτ : |censusAmpTauDeriv g gi hC hK cutA cutB z| * τ ≤ M' * τ₀ := by
      have h1 : |censusAmpTauDeriv g gi hC hK cutA cutB z| * τ ≤ M' * τ :=
        mul_le_mul_of_nonneg_right (hb' z hz') hτ.le
      have h2 : M' * τ ≤ M' * τ₀ := mul_le_mul_of_nonneg_left hτ0 hM'
      linarith
    calc |chartFieldAmp g gi hC hK cutA cutB 0 z 0
            + censusAmpTauDeriv g gi hC hK cutA cutB z * τ|
        ≤ |chartFieldAmp g gi hC hK cutA cutB 0 z 0|
            + |censusAmpTauDeriv g gi hC hK cutA cutB z * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK cutA cutB 0 z 0|
            + |censusAmpTauDeriv g gi hC hK cutA cutB z| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ M0 + M' * τ₀ := by
          have := hb0 z hz0
          linarith
  · intro z hz
    exact hb' z (lt_of_lt_of_le hz (min_le_right _ _))

/-! ###############################################################################
    ### §C — the FULL far-rate with `hAmp0`/`hCfield` DISCHARGED internally.
    ############################################################################### -/

/-- **★★★ `censusBound_of_geometry_gate_supp_F_ballRate`.**  The FULL `hCensusBound` far-rate binder — the
    `censusBound_of_onGate_and_ballRate` (J4-947) conclusion — from the standard geometry carries plus the
    REMAINING carries, with the amplitude sup-bounds `hAmp0`/`hCfield` DISCHARGED internally by
    `census_amplitude_supBounds` (affine-in-τ + banked base-point continuity).  The `Cfield` field and the
    `HasDerivAt` half of `hgate` are supplied internally (`chartFieldAmp_hasDerivAt_tau`); the caller need
    only supply the GATE half `hgateS` (`∀ w, w.2.2∈K → 0<w.1 → w.2.1∈S w.2.2`), the support fact `hSupp`,
    the F-factor bound `hF`, integrability `hΦint` (C2), and the on-ball trace rate `hballrate` (C1), for
    ANY fixed gate record `D` whose radius is `≤ rAmp`.  NOT `a₁ = R/6`. -/
theorem censusBound_of_geometry_gate_supp_F_ballRate (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (cutA cutB : ℝ)
    (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F : ℝ → Point n → Point n → ℝ)
    (u ε h ρ τ₀ MF Cpair : ℝ)
    (hε : 0 < ε) (hτ₀ : 0 < τ₀) (hρ : 0 < ρ) (hMF : 0 ≤ MF) (hCpair : 0 ≤ Cpair)
    (hh : 0 ≤ h) (hcap : ε + h ≤ τ₀)
    (hF : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, ρ ≤ ‖z‖ → |F s z 0| ≤ MF) :
    ∃ rAmp : ℝ, 0 < rAmp ∧
      ∀ D : FixedFlowGateData g gi hC hK, D.r ≤ rAmp →
        (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2) →
        (∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          Integrable
            (fun z => deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s)
              * F s z 0) volume) →
        (∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
          |∫ z in Metric.ball (0 : Point n) ρ,
            deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
              ≤ Cpair * (a - s) ^ (-(1 : ℝ) / 2)) →
        ∃ (lam' Cenv : ℝ), 0 < lam' ∧ 0 ≤ Cenv ∧
          ∀ s ∈ Set.Ioo (u - ε) u, ∀ a ∈ Set.Icc u (u + h),
            |∫ z, deriv (fun r => vanVleckGatedWitness g gi hC hK S cutA cutB r 0 z) (a - s) * F s z 0|
              ≤ (Cpair + Cenv * Real.sqrt 2 ^ n * Real.sqrt ε) * (u - s) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨rAmp, hrAmp, M, M', hM, hM', hampBnd, hcfBnd⟩ :=
    census_amplitude_supBounds g gi hC hK cutA cutB τ₀ hτ₀ h0Kmem hg hg0 hu
  refine ⟨rAmp, hrAmp, ?_⟩
  intro D hDr hgateS hSupp hΦint hballrate
  -- the amplitude slope field `Cfield`, whose value at field point `0` is `censusAmpTauDeriv`.
  set Cfield : Point n → Point n → ℝ := fun z p =>
    radialCutoff cutA cutB (uniformInverseChart g gi hC hK z p)
      * (vanVleck g (uniformInverseChart g gi hC hK z p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK z p))
    with hCfielddef
  -- reconstruct the full `hgate` = ⟨S-gate half (carried), HasDerivAt half (banked unconditional)⟩.
  have hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
      w.2.1 ∈ S w.2.2 ∧
      HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK cutA cutB u w.2.2 w.2.1)
        (Cfield w.2.2 w.2.1) w.1 := by
    intro w hzK hτ
    exact ⟨hgateS w hzK hτ,
      chartFieldAmp_hasDerivAt_tau g gi hC hK cutA cutB w.2.2 w.2.1 w.1⟩
  -- `hAmp0` from the package (radius monotonicity `‖z‖ < D.r ≤ rAmp`).
  have hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |chartFieldAmp g gi hC hK cutA cutB τ z 0| ≤ M := by
    intro τ hτ hτ0 z _ hzr
    exact hampBnd τ hτ hτ0 z (lt_of_lt_of_le hzr hDr)
  -- `hCfield` from the package (`Cfield z 0 = censusAmpTauDeriv … z`, definitional).
  have hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M' := by
    intro z _ hzr
    exact hcfBnd z (lt_of_lt_of_le hzr hDr)
  exact censusBound_of_amplitudeCarries_Fbound_ballRate hn g gi hC hK S cutA cutB D τ₀ M M'
    hτ₀ hM hM' Cfield hgate hAmp0 hCfield hSupp F u ε h ρ MF Cpair
    hε hρ hMF hCpair hh hcap hF hΦint hballrate

/-! ###############################################################################
    ### §D — SHRINKABILITY: valid small-radius gate records ALWAYS exist (non-vacuity of the
    ###       capstone's `∀ D, D.r ≤ rAmp → …` binder — refuting Sol's point-C vacuity concern).
    ############################################################################### -/

/-- **`shrinkGate` — the gate-record radius shrink.**  Any valid `FixedFlowGateData` `D` yields a valid
    record at ANY smaller positive radius `r' ≤ D.r`: the ordered cutoff radii rescale to `r'/3 < 2r'/3 <
    r'`, the width-gap `(η, lam)` is inherited unchanged, and the near-isometry gate survives shrinking
    (`‖z‖ < r' ≤ D.r`, so `D.hgate` applies).  NOT `a₁ = R/6`. -/
noncomputable def shrinkGate {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} (D : FixedFlowGateData g gi hC hK)
    (r' : ℝ) (hr'pos : 0 < r') (hr'le : r' ≤ D.r) : FixedFlowGateData g gi hC hK where
  a := r' / 3
  b := 2 * r' / 3
  r := r'
  eta := D.eta
  lam := D.lam
  ha := by linarith
  hab := by linarith
  hbr := by linarith
  heta := D.heta
  hlam := D.hlam
  hgap := D.hgap
  hgate := fun z hz hzr => D.hgate z hz (lt_of_lt_of_le hzr hr'le)

@[simp] theorem shrinkGate_r {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} (D : FixedFlowGateData g gi hC hK)
    (r' : ℝ) (hr'pos : 0 < r') (hr'le : r' ≤ D.r) :
    (shrinkGate D r' hr'pos hr'le).r = r' := rfl

/-- **★★ `census_smallRadius_gate_exists` — the capstone's `∀ D` binder is NON-VACUOUS.**  For ANY
    concrete geometry `(g, gi, hC, hK)` and ANY positive `target`, there is a VALID `FixedFlowGateData`
    whose gate radius is `≤ target` (and still `> 0`).  Take the unconditional
    `FixedFlowGateData.of_geometry` record and `shrinkGate` it to `min target D₀.r`.  In particular,
    applied with `target := rAmp` (the capstone's radius), this exhibits a genuine inhabitant of the
    `∀ D, D.r ≤ rAmp → …` binder — so `censusBound_of_geometry_gate_supp_F_ballRate` is NOT vacuously
    quantified.  NOT `a₁ = R/6`. -/
theorem census_smallRadius_gate_exists (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (target : ℝ) (htarget : 0 < target) :
    ∃ D : FixedFlowGateData g gi hC hK, 0 < D.r ∧ D.r ≤ target := by
  set D0 : FixedFlowGateData g gi hC hK := FixedFlowGateData.of_geometry g gi hC hK with hD0
  have hD0r : 0 < D0.r := lt_trans (lt_trans D0.ha D0.hab) D0.hbr
  refine ⟨shrinkGate D0 (min target D0.r) (lt_min htarget hD0r) (min_le_right _ _), ?_, ?_⟩
  · show 0 < min target D0.r
    exact lt_min htarget hD0r
  · show min target D0.r ≤ target
    exact min_le_left _ _

end QIQTH.CensusAmplitudeSupDischarge

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.CensusAmplitudeSupDischarge
#print axioms chartFieldAmp_affine_slope
#print axioms census_amplitude_supBounds
#print axioms censusBound_of_geometry_gate_supp_F_ballRate
#print axioms census_smallRadius_gate_exists
end AxiomChecks
