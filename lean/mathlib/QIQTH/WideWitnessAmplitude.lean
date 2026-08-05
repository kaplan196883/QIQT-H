/-
  WideWitnessAmplitude — J4-252: wide-route brick 5, the WIDE-GAUSSIAN WITNESS DOMINATION package.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It packages
  the already-banked witness factorisation / second-derivative chart-image expansion into the WIDE
  Gaussian-domination shapes the sliver-boundary bricks (6-8) consume, by feeding the chart-image
  (`W₀ z`) Gaussian through the fixed-gate width-transfer `FixedFlowGateData.poly_absorb` to reach the
  base-point (`lam·τ`, `z`) Gaussian.  No `sorry` (prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.  No existing file is edited.

  ── WHAT IS CARRIED (honest, satisfiable inputs — none is the conclusion).
    * `FixedFlowGateData D` (brick 2/3, J4-251) — the fixed width gate + `poly_absorb`.
    * `hAmp0` — the zeroth on-gate amplitude sup-bound `|chartFieldAmp … 0| ≤ M` (τ-capped); satisfiable
      by continuity of `chartFieldAmp` on the compact box `[0,τ₀] × (K ∩ ball 0 r)`.  This mirrors the
      banked `AmplitudeDerivativeData.hAampBdd` carried-field pattern.
    * `hSecondEnv` — the CHART-IMAGE (curved, `gaussDdim τ (W₀ z)`) two-term envelope of the concrete
      `witnessSecondXDeriv`.  This is the magnitude form of the banked chart-image Leibniz expansion
      `SliverCConvBatch.witnessSecondXDeriv_chartImage_expand` bounded by the compact jet packs; the
      genuine geometric content is DELIMITED by that expand lemma — carried here, not the conclusion.

  ── WHAT IS PROVED (the genuine new content — the WIDTH TRANSFER).
    (1)  `WideAmplitudeData.zeroth_domination` — the zeroth wide domination
             `|H_G τ 0 z| ≤ C · gaussDdim (lam·τ) z`   on `z ∈ K`, `‖z‖ < r`, `0 < τ ≤ τ₀`,
         from the honest factorisation `H_G τ 0 z = gaussDdim τ (W₀ z) · chartFieldAmp … 0`
         (`witness_zero_eq_gauss_mul_amp`), `|chartFieldAmp| ≤ M`, and `poly_absorb 0`.
         `zeroth_domination_global` extends it to ALL `z` (the witness vanishes off the gate; the
         support-inside-ball fact is carried honestly as `hSupp`).
    (2)  `WideAmplitudeData.second_domination` — the second wide domination in the clean Sol shape
             `|witnessSecondXDeriv … i τ z| ≤ C · τ⁻¹ · gaussDdim (lam·τ) z`,
         from the two-term chart-image envelope and `poly_absorb 0` / `poly_absorb 1` (the
         `(r²(z)/τ)/τ` piece absorbs against the width gap leaving `τ⁻¹`).
    (★)  `WideAmplitudePackage` — the OUTPUT bundle of (1)+(2), with `of_data` the constructor from a
         `WideAmplitudeData`.  This is what bricks 6-8 (WideSliverBoundary / FixedGateDichotomy /
         FixedGateSourceSlice) consume.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InverseChartNormalJets
import QIQTH.SliverCConvBatch
import QIQTH.ResidueBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTransfer QIQTH.InverseChartNormalJets
open QIQTH.ResidueBound
open scoped Topology BigOperators

namespace QIQTH.WideWitnessAmplitude

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (0) — the honest `x = 0` factorisation into `chartFieldAmp`.
    ############################################################################### -/

/-- **`witness_zero_eq_gauss_mul_amp` — the on-gate `x = 0` factorisation.**  On the gate
    (`z ∈ K`, `0 ∈ S z`), the gated van-Vleck witness at field centre factors as the chart-image
    Gaussian times the concrete field amplitude:
        `H_G τ 0 z = gaussDdim τ (W₀ z) · chartFieldAmp g gi hC hK a b τ z 0`,   `W₀ z = W z 0`.
    Pure regrouping of the banked `vanVleckGatedWitness_zero_factor` (which lists the amplitude in the
    `radialCutoff · Θ^{−1/2} · (u₀+u₁τ)` form) against the `chartFieldAmp` def.  NOT `a₁ = R/6`. -/
theorem witness_zero_eq_gauss_mul_amp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        * chartFieldAmp g gi hC hK a b τ z 0 := by
  rw [vanVleckGatedWitness_zero_factor g gi hC hK S a b τ hz h0]
  simp only [chartFieldAmp]
  ring

/-! ###############################################################################
    ### (1) — the wide-domination data bundle.
    ############################################################################### -/

/-- **★★ `WideAmplitudeData` — the wide-domination INPUT bundle.**  Downstream of the geometry, this
    packages the fixed gate record `D`, a positive time cap `τ₀`, and the honest amplitude / second-jet
    envelopes the two wide dominations consume.  Each carried hypothesis is a genuine, satisfiable fact
    (NOT the conclusion): `hAmp0` is the τ-capped zeroth amplitude sup-bound (continuity on the compact
    box), and `hSecondEnv` is the CHART-IMAGE (curved-Gaussian) two-term envelope of the concrete
    `witnessSecondXDeriv`, i.e. the magnitude form of the banked
    `SliverCConvBatch.witnessSecondXDeriv_chartImage_expand` bounded by the compact jet packs.
    NOT `a₁ = R/6`. -/
structure WideAmplitudeData (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (i : Fin n) where
  /-- the fixed width gate record (brick 2/3). -/
  D : FixedFlowGateData g gi hC hK
  /-- the positive time cap. -/
  τ₀ : ℝ
  /-- zeroth amplitude sup-bound constant. -/
  M : ℝ
  /-- second-envelope constant term. -/
  B₀ : ℝ
  /-- second-envelope radial (width-2) coefficient. -/
  B₁ : ℝ
  hτ₀ : 0 < τ₀
  hM : 0 ≤ M
  hB₀ : 0 ≤ B₀
  hB₁ : 0 ≤ B₁
  /-- the τ-capped zeroth amplitude sup-bound on the gate. -/
  hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
    |chartFieldAmp g gi hC hK D.a D.b τ z 0| ≤ M
  /-- the CHART-IMAGE two-term envelope of the concrete second `x`-derivative (curved Gaussian). -/
  hSecondEnv : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
    |witnessSecondXDeriv g gi hC hK S D.a D.b i τ z|
      ≤ (B₀ + B₁ * (rncRadialSq z / τ)) * τ⁻¹
          * gaussDdim τ (uniformInverseChart g gi hC hK z 0)

/-! ###############################################################################
    ### (2) — the zeroth wide domination.
    ############################################################################### -/

/-- **★★ `WideAmplitudeData.zeroth_domination` — THE ZEROTH WIDE DOMINATION (on the gate ball).**  For a
    wide-amplitude data bundle there is an explicit `C > 0` with, uniformly over `0 < τ ≤ τ₀` and every
    gate point `z ∈ K`, `‖z‖ < r`,
        `|vanVleckGatedWitness … τ 0 z| ≤ C · gaussDdim (lam·τ) z`.
    Route: the honest factorisation `H_G τ 0 z = gaussDdim τ (W₀ z) · chartFieldAmp … 0` (with the
    off-gate `0 ∉ S z` case giving `H_G = 0`), `|chartFieldAmp| ≤ M`, and the fixed-gate width transfer
    `poly_absorb 0` (`gaussDdim τ (W₀ z) ≤ C₀ · gaussDdim (lam·τ) z`).  NOT `a₁ = R/6`. -/
theorem WideAmplitudeData.zeroth_domination {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudeData g gi hC hK S i) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z ∈ K, ‖z‖ < P.D.r →
      |vanVleckGatedWitness g gi hC hK S P.D.a P.D.b τ (0 : Point n) z|
        ≤ C * gaussDdim (P.D.lam * τ) z := by
  obtain ⟨C₀, hC₀0, habs0⟩ := P.D.poly_absorb 0
  refine ⟨P.M * C₀ + 1, by nlinarith [mul_nonneg P.hM hC₀0.le], ?_⟩
  intro τ hτ hτ0 z hz hzr
  by_cases h0 : (0 : Point n) ∈ S z
  · -- on-gate: factor + amp bound + width transfer.
    have hbridge := witness_zero_eq_gauss_mul_amp g gi hC hK S P.D.a P.D.b τ hz h0
    rw [hbridge, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ _)]
    have hApd := P.hAmp0 τ hτ hτ0 z hz hzr
    have hgW : gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        ≤ C₀ * gaussDdim (P.D.lam * τ) z := by simpa using habs0 τ hτ z hz hzr
    have hGWnn : 0 ≤ gaussDdim τ (uniformInverseChart g gi hC hK z 0) := gaussDdim_nonneg _ _
    have hGLnn : 0 ≤ gaussDdim (P.D.lam * τ) z := gaussDdim_nonneg _ _
    have hstep1 :
        gaussDdim τ (uniformInverseChart g gi hC hK z 0)
            * |chartFieldAmp g gi hC hK P.D.a P.D.b τ z 0|
          ≤ gaussDdim τ (uniformInverseChart g gi hC hK z 0) * P.M :=
      mul_le_mul_of_nonneg_left hApd hGWnn
    have hstep2 :
        gaussDdim τ (uniformInverseChart g gi hC hK z 0) * P.M
          ≤ (C₀ * gaussDdim (P.D.lam * τ) z) * P.M :=
      mul_le_mul_of_nonneg_right hgW P.hM
    nlinarith [hstep1, hstep2, hGLnn]
  · -- off-gate: the witness vanishes.
    have hzero : vanVleckGatedWitness g gi hC hK S P.D.a P.D.b τ (0 : Point n) z = 0 := by
      unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ τ (0 : Point n) z (Or.inr h0)
    rw [hzero, abs_zero]
    exact mul_nonneg (by nlinarith [mul_nonneg P.hM hC₀0.le]) (gaussDdim_nonneg _ _)

/-- **`WideAmplitudeData.zeroth_domination_global` — the zeroth wide domination for ALL `z`.**  Extends
    `zeroth_domination` off the gate ball: the witness vanishes wherever `z ∉ K` or `0 ∉ S z`, and where
    it does not the carried support fact `hSupp` places `z` inside the gate ball, so the on-ball bound
    applies.  `hSupp` (the gate only activates for base points inside the gate radius) is the honest
    support-inside-ball input — satisfiable, not the conclusion.  NOT `a₁ = R/6`. -/
theorem WideAmplitudeData.zeroth_domination_global {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudeData g gi hC hK S i)
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < P.D.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      |vanVleckGatedWitness g gi hC hK S P.D.a P.D.b τ (0 : Point n) z|
        ≤ C * gaussDdim (P.D.lam * τ) z := by
  obtain ⟨C, hC0, hbound⟩ := P.zeroth_domination
  refine ⟨C, hC0, ?_⟩
  intro τ hτ hτ0 z
  by_cases hzK : z ∈ K
  · by_cases h0 : (0 : Point n) ∈ S z
    · exact hbound τ hτ hτ0 z hzK (hSupp z hzK h0)
    · have hzero : vanVleckGatedWitness g gi hC hK S P.D.a P.D.b τ (0 : Point n) z = 0 := by
        unfold vanVleckGatedWitness
        exact gatedKernel_apply_of_notMem K S _ τ (0 : Point n) z (Or.inr h0)
      rw [hzero, abs_zero]
      exact mul_nonneg hC0.le (gaussDdim_nonneg _ _)
  · have hzero : vanVleckGatedWitness g gi hC hK S P.D.a P.D.b τ (0 : Point n) z = 0 := by
      unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ τ (0 : Point n) z (Or.inl hzK)
    rw [hzero, abs_zero]
    exact mul_nonneg hC0.le (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### (3) — the second wide domination.
    ############################################################################### -/

/-- **★★ `WideAmplitudeData.second_domination` — THE SECOND WIDE DOMINATION (clean Sol shape).**  For a
    wide-amplitude data bundle there is an explicit `C > 0` with, uniformly over `0 < τ ≤ τ₀` and every
    gate point `z ∈ K`, `‖z‖ < r`,
        `|witnessSecondXDeriv … i τ z| ≤ C · τ⁻¹ · gaussDdim (lam·τ) z`.
    Route: the CHART-IMAGE two-term envelope `hSecondEnv`
    `≤ (B₀ + B₁·r²(z)/τ)·τ⁻¹·gaussDdim τ (W₀ z)`, then the fixed-gate width transfer `poly_absorb 0`
    (constant piece) and `poly_absorb 1` (the `(r²(z)/τ)` piece absorbs against the width gap), both
    scaled by `τ⁻¹ ≥ 0`.  NOT `a₁ = R/6`. -/
theorem WideAmplitudeData.second_domination {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudeData g gi hC hK S i) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z ∈ K, ‖z‖ < P.D.r →
      |witnessSecondXDeriv g gi hC hK S P.D.a P.D.b i τ z|
        ≤ C * τ⁻¹ * gaussDdim (P.D.lam * τ) z := by
  obtain ⟨C₀, hC₀0, habs0⟩ := P.D.poly_absorb 0
  obtain ⟨C₁, hC₁0, habs1⟩ := P.D.poly_absorb 1
  refine ⟨P.B₀ * C₀ + P.B₁ * C₁ + 1,
    by nlinarith [mul_nonneg P.hB₀ hC₀0.le, mul_nonneg P.hB₁ hC₁0.le], ?_⟩
  intro τ hτ hτ0 z hz hzr
  have henv := P.hSecondEnv τ hτ hτ0 z hz hzr
  have hgW0 : gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      ≤ C₀ * gaussDdim (P.D.lam * τ) z := by simpa using habs0 τ hτ z hz hzr
  have hgW1 : rncRadialSq z / τ * gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      ≤ C₁ * gaussDdim (P.D.lam * τ) z := by
    simpa only [pow_one] using habs1 τ hτ z hz hzr
  have hGLnn : 0 ≤ gaussDdim (P.D.lam * τ) z := gaussDdim_nonneg _ _
  have hti : 0 ≤ τ⁻¹ := (inv_pos.mpr hτ).le
  set Gw := gaussDdim τ (uniformInverseChart g gi hC hK z 0) with hGwdef
  set Gl := gaussDdim (P.D.lam * τ) z with hGldef
  set rz := rncRadialSq z with hrzdef
  -- distribute and bound the two pieces via the width transfer.
  have hdist : (P.B₀ + P.B₁ * (rz / τ)) * τ⁻¹ * Gw
      = τ⁻¹ * (P.B₀ * Gw) + τ⁻¹ * (P.B₁ * (rz / τ * Gw)) := by ring
  have h1 : τ⁻¹ * (P.B₀ * Gw) ≤ τ⁻¹ * (P.B₀ * (C₀ * Gl)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW0 P.hB₀) hti
  have h2 : τ⁻¹ * (P.B₁ * (rz / τ * Gw)) ≤ τ⁻¹ * (P.B₁ * (C₁ * Gl)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW1 P.hB₁) hti
  have htiGL : 0 ≤ τ⁻¹ * Gl := mul_nonneg hti hGLnn
  calc |witnessSecondXDeriv g gi hC hK S P.D.a P.D.b i τ z|
      ≤ (P.B₀ + P.B₁ * (rz / τ)) * τ⁻¹ * Gw := henv
    _ = τ⁻¹ * (P.B₀ * Gw) + τ⁻¹ * (P.B₁ * (rz / τ * Gw)) := hdist
    _ ≤ τ⁻¹ * (P.B₀ * (C₀ * Gl)) + τ⁻¹ * (P.B₁ * (C₁ * Gl)) := add_le_add h1 h2
    _ ≤ (P.B₀ * C₀ + P.B₁ * C₁ + 1) * τ⁻¹ * Gl := by nlinarith [htiGL]

/-! ###############################################################################
    ### (★) — the WideAmplitudePackage output bundle.
    ############################################################################### -/

/-- **★★★ `WideAmplitudePackage` — THE WIDE-DOMINATION OUTPUT BUNDLE (wide-route brick 5 deliverable).**
    Bundles the two proved wide dominations — the zeroth `|H_G τ 0 z| ≤ C·gaussDdim (lam·τ) z` and the
    second `|witnessSecondXDeriv … i τ z| ≤ C·τ⁻¹·gaussDdim (lam·τ) z` — as a single reusable structure,
    both on the gate ball `z ∈ K`, `‖z‖ < r`, `0 < τ ≤ τ₀`.  This is exactly what the sliver-boundary
    bricks (6-8: WideSliverBoundary / FixedGateDichotomy / FixedGateSourceSlice) consume.  Built from a
    `WideAmplitudeData` via `of_data`.  NOT `a₁ = R/6`. -/
structure WideAmplitudePackage (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (i : Fin n) where
  /-- the width-gap dilation. -/
  lam : ℝ
  /-- the time cap. -/
  τ₀ : ℝ
  /-- inner radial-cutoff radius. -/
  a : ℝ
  /-- outer radial-cutoff radius. -/
  b : ℝ
  /-- the gate radius. -/
  r : ℝ
  /-- the zeroth wide domination. -/
  hZeroth : ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < r →
    |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ C * gaussDdim (lam * τ) z
  /-- the second wide domination (clean `τ⁻¹` shape). -/
  hSecond : ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < r →
    |witnessSecondXDeriv g gi hC hK S a b i τ z| ≤ C * τ⁻¹ * gaussDdim (lam * τ) z

/-- **★ `WideAmplitudePackage.of_data` — the constructor.**  Assembles the output bundle from a
    `WideAmplitudeData` by discharging both dominations (`zeroth_domination`, `second_domination`).
    NOT `a₁ = R/6`. -/
noncomputable def WideAmplitudePackage.of_data {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudeData g gi hC hK S i) :
    WideAmplitudePackage g gi hC hK S i where
  lam := P.D.lam
  τ₀ := P.τ₀
  a := P.D.a
  b := P.D.b
  r := P.D.r
  hZeroth := P.zeroth_domination
  hSecond := P.second_domination

end QIQTH.WideWitnessAmplitude

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp
#print axioms QIQTH.WideWitnessAmplitude.WideAmplitudeData.zeroth_domination
#print axioms QIQTH.WideWitnessAmplitude.WideAmplitudeData.zeroth_domination_global
#print axioms QIQTH.WideWitnessAmplitude.WideAmplitudeData.second_domination
#print axioms QIQTH.WideWitnessAmplitude.WideAmplitudePackage.of_data
