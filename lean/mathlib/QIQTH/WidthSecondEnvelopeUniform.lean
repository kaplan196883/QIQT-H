/-
  WidthSecondEnvelopeUniform — the UNIFORM (fixed-`B₀,B₁`-over-the-compact-gate-box) `hSecondEnv`
  envelope, assembled from the pointwise `witnessSecondXDeriv_chartImage_envelope` (J4-770).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE IS

  J4-770 proved the POINTWISE chart-image second-envelope
  (`WidthSecondEnvelope.witnessSecondXDeriv_chartImage_envelope`): at a SINGLE `(i, τ, z)`, with
  per-point constants `cW,CP,CS,CPQ,M₀,M₁,M₂`,

      |witnessSecondXDeriv … i τ z|
        ≤ (B₀ + B₁·(rncRadialSq z / τ))·τ⁻¹·gaussDdim τ (W₀ z),
      B₀ = (CS+CPQ)·M₀/2 + CP·M₁ + M₂·τ₀,   B₁ = cW·M₀/4.

  The `WideWitnessAmplitude.WideAmplitudeData.hSecondEnv` FIELD demands this bound with `B₀,B₁` FIXED
  over the WHOLE compact gate box — i.e. constants that do NOT depend on the particular `(τ,z)`, only
  `∀ τ ∈ (0,τ₀], ∀ z ∈ K, ‖z‖ < r`.  This file supplies that **uniformisation plumbing**:

  * `witnessSecondXDeriv_hSecondEnv_uniform` — THE UNIFORM ENVELOPE.  Given FIXED constants
    `cW,CP,CS,CPQ,M₀,M₁,M₂` (with the usual non-negativity) and a UNIFORM per-`(τ,z)` data bundle
    `hData` — for every `τ ∈ (0,τ₀]` and every gate point `z ∈ K`, `‖z‖ < r`, there exist the chart
    jets `Pi,Q` with their `HasDerivAt` shapes, the amplitude `PdiffAt` differentiability facts, the
    open-gate facts, the upper near-isometry, and the jet / amplitude sup bounds **all against the SAME
    fixed constants** — the two-term envelope holds with the SINGLE pair `B₀,B₁` for all `(τ,z)`.
    This is EXACTLY the `hSecondEnv` field shape.  Proof: intro `(τ,z)`, unpack `hData`, fire the
    pointwise J4-770 core.

  * `hSecondEnv_uniform_forGate` — the FixedFlowGateData-keyed restatement, delivering the bound in the
    literal `(D.a, D.b, D.r, τ₀)` form the `hSecondEnv` field of a `WideAmplitudeData` over `D` carries.

  ## WHY THE CONSTANTS ARE CARRIED, NOT DISCHARGED FROM GEOMETRY (honest scope).

  The FIXED constants would be produced by `CompactJetBounds.exists_bound_closedBall` (the standard
  `IsCompact.exists_bound_of_continuousOn` sup lever), and the near-isometry `chartW0_rncRadialSq_error`
  is ALREADY uniform over `z ∈ K, ‖z‖ < r₀`.  The one genuinely non-mechanical piece is the sup bound
  on the CHART JETS `Pi 0, Q` (field derivatives of `uniformInverseChart`) uniformly in `z`: these
  inherit the documented C²-chart / `.choose`-opacity wall (`uniformInverseChart` carries no
  continuous-in-`z` structure at the raw level — J4-746), so their sup constants are NOT discharged
  here.  The `hData` bundle therefore carries the per-`z` jet EXISTENCE together with the sup bounds
  against the fixed constants — a genuine, satisfiable weakening of the conclusion, NOT the conclusion.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6`.  It is the QUANTIFIER-MANAGEMENT ("uniform over
  the compact box") plumbing layer that lifts the pointwise J4-770 envelope to the fixed-`B₀,B₁`
  `hSecondEnv` field shape.  No new geometry.  The hypothesis `hData` is strictly weaker than the
  conclusion (per-point jet/amplitude sup bounds + the near-isometry), manifestly satisfiable, and none
  of its conjuncts equals the envelope conclusion.  No `sorry`, no new axioms, no `:= True`, no vacuous
  / unsatisfiable / conclusion-equal hypothesis, no existing file edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthSecondEnvelope
import QIQTH.InverseChartNormalJets

open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.VanVleck QIQTH.SliverCConvBatch QIQTH.WidthSecondEnvelope
open QIQTH.InverseChartNormalJets
open scoped BigOperators

namespace QIQTH.WidthSecondEnvelopeUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `witnessSecondXDeriv_hSecondEnv_uniform` — the UNIFORM (fixed-`B₀,B₁`) chart-image second
    envelope.**  With the constants `cW,CP,CS,CPQ,M₀,M₁,M₂,τ₀` FIXED (independent of `(τ,z)`) and the
    uniform per-`(τ,z)` data bundle `hData` supplying, for every `τ ∈ (0,τ₀]` and every gate point
    `z ∈ K`, `‖z‖ < r`, the chart jets `Pi,Q` (with their `HasDerivAt` shapes), the amplitude
    differentiability (`PdiffAt`) facts, the open-gate facts, the upper near-isometry
    `⟨W₀z,Pi 0⟩² ≤ cW·rncRadialSq z`, and the jet / amplitude sup bounds **all against those same fixed
    constants**, the two-term Gaussian envelope

        |witnessSecondXDeriv … i τ z|
          ≤ (B₀ + B₁·(rncRadialSq z / τ))·τ⁻¹·gaussDdim τ (W₀ z),
        B₀ = (CS+CPQ)·M₀/2 + CP·M₁ + M₂·τ₀,   B₁ = cW·M₀/4,

    holds with this SINGLE `B₀,B₁` pair uniformly over the whole compact gate box `{τ∈(0,τ₀]}×{z∈K,
    ‖z‖<r}`.  This is EXACTLY the `WideWitnessAmplitude.WideAmplitudeData.hSecondEnv` field shape.  Each
    `(τ,z)` is discharged by the pointwise J4-770 core `witnessSecondXDeriv_chartImage_envelope`.
    ⚠ NOT `a₁ = R/6`. -/
theorem witnessSecondXDeriv_hSecondEnv_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (r : ℝ)
    (τ₀ cW CP CS CPQ M0 M1 M2 : ℝ) (hτ0 : 0 < τ₀) (hcW : 0 ≤ cW)
    (hM0n : 0 ≤ M0) (hM1n : 0 ≤ M1) (hM2n : 0 ≤ M2)
    (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCPQ : 0 ≤ CPQ)
    (hData : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < r →
      IsOpen (S z) ∧ (0 : Point n) ∈ S z ∧
      ∃ Pi : Point n → Fin n → ℝ, ∃ Q : Fin n → ℝ,
        (∀ x ∈ S z, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
        ∧ (∀ k, HasDerivAt
            (fun s : ℝ => Pi (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
        ∧ (∀ x ∈ S z, PdiffAt (chartFieldAmp g gi hC hK a b τ z) i x)
        ∧ PdiffAt (chartFieldAmp g gi hC hK a b τ z) i (0 : Point n)
        ∧ PdiffAt (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i (0 : Point n)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) ^ 2 ≤ cW * rncRadialSq z
        ∧ |∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k| ≤ CP
        ∧ |∑ k, Pi 0 k * Pi 0 k| ≤ CS
        ∧ |∑ k, uniformInverseChart g gi hC hK z 0 k * Q k| ≤ CPQ
        ∧ |chartFieldAmp g gi hC hK a b τ z 0| ≤ M0
        ∧ |pd (chartFieldAmp g gi hC hK a b τ z) i 0| ≤ M1
        ∧ |pd (fun y => pd (chartFieldAmp g gi hC hK a b τ z) i y) i 0| ≤ M2) :
    ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < r →
      |witnessSecondXDeriv g gi hC hK S a b i τ z|
        ≤ (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
            + cW * M0 / 4 * (rncRadialSq z / τ)) * τ⁻¹
            * gaussDdim τ (uniformInverseChart g gi hC hK z 0) := by
  intro τ hτ hτ0le z hz hzr
  obtain ⟨hSopen, h0, Pi, Q, hJetVi, hJetQ, hAmpj1, hAmpi1, hAmp2,
          hP2, hPabs, hS2, hPQ, hM0, hM1, hM2⟩ := hData τ hτ hτ0le z hz hzr
  exact witnessSecondXDeriv_chartImage_envelope g gi hC hK S a b i τ hτ z hz hSopen h0
    Pi Q hJetVi hJetQ hAmpj1 hAmpi1 hAmp2
    τ₀ cW CP CS CPQ M0 M1 M2 hτ0le hcW hP2 hPabs hS2 hPQ hM0 hM1 hM2
    hM0n hM1n hM2n hCP hCS hCPQ

/-- **★★ `hSecondEnv_uniform_forGate` — the uniform envelope in the literal `hSecondEnv` field shape.**
    Restates `witnessSecondXDeriv_hSecondEnv_uniform` keyed to a `FixedFlowGateData D`, delivering the
    bound in the exact `(D.a, D.b, D.r, τ₀)` form that the `hSecondEnv` field of a
    `WideWitnessAmplitude.WideAmplitudeData` over `D` carries — with the SINGLE constant pair
    `B₀ = (CS+CPQ)·M₀/2 + CP·M₁ + M₂·τ₀`, `B₁ = cW·M₀/4` fixed over the whole compact gate box.
    ⚠ NOT `a₁ = R/6`. -/
theorem hSecondEnv_uniform_forGate
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (i : Fin n)
    (D : FixedFlowGateData g gi hC hK)
    (τ₀ cW CP CS CPQ M0 M1 M2 : ℝ) (hτ0 : 0 < τ₀) (hcW : 0 ≤ cW)
    (hM0n : 0 ≤ M0) (hM1n : 0 ≤ M1) (hM2n : 0 ≤ M2)
    (hCP : 0 ≤ CP) (hCS : 0 ≤ CS) (hCPQ : 0 ≤ CPQ)
    (hData : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      IsOpen (S z) ∧ (0 : Point n) ∈ S z ∧
      ∃ Pi : Point n → Fin n → ℝ, ∃ Q : Fin n → ℝ,
        (∀ x ∈ S z, ∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (Pi x k) (x i))
        ∧ (∀ k, HasDerivAt
            (fun s : ℝ => Pi (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
        ∧ (∀ x ∈ S z, PdiffAt (chartFieldAmp g gi hC hK D.a D.b τ z) i x)
        ∧ PdiffAt (chartFieldAmp g gi hC hK D.a D.b τ z) i (0 : Point n)
        ∧ PdiffAt (fun y => pd (chartFieldAmp g gi hC hK D.a D.b τ z) i y) i (0 : Point n)
        ∧ (∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k) ^ 2 ≤ cW * rncRadialSq z
        ∧ |∑ k, uniformInverseChart g gi hC hK z 0 k * Pi 0 k| ≤ CP
        ∧ |∑ k, Pi 0 k * Pi 0 k| ≤ CS
        ∧ |∑ k, uniformInverseChart g gi hC hK z 0 k * Q k| ≤ CPQ
        ∧ |chartFieldAmp g gi hC hK D.a D.b τ z 0| ≤ M0
        ∧ |pd (chartFieldAmp g gi hC hK D.a D.b τ z) i 0| ≤ M1
        ∧ |pd (fun y => pd (chartFieldAmp g gi hC hK D.a D.b τ z) i y) i 0| ≤ M2) :
    ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |witnessSecondXDeriv g gi hC hK S D.a D.b i τ z|
        ≤ (((CS + CPQ) * M0 / 2 + CP * M1 + M2 * τ₀)
            + cW * M0 / 4 * (rncRadialSq z / τ)) * τ⁻¹
            * gaussDdim τ (uniformInverseChart g gi hC hK z 0) :=
  witnessSecondXDeriv_hSecondEnv_uniform g gi hC hK S D.a D.b i D.r
    τ₀ cW CP CS CPQ M0 M1 M2 hτ0 hcW hM0n hM1n hM2n hCP hCS hCPQ hData

end QIQTH.WidthSecondEnvelopeUniform
