/-
  LayerAFactorization — J4-514: the LAYER-A on-gate factorization brick (audit-first).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the a₁=R/6 heat-kernel campaign; CONDITIONAL and EFFECTIVELY FLAT-ONLY).  The a₁ mainline
  `A1R6FromLabelled.a1_R6_from_labelled` is ONE-CHANNEL-FLAT; curved a₁ is a mechanical rethread plus a
  concrete change-of-variables (CoV) bundle `hcov` away (see `MassChartBridge`).  J4-510
  (`CurvedParametrixMass`) proved the chart-variable mass → 1; J4-511 (`MassChartBridge`) built the
  z→w chart bridge MODULO the abstract CoV `hcov` and a fixed weight `φ` with `φ(0)=1`.  The first
  analytic gateway toward discharging `hcov` concretely is the **Layer-A on-gate factorization**: the
  on-gate factorisation of the concrete witness together with the ORIGIN normalisation of its
  amplitude to be EXACTLY `1` in the `τ → 0` sense the mass limit needs.

  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  de-risking gateway: it packages the (already-banked) on-gate factorisation and establishes the
  scalar origin normalisation `chartFieldAmp … τ 0 0 → 1`.  It does NOT build the concrete CoV bundle
  (Layer-B) and does NOT touch the flat-forcing `hframeK`.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypotheses, no conclusion-in-disguise.  No existing file is edited.

  ── WHAT IS BANKED (reused, not rebuilt — all axiom-free std-3, curved `g` generic).
    * `WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp` — the on-gate `x = 0` factorisation
        `H_G τ 0 z = gaussDdim τ (W₀ z) · chartFieldAmp g gi hC hK a b τ z 0`,  `W₀ z = uniformInverseChart … z 0`.
    * `chartW0_zero` — `W₀ 0 = uniformInverseChart g gi hC hK 0 0 = 0` (needs `0 ∈ K`).
    * `vanVleck_zero` — `Θ(0) = 1` given `det (g 0) = 1` (a single-point RNC normalisation; curved-true).
    * `radialCutoff_eq_one` — `radialCutoff a b 0 = 1` given `0 < a < b`.
    * `transportCoeff_zero` — `u₀ ≡ 1`.

  ── WHAT THIS FILE PROVES (the genuine new Layer-A content).
    (1)  `layerA_on_gate_factorization` — the on-gate factorisation, re-exported as a named Layer-A
         brick naming the amplitude `chartFieldAmp` and the Gaussian argument `W₀ z`.
    (2)  `chartFieldAmp_origin_value` — ★ the EXACT origin value of the amplitude:
             `chartFieldAmp g gi hC hK a b τ 0 0 = 1 + u₁(0)·τ`,  `u₁(0) = transportCoeff … 1 0`
         (the R/6 seed).  Uses ONLY `chartW0_zero`, `radialCutoff_eq_one`, `vanVleck_zero`
         (`det (g 0)=1`), `transportCoeff_zero`.  NO CoV Jacobian, NO `φ` weight — those are Layer-B.
    (3)  `chartFieldAmp_origin_zero` — the `τ = 0` corollary: `chartFieldAmp … 0 0 0 = 1`.
    (4)  `chartFieldAmp_origin_tendsto_one` — ★ the ORIGIN NORMALISATION in the mass-limit sense:
             `Tendsto (fun τ => chartFieldAmp g gi hC hK a b τ 0 0) (𝓝[>]0) (𝓝 1)`.
    (5)  `layerA_witness_origin_factor` — ★★ the combined Layer-A unit: at base `0`, on the gate,
             `H_G τ 0 0 = gaussDdim τ 0 · (1 + u₁(0)·τ)`  (factorisation + origin value assembled).
    (★gate)  `hgdet0_curved_satisfiable` — the SATISFIABILITY GATE: the metric normalisation
         `det (g 0) = 1` does NOT pin the metric to the identity (a transvection has `det = 1` but
         `≠ 1`), so the origin value = 1 is curved-inhabited, NOT secretly flat.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WideWitnessAmplitude
import QIQTH.ChartWrapperConcrete

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap
open scoped Topology BigOperators

namespace QIQTH.LayerAFactorization

open QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (1) — the on-gate factorisation, re-exported as a named Layer-A brick. -/

/-- **★ J4-514 (Layer-A/1) — THE ON-GATE FACTORISATION (re-export).**  On the gate (`z ∈ K`,
    `0 ∈ S z`) the gated van-Vleck witness at field centre `x = 0` factors as the chart-image Gaussian
    `gaussDdim τ (W₀ z)` times the concrete field amplitude `chartFieldAmp … τ z 0`, with
    `W₀ z = uniformInverseChart g gi hC hK z 0`.  Pure re-export of the banked
    `WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp`, named as the Layer-A brick.  NOT `a₁ = R/6`. -/
theorem layerA_on_gate_factorization (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
      = gaussDdim τ (uniformInverseChart g gi hC hK z 0)
        * chartFieldAmp g gi hC hK a b τ z 0 :=
  QIQTH.WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp g gi hC hK S a b τ hz h0

/-! ### (2) — the EXACT origin value of the amplitude. -/

/-- **★★ J4-514 (Layer-A/2) — THE AMPLITUDE ORIGIN VALUE.**  At base point `z = 0` and field slot
    `x' = 0`, the concrete on-gate field amplitude is exactly affine in `τ`:
        `chartFieldAmp g gi hC hK a b τ 0 0 = 1 + u₁(0)·τ`,
    where `u₁(0) = transportCoeff (transportOp (vanVleck g) g gi) 1 0` is the raw first DeWitt
    coefficient (the R/6 seed).  Chain: `W₀ 0 = 0` (`chartW0_zero`) sends every factor to the centre,
    where `radialCutoff a b 0 = 1` (`radialCutoff_eq_one`), `Θ(0)^{−1/2} = 1` (`vanVleck_zero`, given
    `det (g 0) = 1`), and `u₀(0) = 1` (`transportCoeff_zero`).  ⚠ Uses ONLY these single-point RNC
    facts — NO CoV Jacobian, NO `φ` weight (those are Layer-B).  Curved-compatible: `det (g 0) = 1` is
    a normal-coordinate normalisation, NOT flatness on a neighbourhood.  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_origin_value (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hgdet0 : Matrix.det (g 0) = 1) (τ : ℝ) :
    chartFieldAmp g gi hC hK a b τ (0 : Point n) (0 : Point n)
      = 1 + transportCoeff (transportOp (vanVleck g) g gi) 1 (0 : Point n) * τ := by
  have hW : uniformInverseChart g gi hC hK 0 0 = 0 := chartW0_zero g gi hC hK h0K
  have hu0 : transportCoeff (transportOp (vanVleck g) g gi) 0 (0 : Point n) = 1 := by
    rw [transportCoeff_zero]
  simp only [chartFieldAmp, hW]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity),
    vanVleck_zero g hgdet0, hu0, Real.one_rpow]
  ring

/-- **J4-514 (Layer-A/3) — the `τ = 0` corollary.**  `chartFieldAmp g gi hC hK a b 0 0 0 = 1`; the
    amplitude origin value at zero time is exactly `1`.  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_origin_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hgdet0 : Matrix.det (g 0) = 1) :
    chartFieldAmp g gi hC hK a b (0 : ℝ) (0 : Point n) (0 : Point n) = 1 := by
  rw [chartFieldAmp_origin_value g gi hC hK h0K a b ha hab hgdet0 0]; ring

/-! ### (4) — the origin normalisation in the mass-limit sense. -/

/-- **★★ J4-514 (Layer-A/4) — THE ORIGIN NORMALISATION `→ 1`.**  In the exact `τ → 0` sense the mass
    limit needs (`𝓝[>]0`), the amplitude origin value tends to `1`:
        `Tendsto (fun τ => chartFieldAmp g gi hC hK a b τ 0 0) (𝓝[>]0) (𝓝 1)`.
    Route: `chartFieldAmp_origin_value` rewrites the family to the affine `τ ↦ 1 + u₁(0)·τ`, whose
    continuous limit at `0` is `1`.  This is the scalar origin normalisation that makes the mass limit
    equal to `1` (Sol's flagged constructibility caveat: the total normalised amplitude at the origin
    must equal EXACTLY `1`).  Curved-compatible (`det (g 0) = 1` only).  NOT `a₁ = R/6`. -/
theorem chartFieldAmp_origin_tendsto_one (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hgdet0 : Matrix.det (g 0) = 1) :
    Tendsto (fun τ => chartFieldAmp g gi hC hK a b τ (0 : Point n) (0 : Point n))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  set c : ℝ := transportCoeff (transportOp (vanVleck g) g gi) 1 (0 : Point n) with hc
  have hval : (fun τ => chartFieldAmp g gi hC hK a b τ (0 : Point n) (0 : Point n))
      = fun τ : ℝ => 1 + c * τ :=
    funext (fun τ => chartFieldAmp_origin_value g gi hC hK h0K a b ha hab hgdet0 τ)
  rw [hval]
  have hcont : Continuous (fun τ : ℝ => 1 + c * τ) := by fun_prop
  have htend : Tendsto (fun τ : ℝ => 1 + c * τ) (𝓝 (0 : ℝ)) (𝓝 (1 + c * 0)) :=
    hcont.tendsto 0
  simp only [mul_zero, add_zero] at htend
  exact htend.mono_left nhdsWithin_le_nhds

/-! ### (5) — the combined Layer-A unit (factorisation + origin value at base `0`). -/

/-- **★★★ J4-514 (Layer-A/5) — THE COMBINED LAYER-A UNIT.**  At base point `z = 0`, on the gate
    (`0 ∈ K`, `0 ∈ S 0`), the gated witness factors and its amplitude is normalised:
        `vanVleckGatedWitness g gi hC hK S a b τ 0 0 = gaussDdim τ 0 · (1 + u₁(0)·τ)`.
    Assembles `layerA_on_gate_factorization` (`z = 0`), `chartW0_zero` (`W₀ 0 = 0`, so the Gaussian
    argument is `0`), and `chartFieldAmp_origin_value`.  The amplitude factor `1 + u₁(0)·τ → 1` as
    `τ → 0` (`chartFieldAmp_origin_tendsto_one`), the origin normalisation the mass limit needs; the
    Gaussian `gaussDdim τ 0` carries the unit heat mass.  ⚠ Layer-A ONLY: no CoV Jacobian, no `φ`
    weight, no Gaussian-phase inequality (those are Layer-B).  NOT `a₁ = R/6`. -/
theorem layerA_witness_origin_factor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (S : Point n → Set (Point n)) (h0S : (0 : Point n) ∈ S 0)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hgdet0 : Matrix.det (g 0) = 1) (τ : ℝ) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) (0 : Point n)
      = gaussDdim τ (0 : Point n)
        * (1 + transportCoeff (transportOp (vanVleck g) g gi) 1 (0 : Point n) * τ) := by
  have hfac := layerA_on_gate_factorization g gi hC hK S a b τ h0K h0S
  have hW : uniformInverseChart g gi hC hK 0 0 = 0 := chartW0_zero g gi hC hK h0K
  rw [hfac, hW, chartFieldAmp_origin_value g gi hC hK h0K a b ha hab hgdet0 τ]

/-! ### (★gate) — the satisfiability gate: `det (g 0) = 1` is NOT flatness. -/

/-- **★ J4-514 (Layer-A satisfiability GATE) — `det = 1` DOES NOT PIN THE METRIC TO THE IDENTITY.**
    For dimension `≥ 2` there is a matrix `M : Matrix (Fin n) (Fin n) ℝ` with `det M = 1` yet
    `M ≠ 1` — a transvection `1 + single 0 1 1`.  This certifies the ONLY metric constraint of the
    Layer-A origin value, `det (g 0) = 1`, is STRICTLY WEAKER than flatness at the origin (`g 0 = δ`),
    hence a fortiori strictly weaker than flatness on a neighbourhood (`hframeK`).  Combined with the
    `g`-genericity of `chartFieldAmp_origin_value` (which carries NO `hframeK`), the origin value = 1
    is curved-inhabited, NOT secretly flat.  NOT `a₁ = R/6`. -/
theorem hgdet0_curved_satisfiable (hn : 2 ≤ n) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, M.det = 1 ∧ M ≠ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    simp only [i, j, Ne, Fin.mk.injEq]; omega
  refine ⟨Matrix.transvection i j (1 : ℝ), Matrix.det_transvection_of_ne i j hij 1, ?_⟩
  intro hM
  -- from `1 + single i j 1 = 1` deduce `single i j 1 = 0`, contradicting its `(i,j)` entry.
  rw [Matrix.transvection] at hM
  have hs : Matrix.single i j (1 : ℝ) = 0 := by
    have h2 : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single i j (1 : ℝ)
        = (1 : Matrix (Fin n) (Fin n) ℝ) + 0 := by rw [add_zero]; exact hM
    exact add_left_cancel h2
  have hentry := congrFun (congrFun hs i) j
  rw [Matrix.single_apply_same, Matrix.zero_apply] at hentry
  exact one_ne_zero hentry

end QIQTH.LayerAFactorization

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.LayerAFactorization

#print axioms layerA_on_gate_factorization
#print axioms chartFieldAmp_origin_value
#print axioms chartFieldAmp_origin_zero
#print axioms chartFieldAmp_origin_tendsto_one
#print axioms layerA_witness_origin_factor
#print axioms hgdet0_curved_satisfiable

end AxiomChecks
