import QIQTH.CurvedRNCBaseWitnessDomCollar
import QIQTH.ConcreteDominations
import QIQTH.NearIsometryBudget
import QIQTH.UniformChartRadius
import QIQTH.ConvApproximants
import QIQTH.WidthAdapters
import QIQTH.A1R6CoreAtGate

/-!
# J4-535 — the BASE-POINT-VARYING curved base-witness domination (`hAdom` + `hWDom` binders)

The J4-534 base-witness Gaussian domination `CurvedRNCBaseWitnessDomCollar.curvedRNC_baseWitness_dom_collar`
delivers, for the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`, `Ric(0)=(n−1)Kδ ≠ 0`),
the FULLY-DISCHARGED amplitude Gaussian domination at the FROZEN base point `p = 0` on the reach collar
`z ∈ Kset`, `‖z‖ < r`.  The `a₁ = R/6` trace capstone
`A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary`, however, consumes the
BASE-POINT-VARYING binder

```
hAdom : ∀ τ, 0 < τ → ∀ p q, |vanVleckGatedWitness g^K gi^K hChr hKset (constGate …) a b τ p q|
          ≤ (A₀ + A₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p − q)
```

together with the frozen `p = 0` window slice

```
hWDom : ∀ τ, 0 < τ → τ ≤ τ0fr → ∀ z, |vanVleckGatedWitness g^K gi^K hChr hKset (constGate …) a b τ 0 z|
          ≤ CW·gaussDdim (lam·τ) z .
```

This brick assembles BOTH, for `g^K`, on the constant-radius flow-ball gate `constGate g^K gi^K hChr hKset c`.

## Route (every step banked)

The witness unfolds definitionally (`ConvApproximants.vanVleckGatedWitness`) to the concrete gated
order-1 cutoff parametrix `gatedKernel Kset (constGate …) (globalCutoffParametrixWitnessN 1 (vanVleck g^K)
(transportCoeff (transportOp (vanVleck g^K) g^K gi^K)) a b (uniformInverseChart g^K gi^K hChr hKset))`.
Hence the **BANKED GENERIC recenter-of-domination lemma** `ConcreteDominations.exists_D1_constants_of_gateSqControl`
(the base-point-varying D1 domination for ANY concrete gated cutoff parametrix, given amplitude
smoothness + a `GateSqControl` certificate) produces the exact `hAdom` shape.  The two inputs, for `g^K`:

* **`GateSqControl` (base-point-varying, discharged)** — via `ConcreteDominations.gateSqControl_of_flowBall`
  from the ball-local UNIFORM-over-`Kset` near-isometry width budget `NearIsometryBudget.uniformFlowExp_hdisp_ball`
  (`3/2·rncRadialSq (φ_q v − q) ≤ 2·rncRadialSq v` for `‖v‖ < r₁`, all `q ∈ Kset`) and the chart-inverse
  germ `UniformChartRadius.uniformInverseChart_huniformChart` (`W_q (φ_q v) = v` on `‖v‖ < δ₀`).  Both
  hold for ANY smooth metric (need only `hChr`) and are UNIFORM in the base point `q` — this IS the
  base-point-varying content.  The gate radius `c := min r₁ (δ₀/2) > 0` makes both usable.
* **amplitude smoothness (`hw`, carried)** — `∀ k, ContDiff ℝ ⊤ (foldedCoeff (vanVleck g^K)
  (transportCoeff …) k)`, the SAME `hw` carried mainline-wide (never derived for the concrete
  van-Vleck coefficients); feeds the compact-support amplitude sups `exists_cutoff_foldedCoeff_bound`.

The `hWDom` conjunct is then the `p = 0` slice of `hAdom` on the window `τ ≤ τ0fr`: at `p = 0`,
`gaussDdim (3/2·τ) (0 − z) = gaussDdim (3/2·τ) z` (`WidthAdapters.gaussDdim_neg`, evenness), and the
affine amplitude `A₀ + A₁·τ ≤ A₀ + A₁·τ0fr =: CW/√(3/2)ⁿ` on the window.

## Honest scope

`K < 0` is genuinely curved (`curvedRNCMetric_ricci_trace_diag_ne`; satisfiability re-exported below,
`c = 4/5 ≠ ±1` real contraction — NOT the flat `W z = ±z`).  The GateSqControl is FULLY discharged
(base-point-varying, no collar/frozen restriction on `q`); the ONLY carried residual is the amplitude
smoothness `hw`, the mainline-standard van-Vleck coefficient regularity carry.  This lifts the frozen
`p = 0` collar domination #1 to the capstone's base-point-varying `hAdom`/`hWDom` binder shape.  It does
**not** derive the coefficient: `a₁ = R/6` still needs the entire heatOp/Levi/error-kernel domination
pile plus the Duhamel assembly and coefficient extraction, and remains CONDITIONAL and effectively
FLAT-ONLY.
-/

open QIQTH.Curvature QIQTH.RadialDistance QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.VanVleck QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.ResidueBound
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.FlatHeatEquation
open QIQTH.WidthAdapters QIQTH.A1R6CoreAtGate
open scoped BigOperators

namespace QIQTH.CurvedRNCBaseWitnessDomAdom

variable {n : ℕ}

/-- **★★★ J4-535 — `curvedRNC_baseWitness_dom_adom`.**  THE BASE-POINT-VARYING CURVED BASE-WITNESS
    DOMINATION.  For the genuinely-curved witness `g^K = curvedRNCMetric K` (`K < 0`), radii
    `0 < a < b`, a compact gate seed `Kset`, and a window cap `τ0fr > 0`, given ONLY the mainline
    amplitude-smoothness carry `hw` (`foldedCoeff (vanVleck g^K) (transportCoeff …) k ∈ C^∞`), there
    are affine constants `A₀, A₁ ≥ 0`, a gate radius `c > 0`, and window constants `CW ≥ 0`, `lam > 0`
    such that the gated van-Vleck witness on the constant-radius flow-ball gate `constGate g^K gi^K
    hChr hKset c` satisfies BOTH:

    * `hAdom` (base-point-varying): `∀ τ > 0, ∀ p q,
        |vanVleckGatedWitness … τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim ((3/2)τ) (p−q)`;
    * `hWDom` (frozen `p=0` window): `∀ τ ∈ (0,τ0fr], ∀ z,
        |vanVleckGatedWitness … τ 0 z| ≤ CW·gaussDdim (lam·τ) z`.

    Both are the EXACT binders `a1_R6_from_labelled_curved_boundary` consumes.  The `GateSqControl`
    certificate is fully discharged (base-point-varying, via the uniform near-isometry `uniformFlowExp_hdisp_ball`
    + chart-inverse germ), and `hAdom` follows from the banked generic recenter-of-domination
    `exists_D1_constants_of_gateSqControl`; `hWDom` is its `p=0` window slice (`gaussDdim_neg`).  The
    sole carried residual is the amplitude smoothness `hw`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_baseWitness_dom_adom
    (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (τ0fr : ℝ) (hτ0fr : 0 < τ0fr)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric K))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
          (curvedRNCMetric K) (curvedRNCInv K))) k : Point n → ℝ)) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧ ∃ c > (0 : ℝ), ∃ CW lam : ℝ, 0 ≤ CW ∧ 0 < lam ∧
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
            (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ τ0fr → ∀ z : Point n,
        |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
            (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z|
          ≤ CW * gaussDdim (lam * τ) z) := by
  -- ── the two banked UNIFORM-over-`Kset` flow-ball radii.
  obtain ⟨r₁, hr₁pos, hdisp⟩ :=
    uniformFlowExp_hdisp_ball (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
  obtain ⟨δ₀, hδ₀pos, hchart⟩ :=
    uniformInverseChart_huniformChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
  -- the gate radius usable for BOTH the chart inverse (`< δ₀`) and the near-isometry (`≤ r₁`).
  set c : ℝ := min r₁ (δ₀ / 2) with hcdef
  have hc0 : 0 < c := lt_min hr₁pos (half_pos hδ₀pos)
  have hcr₁ : c ≤ r₁ := min_le_left _ _
  have hcδ₀ : c < δ₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- ── chart-inverse property `W_q (φ_q v) = v` on the collar `‖v‖ < c`, all `q ∈ Kset`.
  have hinv : ∀ q ∈ Kset, ∀ v : Point n, ‖v‖ < c →
      uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset q
          (uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset q v) = v := by
    intro q hq v hv
    obtain ⟨hgerms, _⟩ := hchart q hq
    obtain ⟨hgerm, _⟩ := hgerms v (lt_trans hv hcδ₀)
    simpa using hgerm.eq_of_nhds
  -- ── the base-point-varying `GateSqControl`, fully discharged.
  have hgate : GateSqControl Kset
      (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c)
      (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset) :=
    gateSqControl_of_flowBall Kset
      (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset)
      (uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset) c r₁ hcr₁ hinv hdisp
  -- ── the banked GENERIC recenter-of-domination: base-point-varying D1 for the concrete gated witness.
  obtain ⟨A₀, A₁, hA₀, hA₁, hdom⟩ :=
    exists_D1_constants_of_gateSqControl (vanVleck (curvedRNCMetric K))
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric K))
        (curvedRNCMetric K) (curvedRNCInv K)))
      a b (uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset)
      Kset (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) ha hab hw hgate
  -- window constants for `hWDom`.
  refine ⟨A₀, A₁, hA₀, hA₁, c, hc0,
    (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n, 3 / 2,
    mul_nonneg (add_nonneg hA₀ (mul_nonneg hA₁ hτ0fr.le)) (pow_nonneg (Real.sqrt_nonneg _) n),
    by norm_num, ?_, ?_⟩
  · -- `hAdom`: the base-point-varying binder — DEFINITIONALLY the D1 conclusion.
    intro τ hτ p q
    exact hdom τ p q hτ
  · -- `hWDom`: the frozen `p = 0` window slice of `hAdom`.
    intro τ hτ hτle z
    have hz := hdom τ (0 : Point n) z hτ
    rw [zero_sub, gaussDdim_neg] at hz
    have hstep : (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n
        ≤ (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) n)
      have := mul_le_mul_of_nonneg_left hτle hA₁
      linarith
    calc |vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
              (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z := hz
      _ ≤ (A₀ + A₁ * τ0fr) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) z :=
          mul_le_mul_of_nonneg_right hstep (gaussDdim_nonneg _ _)

/-- **★ J4-535 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  Re-exports the J4-534 radial-squeeze
    witness: the phase/near-isometry budget underlying the discharged domination is inhabited by a
    GENUINELY radially-distorting map `W z = c·z`, `c = 4/5 ≠ ±1`, for every `z`.  So the base-point-varying
    domination tolerates the real curved-normal-coordinate contraction and is NOT the flat `W z = ±z`.
    Curved-inhabited.  NOT `a₁ = R/6`. -/
theorem curvedRNC_baseWitness_dom_adom_curved_satisfiable :
    ∃ c : ℝ, c ≠ 1 ∧ c ≠ -1 ∧ ∀ z : Point n,
      (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (fun i => c * z i) :=
  QIQTH.CurvedRNCBaseWitnessDomCollar.curvedRNC_baseWitness_dom_collar_curved_satisfiable

end QIQTH.CurvedRNCBaseWitnessDomAdom

section AxiomChecks
open QIQTH.CurvedRNCBaseWitnessDomAdom
#print axioms curvedRNC_baseWitness_dom_adom
#print axioms curvedRNC_baseWitness_dom_adom_curved_satisfiable
end AxiomChecks
