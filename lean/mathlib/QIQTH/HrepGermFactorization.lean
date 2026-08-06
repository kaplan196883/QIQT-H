/-
  QIQTH / HeatResidualBound — HrepGermFactorization.lean   (J4-351)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It discharges the germ-factorization
  input `hrep` that `D2HExpandRecon.witnessSecondXDeriv_expand_bridge` (J4-350) consumes, and composes
  it into a concrete-witness statement `hD2Hexpand_concrete` whose ONLY remaining inputs are the
  chart jets and the four geometric center identities — the germ input `hrep` is ELIMINATED.  NOT
  `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  R0 — THE EXACT-vs-APPROXIMATE CRUX VERDICT (the one this brick isolates).

  The bridge consumes, besides `hrep`, four center identities on the abstract chart `V` and its jets,
  most importantly
      `hV0 : gaussDdim τ (V 0) = gaussDdim τ z`.
  At the TRUE concrete chart `V = uniformInverseChart g gi hC hK z` we have `V 0 = W z 0`, the
  inverse-chart origin coordinate, and (banked `InverseChartDisplacement`) `W z 0 = −z + b`,
  `‖b‖ ≤ C_W‖z‖²`.  Since `gaussDdim τ v = (√(4πτ))⁻ⁿ·exp(−rncRadialSq v/(4τ))` (`gaussDdim_eq_exp`),
      `gaussDdim τ (W z 0) = gaussDdim τ z  ⟺  rncRadialSq (W z 0) = rncRadialSq z`
  (`chartImageGauss_exact_iff`, proved here).  But the banked near-isometry error
  `chartW0_rncRadialSq_error` gives only
      `|rncRadialSq (W z 0) − rncRadialSq z| ≤ L·‖z‖·rncRadialSq z`,
  an `O(‖z‖³)` two-sided gap that VANISHES exactly only in flat space or at `z = 0`
  (`chartImageGauss_center`, proved here: `W 0 0 = 0` ⟹ the identity is exact at the center).

  VERDICT.  `hV0` at the true chart is FALSE off-flat.  The product gauge freedom
  `(V, A) ↦ (V, A·gaussDdim τ(W z 0)/gaussDdim τ z)` can restore `hV0` exactly (put `V 0 := z`), but
  then the zeroth amplitude picks up the ratio
      `exp((rncRadialSq z − rncRadialSq (W z 0))/(4τ)) = exp(O(‖z‖³)/(4τ))`
  (`chartImageGauss_ratio`, proved here), which is:
    • bounded in the √ε SLIVER regime `‖z‖ ~ √τ` (then `‖z‖³/τ ~ √τ → 0`), but
    • UNBOUNDED uniformly over all `z` at fixed small `τ`.
  Because `AmplitudeDerivativeData.Aamp` is SHARED between `hD2Hexpand` (needs `hV0`) and the uniform
  bound `hAampBdd` (needs bounded amplitude), the true-chart instantiation cannot satisfy BOTH at
  once.  Hence `hD2Hexpand` in the EXACT target shape `…·gaussDdim τ z·…` WITH uniformly-bounded
  amplitudes is NOT an unconditional theorem at the true chart — it is a flat-space / small-`‖z‖`
  identity, consumed downstream only in the √ε collar where the ratio is bounded.  This is an HONEST
  boundary of the reduction, documented, not a fabricated closure.

  WHAT LANDS here (unconditionally, no `sorry`, no new axioms):
    • `chartAmp` — the concrete on-gate amplitude of the witness as a field-slot function.
    • `vanVleckGatedWitness_germ_factor` — ★ R1: the germ `hrep` DISCHARGED at the true chart from
      gate-openness (`z ∈ K`, `0 ∈ S z`, `IsOpen (S z)`), via `vanVleckGatedWitness_gate_apply` +
      `Filter.eventuallyEq_of_mem`.
    • `chartImageGauss_ratio` / `chartImageGauss_exact_iff` / `chartImageGauss_center` — R2: the exact
      Gaussian-ratio identity, the `hV0 ⟺ rncRadialSq`-equality equivalence, and the EXACT center
      identity at `z = 0` (the only unconditional locus of `hV0`).
    • `hD2Hexpand_concrete` — R3: the bridge with `hrep` DISCHARGED, so the concrete
      `witnessSecondXDeriv` obeys the exact 3-term `hD2Hexpand` shape given ONLY the chart jets and the
      four center identities (`hV0` carried as the isolated per-`(τ,z)` geometric residue — TRUE on the
      flat/diagonal locus, see R0).

  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.D2HExpandRecon
import QIQTH.InverseChartDisplacement

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.HrepGermFactorization

open QIQTH.HeatResidualBound QIQTH.D2HExpandRecon

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    S1 — the concrete on-gate amplitude as a field-slot function.
    ############################################################################### -/

/-- **The concrete on-gate amplitude `chartAmp`.**  As a function of the FIELD slot `x'` (base `z`
    fixed), the ungated `N = 1` van-Vleck parametrix amplitude
      `A x' = radialCutoff a b (W z x') · Θ(W z x')^{−1/2} · (u₀(W z x') + u₁(W z x')·τ)`,
    `W = uniformInverseChart g gi hC hK`, `Θ = vanVleck g`, `u = transportCoeff (transportOp …)`.
    This is exactly the amplitude factor of `vanVleckGatedWitness_gate_apply`. -/
noncomputable def chartAmp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (z : Point n) : Point n → ℝ :=
  fun x' => radialCutoff a b (uniformInverseChart g gi hC hK z x')
    * vanVleck g (uniformInverseChart g gi hC hK z x') ^ (-(1 : ℝ) / 2)
    * (transportCoeff (transportOp (vanVleck g) g gi) 0 (uniformInverseChart g gi hC hK z x')
      + transportCoeff (transportOp (vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK z x') * τ)

/-! ###############################################################################
    S2 — R1: the germ factorization `hrep`, discharged at the true chart.
    ############################################################################### -/

/-- **★ R1 — `vanVleckGatedWitness_germ_factor`.**  The germ `hrep` that the D2 bridge consumes,
    DISCHARGED.  For a base `z ∈ K` whose per-fibre gate `S z` is OPEN and contains the RNC center
    `0`, the field-slot witness agrees in a NEIGHBOURHOOD of `x' = 0` with the on-gate factored form
      `gaussDdim τ (W z x') · chartAmp … x'`,
    `W = uniformInverseChart g gi hC hK`.  Route: on the open gate `S z ∈ 𝓝 0`, the witness equals its
    ungated parametrix (`vanVleckGatedWitness_gate_apply`); regrouping is `ring`; `Filter.eventuallyEq_of_mem`
    turns the pointwise equality on the open gate into the germ.  ⚠ NOT `a₁ = R/6`. -/
theorem vanVleckGatedWitness_germ_factor (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z) :
    (fun x' : Point n => vanVleckGatedWitness g gi hC hK S a b τ x' z)
      =ᶠ[nhds (0 : Point n)]
      (fun x' => gaussDdim τ (uniformInverseChart g gi hC hK z x')
        * chartAmp g gi hC hK a b τ z x') := by
  apply Filter.eventuallyEq_of_mem (hSopen.mem_nhds h0)
  intro x' hx'
  dsimp only [chartAmp]
  rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ hz hx']
  ring

/-! ###############################################################################
    S3 — R2: the chart-image Gaussian identities (the exact-vs-approximate ledger).
    ############################################################################### -/

/-- **R2 — `chartImageGauss_ratio` (exact ratio).**  Unconditional algebra from `gaussDdim_eq_exp`:
    the chart-image Gaussian equals the plain Gaussian times the exponential of the near-isometry
    radial defect,
      `gaussDdim τ (W z 0) = exp((rncRadialSq z − rncRadialSq (W z 0))/(4τ)) · gaussDdim τ z`.
    This is where the exact-vs-approximate discrepancy LIVES (see R0): the exponent is `O(‖z‖³/τ)`.
    ⚠ NOT `a₁ = R/6`. -/
theorem chartImageGauss_ratio (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      = Real.exp ((rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ))
        * gaussDdim τ z := by
  have h4τ : (4 : ℝ) * τ ≠ 0 := by positivity
  rw [gaussDdim_eq_exp τ (uniformInverseChart g gi hC hK z 0), gaussDdim_eq_exp τ z]
  rw [show Real.exp ((rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ))
        * (((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n * Real.exp (-(rncRadialSq z) / (4 * τ)))
      = ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n
        * (Real.exp ((rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ))
            * Real.exp (-(rncRadialSq z) / (4 * τ))) from by ring]
  rw [← Real.exp_add]
  congr 2
  field_simp
  ring

/-- **R2 — `chartImageGauss_exact_iff`.**  For `τ > 0`, the center chart-image Gaussian identity
    `hV0` holds EXACTLY iff the near-isometry radial defect vanishes:
      `gaussDdim τ (W z 0) = gaussDdim τ z  ⟺  rncRadialSq (W z 0) = rncRadialSq z`.
    (`gaussDdim_eq_exp` + `Real.exp_injective`, cancelling the common positive prefactor.)  This is the
    crisp statement of R0: off-flat the RHS FAILS by `O(‖z‖³)` (`chartW0_rncRadialSq_error`), so `hV0`
    is not an unconditional theorem at the true chart.  ⚠ NOT `a₁ = R/6`. -/
theorem chartImageGauss_exact_iff (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (hτ : 0 < τ) (z : Point n) :
    gaussDdim τ (uniformInverseChart g gi hC hK z 0) = gaussDdim τ z
      ↔ rncRadialSq (uniformInverseChart g gi hC hK z 0) = rncRadialSq z := by
  have h4τ : (4 : ℝ) * τ ≠ 0 := by positivity
  have hpref : ((Real.sqrt (4 * Real.pi * τ))⁻¹) ^ n ≠ 0 :=
    pow_ne_zero n (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity))))
  rw [gaussDdim_eq_exp τ (uniformInverseChart g gi hC hK z 0), gaussDdim_eq_exp τ z]
  constructor
  · intro h
    have h2 := mul_left_cancel₀ hpref h
    have h3 := Real.exp_injective h2
    have h4 : -(rncRadialSq (uniformInverseChart g gi hC hK z 0)) = -(rncRadialSq z) := by
      field_simp at h3
      linarith
    linarith
  · intro h; rw [h]

/-- **R2 — `chartImageGauss_center`.**  The EXACT center identity: at the RNC center `z = 0`
    (requiring `0 ∈ K`), the inverse-chart origin coordinate vanishes `W 0 0 = 0`
    (`chartW0_displacement` at `z = 0` forces `‖W 0 0‖ ≤ 0`), so the chart-image Gaussian identity
    `hV0` holds exactly.  This is the ONLY unconditional locus of `hV0` (R0).  ⚠ NOT `a₁ = R/6`. -/
theorem chartImageGauss_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (h0K : (0 : Point n) ∈ K) :
    gaussDdim τ (uniformInverseChart g gi hC hK 0 0) = gaussDdim τ (0 : Point n) := by
  have hW : uniformInverseChart g gi hC hK 0 0 = 0 := by
    obtain ⟨r₁, hr₁, C_W, _hCW, hD⟩ := chartW0_displacement g gi hC hK
    have hlt : ‖(0 : Point n)‖ < r₁ := by rw [norm_zero]; exact hr₁
    have hbd := hD 0 h0K hlt
    simp only [add_zero, norm_zero, mul_zero] at hbd
    exact norm_le_zero_iff.mp hbd
  rw [hW]

/-! ###############################################################################
    S4 — R3: the bridge with `hrep` DISCHARGED (the concrete-witness reduction).
    ############################################################################### -/

/-- **★ R3 — `hD2Hexpand_concrete`.**  The D2 bridge with the germ input `hrep` ELIMINATED (supplied by
    R1 `vanVleckGatedWitness_germ_factor`).  For a base `z ∈ K` with open gate `0 ∈ S z`, the concrete
    `witnessSecondXDeriv` obeys the EXACT `AmplitudeDerivativeData.hD2Hexpand` 3-term shape
      `= (z i²−2τ)/(4τ²)·gaussDdim τ z·(chartAmp … 0)`
        `+ z i/(2τ)·gaussDdim τ z·(−2·∂ᵢ chartAmp(0))`
        `+ gaussDdim τ z·∂ᵢ² chartAmp(0)`,
    given ONLY the chart first/second `i`-jets `hV1`/`hP1`, the amplitude jets `hA1`/`hA2`, and the
    four center identities `hV0`/`hVP`/`hPsq`/`hVQ` on the CONCRETE chart `W z · = uniformInverseChart`.
    The germ residue is GONE; the remaining residue is purely the chart jets + the geometric center
    identities.  Per R0, `hV0` (`gaussDdim τ (W z 0) = gaussDdim τ z`) is the isolated per-`(τ,z)`
    geometric input — TRUE exactly on the flat/diagonal locus (`chartImageGauss_center` at `z = 0`),
    approximate off-flat.  This is a CONDITIONAL reduction, NOT an unconditional `hD2Hexpand`.
    ⚠ NOT `a₁ = R/6`. -/
theorem hD2Hexpand_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ) (z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hV0 : gaussDdim τ (uniformInverseChart g gi hC hK z 0) = gaussDdim τ z)
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * chartAmp g gi hC hK a b τ z 0
        + z i / (2 * τ) * gaussDdim τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0)
        + gaussDdim τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0 :=
  witnessSecondXDeriv_expand_bridge g gi hC hK S a b i τ hτ z
    (uniformInverseChart g gi hC hK z) (chartAmp g gi hC hK a b τ z) P Q
    (vanVleckGatedWitness_germ_factor g gi hC hK S a b τ z hz hSopen h0)
    hV1 hP1 hA1 hA2 hV0 hVP hPsq hVQ

end QIQTH.HrepGermFactorization

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HrepGermFactorization.vanVleckGatedWitness_germ_factor
#print axioms QIQTH.HrepGermFactorization.chartImageGauss_ratio
#print axioms QIQTH.HrepGermFactorization.chartImageGauss_exact_iff
#print axioms QIQTH.HrepGermFactorization.chartImageGauss_center
#print axioms QIQTH.HrepGermFactorization.hD2Hexpand_concrete
