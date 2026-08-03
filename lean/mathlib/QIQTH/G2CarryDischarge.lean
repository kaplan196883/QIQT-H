/-
  G2CarryDischarge — J4-163: concrete discharge of several of the SIX carries that
  `QIQTH.WitnessDerivMeasurability.g2_bundle_assembled` (J4-160/161/162) consumes for the concrete
  first-derivative kernel `dH := witnessFieldDeriv` of the gated `N = 1` van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It takes the SIX
  labelled carries of `g2_bundle_assembled` (`hC2fam`, `henv`, `hKmeas`, `hFmeas`, `hjoint`, `hdomS`)
  and discharges / reduces as many as possible CONCRETELY from banked facts, replacing heavier
  carries with strictly lighter, satisfiable, non-vacuous ones.  Never the conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    ● THE GEOMETRIC ENVELOPE CORE (real math for carry `henv` / `hdomS`).
      • `gaussDdim_coercivity_envelope` — ★ THE x-FREE GAUSSIAN ENVELOPE.  For `τ > 0` and any two
          points `w`, `base` with the near-isometry COERCIVITY `½·r²_base ≤ r²_w`
          (`r² = rncRadialSq`),
            `G_τ(w) ≤ (√2)^n · G_{2τ}(base)`,
          with the constant `(√2)^n` and width `2τ` BOTH `base`/`w`-free.  Route: `gaussDdim_eq_Gk`,
          the radial antitonicity `Gk_anti` at `r²_w ≥ ½·r²_base`, then the scaled-width identity
          `Gk_scaled` (`s = ½`, `(√½)⁻¹ = √2`, `τ/(½) = 2τ`).  This is the standalone `≤`-form of the
          `hhalf` step inside `GaussianMomentEnvelope.gaussDdim_replace_bound`.
      • `witnessFieldDeriv_gate_envelope_coercive` — plugs the geometric envelope into
          `WitnessDerivDomination.witnessFieldDeriv_gate_envelope`, giving the on-gate x-free bound
            `|dH i τ p z| ≤ ((Bs·Ba+Bd)·(√2)^n)·G_{2τ}(z)`
          from the E2 factor sup-bounds + the pure-geometry chart coercivity
          `½·r²_z ≤ r²_{W z p}` (the `InverseChartDisplacement` near-isometry output at field point
          `p`).  The carry `hgauss_env` of `witnessFieldDeriv_gate_envelope` is thereby REPLACED by
          the proved geometric envelope + a coercivity hypothesis.

    ● CARRY 6 — `hdomS` (REDUCED to the x-uniform bare envelope).
      • `hdomS_from_uniform` — ★ THE REORDER.  From an x-UNIFORM bare-kernel envelope `henvU`
          (`∀ᶠ x` OUTSIDE the `∀ᵐ s`, no `F` factor) plus the scalar sup-bound `|F| ≤ Cf`, the EXACT
          `hdomS` shape (`∀ᶠ x → ∀ᵐ s → ∀ᵐ z`, F-weighted) follows by pure `filter_upwards` + the
          `mul_le_mul` F-weighting.  `hdomS` (itself a carry of the bundle) is thereby reduced to the
          uniform bare envelope `henvU` — strictly lighter (no `F`, no integral), satisfiable from the
          x-free `witnessFieldDeriv_gate_envelope_coercive` (whose bound is x-free, hence the
          neighbourhood is uniform in `s`).

    ● CARRY 3 — `hKmeas` (REDUCED to witness z-measurability + field-slice differentiability).
      • `pd_aestronglyMeasurable_of_slice` — ★ THE GENERAL MEASURABILITY LEVER (reusable).  For a
          two-variable `H : ℝ → Point n → ℝ` whose every field-slice `z ↦ H w z` is
          `AEStronglyMeasurable` and whose line `w ↦ H w z` has a derivative `d z` at `a` for a.e.
          `z`, the derivative `d` is `AEStronglyMeasurable`.  Route: `d z` is the `atTop` limit of the
          measurable difference quotients `slope (H · z) a (a + 1/(k+1))` (each a `const_smul` of a
          difference of measurables), via `hasDerivAt_iff_tendsto_slope` composed with
          `a + 1/(k+1) → a` within `{≠ a}`, then `aestronglyMeasurable_of_tendsto_ae`.
      • `hKmeas_from_witness` — the EXACT `hKmeas` shape, reduced (via the lever) to the two lighter
          carries `hWmeas` (z-ae-measurability of the WITNESS `z ↦ H_G τ (update x i w) z`, for all
          field shifts `w`) and `hWdiff` (field-slice differentiability of the witness to the
          derivative kernel).  Both are strictly weaker than / different from the DERIVATIVE
          measurability they produce.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hC2fam` — the field-slot `ContDiffAt ℝ 2` family of the gated witness at a general centre
      `x₀ ∈ u` and general base `z`.  `SpatialC2.hCH_discharge` proves exactly this at the field
      CENTRE (`p = 0`, `z = 0`); the general-centre/general-base version is the honest regularity
      input (strictly stronger than, different from, the continuity conclusion).  UNTOUCHED here.
    • `hFmeas` — z-ae-measurability of each `F`-slice `z ↦ F s z`; a property of the source term `F`,
      discharged at instantiation where `F` is explicit.  UNTOUCHED here.
    • `hjoint` — joint `(s,z)`-ae-measurability of `(s,z) ↦ dH·F`.  A genuine joint-measurability
      input on the product measure (the `s`-parametrised derivative family measured jointly); the
      `hKmeas`-style lever does not directly transfer because `s` enters the kernel through the width
      `τ = t − s`.  CARRIED (satisfiable from the same gate/Gaussian/amplitude structure measured
      jointly, exactly as `hKmeas`); not reduced here.
    • `hWmeas`, `hWdiff` (new, lighter) — the reductions of `hKmeas` above; satisfiable from the
      on-gate factorisation `H_G = G_τ(W·)·A` (a measurable-set-glued product of measurables) and the
      field-slot regularity of the gated witness, respectively.
    • `henvU` (new, lighter) — the x-uniform bare-kernel envelope; GROUNDED in
      `witnessFieldDeriv_gate_envelope_coercive` (x-free bound ⟹ uniform neighbourhood).

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessDerivDomination
import QIQTH.ChartGaussAdapter

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination
open scoped Interval Topology BigOperators

namespace QIQTH.G2CarryDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE GEOMETRIC ENVELOPE CORE (real math for `henv` / `hdomS`).
    ############################################################################### -/

/-- **★ `gaussDdim_coercivity_envelope`.**  THE x-FREE GAUSSIAN ENVELOPE.  For `τ > 0` and any two
    points `w`, `base` with the near-isometry COERCIVITY `½·r²_base ≤ r²_w` (`r² = rncRadialSq`),
      `G_τ(w) ≤ (√2)^n · G_{2τ}(base)`,
    with the constant `(√2)^n` and the width `2τ` BOTH `w`/`base`-free.  Route:
    `gaussDdim_eq_Gk`, the radial antitonicity `Gk_anti` (`r²_w ≥ ½·r²_base`), then the scaled-width
    identity `Gk_scaled` (`s = ½`, `(√½)⁻¹ = √2`, `τ/(½) = 2τ`).  The standalone `≤`-form of the
    `hhalf` step in `GaussianMomentEnvelope.gaussDdim_replace_bound`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_coercivity_envelope (τ : ℝ) (hτ : 0 < τ) (w base : Point n)
    (hmin : (1 / 2 : ℝ) * rncRadialSq base ≤ rncRadialSq w) :
    gaussDdim τ w ≤ (Real.sqrt 2) ^ n * gaussDdim (2 * τ) base := by
  rw [gaussDdim_eq_Gk τ w]
  have hstep : Gk n τ (rncRadialSq w) ≤ Gk n τ ((1 / 2 : ℝ) * rncRadialSq base) :=
    Gk_anti τ hτ hmin
  have hs2 : (Real.sqrt (1 / 2))⁻¹ = Real.sqrt 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ from by norm_num, Real.sqrt_inv, inv_inv]
  have hscaled : Gk n τ ((1 / 2 : ℝ) * rncRadialSq base)
      = (Real.sqrt 2) ^ n * gaussDdim (2 * τ) base := by
    rw [Gk_scaled (1 / 2) τ (by norm_num) hτ base, hs2, show τ / (1 / 2) = 2 * τ from by ring]
  rw [hscaled] at hstep
  exact hstep

/-- **`witnessFieldDeriv_gate_envelope_coercive`.**  The on-gate x-free Gaussian domination of the
    first-derivative kernel with the concrete constant `(Bs·Ba+Bd)·(√2)^n` and width `2τ`, obtained
    by feeding `gaussDdim_coercivity_envelope` (with `w := W z p`, `base := z`) into
    `WitnessDerivDomination.witnessFieldDeriv_gate_envelope`.  The chart-Gaussian carry `hgauss_env`
    of the latter is thereby REPLACED by the proved geometric envelope + the pure-geometry chart
    coercivity `½·r²_z ≤ r²_{W z p}` (the `InverseChartDisplacement` near-isometry).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gate_envelope_coercive (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (Bs Ba Bd : ℝ)
    (hSc : |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ))| ≤ Bs)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (hmin : (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z p)) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) * gaussDdim (2 * τ) z :=
  witnessFieldDeriv_gate_envelope g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV hAmp1
    Bs Ba Bd hSc hBa hBd (2 * τ) ((Real.sqrt 2) ^ n)
    (gaussDdim_coercivity_envelope τ hτ (uniformInverseChart g gi hC hK z p) z hmin)

/-! ###############################################################################
    ### CARRY 6 — `hdomS` reorder from the x-uniform bare envelope.
    ############################################################################### -/

/-- **★ `hdomS_from_uniform`.**  THE `hdomS` REORDER.  From an x-UNIFORM bare-kernel Gaussian envelope
    `henvU` (`∀ᶠ x` OUTSIDE the `∀ᵐ s`, NO `F` factor) and the scalar sup-bound `|F| ≤ Cf`, the EXACT
    `hdomS` slot of `g2_bundle_assembled` (`∀ᶠ x → ∀ᵐ s → ∀ᵐ z`, F-weighted, dominator
    `(C₀·Cf)·G_{κ(t−s)}(z)`) follows by pure `filter_upwards` + the `mul_le_mul` F-weighting.  `hdomS`
    is thereby reduced to `henvU` — strictly lighter (no `F`, no integral), satisfiable from the
    x-free `witnessFieldDeriv_gate_envelope_coercive`.  NOT `a₁ = R/6`. -/
theorem hdomS_from_uniform (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (u : Set (Point n))
    (κ C₀ Cf : ℝ) (hC₀ : 0 ≤ C₀)
    (hFbd : ∀ s z, |F s z| ≤ Cf)
    (henvU : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂(volume : Measure (Point n)),
          |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| ≤ C₀ * gaussDdim (κ * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᵐ z ∂(volume : Measure (Point n)),
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ (C₀ * Cf) * gaussDdim (κ * (t - s)) z := by
  intro x₀ hx₀ i
  filter_upwards [henvU x₀ hx₀ i] with x hx
  filter_upwards [hx] with s hs hmem
  filter_upwards [hs hmem] with z hz
  have hGnn : 0 ≤ gaussDdim (κ * (t - s)) z := gaussDdim_nonneg _ _
  rw [Real.norm_eq_abs, abs_mul]
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C₀ * gaussDdim (κ * (t - s)) z) * Cf :=
        mul_le_mul hz (hFbd s z) (abs_nonneg _) (mul_nonneg hC₀ hGnn)
    _ = (C₀ * Cf) * gaussDdim (κ * (t - s)) z := by ring

/-! ###############################################################################
    ### CARRY 3 — `hKmeas` reduction: the measurability lever + concrete wrapper.
    ############################################################################### -/

/-- **★ `pd_aestronglyMeasurable_of_slice` — THE GENERAL MEASURABILITY LEVER.**  For a two-variable
    `H : ℝ → Point n → ℝ` whose every field-slice `z ↦ H w z` is `AEStronglyMeasurable` and whose line
    `w ↦ H w z` has a derivative `d z` at `a` for a.e. `z`, the derivative `d` is
    `AEStronglyMeasurable`.  `d z` is the `atTop` limit of the measurable difference quotients
    `slope (H · z) a (a + 1/(k+1))` (each a `const`-divided difference of `AEStronglyMeasurable`
    slices) via `hasDerivAt_iff_tendsto_slope` composed with `a + 1/(k+1) → a` inside `{≠ a}`, then
    `aestronglyMeasurable_of_tendsto_ae`.  NOT `a₁ = R/6`. -/
theorem pd_aestronglyMeasurable_of_slice (H : ℝ → Point n → ℝ) (d : Point n → ℝ) (a : ℝ)
    (ν : Measure (Point n))
    (hmeas : ∀ w : ℝ, AEStronglyMeasurable (fun z => H w z) ν)
    (hderiv : ∀ᵐ z ∂ν, HasDerivAt (fun w => H w z) (d z) a) :
    AEStronglyMeasurable d ν := by
  -- the sequence `w k = a + 1/(k+1) → a` inside `{≠ a}`.
  have ha : Tendsto (fun k : ℕ => a + 1 / ((k : ℝ) + 1)) atTop (𝓝 a) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add a
  have hne : ∀ᶠ (k : ℕ) in atTop, (a + 1 / ((k : ℝ) + 1)) ∈ ({a}ᶜ : Set ℝ) := by
    filter_upwards with k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; linarith
  have hwk : Tendsto (fun k : ℕ => a + 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha hne
  -- each difference quotient (in `z`) is `AEStronglyMeasurable`.
  have hf_meas : ∀ k : ℕ,
      AEStronglyMeasurable (fun z => slope (fun w => H w z) a (a + 1 / ((k : ℝ) + 1))) ν := by
    intro k
    have hrw : (fun z => slope (fun w => H w z) a (a + 1 / ((k : ℝ) + 1)))
        = (fun z => ((a + 1 / ((k : ℝ) + 1)) - a)⁻¹ • (H (a + 1 / ((k : ℝ) + 1)) z - H a z)) := by
      funext z; rw [slope_def_module]
    rw [hrw]
    exact ((hmeas (a + 1 / ((k : ℝ) + 1))).sub (hmeas a)).const_smul
      (((a + 1 / ((k : ℝ) + 1)) - a)⁻¹)
  -- a.e.-`z` convergence of the quotients to `d z`.
  have hlim : ∀ᵐ z ∂ν,
      Tendsto (fun k : ℕ => slope (fun w => H w z) a (a + 1 / ((k : ℝ) + 1))) atTop (𝓝 (d z)) := by
    filter_upwards [hderiv] with z hz
    exact (hz.tendsto_slope).comp hwk
  exact aestronglyMeasurable_of_tendsto_ae atTop hf_meas hlim

/-- **`hKmeas_from_witness`.**  THE EXACT `hKmeas` SLOT of `g2_bundle_assembled`, reduced (via
    `pd_aestronglyMeasurable_of_slice`) to two strictly lighter carries: `hWmeas` — the z-ae-
    measurability of the WITNESS field-slices `z ↦ H_G (t−s) (update x i w) z` for every field shift
    `w` — and `hWdiff` — the field-slice differentiability of the witness to the derivative kernel
    (`HasDerivAt (fun w ↦ H_G (t−s) (update x i w) z) (witnessFieldDeriv … x z) (x i)`).  Both are
    about the WITNESS (0-th slot), strictly weaker than / different from the DERIVATIVE-kernel
    z-measurability they produce.  NOT `a₁ = R/6`. -/
theorem hKmeas_from_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (u : Set (Point n))
    (hWmeas : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
          (volume : Measure (Point n)))
    (hWdiff : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ z ∂(volume : Measure (Point n)),
          HasDerivAt (fun w => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
            (witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z)
        (volume : Measure (Point n)) := by
  intro x₀ hx₀ i
  filter_upwards [hWmeas x₀ hx₀ i, hWdiff x₀ hx₀ i] with s hWm hWd hmem
  filter_upwards [hWm hmem, hWd hmem] with x hWmx hWdx
  exact pd_aestronglyMeasurable_of_slice
    (fun w z => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
    (fun z => witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i)
    (volume : Measure (Point n)) hWmx hWdx

end QIQTH.G2CarryDischarge

section AxiomChecks
open QIQTH.G2CarryDischarge
#print axioms gaussDdim_coercivity_envelope
#print axioms witnessFieldDeriv_gate_envelope_coercive
#print axioms hdomS_from_uniform
#print axioms pd_aestronglyMeasurable_of_slice
#print axioms hKmeas_from_witness
end AxiomChecks
