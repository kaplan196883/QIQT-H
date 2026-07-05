/-
  THE HEAT-KERNEL PREFACTOR (increments P1–P3) — the general-d flat-space heat-kernel
  prefactor and the π-content of the induced-Newton-constant 12π normalization.

  WHAT IS DERIVED HERE (and the honest boundary — read it).
  This file moves ONE transcendental — the `π²` inside the `(4π)⁻² = 1/(16π²)` heat-kernel
  prefactor, i.e. the entire π-content of the cited `12π` induced-Newton normalization — from
  CITED to DERIVED, continuing the a₁ Gaussian-moment campaign. Concretely:

    • `heatDensity_dDim` : the general-d flat-space prefactor
        `(1/2π)^d · ∫_{k∈ℝ^d} e^{−t ∑ᵢ kᵢ²} = (1/√(4πt))^d = (4πt)^{−d/2}`,
      proved as the d-fold product of the derived 1-D density `heatDensity_oneD`
      (exp-of-a-sum → product of exponentials, then Fubini `integral_fintype_prod_volume_eq_pow`).
    • `heat_prefactor_fourD` : its d = 4 value `1/(16π²t²)` (pure `√`-algebra).
    • `inducedInvG_normalization_assembly` : the assembly
        `(16π)·½·(1/16π²)·(κ−ξ) = (κ−ξ)/(2π)`, with corollary `= 1/(12π)` at `ξ=0, κ=1/6`,
      matching the `12π` in `SakharovRatio` and `InducedNewtonConstant.effSpeciesN`.

  ⚠ HONESTY (binding). The DERIVED content is the π-transcendental ONLY (the `π²` in `1/16π²`,
  the `π` in `(4πt)^{−d/2}`). The rational/convention factors `½`, `16π`, the conformal-coupling
  value `κ = 1/6`, and the species charge `b = ∑ᵢ nᵢcᵢ` remain CARRIED/cited. This file does NOT
  compute the numerical value of `G`, does NOT derive `κ` or the effective-action conventions,
  does NOT formalize a curved-space (Riemannian) heat kernel, and does NOT build the physical d=4
  proper-time integral `∫ds/s² e^{−sm²}` (which is DIVERGENT — regularized by the already-discharged
  `Λ²` cutoff `cutoff_moment`). After P1–P3 the flat-space analysis vein is EXHAUSTED.
-/
import Mathlib
import QIQTH.HeatKernelOneD

namespace QIQTH.HeatKernelDDim

open Real MeasureTheory QIQTH.HeatKernelOneD

/-- **P1 — the general-d flat-space heat-kernel prefactor (the DERIVED nugget).**
    `(1/2π)^d · ∫_{k ∈ ℝ^d} e^{−t ∑ᵢ kᵢ²} = (1/√(4πt))^d`, the `d`-dimensional momentum-space
    trace density of `e^{tΔ}`, i.e. the universal `(4πt)^{−d/2}`. Proved as the `d`-fold product
    of the derived 1-D density `heatDensity_oneD`: the Gaussian in `∑ᵢ kᵢ²` factors into a product
    of one-dimensional Gaussians (`Real.exp_sum`), Fubini (`integral_fintype_prod_volume_eq_pow`)
    turns the integral into a `d`-th power, and `heatDensity_oneD` supplies the base. -/
theorem heatDensity_dDim (d : ℕ) (t : ℝ) (ht : 0 < t) :
    (1 / (2 * Real.pi)) ^ d * ∫ k : (Fin d → ℝ), Real.exp (-(t * ∑ i, (k i) ^ 2))
      = (1 / Real.sqrt (4 * Real.pi * t)) ^ d := by
  have hpt : ∀ k : Fin d → ℝ,
      Real.exp (-(t * ∑ i, (k i) ^ 2)) = ∏ i, Real.exp (-(t * (k i) ^ 2)) := by
    intro k
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [integral_congr_ae (ae_of_all _ hpt),
      integral_fintype_prod_volume_eq_pow (fun y : ℝ => Real.exp (-(t * y ^ 2))),
      Fintype.card_fin, ← mul_pow, heatDensity_oneD t ht]

/-- **P2 — the d = 4 specialization.**
    `(1/2π)^4 · ∫_{k ∈ ℝ⁴} e^{−t ∑ᵢ kᵢ²} = 1/(16π²t²)`. The `d = 4` value of the prefactor,
    `(1/√(4πt))^4 = (4πt)^{−2} = 1/(16π²t²)`, by `√`-algebra (`Real.sq_sqrt`). -/
theorem heat_prefactor_fourD (t : ℝ) (ht : 0 < t) :
    (1 / (2 * Real.pi)) ^ 4 * ∫ k : (Fin 4 → ℝ), Real.exp (-(t * ∑ i, (k i) ^ 2))
      = 1 / (16 * Real.pi ^ 2 * t ^ 2) := by
  rw [heatDensity_dDim 4 t ht]
  have hnn : (0 : ℝ) ≤ 4 * Real.pi * t := by positivity
  rw [div_pow, one_pow,
      show (Real.sqrt (4 * Real.pi * t)) ^ 4 = ((Real.sqrt (4 * Real.pi * t)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hnn]
  ring

/-- **P3 — the normalization assembly (the a₁-style wire into `12π`).**
    `(16π)·½·P·(κ−ξ) = (κ−ξ)/(2π)` when `P = 1/(16π²)` (the DERIVED `t`-independent prefactor of
    `heat_prefactor_fourD`). Fills the `1/16π²` slot with the derived π-content; `κ = 1/6`, `16π`,
    `½` are CARRIED — the exact analogue of `heat_a1_of_RNC`. The identity holds for any `κ`; the
    conformal value `hκ : κ = 1/6` is carried as a marker of the physics input, not used in the
    pure-π algebra. -/
theorem inducedInvG_normalization_assembly (ξ P κ : ℝ)
    (hP : P = 1 / (16 * Real.pi ^ 2)) (hκ : κ = 1 / 6) :
    (16 * Real.pi) * (1 / 2) * P * (κ - ξ) = (κ - ξ) / (2 * Real.pi) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  subst hP
  field_simp

/-- **P3 (corollary) — the conformal `ξ = 0`, `κ = 1/6` value `1/(12π)`.**
    `(16π)·½·(1/16π²)·(1/6 − 0) = 1/(12π)` — matching the `12π` cited verbatim in
    `SakharovRatio.lean` and `InducedNewtonConstant.effSpeciesN`. -/
theorem inducedInvG_normalization_assembly_zero (P : ℝ) (hP : P = 1 / (16 * Real.pi ^ 2)) :
    (16 * Real.pi) * (1 / 2) * P * ((1 : ℝ) / 6 - 0) = 1 / (12 * Real.pi) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  subst hP
  field_simp
  ring

end QIQTH.HeatKernelDDim
