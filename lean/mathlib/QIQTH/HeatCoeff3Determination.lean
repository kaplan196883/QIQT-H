/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Determination of the REDUCIBLE weight-6 Seeley–DeWitt heat coefficient `a₃`

This file DETERMINES the *reducible* (product-of-lower-order) universal constants of the
weight-6 diagonal heat coefficient `a₃` of the scalar Laplacian, in the sub-basis

  `a₃ᵣ = cR3·R³ + cRRic·R·|Ric|² + cRRm·R·|Rm|²`,

SELF-CONTAINED from heat-coefficient product-multiplicativity + `a₁ = R/6` + the a₂
constants, and cross-checks them against Gilkey `(35/9, −14/3, 14/3)/7!`. Everything here
is pure real-number algebra: the curvature invariants are represented as real variables.
This is the weight-6 analogue of `HeatCoeff2Determination` (weight-4) and
`HeatCoeffDetermination` (`a₁ = R/6`), one order up.

## Mechanism
Heat coefficients multiply under Riemannian products (`Θ_{M×N} = Θ_M·Θ_N`), giving the
Cauchy-product/convolution rule `a_k(M×N) = ∑_{i+j=k} a_i(M)·a_j(N)`. At `k = 3` (with
`a₀ = 1`):

  `a₃(M×N) = a₃(M) + a₃(N) + a₁(M)·a₂(N) + a₂(M)·a₁(N)`.

On a block-diagonal product the invariants `R, |Ric|², |Rm|²` are ADDITIVE
(`R = R_M + R_N`, etc.). Substituting `a₁ = R/6`, the reducible weight-4 part
`a₂ = (1/360)(5R² − 2|Ric|² + 2|Rm|²)`, and the reducible ansatz `a₃ᵣ`, the product rule —
restricted to the pure-curvature sector — FORCES `(cR3, cRRic, cRRm) = (1/1296, −1/1080,
1/1080)`, which equal Gilkey's `(35/9, −14/3, 14/3)/7!` exactly (`7! = 5040`).

## Statements
* `a2pure`       — the reducible weight-4 coefficient `(1/360)(5R² − 2|Ric|² + 2|Rm|²)`.
* `a3red`        — the reducible weight-6 ansatz `cR3·R³ + cRRic·R·|Ric|² + cRRm·R·|Rm|²`.
* `a3_reducible_from_product` — ★ SELF-CONTAINED: from the reducible product-rule identity
  (product multiplicativity + `a₁ = R/6` + the a₂ constants) the ansatz FORCES
  `cR3 = 1/1296 ∧ cRRic = −1/1080 ∧ cRRm = 1/1080`. No carried `a₃` value is used.
* `a3_reducible_gilkey` — the Gilkey cross-check: the self-contained values equal
  `(35/9, −14/3, 14/3)/7!`.
* `heatProductConvolution` — the `k = 3` Cauchy-product/convolution structure behind the
  product multiplicativity.

## Honest firewall (binding)
DETERMINES the REDUCIBLE weight-6 `a₃` coefficients (`R³, R·|Ric|², R·|Rm|²`)
SELF-CONTAINED from heat-coefficient product-multiplicativity + `a₁ = R/6` + the a₂
constants — matching Gilkey `(35/9, −14/3, 14/3)/7!` exactly. The PRIMITIVE weight-6
invariants (`|Ric|³`/`Ric·Ric·Ric`-contractions, `Rm³`-contractions, and the derivative
terms `|∇R|², |∇Ric|², |∇Rm|², R·ΔR, Δ²R`) are ADDITIVE on products (no cross-terms), so
products do NOT determine them — they remain the carried/cited Gilkey coefficients, NOT
done here. This does NOT construct the manifold heat kernel and does NOT prove that `a₃(x)`
equals the Gilkey invariant for an arbitrary metric — that is the manifold heat-kernel
PARAMETRIX (the wall). Same rigorous status as the `a₁`/`a₂` determinations. NOT the
conjecture, NOT the strong holographic principle, NOT QG. No axioms beyond Mathlib's, no
`sorry`.
-/

namespace QIQTH.HeatCoeff3Determination

/-- The reducible (pure-curvature) part of the weight-4 heat coefficient `a₂`:
`(1/360)(5R² − 2|Ric|² + 2|Rm|²)`, with the invariants represented as real variables. -/
noncomputable def a2pure (R Ric2 Rm2 : ℝ) : ℝ :=
  (1 / 360) * (5 * R ^ 2 - 2 * Ric2 + 2 * Rm2)

/-- The reducible weight-6 ansatz for `a₃`:
`cR3·R³ + cRRic·R·|Ric|² + cRRm·R·|Rm|²`, with the invariants represented as real
variables. -/
def a3red (cR3 cRRic cRRm R Ric2 Rm2 : ℝ) : ℝ :=
  cR3 * R ^ 3 + cRRic * R * Ric2 + cRRm * R * Rm2

/-- ★★★ SELF-CONTAINED CENTERPIECE.
The heat trace multiplies under Riemannian products, giving at `k = 3` the product rule
`a₃(M×N) = a₃(M) + a₃(N) + a₁(M)·a₂(N) + a₂(M)·a₁(N)` with `a₁ = R/6`. On a block-diagonal
product the invariants `R, |Ric|², |Rm|²` are additive, and the reducible sector of this
identity reads, for all factor data,

  `a3red c d e (RM+RN) (RicM+RicN) (RmM+RmN)`
  ` − a3red c d e RM RicM RmM − a3red c d e RN RicN RmN`
  ` = (RM/6)·a2pure RN RicN RmN + a2pure RM RicM RmM·(RN/6)`.

If the reducible ansatz `a3red` satisfies this for ALL factor data, then
`(cR3, cRRic, cRRm) = (1/1296, −1/1080, 1/1080)`. Derived from ONLY the product rule,
`a₁ = R/6`, and the a₂ constants — no carried `a₃` value. -/
theorem a3_reducible_from_product (cR3 cRRic cRRm : ℝ)
    (hyp : ∀ RM RN RicM RicN RmM RmN : ℝ,
      a3red cR3 cRRic cRRm (RM + RN) (RicM + RicN) (RmM + RmN)
          - a3red cR3 cRRic cRRm RM RicM RmM
          - a3red cR3 cRRic cRRm RN RicN RmN
        = (RM / 6) * a2pure RN RicN RmN + a2pure RM RicM RmM * (RN / 6)) :
    cR3 = 1 / 1296 ∧ cRRic = -1 / 1080 ∧ cRRm = 1 / 1080 := by
  -- Isolate each monomial by specializing the factor data.
  have hc := hyp 1 1 0 0 0 0   -- pins `cR3` via the `R³` cross-terms
  have hd := hyp 1 0 0 1 0 0   -- pins `cRRic` via the `R·|Ric|²` cross-term
  have he := hyp 1 0 0 0 0 1   -- pins `cRRm` via the `R·|Rm|²` cross-term
  simp only [a3red, a2pure] at hc hd he
  refine ⟨by nlinarith [hc], by nlinarith [hd], by nlinarith [he]⟩

/-- The self-contained reducible `a₃` coefficients equal Gilkey's `(35/9, −14/3, 14/3)/7!`
(`7! = 5040`): `1/1296 = (35/9)/5040`, `−1/1080 = (−14/3)/5040`, `1/1080 = (14/3)/5040`. -/
theorem a3_reducible_gilkey :
    (1 : ℝ) / 1296 = (35 / 9) / 5040 ∧
      (-1 : ℝ) / 1080 = (-14 / 3) / 5040 ∧
      (1 : ℝ) / 1080 = (14 / 3) / 5040 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The `k = 3` Cauchy-product/convolution structure behind heat-coefficient product
multiplicativity: the `t³` coefficient of the product of two heat traces with coefficient
sequences `a, b : ℕ → ℝ` is `∑_{i+j=3} a i · b j`. With `a 0 = b 0 = 1` this is exactly
`a₃(M×N) = a₃(M) + a₃(N) + a₁(M)·a₂(N) + a₂(M)·a₁(N)`. -/
theorem heatProductConvolution (a b : ℕ → ℝ) :
    ∑ i ∈ Finset.range 4, a i * b (3 - i)
      = a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 := by
  simp [Finset.sum_range_succ]

end QIQTH.HeatCoeff3Determination
