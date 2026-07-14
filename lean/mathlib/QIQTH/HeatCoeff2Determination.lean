/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Determination of the weight-4 Seeley–DeWitt heat coefficient `a₂` (Gilkey constants)

This file DETERMINES the universal constants of the weight-4 diagonal heat coefficient of
the scalar Laplacian, written in the Gilkey invariant basis

  `a₂ = α·R² + β·|Ric|² + γ·|Rm|² + δ·ΔR`,

and reproduces Gilkey's answer `a₂ = (1/360)(5R² − 2|Ric|² + 2|Rm|² + 12ΔR)`, i.e.
`(α,β,γ,δ) = (1/72, −1/180, 1/180, 1/30) = (5,−2,2,12)/360`. Everything here is pure
real-number algebra: the invariants are represented as real variables. This is the
weight-4 analogue of `HeatCoeffDetermination` (which determined `a₁ = R/6`), using the
same "carry the invariance ansatz + model values, DERIVE the constants" pattern.

## Statements
* `a2Invariant`      — the ansatz `α·R² + β·|Ric|² + γ·|Rm|² + δ·ΔR`.
* `alpha_from_product` — ★ SELF-CONTAINED: from the heat-trace product rule
  `a₂(M×N) = a₂(M) + a₂(N) + a₁(M)·a₁(N)` with `a₁ = R/6` and additive `R,|Ric|²,|Rm|²,ΔR`,
  the ansatz FORCES `α = 1/72`. No carried `a₂` value is used.
* `constCurvA2`      — the ansatz on constant-curvature invariants `R = κm(m−1)`,
  `|Ric|² = κ²m(m−1)²`, `|Rm|² = 2κ²m(m−1)`, `ΔR = 0`.
* `constants_determined` — the three carried round-sphere values `a₂(S²)=1/15`,
  `a₂(S³)=1/2`, `a₂(S⁴)=29/15` FORCE `α=1/72 ∧ β=−1/180 ∧ γ=1/180`.
* `a2_formula`       — the ansatz at `(5,−2,2,12)/360` equals Gilkey's `(1/360)(…)`.
* `a2_gilkey`        — capstone: the constants forced by the product rule AND the sphere
  system equal Gilkey's `(5,−2,2)/360`, and the assembled invariant is the Gilkey `a₂`.

## Honest firewall (binding)
This DETERMINES the universal `a₂` constants from the invariance ansatz (carried, Gilkey
Lemma 4.8.5) + the product-multiplicativity structure + carried classical sphere values —
the SAME rigorous status as `HeatCoeffDetermination` for `a₁ = R/6`. `α = 1/72` is
genuinely SELF-CONTAINED (product rule + `a₁ = R/6`); `β, γ` use carried classical round-
sphere `a₂` values; `δ = 12/360 = 1/30` is the cited classical `ΔR` coefficient (it needs a
non-homogeneous computation — `ΔR = 0` on all homogeneous models — and is carried, clearly
labelled). This does NOT construct the manifold heat kernel and does NOT prove that `a₂(x)`
equals this invariant for an arbitrary metric — that is the manifold heat-kernel PARAMETRIX
(the wall). NOT the conjecture, NOT the strong holographic principle, NOT QG.
No axioms beyond Mathlib's, no `sorry`.
-/

namespace QIQTH.HeatCoeff2Determination

/-- The weight-4 Gilkey invariant ansatz for the heat coefficient `a₂`:
`α·R² + β·|Ric|² + γ·|Rm|² + δ·ΔR`, with the invariants represented as real variables. -/
def a2Invariant (α β γ δ R Ric2 Rm2 boxR : ℝ) : ℝ :=
  α * R ^ 2 + β * Ric2 + γ * Rm2 + δ * boxR

/-- ★★ SELF-CONTAINED CENTERPIECE.
The heat trace multiplies under Riemannian products, giving the product rule
`a₂(M×N) = a₂(M) + a₂(N) + a₁(M)·a₁(N)` with `a₁ = R/6`. On a product the invariants
`R, |Ric|², |Rm|², ΔR` are all additive EXCEPT `R² = (R_M+R_N)²`, whose cross-term is the
only new contribution. If the ansatz `a2Invariant` satisfies this rule for ALL factor
data, then `α = 1/72`. Derived from ONLY the product rule and `a₁ = R/6` — no carried
`a₂` value. -/
theorem alpha_from_product (α β γ δ : ℝ)
    (hyp : ∀ RM RN RicM RicN RmM RmN boxM boxN : ℝ,
      a2Invariant α β γ δ (RM + RN) (RicM + RicN) (RmM + RmN) (boxM + boxN)
        = a2Invariant α β γ δ RM RicM RmM boxM
          + a2Invariant α β γ δ RN RicN RmN boxN
          + (RM / 6) * (RN / 6)) :
    α = 1 / 72 := by
  have h := hyp 1 1 0 0 0 0 0 0
  simp only [a2Invariant] at h
  nlinarith [h]

/-- The ansatz evaluated on the invariants of a space of constant sectional curvature `κ`
in dimension `m`: `R = κm(m−1)`, `|Ric|² = κ²m(m−1)²`, `|Rm|² = 2κ²m(m−1)`, `ΔR = 0`. -/
def constCurvA2 (α β γ δ κ m : ℝ) : ℝ :=
  a2Invariant α β γ δ (κ * m * (m - 1)) (κ ^ 2 * m * (m - 1) ^ 2)
    (2 * κ ^ 2 * m * (m - 1)) 0

/-- ★★ The three carried classical round-sphere (`κ = 1`) values
`a₂(S²) = 1/15`, `a₂(S³) = 1/2`, `a₂(S⁴) = 29/15` FORCE the curvature-squared constants
`α = 1/72`, `β = −1/180`, `γ = 1/180`. (Three linear equations in `(α,β,γ)`; `δ` is
invisible since `ΔR = 0` on spheres. The `α` here independently CROSS-CHECKS
`alpha_from_product`.) -/
theorem constants_determined (α β γ δ : ℝ)
    (h2 : constCurvA2 α β γ δ 1 2 = 1 / 15)
    (h3 : constCurvA2 α β γ δ 1 3 = 1 / 2)
    (h4 : constCurvA2 α β γ δ 1 4 = 29 / 15) :
    α = 1 / 72 ∧ β = -1 / 180 ∧ γ = 1 / 180 := by
  simp only [constCurvA2, a2Invariant] at h2 h3 h4
  ring_nf at h2 h3 h4
  refine ⟨?_, ?_, ?_⟩ <;> linarith [h2, h3, h4]

/-- The Gilkey normalization `(α,β,γ,δ) = (5,−2,2,12)/360` reproduces the standard form
`a₂ = (1/360)(5R² − 2|Ric|² + 2|Rm|² + 12ΔR)`. -/
theorem a2_formula (R Ric2 Rm2 boxR : ℝ) :
    a2Invariant (5 / 360) (-2 / 360) (2 / 360) (12 / 360) R Ric2 Rm2 boxR
      = (1 / 360) * (5 * R ^ 2 - 2 * Ric2 + 2 * Rm2 + 12 * boxR) := by
  unfold a2Invariant
  ring

/-- ★★ CAPSTONE. The curvature-squared constants forced by BOTH the product rule
(`α`, via `alpha_from_product`) AND the round-sphere system (via `constants_determined`)
are `(α,β,γ) = (1/72, −1/180, 1/180)`, which equal Gilkey's `(5,−2,2)/360`; and the
assembled invariant with `δ = 12/360` is Gilkey's `a₂`. -/
theorem a2_gilkey (α β γ δ : ℝ)
    (hprod : ∀ RM RN RicM RicN RmM RmN boxM boxN : ℝ,
      a2Invariant α β γ δ (RM + RN) (RicM + RicN) (RmM + RmN) (boxM + boxN)
        = a2Invariant α β γ δ RM RicM RmM boxM
          + a2Invariant α β γ δ RN RicN RmN boxN
          + (RM / 6) * (RN / 6))
    (h2 : constCurvA2 α β γ δ 1 2 = 1 / 15)
    (h3 : constCurvA2 α β γ δ 1 3 = 1 / 2)
    (h4 : constCurvA2 α β γ δ 1 4 = 29 / 15) :
    α = 5 / 360 ∧ β = -2 / 360 ∧ γ = 2 / 360 ∧
      ∀ R Ric2 Rm2 boxR : ℝ,
        a2Invariant α β γ (12 / 360) R Ric2 Rm2 boxR
          = (1 / 360) * (5 * R ^ 2 - 2 * Ric2 + 2 * Rm2 + 12 * boxR) := by
  -- `α` is pinned two ways; `β, γ` by the sphere system.
  have hα : α = 1 / 72 := alpha_from_product α β γ δ hprod
  obtain ⟨hα', hβ, hγ⟩ := constants_determined α β γ δ h2 h3 h4
  refine ⟨by rw [hα]; norm_num, by rw [hβ]; norm_num, by rw [hγ]; norm_num, ?_⟩
  intro R Ric2 Rm2 boxR
  rw [hα, hβ, hγ]
  unfold a2Invariant
  ring
end QIQTH.HeatCoeff2Determination
