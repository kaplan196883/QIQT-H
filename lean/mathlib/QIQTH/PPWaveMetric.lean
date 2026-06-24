/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# A1-ppwave — the pp-wave metric (a non-flat Raychaudhuri-congruence witness)

The flat (constant) metric discharges the GR Raychaudhuri congruence premises but is degenerate (`Ric=0`).
This file builds a genuinely curved witness: the **pp-wave** `ds² = 2 du dv + H du² + dx² + dy²` (coords
`(u,v,x,y)=(0,1,2,3)`, with `H` independent of `v=x¹`), whose null field `∂_v` is covariantly constant — so
`hcov`/`hWgeo`/`hWequil` hold on a curved spacetime.

Stage 1 (this file): the metric `ppMetric`, its inverse `ppMetricInv`, symmetry, and `g·gi = I`.
Stages 2–3 (next): `christoffel … 1 ≡ 0` ⟹ `∂_v` covariantly constant ⟹ the congruence premises.
Stage 4: `Ric ≠ 0` for a non-harmonic `H` (non-degeneracy).

Axiom-free.
-/
import QIQTH.RaychaudhuriCongruence
import Mathlib.Tactic

namespace QIQTH.Curvature

/-- The **pp-wave metric** `ds² = 2 du dv + H du² + dx² + dy²`, coords `(u,v,x,y) = (0,1,2,3)`:
    `g₀₀ = H`, `g₀₁ = g₁₀ = 1`, `g₂₂ = g₃₃ = 1`, rest `0`. -/
noncomputable def ppMetric (H : Point 4 → ℝ) (x : Point 4) (a b : Fin 4) : ℝ :=
  if a = 0 ∧ b = 0 then H x
  else if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1
  else if (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 3) then 1
  else 0

/-- The **inverse pp-wave metric**: `gi₀₁ = gi₁₀ = 1`, `gi₁₁ = −H`, `gi₂₂ = gi₃₃ = 1`, rest `0`. -/
noncomputable def ppMetricInv (H : Point 4 → ℝ) (x : Point 4) (a b : Fin 4) : ℝ :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1
  else if a = 1 ∧ b = 1 then -H x
  else if (a = 2 ∧ b = 2) ∨ (a = 3 ∧ b = 3) then 1
  else 0

theorem ppMetric_symm (H : Point 4 → ℝ) (x : Point 4) (a b : Fin 4) :
    ppMetric H x a b = ppMetric H x b a := by
  fin_cases a <;> fin_cases b <;> simp [ppMetric]

theorem ppMetric_inv (H : Point 4 → ℝ) (x : Point 4) (a b : Fin 4) :
    (∑ σ, ppMetric H x a σ * ppMetricInv H x σ b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [ppMetric, ppMetricInv, Fin.sum_univ_four] <;> ring

end QIQTH.Curvature
