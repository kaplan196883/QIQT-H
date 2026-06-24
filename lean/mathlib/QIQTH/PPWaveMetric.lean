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

/-! ### Stage 2 — the Christoffels with last index `1` vanish. -/

/-- The metric component `g_{a1}` is constant (independent of the point), so its `pd` vanishes. -/
theorem pd_ppMetric_snd_one (H : Point 4 → ℝ) (a c : Fin 4) (x : Point 4) :
    pd (fun y => ppMetric H y a 1) c x = 0 := by
  fin_cases a <;> simp [ppMetric, pd_const]

/-- The derivative of any metric component in the `v = x¹` direction vanishes: every component is
    constant except `g₀₀ = H`, and `pd H 1 = 0`. -/
theorem pd_ppMetric_dir_one (H : Point 4 → ℝ) (hHv : ∀ x, pd H 1 x = 0) (a b : Fin 4) (x : Point 4) :
    pd (fun y => ppMetric H y a b) 1 x = 0 := by
  fin_cases a <;> fin_cases b <;> simp [ppMetric, pd_const, hHv]

/-- **★ Stage 2 — every Christoffel with last (lower) index `1` vanishes.**  All three metric-derivative
    terms in `Γ^μ_{ν1}` are zero: `∂_ν g_{α1}` and `∂_α g_{ν1}` (the `g_{·1}` components are constant) and
    `∂_1 g_{αν}` (nothing depends on `v=x¹`, `pd H 1 = 0`).  Hence `Γ^μ_{ν1} ≡ 0`. -/
theorem christoffel_ppMetric_last_one (H : Point 4 → ℝ) (hHv : ∀ x, pd H 1 x = 0)
    (μ ν : Fin 4) (x : Point 4) :
    christoffel (ppMetric H) (ppMetricInv H) μ ν 1 x = 0 := by
  simp only [christoffel]
  have hb : ∀ α : Fin 4,
      pd (fun y => ppMetric H y α 1) ν x + pd (fun y => ppMetric H y α ν) 1 x
        - pd (fun y => ppMetric H y ν 1) α x = 0 := by
    intro α
    rw [pd_ppMetric_snd_one, pd_ppMetric_dir_one H hHv, pd_ppMetric_snd_one]; ring
  simp_rw [hb, mul_zero, Finset.sum_const_zero, mul_zero]

/-! ### Stage 3 — `∂_v` is covariantly constant ⟹ the Raychaudhuri congruence premises (on a curved metric). -/

/-- The pp-wave null field `∂_v` (`V^μ = δ^μ₁`). -/
def ppV : Point 4 → Fin 4 → ℝ := fun _ μ => if μ = 1 then (1 : ℝ) else 0

/-- **★ Stage 3 — `∂_v` is covariantly constant** in the pp-wave: `∇ ∂_v ≡ 0`.  The `∂V`-term vanishes (`V`
    is constant) and the connection term is `Γ^μ_{ν1}·1 = 0` (`christoffel_ppMetric_last_one`). -/
theorem ppMetric_covDerivVec_v_zero (H : Point 4 → ℝ) (hHv : ∀ x, pd H 1 x = 0)
    (a b : Fin 4) (x : Point 4) :
    covDerivVec (ppMetric H) (ppMetricInv H) ppV a b x = 0 := by
  simp only [covDerivVec, ppV]
  rw [Finset.sum_eq_single (1 : Fin 4)]
  · simp [pd_const, christoffel_ppMetric_last_one H hHv]
  · intro σ _ hσ; simp [hσ]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **★★ Stage 3 — the Raychaudhuri congruence premises hold for the pp-wave `∂_v`.**  A non-flat (curved)
    witness that `hWgeo` (geodesic) and `hWequil` (equilibrium) are satisfiable — via the covariantly-constant
    null field `∂_v`, composing `raychaudhuri_setup_of_covConst`. -/
theorem ppMetric_raychaudhuri_setup (H : Point 4 → ℝ) (hHv : ∀ x, pd H 1 x = 0) (x : Point 4) :
    (∀ y μ, ∑ ν, ppV y ν * covDerivVec (ppMetric H) (ppMetricInv H) ppV ν μ y = 0)
      ∧ (∑ μ, ∑ ν, covDerivVec (ppMetric H) (ppMetricInv H) ppV μ ν x
          * covDerivVec (ppMetric H) (ppMetricInv H) ppV ν μ x = 0) :=
  raychaudhuri_setup_of_covConst (ppMetric H) (ppMetricInv H) ppV x
    (fun a b y => ppMetric_covDerivVec_v_zero H hHv a b y)

/-! ### Stage 4 (partial) — the connection is non-trivial: `Γ^x_{uu} = −½ ∂_x H`.

The full Riemann/Ricci `Ric₀₀ = −½(∂_x²+∂_y²)H` (≠ 0 for non-harmonic `H`, e.g. `−1` for `H = (x²)²`) is the
standard non-degeneracy certificate, but its evaluation in the bespoke `Point`/`christoffel` setup needs many
Christoffel + `pd`-of-Christoffel + quadratic-product lemmas — a documented sub-frontier (plan §2 Stage 4).
We record the load-bearing piece: the transverse-`uu` Christoffel is `−½ ∂_x H`, non-zero for non-constant `H`,
so the connection genuinely depends on `H` (the metric is not the flat constant metric in disguise). -/

/-- `Γ^x_{uu} = −½ ∂_x H` (index `2 = x`, `0 = u`).  Non-zero for non-constant `H` — the connection is
    H-dependent. -/
theorem christoffel_ppMetric_x_uu (H : Point 4 → ℝ) (x : Point 4) :
    christoffel (ppMetric H) (ppMetricInv H) 2 0 0 x = -(1 / 2) * pd H 2 x := by
  unfold christoffel
  rw [Finset.sum_eq_single (2 : Fin 4)]
  · have hgi : ppMetricInv H x 2 2 = 1 := by simp [ppMetricInv]
    have h20 : pd (fun y => ppMetric H y 2 0) 0 x = 0 := by simp [ppMetric, pd_const]
    have h00 : pd (fun y => ppMetric H y 0 0) 2 x = pd H 2 x := by simp [ppMetric]
    rw [hgi, h20, h00]; ring
  · intro α _ hα
    have : ppMetricInv H x 2 α = 0 := by fin_cases α <;> simp_all [ppMetricInv]
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end QIQTH.Curvature
