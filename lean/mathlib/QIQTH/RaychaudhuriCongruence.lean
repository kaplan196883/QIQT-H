/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-GR-Raychaudhuri — the congruence premises from one covariantly-constant condition

The QIQT→GR capstones take a per-generator congruence `W` with the geodesic premise `hWgeo` and the equilibrium
premise `hWequil`.  This file reduces BOTH to the single geometric condition "`W` is covariantly constant"
(`covDerivVec g gi W ≡ 0`), and discharges that condition fully for a constant (flat) metric — a non-vacuity
certificate that the Raychaudhuri congruence setup is satisfiable.

The general curved geodesic congruence (a non-flat covariantly-constant null field, e.g. a pp-wave) needs a
geodesic-ODE / exp-map construction Mathlib lacks for this `Point`/`christoffel` setup — the cited geometric
frontier (see `T3-GR-RAYCHAUDHURI_PLAN.md` §4).  Axiom-free.
-/
import QIQTH.Raychaudhuri
import QIQTH.QiqtGrWitness

namespace QIQTH.Curvature

variable {n : ℕ}

/-- **Stage 1 — the Raychaudhuri congruence setup from one condition.**  A covariantly-constant congruence `V`
    (`covDerivVec g gi V ≡ 0`) satisfies BOTH the geodesic premise `hWgeo` and the equilibrium premise `hWequil`
    — trivially, since every covariant derivative term is zero.  This reduces the two labelled premises to the
    single geometric condition "`V` is covariantly constant." -/
theorem raychaudhuri_setup_of_covConst (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (x : Point n)
    (hcov : ∀ a b y, covDerivVec g gi V a b y = 0) :
    (∀ y μ, ∑ ν, V y ν * covDerivVec g gi V ν μ y = 0)
      ∧ (∑ μ, ∑ ν, covDerivVec g gi V μ ν x * covDerivVec g gi V ν μ x = 0) := by
  refine ⟨fun y μ => ?_, ?_⟩ <;> simp [hcov]

/-- **Stage 2 — flat witness.**  In a constant (flat) metric `g = fun _ => G` (Christoffels vanish,
    `christoffel_constMetric`), a constant congruence `V = fun _ => v` is covariantly constant: every
    `covDerivVec` term is `∂(const) + Γ·v = 0 + 0`.  Hence the Raychaudhuri premises hold for flat space (a
    non-vacuity certificate for the congruence bundle). -/
theorem covDerivVec_constMetric_const (G : Fin n → Fin n → ℝ)
    (gi : Point n → Fin n → Fin n → ℝ) (v : Fin n → ℝ) (a b : Fin n) (y : Point n) :
    covDerivVec (fun _ => G) gi (fun _ => v) a b y = 0 := by
  simp only [covDerivVec, pd_const, QIQTH.QiqtGrWitness.christoffel_constMetric, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- **Stage 3 — zero expansion for a covariantly-constant congruence.**  The expansion `θ = ∑_μ ∇_μ V^μ`
    of a covariantly-constant `V` vanishes identically (every `∇_μ V^μ = 0`). -/
theorem expansion_eq_zero_of_covConst (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (hcov : ∀ a b y, covDerivVec g gi V a b y = 0) (x : Point n) :
    expansion g gi V x = 0 := by
  simp only [expansion]
  exact Finset.sum_eq_zero (fun μ _ => hcov μ μ x)

/-- The coordinate derivative of the (identically-zero) expansion is zero. -/
theorem pd_expansion_zero_of_covConst (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (hcov : ∀ a b y, covDerivVec g gi V a b y = 0)
    (ν : Fin n) (x : Point n) :
    pd (fun y => expansion g gi V y) ν x = 0 := by
  have h0 : (fun y => expansion g gi V y) = (fun _ => (0 : ℝ)) :=
    funext (fun y => expansion_eq_zero_of_covConst g gi V hcov y)
  rw [h0]; exact pd_const 0 ν x

/-- **Stage 3 — the area-derivative witness `hA` for a covariantly-constant congruence.**  A covariantly-
    constant congruence has identically-zero expansion, so the Raychaudhuri area-rate
    `-∑_ν V^ν ∂_ν θ` is `0`, and a constant cross-sectional area satisfies the capstone's `hA`
    (`HasDerivAt (area) (rate) 0`) — the `θ = 0` case (area preserved along a shear-free, expansion-free
    congruence).  Discharges `hA` for the flat / pp-wave (∂_v) congruence, the same setting in which
    `hWgeo`/`hWequil` reduce.  The expanding (θ≠0) curved case needs the geodesic-ODE / area-element
    machinery Mathlib lacks (the cited frontier, header). -/
theorem area_hasDerivAt_of_covConst (g gi : Point n → Fin n → Fin n → ℝ)
    (V : Point n → Fin n → ℝ) (hcov : ∀ a b y, covDerivVec g gi V a b y = 0)
    (x : Point n) (c : ℝ) :
    HasDerivAt (fun _ : ℝ => c)
      (-∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x) 0 := by
  have hrate : (-∑ ν, V x ν * pd (fun y => expansion g gi V y) ν x) = 0 := by
    simp [pd_expansion_zero_of_covConst g gi V hcov]
  rw [hrate]; exact hasDerivAt_const 0 c

end QIQTH.Curvature
