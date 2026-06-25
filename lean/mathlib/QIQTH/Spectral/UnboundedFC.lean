/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Stone, Phase 1 (M1) — the unbounded functional calculus `∫ f dE` on a PVM

`STONE_THEOREM_PLAN.md` Phase 1 / `P4_TO_GR_MASTER_PLAN.md` M1.  The keystone that makes the modular
Hamiltonian `K = ∫ log(r/(2−r)) dE_R` a genuine self-adjoint operator (Phase 2) — built on the EXISTING
`ProjectionValuedMeasure` substrate (`scalarMeasure`, `boundedFC`), no general Stone theorem, no Cayley.

This file delivers the **domain**: for a real Borel symbol `f`, the set of vectors with finite spectral
energy `∫ f² dμ_x < ∞` is a `ℂ`-submodule `fcDomain P f` of `H` — the natural domain `D(∫ f dE)` of the
(unbounded) self-adjoint operator.  The operator on this domain, its symmetry and self-adjointness, and the
exponential law `exp(it ∫f dE) = ∫ e^{itf} dE` are the subsequent Phase-1/2 increments.

Axiom-free.  Uses the spectral scaling `μ_{c·x} = ‖c‖²·μ_x` and the parallelogram identity
`μ_{x+y} + μ_{x−y} = 2μ_x + 2μ_y` already proved in `QIQTH/Spectral/PVM.lean`.
-/
import QIQTH.Spectral.PVM

namespace QIQTH.Spectral.ProjectionValuedMeasure

open MeasureTheory
open scoped ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : ProjectionValuedMeasure Ω H)

/-- The **spectral energy** `∫ f² dμ_x ∈ ℝ≥0∞` of a vector `x` against a real Borel symbol `f`
    (`μ_x = P.scalarMeasure x`).  Finite energy is the defining condition of the FC domain. -/
noncomputable def fcEnergy (f : Ω → ℝ) (x : H) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x)

/-- The scalar spectral measure of `0` is the zero measure (`E s 0 = 0`). -/
theorem scalarMeasure_zero : P.scalarMeasure (0 : H) = 0 := by
  have h := P.scalarMeasure_smul (0 : ℂ) (0 : H)
  simpa using h

@[simp] theorem fcEnergy_zero (f : Ω → ℝ) : P.fcEnergy f (0 : H) = 0 := by
  rw [fcEnergy, P.scalarMeasure_zero, lintegral_zero_measure]

/-- **Homogeneity of the energy:** `‖c‖²` scales out (`μ_{c·x} = ‖c‖²·μ_x`). -/
theorem fcEnergy_smul (f : Ω → ℝ) (c : ℂ) (x : H) :
    P.fcEnergy f (c • x) = ENNReal.ofReal (‖c‖ ^ 2) * P.fcEnergy f x := by
  rw [fcEnergy, fcEnergy, P.scalarMeasure_smul, lintegral_smul_measure, smul_eq_mul]

/-- **Sub-additivity of the energy** (the parallelogram bound `μ_{x+y} ≤ 2μ_x + 2μ_y`):
    `∫ f² dμ_{x+y} ≤ 2∫ f² dμ_x + 2∫ f² dμ_y`. -/
theorem fcEnergy_add_le (f : Ω → ℝ) (x y : H) :
    P.fcEnergy f (x + y) ≤ 2 * P.fcEnergy f x + 2 * P.fcEnergy f y := by
  unfold fcEnergy
  have hpar := P.scalarMeasure_parallelogram_measure x y
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y))
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y))
        + ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x - y)) := le_self_add
    _ = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y) + P.scalarMeasure (x - y)) := by
        rw [lintegral_add_measure]
    _ = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2)
        ∂((2 : ℝ≥0∞) • P.scalarMeasure x + (2 : ℝ≥0∞) • P.scalarMeasure y) := by
        rw [hpar]
    _ = 2 * (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x))
        + 2 * (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure y)) := by
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
          smul_eq_mul, smul_eq_mul]

/-- **The domain of `∫ f dE`** — the vectors of finite spectral energy — as a `ℂ`-submodule of `H`.
    `0` has zero energy; energy is sub-additive (parallelogram) and `‖c‖²`-homogeneous, so the
    finite-energy set is closed under `+` and `•`.  This is the natural (dense) domain `D(∫ f dE)` of the
    unbounded self-adjoint operator built in the next increment. -/
noncomputable def fcDomain (f : Ω → ℝ) : Submodule ℂ H where
  carrier := {x | P.fcEnergy f x ≠ ⊤}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at *
    refine ne_top_of_le_ne_top ?_ (P.fcEnergy_add_le f x y)
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) hx, ENNReal.mul_ne_top (by simp) hy⟩
  smul_mem' := fun c {x} hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [P.fcEnergy_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx

@[simp] theorem mem_fcDomain {f : Ω → ℝ} {x : H} :
    x ∈ P.fcDomain f ↔ P.fcEnergy f x ≠ ⊤ := Iff.rfl

/-- **A bounded symbol has full domain.**  If `|f| ≤ C` then every vector has finite energy
    (`∫ f² dμ_x ≤ C²‖x‖²`), so `x ∈ fcDomain f`.  (This is why `K = ∫ log(r/(2−r)) dE_R` is genuinely
    *unbounded* — its domain is proper precisely because `log` is unbounded, not bounded.) -/
theorem mem_fcDomain_of_bounded {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (x : H) :
    x ∈ P.fcDomain f := by
  rw [mem_fcDomain]
  have hpt : ∀ ω, ENNReal.ofReal (f ω ^ 2) ≤ ENNReal.ofReal (C ^ 2) := fun ω =>
    ENNReal.ofReal_le_ofReal (by nlinarith [hC ω, abs_nonneg (f ω), sq_abs (f ω)])
  have hbound : P.fcEnergy f x ≤ ENNReal.ofReal (C ^ 2) * P.scalarMeasure x Set.univ := by
    rw [fcEnergy]
    calc ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x)
        ≤ ∫⁻ _, ENNReal.ofReal (C ^ 2) ∂(P.scalarMeasure x) := lintegral_mono hpt
      _ = ENNReal.ofReal (C ^ 2) * P.scalarMeasure x Set.univ := by rw [lintegral_const]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by rw [P.scalarMeasure_univ]; exact ENNReal.ofReal_ne_top)) hbound

/-- **A bounded symbol's FC domain is all of `H`** — the consistency bridge to the bounded functional
    calculus `boundedFC` (where the operator is total). -/
theorem fcDomain_eq_top_of_bounded {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    P.fcDomain f = ⊤ :=
  Submodule.eq_top_iff'.mpr (P.mem_fcDomain_of_bounded hC)

end QIQTH.Spectral.ProjectionValuedMeasure
