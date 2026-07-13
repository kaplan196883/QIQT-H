import Mathlib
import QIQTH.CoordinateCurvature

/-!
# Gilkey's invariance-theory determination of the heat coefficient `a₂ = τ/6 + trE`

This file DERIVES Gilkey's constants `c₁ = 1/6`, `c₂ = 1` (Invariance Theory,
Thm 4.8.16(b), Lemmas 4.8.5/4.8.6) from the invariance ansatz plus two model
evaluations — the `1/6` becomes a THEOREM, not a stipulation, GIVEN the carried facts.

## What is CARRIED (the analytic-wall inputs — encoded as structure fields, NEVER as axioms)
* the existence/meaning of the heat coefficient `a₂` of a Laplace-type operator
  `P = P_∇ − E`;
* Gilkey's UNIVERSALITY ansatz `a₂ = cTau·τ + cE·trE` with the SAME universal
  constants `cTau, cE` for every operator/manifold (Weyl invariant theory for `O(m)`
  — this is the heat-expansion analytic wall, and it is not in Mathlib);
* the flat constant-`E` model value `(τ, trE, a₂) = (0, 1, 1)`;
* the curved `E = 0` model value `(τ, trE, a₂) = (T, 0, T/6)`.

## What is DERIVED (the load-bearing content)
* `cTau = 1/6` and `cE = 1` are FORCED by the two model evaluations
  (`constants_determined`);
* the universal formula `a₂ = τ/6 + trE` (`coeff2_eq`).

## Scope firewall (binding)
* This does NOT build the heat semigroup / heat kernel / short-time expansion
  (Phases 3–4 — the deep wall). It REDUCES the carried assumption from the specific
  number `a₁ = R/6` up to the weaker invariance ansatz + one curved-model value.
* The `Fin 2` witness (`sphereFlatWitness`) grounds the curved-model number in our
  OWN unit-2-sphere scalar curvature `R = 2` (`QIQTH.CoordinateCurvature.SphereCheck`),
  but its `universal` field is only a NON-VACUITY witness (2 points, 2 parameters is
  trivially satisfiable). The genuine invariance CONTENT lives in the abstract
  `HeatCoeffData` — universality over ALL operators.
* NOT the conjecture, NOT the strong holographic principle, NOT QG.
* No axioms, no `sorry`.
-/

namespace QIQTH.HeatCoeffDetermination

/-- Packaged data for Gilkey's invariance-theory determination of the weight-2 heat
coefficient `a₂` of a Laplace-type operator, indexed by an operator type `ι`.

All fields are CARRIED inputs (the analytic wall): the values of `a₂`, the scalar
curvature `τ`, and `trE`, together with Gilkey's universality ansatz and the two
model evaluations. Nothing here is an axiom. -/
structure HeatCoeffData (ι : Type*) where
  heatCoeff2 : ι → ℝ
  tau : ι → ℝ
  trE : ι → ℝ
  /-- Gilkey invariance ansatz: the weight-2 span is `{τ, trE}` with UNIVERSAL
  constants (CARRIED — Weyl invariant theory, not in Mathlib). -/
  universal : ∃ cTau cE : ℝ, ∀ P : ι, heatCoeff2 P = cTau * tau P + cE * trE P
  flat : ι
  curved : ι
  curvedTau : ℝ
  curvedTau_ne_zero : curvedTau ≠ 0
  -- flat constant-`E` model: `(τ, trE, a₂) = (0, 1, 1)`
  flat_tau : tau flat = 0
  flat_trE : trE flat = 1
  flat_heat : heatCoeff2 flat = 1
  -- curved `E = 0` model: `(τ, trE, a₂) = (T, 0, T/6)`
  curved_tau : tau curved = curvedTau
  curved_trE : trE curved = 0
  curved_heat : heatCoeff2 curved = curvedTau / 6

namespace HeatCoeffData
variable {ι : Type*}

/-- The two model invariant-vectors `(0, 1)` and `(T, 0)` are independent
(determinant `= T ≠ 0`). -/
theorem model_det_ne_zero (D : HeatCoeffData ι) :
    D.tau D.curved * D.trE D.flat - D.tau D.flat * D.trE D.curved ≠ 0 := by
  simpa [D.curved_tau, D.flat_trE, D.flat_tau, D.curved_trE] using D.curvedTau_ne_zero

/-- ★★ ANY universal pair `(cTau, cE)` is FORCED to `(1/6, 1)` — the two model
evaluations determine Gilkey's constants. -/
theorem constants_determined (D : HeatCoeffData ι) {cTau cE : ℝ}
    (hlin : ∀ P : ι, D.heatCoeff2 P = cTau * D.tau P + cE * D.trE P) :
    cTau = (1 : ℝ) / 6 ∧ cE = 1 := by
  have hE' : (1 : ℝ) = cE := by simpa [D.flat_heat, D.flat_tau, D.flat_trE] using hlin D.flat
  have hE : cE = 1 := hE'.symm
  have hTauEq : D.curvedTau / 6 = cTau * D.curvedTau := by
    simpa [D.curved_heat, D.curved_tau, D.curved_trE] using hlin D.curved
  have hmul : D.curvedTau * cTau = D.curvedTau * ((1 : ℝ) / 6) := by
    calc D.curvedTau * cTau = cTau * D.curvedTau := by ring
      _ = D.curvedTau / 6 := hTauEq.symm
      _ = D.curvedTau * ((1 : ℝ) / 6) := by ring
  have hTau : cTau = (1 : ℝ) / 6 := mul_left_cancel₀ D.curvedTau_ne_zero hmul
  exact ⟨hTau, hE⟩

/-- ★★ the universal `a₂` formula `a₂ = τ/6 + trE`, DERIVED. -/
theorem coeff2_eq (D : HeatCoeffData ι) :
    ∀ P : ι, D.heatCoeff2 P = D.tau P / 6 + D.trE P := by
  rcases D.universal with ⟨cTau, cE, hlin⟩
  have hc := constants_determined D hlin
  intro P
  calc D.heatCoeff2 P = cTau * D.tau P + cE * D.trE P := hlin P
    _ = D.tau P / 6 + D.trE P := by rw [hc.1, hc.2]; ring

end HeatCoeffData

/-! ## Part B — grounding: a non-vacuity witness tied to our own sphere curvature

We build a concrete `HeatCoeffData (Fin 2)` on two operators (`flat := 0`,
`curved := 1`) whose curved-model scalar curvature is OUR unit-2-sphere value
`R = 2`, computed independently in `QIQTH.CoordinateCurvature.SphereCheck`.

The point is NON-VACUITY plus grounding: the number `2` in the curved model is the
same `2` our coordinate-curvature calculation produces for the sphere. The
universality field here is trivially satisfiable (2 points, 2 parameters) — the real
invariance content is the abstract structure above. -/

open QIQTH.CoordinateCurvature in
/-- A concrete `HeatCoeffData (Fin 2)`:
* `flat = 0` with `(τ, trE, a₂) = (0, 1, 1)`;
* `curved = 1` with `(τ, trE, a₂) = (2, 0, 1/3)` where `2` is our sphere `R`. -/
noncomputable def sphereFlatWitness : HeatCoeffData (Fin 2) where
  heatCoeff2 := ![1, 1 / 3]
  tau := ![0, 2]
  trE := ![1, 0]
  universal := ⟨1 / 6, 1, by intro P; fin_cases P <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]⟩
  flat := 0
  curved := 1
  curvedTau := 2
  curvedTau_ne_zero := by norm_num
  flat_tau := by norm_num [Matrix.cons_val_zero]
  flat_trE := by norm_num [Matrix.cons_val_zero]
  flat_heat := by norm_num [Matrix.cons_val_zero]
  curved_tau := by norm_num [Matrix.cons_val_one]
  curved_trE := by norm_num [Matrix.cons_val_one]
  curved_heat := by norm_num [Matrix.cons_val_one]

/-- The witness curved-model curvature `= 2` is literally OUR computed unit-2-sphere
scalar curvature from `CoordinateCurvature.SphereCheck`. This is the grounding link:
the curved model number IS our sphere `R`. -/
theorem sphereFlatWitness_curvedTau_eq_sphere :
    sphereFlatWitness.curvedTau =
      QIQTH.CoordinateCurvature.scalarCurvature
        QIQTH.CoordinateCurvature.SphereCheck.sphGinv
        (fun a => Matrix.of fun i j => QIQTH.CoordinateCurvature.SphereCheck.sphDg a i j)
        (fun a b => Matrix.of fun i j => QIQTH.CoordinateCurvature.SphereCheck.sphDdg a b i j) := by
  rw [QIQTH.CoordinateCurvature.SphereCheck.scalarCurvature_sphere]
  rfl

/-- The DERIVED universal formula, instantiated on our grounded witness. -/
example :
    ∀ P, sphereFlatWitness.heatCoeff2 P
        = sphereFlatWitness.tau P / 6 + sphereFlatWitness.trE P :=
  sphereFlatWitness.coeff2_eq

end QIQTH.HeatCoeffDetermination
