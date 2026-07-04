/-
  N2 (THE_NON_TRACIALITY_PLAN.md) — THE TOWER VACUUM VECTOR STATE IS NON-TRACIAL.

  The GNS vacuum `Ω = towerCyclicVec` implements the Gibbs state `ω(·) = ⟪Ω, π(·)Ω⟫`
  (`towerRep_inner_cyclicVec`). Collapsing the two-operator words through the
  ⋆-representation's multiplicativity,

      ⟪Ω, π(E_nm)(π(E_mn) Ω)⟫ = ⟪Ω, π(E_nm · E_mn) Ω⟫ = ω(E_nm · E_mn) = w_n,
      ⟪Ω, π(E_mn)(π(E_nm) Ω)⟫ = ⟪Ω, π(E_mn · E_nm) Ω⟫ = ω(E_mn · E_nm) = w_m,

  so the vacuum vector state is NOT tracial whenever the Gibbs weights differ (`w_n ≠ w_m`):
  the two orders of the matrix-unit word have DIFFERENT vacuum expectation values.

  Route: `towerRep C` is a unital ⋆-algebra homomorphism into the bounded operators, so
  `π(a)(π(b) Ω) = (π(a) * π(b)) Ω = π(a·b) Ω` (`ContinuousLinearMap.mul_apply` + `map_mul`);
  `towerRep_inner_cyclicVec` turns `⟪Ω, π(a·b) Ω⟫` into `stateOf ρ_C (a·b)`; and N1's
  `gibbs_state_not_tracial` closes the inequality.

  HONEST SCOPE (binding verdict, THE_NON_TRACIALITY_PLAN.md): this is a STATE
  non-traciality statement — the concrete inequality of the two vacuum expectation values —
  and NOTHING MORE. It is NOT a type statement: it does NOT claim `towerLimitVN` is "not
  type II₁" as an ALGEBRA statement (ω being non-tracial does not preclude some OTHER
  faithful normal tracial state; each finite stage is a full matrix algebra = type I_finite
  and DOES carry the normalized trace — ω simply is not it). No type III / III_λ / III₁
  claim, no Connes invariant, no modular-spectrum statement is made. Mathlib has no
  trace/tracial-state/type API at this pin; only the concrete inequalities are proved.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.NonTracial.FiniteNonTrace
import QIQTH.TowerGNS.CyclicVector

namespace QIQTH.NonTracial

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory QIQTH.TowerGNS
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-- **★ N2 — THE TOWER VACUUM VECTOR STATE IS NON-TRACIAL.** The vacuum vector state
    `ω(·) = ⟪Ω, π(·)Ω⟫` is not a trace: on the matrix-unit word `E_nm · E_mn` the two cyclic
    orders have DIFFERENT vacuum expectation values whenever the Gibbs weights differ,

        ⟪Ω, π(E_nm)(π(E_mn) Ω)⟫ = w_n ≠ w_m = ⟪Ω, π(E_mn)(π(E_nm) Ω)⟫.

    Multiplicativity of the ⋆-representation collapses each two-operator word,
    `π(a)(π(b) Ω) = π(a·b) Ω`; `towerRep_inner_cyclicVec` reads it back as `stateOf ρ_C (a·b)`;
    and N1's `gibbs_state_not_tracial` supplies the inequality.

    HONEST: a state-level inequality, NOT a type classification (see the file header / the
    binding verdict). -/
theorem towerVacuum_not_tracial (C : Finset M) (n m : Micro L C)
    (h : gibbsWeight L C ω β n ≠ gibbsWeight L C ω β m) :
    ⟪towerCyclicVec L ω β, towerRep L ω β C (Matrix.single n m 1)
        (towerRep L ω β C (Matrix.single m n 1) (towerCyclicVec L ω β))⟫_ℂ
      ≠ ⟪towerCyclicVec L ω β, towerRep L ω β C (Matrix.single m n 1)
        (towerRep L ω β C (Matrix.single n m 1) (towerCyclicVec L ω β))⟫_ℂ := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply,
    ← map_mul (towerRep L ω β C), ← map_mul (towerRep L ω β C),
    towerRep_inner_cyclicVec, towerRep_inner_cyclicVec]
  exact gibbs_state_not_tracial L ω β C n m h

end QIQTH.NonTracial
