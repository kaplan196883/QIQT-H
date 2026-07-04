/-
  ID4 (THE_IDENTIFICATION_PLAN.md) — ★ THE IDENTIFICATION ★: THE TRANSPORTED PHYSICAL FLOW
  IS THE SPECTRAL MODULAR FLOW OF Δ —

      towerModUnitary t = towerFlow t        (U_t = Δ^{it} as bounded operators, ∀ t)

  — the exponential-recovery wall, crossed by the eigenvector route: no `exp(it·towerGen)`
  is ever formed.  Two bounded operators agreeing on a dense span are equal, and BOTH act on
  every coerced pure matrix-unit component as the SAME pure phase
  `exp(i·t·(log w_n − log w_m))` — the flow side by `towerFlow_of_eq_sum_single` (ID1,
  extracted from the horbit block), the Δ^{it} side by `towerModUnitary_of_single` (ID3,
  through the resolvent FC), with the scalars matching character-for-character.

  Route:
  • `towerOf_coe_eq_sum_single` — the UNWEIGHTED coerced decomposition
    `↑(of C a) = Σ_{n,m} ↑(of C (E_{nm} (a n m)))` (`Matrix.matrix_eq_sum_single` pushed
    through `towerOf_sum_single_smul_coe` at scalar `1`);
  • `towerModUnitary_of_eq_sum_single` — `U_t ↑(of C a)` as the phase-rotated sum
    (`map_sum` of the CLM + ID3 per summand) — the exact `towerFlow_of_eq_sum_single` shape;
  • ★★ `towerModUnitary_eq_towerFlow` — `ContinuousLinearMap.ext_on` on R8's dense span
    (`dense_span_towerRep_cyclicVec`, the Separation.lean consumption pattern),
    `towerRep_cyclicVec_of` converting the orbit generator to `↑(of C a)` form, both sides
    rewritten to the SAME finite sum;
  • `towerFlow_eq_towerModUnitary` — the symmetric function-level form;
  • `towerGen_eq_stoneGen_towerModUnitary` — `towerGen = stoneGen (towerModUnitary)`:
    the group-level content of `towerGen = log Δ` (the generator of the physics is the
    Stone generator of the modular group of Δ).

  HONEST SCOPE (binding): the operator identification `U_t = towerFlow t` and its immediate
  function-level/generator-definition corollaries ONLY.  No Tomita covariance statement
  Δ^{it} M Δ^{−it} = M is made here (that is ID5); no J, no polar decomposition, no
  strip-KMS at the limit, no type classification.  Axiom-free.
-/
import Mathlib
import QIQTH.TowerGNS.ModularEigenbasis
import QIQTH.TowerGNS.ModularUnitaryEigen
import QIQTH.TowerGNS.CyclicVector

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open QIQTH.Spectral QIQTH.SpectralTheorem
open scoped Matrix DirectSum

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The unweighted coerced decomposition into matrix-unit components -/

/-- **The coerced pure component is the sum of its coerced matrix-unit components**:
    `↑(of C a) = Σ_{n,m} ↑(of C (E_{nm} (a n m)))` — `Matrix.matrix_eq_sum_single` under
    the coercion, via the scalar-`1` instance of `towerOf_sum_single_smul_coe`. -/
theorem towerOf_coe_eq_sum_single (C : Finset M) (a : DiamondAlg L C) :
    ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      = ∑ n : Micro L C, ∑ m : Micro L C,
          ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
            TowerGNS L ω β) := by
  have h := towerOf_sum_single_smul_coe L ω β C a (fun _ _ => (1 : ℂ))
  simp only [one_smul] at h
  conv_lhs => rw [Matrix.matrix_eq_sum_single a]
  exact h

/-! ### U_t on a general coerced pure component -/

/-- **`U_t` acts on every coerced pure component as the phase-rotated matrix-unit sum**:
    `U_t ↑(of C a) = Σ_{n,m} exp(i·t·(log w_n − log w_m)) • ↑(of C (E_{nm} (a n m)))` —
    the decomposition `towerOf_coe_eq_sum_single` pushed through the CLM (`map_sum`), ID3's
    `towerModUnitary_of_single` on each summand.  The right-hand side is CHARACTER-FOR-
    CHARACTER the `towerFlow_of_eq_sum_single` sum — the two flows now share one normal
    form on the dense span. -/
theorem towerModUnitary_of_eq_sum_single (t : ℝ) (C : Finset M) (a : DiamondAlg L C) :
    towerModUnitary L ω β t
        ((towerOf L ω β C a : TowerPre L ω β) : TowerGNS L ω β)
      = ∑ n : Micro L C, ∑ m : Micro L C,
          Complex.exp (Complex.I * t * ((Real.log (gibbsWeight L C ω β n)
              - Real.log (gibbsWeight L C ω β m) : ℝ) : ℂ))
            • ((towerOf L ω β C (Matrix.single n m (a n m)) : TowerPre L ω β) :
                TowerGNS L ω β) := by
  rw [towerOf_coe_eq_sum_single L ω β C a, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact towerModUnitary_of_single L ω β t C n m (a n m)

/-! ### ★★ THE IDENTIFICATION: U_t = towerFlow t -/

/-- **★★ THE IDENTIFICATION — the transported physical flow IS the spectral modular flow
    of Δ**: `towerModUnitary t = towerFlow t` as bounded operators, for every `t` — the
    exponential-recovery wall crossed WITHOUT forming `exp(it·towerGen)`: both bounded
    operators act on R8's dense orbit span by the SAME finite phase-rotated matrix-unit sum
    (`towerModUnitary_of_eq_sum_single` vs `towerFlow_of_eq_sum_single`), and
    `ContinuousLinearMap.ext_on` over `dense_span_towerRep_cyclicVec` closes.  The modular
    theory of the physics equals the modular theory of the state, at the operator-group
    level. -/
theorem towerModUnitary_eq_towerFlow (t : ℝ) :
    towerModUnitary L ω β t = towerFlow L ω β t := by
  refine ContinuousLinearMap.ext_on (dense_span_towerRep_cyclicVec L ω β) ?_
  rintro v ⟨C, a, rfl⟩
  rw [towerRep_cyclicVec_of L ω β C a,
    towerModUnitary_of_eq_sum_single L ω β t C a,
    towerFlow_of_eq_sum_single L ω β t C a]

/-- **The identification, flow-first form**: `towerFlow t = towerModUnitary t` — the
    symmetric reading (the physical flow is `Δ^{it}`), for rewriting flow-side statements
    into modular-side statements in ID5. -/
theorem towerFlow_eq_towerModUnitary (t : ℝ) :
    towerFlow L ω β t = towerModUnitary L ω β t :=
  (towerModUnitary_eq_towerFlow L ω β t).symm

/-! ### The generator identification, group-level -/

/-- **`towerGen` is the Stone generator of the modular group of Δ**:
    `towerGen = stoneGen (towerModUnitary)` — the definition `towerGen := stoneGen
    (towerFlow)` rewritten under the function-level identification: the group-level content
    of `towerGen = log Δ`. -/
theorem towerGen_eq_stoneGen_towerModUnitary :
    towerGen L ω β = QIQTH.Spectral.stoneGen (towerModUnitary L ω β) := by
  have h : towerModUnitary L ω β = towerFlow L ω β :=
    funext fun t => towerModUnitary_eq_towerFlow L ω β t
  rw [h]
  rfl

end QIQTH.TowerGNS
