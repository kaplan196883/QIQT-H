/-
  LorentzWitness — a CONCRETE NON-TRIVIAL model of the LorentzSelectionStrong
  conditional interface.

  Motivation (GPT-5.5-pro review): the abstract interface admits the trivial
  one-point net, so "a model exists" is vacuous.  This module exhibits a
  *non-degenerate* model — a genuine 2-outcome record system with a real Born
  probability distribution (not a point mass) — proving the interface has
  non-trivial content.  It does NOT touch the continuum realization (still open);
  it refutes "only the trivial model satisfies the structure."

  Geometry: a single causal diamond (`Diam := Unit`).  Record fibre: `Fin 2`
  (two macroscopic record sectors).  Hilbert space: `ℂ²`.  State: the rational
  unit vector `ψ = (3/5, 4/5)` (so `‖ψ‖² = 9/25 + 16/25 = 1`, no √2).  Effects:
  the two diagonal rank-1 projections (a projective measurement / PVM).  Born
  weights: `ω(0) = 9/25`, `ω(1) = 16/25` — a genuine spread distribution.
-/

import QIQTH.LorentzSelection
import QIQTH.LorentzSelectionStrong
import Mathlib.Tactic

namespace QIQTH
namespace LorentzWitness

open LorentzSelection
open LorentzSelectionStrong
open GleasonSelector
open Matrix
open scoped BigOperators ComplexOrder

/- ── The single-diamond record presheaf with a 2-element fibre ──────────── -/

/-- One causal diamond. -/
abbrev Diam := Unit

/-- Record presheaf: each (the) diamond carries the 2-element record sector set
    `Fin 2`; restriction is the identity (only `() ≤ ()`).  Marked `reducible`
    so `Prec.X () ` unfolds to `Fin 2` during instance search. -/
@[reducible] def Prec : RecordPresheaf Unit where
  X := fun _ => Fin 2
  restrict := fun _ x => x
  restrict_id := fun _ => rfl
  restrict_comp := fun _ _ _ => rfl

/-- A global section: select record sector `0`. -/
def sec0 : GlobalSection Prec where
  val := fun _ => 0
  consistent := fun _ => rfl

/- ── The Born data: state (3/5, 4/5) and the diagonal PVM ───────────────── -/

/-- The real components of the unit state. -/
noncomputable def psiR : Fin 2 → ℝ := ![3/5, 4/5]

/-- The rational unit state `(3/5, 4/5) ∈ ℂ²` (real entries coerced to `ℂ`, so
    conjugation acts trivially). -/
noncomputable def psi : Fin 2 → ℂ := fun i => (psiR i : ℂ)

/-- The diagonal rank-1 projection onto basis vector `i`. -/
noncomputable def Eproj (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun j => if j = i then 1 else 0)

theorem psi_unit : star psi ⬝ᵥ psi = 1 := by
  simp only [psi, psiR, dotProduct, Fin.sum_univ_two, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_add]
  norm_num

theorem Eproj_complete : ∑ i, Eproj i = 1 := by
  ext a b
  simp only [Eproj, Matrix.sum_apply, Matrix.diagonal_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem Eproj_herm (i : Fin 2) : (Eproj i)ᴴ = Eproj i := by
  rw [Eproj, Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

theorem Eproj_idem (i : Fin 2) : (Eproj i) * (Eproj i) = Eproj i := by
  rw [Eproj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

/-- The uniform PVM Born data for the witness.  Reducible so `Bwit.d` unfolds to
    `2` and the fields unfold in the weight computations. -/
@[reducible] noncomputable def Bwit : UniformPVMData Prec where
  fin := fun _ => inferInstance
  ddeq := fun _ => inferInstance
  d := 2
  ψ := fun _ => psi
  ψ_unit := fun _ => psi_unit
  E := fun _ i => Eproj i
  complete := fun _ => Eproj_complete
  proj_herm := fun _ i => Eproj_herm i
  proj_idem := fun _ i => Eproj_idem i

/- ── The (trivial single-element) group action and unitary covariance ───── -/

/-- The acting group: the trivial group `Perm (Fin 1)` (one element). -/
abbrev G := Equiv.Perm (Fin 1)

/-- The trivial group action on the single-diamond presheaf. -/
def Awit : GroupAction G Prec where
  act := fun _ => OrderIso.refl Unit
  γ := fun _ _ => Equiv.refl (Fin 2)
  natural := by intros; rfl
  act_one := rfl
  act_mul := fun _ _ => rfl

/-- The trivial unitary covariance (`U = 1`). -/
noncomputable def Cwit : UnitaryCovariance Awit Bwit.toUniformBornData where
  U := fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  U_unit := fun _ _ => by rw [Matrix.conjTranspose_one, Matrix.one_mul]
  ψ_cov := fun _ _ => by simp [Awit, Bwit, one_mulVec]
  E_cov := fun _ _ i => by
    simp only [Awit, Bwit, Equiv.refl_apply, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]

/- ── Non-degeneracy: this is NOT the trivial one-point model ─────────────── -/

/-- The record fibre has **two** elements (the trivial one-point net has one). -/
theorem witness_fibre_card : Fintype.card (Prec.X ()) = 2 := by
  simp [Prec]

/-- The Born weight of sector `0` is `9/25`. -/
theorem witness_weight_zero : ubornω Bwit.toUniformBornData () 0 = 9 / 25 := by
  simp only [ubornω, Bwit, born, Eproj, psi, psiR, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Matrix.diagonal_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_zero]
  norm_num

/-- The Born weight of sector `1` is `16/25`. -/
theorem witness_weight_one : ubornω Bwit.toUniformBornData () 1 = 16 / 25 := by
  simp only [ubornω, Bwit, born, Eproj, psi, psiR, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, Matrix.diagonal_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_zero]
  norm_num

/-- **The distribution is genuinely spread** (not a point mass): both weights are
    strictly between `0` and `1`. -/
theorem witness_nondegenerate :
    0 < ubornω Bwit.toUniformBornData () 0 ∧ ubornω Bwit.toUniformBornData () 0 < 1
    ∧ 0 < ubornω Bwit.toUniformBornData () 1 ∧ ubornω Bwit.toUniformBornData () 1 < 1 := by
  rw [witness_weight_zero, witness_weight_one]
  norm_num

/-- **The capstone witness**: a CONCRETE covariant probability distribution that
    is non-degenerate.  Combining `covariantProbability_of_unitaryPVM` (the
    interface is satisfied) with `witness_nondegenerate` (it is not the trivial
    one-point model), this proves the LorentzSelectionStrong conditional
    interface has genuine non-trivial content. -/
theorem witness_covariantProbability :
    CovariantProbability Awit Bwit.toUniformBornData :=
  covariantProbability_of_unitaryPVM Cwit

/- ── Witness B: a NON-TRIVIAL group acting non-trivially on diamonds ────── -/

/-  The first witness used the trivial group.  Here the acting group genuinely
    moves the geometry: two causal diamonds with the *indiscrete* preorder (so
    every permutation is an order-isomorphism), and `G = Perm` permuting them.
    The record/Born data is homogeneous (the same PVM at every diamond), so the
    covariant-probability theorems hold over a non-trivial Poincaré-style orbit —
    exercising the covariance machinery, not just the probability content.  Still
    rational (no √2), still axiom-free. -/

/-- Two causal diamonds. -/
inductive D2 | d0 | d1
deriving DecidableEq, Fintype

/-- The indiscrete preorder: every diamond is `≤` every diamond, so every
    bijection of `D2` is an order-isomorphism (the geometry imposes no order
    constraint a permutation could violate). -/
instance : Preorder D2 where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

/-- Lift a permutation of diamonds to an order-isomorphism (free, since `≤` is
    indiscrete). -/
def actD (g : Equiv.Perm D2) : D2 ≃o D2 where
  toEquiv := g
  map_rel_iff' := Iff.rfl

/-- Record presheaf over the two diamonds: each carries a `Fin 2` fibre. -/
@[reducible] def Prec2 : RecordPresheaf D2 where
  X := fun _ => Fin 2
  restrict := fun _ x => x
  restrict_id := fun _ => rfl
  restrict_comp := fun _ _ _ => rfl

/-- Homogeneous PVM Born data: the same state and PVM at every diamond. -/
@[reducible] noncomputable def Bwit2 : UniformPVMData Prec2 where
  fin := fun _ => inferInstance
  ddeq := fun _ => inferInstance
  d := 2
  ψ := fun _ => psi
  ψ_unit := fun _ => psi_unit
  E := fun _ i => Eproj i
  complete := fun _ => Eproj_complete
  proj_herm := fun _ i => Eproj_herm i
  proj_idem := fun _ i => Eproj_idem i

/-- The acting group: all permutations of the two diamonds. -/
abbrev G2 := Equiv.Perm D2

/-- `Perm D2` is abelian (two elements), checked by `decide`. -/
theorem perm_d2_comm (g₁ g₂ : Equiv.Perm D2) : g₁ * g₂ = g₂ * g₁ := by
  revert g₁ g₂; decide

/-- The group action: `g` permutes diamonds; the fibres and records are carried
    identically (`γ = refl`). -/
def Awit2 : GroupAction G2 Prec2 where
  act := actD
  γ := fun _ _ => Equiv.refl (Fin 2)
  natural := by intros; rfl
  act_one := by ext y; rfl
  act_mul := fun g₁ g₂ => by
    ext y
    show (g₁ * g₂) y = g₂ (g₁ y)
    rw [perm_d2_comm g₁ g₂]; rfl

/-- The unitary covariance: the homogeneous data is carried with `U = 1`. -/
noncomputable def Cwit2 : UnitaryCovariance Awit2 Bwit2.toUniformBornData where
  U := fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  U_unit := fun _ _ => by rw [Matrix.conjTranspose_one, Matrix.one_mul]
  ψ_cov := fun _ _ => by simp [Awit2, Bwit2, one_mulVec]
  E_cov := fun _ _ i => by
    simp only [Awit2, Bwit2, Equiv.refl_apply, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]

/-- **The group acts NON-trivially on the geometry**: the swap of the two
    diamonds moves `d0` to `d1`.  (Contrast the trivial-group Witness A.) -/
theorem witness2_action_nontrivial :
    (Awit2.act (Equiv.swap D2.d0 D2.d1)) D2.d0 = D2.d1 := by
  simp [Awit2, actD]

/-- **Witness B capstone**: a concrete `CovariantProbability` for a NON-trivial
    group acting non-trivially on the diamond geometry — the covariance machinery
    is exercised over a genuine orbit, not just the probability content. -/
theorem witness2_covariantProbability :
    CovariantProbability Awit2 Bwit2.toUniformBornData :=
  covariantProbability_of_unitaryPVM Cwit2

end LorentzWitness
end QIQTH
