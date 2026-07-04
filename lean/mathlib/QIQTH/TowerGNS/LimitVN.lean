/-
  THE REPRESENTATION R9 (THE_REPRESENTATION_PLAN.md) — THE CAPSTONE: the directed-union limit
  von Neumann algebra of the tower representation.

  Each finite corner contributes its representation image `towerStageAlg C := (towerRep C).range`,
  a unital ⋆-subalgebra of B(TowerGNS). R7's compatibility capstone (`towerRep_cornerEmbed`)
  makes the family MONOTONE in the corner: for `C ⊆ C'` every `π_C(a)` is `π_{C'}(ι a)`, so the
  stage algebras form a directed system inside ONE B(H) — exactly the hypothesis of the C9
  closure layer. `towerLimitVN := limitVN towerStageAlg` is the refinement-tower limit von
  Neumann algebra, with membership characterized by SOT-approximation from the finite stages
  (`mem_towerLimitVN_iff`), and the R8 capstone repackaged as the vector-state restriction
  statement (`towerVectorState_stage`): the vector state of Ω restricted to stage C is the
  finite-corner Gibbs state.

  HONEST SCOPE: the LIMIT ALGEBRA IS NAMED AND CHARACTERIZED, nothing more — no classification
  of its type, no separating property of Ω, no modular theory of the limit state is claimed.

  The ℕ-instantiation `freqTowerLimitVN` is the tower of the code's frequency list
  (M := ℕ, corners = finite mode sets).
-/
import Mathlib
import QIQTH.TowerGNS.CyclicVector
import QIQTH.VonNeumann.DirectedUnionVN

namespace QIQTH.TowerGNS

open QIQTH.Keystone QIQTH.Tower QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped ComplexOrder Matrix DirectSum InnerProductSpace

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (ω : M → ℝ) (β : ℝ)

/-! ### The stage algebras — the representation images of the finite corners -/

/-- **The stage algebra**: the image of the corner algebra `DiamondAlg L C` under the tower
    representation — a unital ⋆-subalgebra of the bounded operators on the tower Hilbert
    space. -/
noncomputable def towerStageAlg (C : Finset M) :
    StarSubalgebra ℂ (TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :=
  (towerRep L ω β C).range

/-- **The stage algebras are monotone in the corner**: for `C ⊆ C'` every represented operator
    `π_C(a)` is also `π_{C'}(ι a)` by the R7 compatibility capstone — the family is a directed
    system inside ONE B(H). -/
theorem towerStageAlg_mono : Monotone (towerStageAlg L ω β) := by
  intro C C' h T hT
  obtain ⟨a, rfl⟩ := hT
  exact ⟨cornerEmbed L C C' h a, towerRep_cornerEmbed L ω β C C' h a⟩

/-! ### R9 CAPSTONE — the limit von Neumann algebra of the tower -/

/-- **R9 CAPSTONE — THE LIMIT VON NEUMANN ALGEBRA OF THE TOWER**: the directed-union limit
    (C9's `limitVN`) of the stage algebras — the von Neumann algebra generated on the tower
    Hilbert space by all the finite-corner representations together. (Named and characterized
    ONLY — its type is NOT classified here.) -/
noncomputable def towerLimitVN : VonNeumannAlgebra (TowerGNS L ω β) :=
  QIQTH.VonNeumann.limitVN (towerStageAlg L ω β) (towerStageAlg_mono L ω β).directed_le

/-- Every represented corner element lies in the limit von Neumann algebra. -/
theorem towerRep_mem_towerLimitVN (C : Finset M) (a : DiamondAlg L C) :
    towerRep L ω β C a ∈ towerLimitVN L ω β :=
  QIQTH.VonNeumann.stage_subset_limitVN (towerStageAlg L ω β)
    (towerStageAlg_mono L ω β).directed_le C ⟨a, rfl⟩

/-- **The membership characterization**: an operator lies in the tower limit von Neumann
    algebra iff it is SOT-approximable from the union of the finite stages (C9's capstone,
    instantiated at the tower). -/
theorem mem_towerLimitVN_iff (T : TowerGNS L ω β →L[ℂ] TowerGNS L ω β) :
    T ∈ towerLimitVN L ω β
      ↔ QIQTH.VonNeumann.SOTApprox
          (⋃ C, (towerStageAlg L ω β C : Set (TowerGNS L ω β →L[ℂ] TowerGNS L ω β))) T :=
  QIQTH.VonNeumann.mem_limitVN_iff (towerStageAlg L ω β)
    (towerStageAlg_mono L ω β).directed_le T

/-- **The vector-state restriction**: the vector state of the cyclic vector Ω, restricted to
    stage C, IS the finite-corner Gibbs state — the R8 capstone repackaged for the limit
    algebra's finite stages. -/
theorem towerVectorState_stage (C : Finset M) (a : DiamondAlg L C) :
    ⟪towerCyclicVec L ω β, towerRep L ω β C a (towerCyclicVec L ω β)⟫_ℂ
      = stateOf (gibbsDensity L C ω β) a :=
  towerRep_inner_cyclicVec L ω β C a

/-! ### The ℕ-instantiation — the QIQT frequency tower -/

/-- **The frequency-tower limit von Neumann algebra**: the tower of the code's frequency list —
    `M := ℕ` indexes the modes (the frequency list `ω : ℕ → ℝ`), the corners are the finite
    mode sets, and the limit von Neumann algebra is the directed-union limit of all
    finite-mode Gibbs-GNS representation images on the one tower Hilbert space. -/
noncomputable def freqTowerLimitVN (L : LinkDims ℕ) (ω : ℕ → ℝ) (β : ℝ) :
    VonNeumannAlgebra (TowerGNS L ω β) :=
  towerLimitVN L ω β

end QIQTH.TowerGNS
