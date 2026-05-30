/-
  EquivarianceGap — Bohmian-style measure preservation is NOT implied
  by support preservation.

  GPT-5.5-pro fourth audit:

      Under the canonical (state-space) reading, the exactly-unitary
      dynamics carries instantiable regional contents to instantiable
      regional contents (the §7.6 closure property — *support
      preservation* of the admissible set).  But support preservation
      is NOT *measure preservation* in the Bohmian sense.

      Bohmian mechanics has |ψ|²-equivariance: if μ_t = |ψ_t|² at one
      time, the guided dynamics preserves this throughout.  QIQT-H's
      closure property (instantiable contents stay instantiable) does
      NOT give an analogous Born-measure preservation theorem.

      Counterexample: a swap bijection on a 2-point space with non-
      uniform measure (3/4, 1/4).  Support is preserved (the swap maps
      the 2-point space to itself), but the measure is shuffled.

  Strategic implication: the paper must not slide from "the set of
  instantiable regional contents is dynamically invariant" to "the Born
  distribution is dynamically preserved".  A genuine equivariance
  theorem (analogous to Bohmian |ψ|²-equivariance) is a *genuine
  additional commitment* (hypothesis (iii) of Theorem 5), not a
  consequence of the framework's current postulates.  Note this is
  about the across-run typicality measure, not about the dynamics,
  which remains exactly unitary.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace QIQTH
namespace EquivarianceGap

/-- Push-forward of a measure `μ : α → ℝ` under a map `T : α → β`. -/
noncomputable def pushForward {α β : Type*} [Fintype α] [DecidableEq β]
    (T : α → β) (μ : α → ℝ) : β → ℝ :=
  fun b => ∑ a, if T a = b then μ a else 0

/-- A dynamics `T` is **support-preserving** for `S` iff every point in
    `S` maps to a point in `S`. -/
def SupportPreserving {α : Type*} (S : Set α) (T : α → α) : Prop :=
  ∀ a ∈ S, T a ∈ S

/-- A dynamics `T` is **measure-preserving** for `μ` iff its push-forward
    coincides with `μ` (Bohmian equivariance form). -/
def MeasurePreserving {α : Type*} [Fintype α] [DecidableEq α]
    (T : α → α) (μ : α → ℝ) : Prop :=
  pushForward T μ = μ

/-- The swap bijection on Fin 2:  0 ↔ 1. -/
def swap : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

/-- The non-uniform measure on Fin 2:  μ(0) = 3/4, μ(1) = 1/4. -/
noncomputable def μ_nonuniform : Fin 2 → ℝ := fun i => if i = 0 then 3/4 else 1/4

private theorem swap_at_0 : swap 0 = 1 := rfl
private theorem swap_at_1 : swap 1 = 0 := rfl

private theorem swap_bijective : Function.Bijective swap := by
  refine ⟨?_, ?_⟩
  · -- Injectivity: swap is its own inverse, so injective.
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [swap]
  · -- Surjectivity
    intro b
    fin_cases b
    · exact ⟨1, swap_at_1⟩
    · exact ⟨0, swap_at_0⟩

/-- **The equivariance gap counterexample.**

    On `Fin 2`, the swap `0 ↔ 1` is a bijection (hence support-preserving).
    But with non-uniform measure `μ(0) = 3/4`, `μ(1) = 1/4`, push-forward
    differs from `μ`:

        pushForward swap μ 0 = μ 1 = 1/4 ≠ 3/4 = μ 0.

    Hence support preservation does NOT imply measure preservation,
    even for trivially reversible dynamics. -/
theorem support_preservation_does_not_imply_measure_preservation :
    ∃ (T : Fin 2 → Fin 2) (μ : Fin 2 → ℝ),
      Function.Bijective T ∧
      SupportPreserving (Set.univ : Set (Fin 2)) T ∧
      ¬ MeasurePreserving T μ := by
  refine ⟨swap, μ_nonuniform, swap_bijective, ?_, ?_⟩
  · -- Support preservation: trivially true on the universe.
    intro _ _; trivial
  · -- pushForward swap μ ≠ μ.
    intro h
    -- Evaluate at index 0.
    have h_at_0 := congr_fun h 0
    -- pushForward swap μ 0 = ∑ i : Fin 2, (if swap i = 0 then μ i else 0)
    --                     = (if swap 0 = 0 then μ 0 else 0) + (if swap 1 = 0 then μ 1 else 0)
    --                     = 0 + μ 1                   (swap 0 = 1, swap 1 = 0)
    --                     = μ_nonuniform 1 = 1/4.
    -- μ_nonuniform 0 = 3/4.
    -- So h_at_0 says 1/4 = 3/4, contradiction.
    have h_lhs : pushForward swap μ_nonuniform 0 = 1/4 := by
      unfold pushForward
      rw [Fin.sum_univ_two]
      rw [swap_at_0, swap_at_1]
      simp [μ_nonuniform]
    have h_rhs : μ_nonuniform 0 = 3/4 := by simp [μ_nonuniform]
    rw [h_lhs, h_rhs] at h_at_0
    linarith

end EquivarianceGap
end QIQTH
