/-
  THE DECOUPLING SHADOW DS1 (THE_DECOUPLING_SHADOW_PLAN.md) — bounded-sector CCR recovery.

  The finite analogue of "the parent contains the free sector" (the weak half of Maldacena's
  decoupling argument, in its honest finite form): at FIXED occupation numbers, the truncated
  oscillator's matrix elements are D-INDEPENDENT once the cutoff clears them, and the commutator's
  matrix elements STABILIZE to the exact-CCR values — the truncation defect lives only at the top
  level, which bounded occupations eventually never see.

  ⚠ HONEST SCOPE (binding verdict): this forces the free-oscillator sector in the
  bounded-occupation sense ONLY — matrix elements and finite support, no operator norms, no
  unbounded operators; it does not force the screen geometry or the Newton constant. NOT a full
  decoupling derivation.
-/
import Mathlib
import QIQTH.CornerConstruction

namespace QIQTH.Decoupling

open QIQTH.CornerConstruction
open scoped Matrix

/-- **Ladder matrix elements at fixed occupations are D-independent**: the entry
    `⟨m|a_D|n⟩ = √n·δ_{m+1,n}` carries no reference to the cutoff. -/
theorem lowering_matrixElement_stable (D : ℕ) (m n : ℕ) (hm : m < D) (hn : n < D) :
    QIQTH.CornerConstruction.lowering D ⟨m, hm⟩ ⟨n, hn⟩
      = if m + 1 = n then ((Real.sqrt n : ℝ) : ℂ) else 0 := rfl

/-- **The commutator's matrix elements STABILIZE to the exact-CCR values**: for occupations
    strictly below the top level, `⟨m|[a_D, a_D†]|n⟩ = δ_{mn}` — the truncation defect
    (`−D·P_top`) is invisible at bounded occupations. -/
theorem commutator_matrixElement_stabilizes (D m n : ℕ) (hm : m + 1 < D) (hn : n + 1 < D) :
    (QIQTH.CornerConstruction.lowering D * (QIQTH.CornerConstruction.lowering D)ᴴ
        - (QIQTH.CornerConstruction.lowering D)ᴴ * QIQTH.CornerConstruction.lowering D)
        ⟨m, Nat.lt_of_succ_lt hm⟩ ⟨n, Nat.lt_of_succ_lt hn⟩
      = if m = n then 1 else 0 := by
  rw [QIQTH.CornerConstruction.truncated_ladder_commutator']
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    QIQTH.CornerConstruction.topProjector, Matrix.diagonal_apply, Fin.mk.injEq,
    smul_eq_mul]
  by_cases h : m = n
  · subst h
    rw [if_pos rfl, if_pos rfl, if_neg (show ¬ m + 1 = D by omega)]
    simp
  · rw [if_neg h, if_neg h]
    simp

/-- **DS1 CAPSTONE — the bounded-occupation sector EVENTUALLY carries exact CCR**: for every
    fixed pair of occupations, for all sufficiently large cutoffs the truncated commutator's
    matrix element equals the exact-CCR value — the free-oscillator sector is FORCED by the
    cutoff limit (the `Filter.atTop` form of the decoupling shadow's weak statement). -/
theorem commutator_eventually_exact (m n : ℕ) :
    ∀ᶠ D in Filter.atTop,
      ∃ (hm : m + 1 < D) (hn : n + 1 < D),
        (QIQTH.CornerConstruction.lowering D * (QIQTH.CornerConstruction.lowering D)ᴴ
            - (QIQTH.CornerConstruction.lowering D)ᴴ * QIQTH.CornerConstruction.lowering D)
            ⟨m, Nat.lt_of_succ_lt hm⟩ ⟨n, Nat.lt_of_succ_lt hn⟩
          = if m = n then 1 else 0 := by
  filter_upwards [Filter.eventually_gt_atTop (max m n + 1)] with D hD
  have hmax1 := le_max_left m n
  have hmax2 := le_max_right m n
  have hm : m + 1 < D := by omega
  have hn : n + 1 < D := by omega
  exact ⟨hm, hn, commutator_matrixElement_stabilizes D m n hm hn⟩

end QIQTH.Decoupling
