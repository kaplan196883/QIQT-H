/-
  QIQT-H Theorem 6 — Effective Macroscopic Definiteness (inner chain)
  -------------------------------------------------------------------
  Mathlib-rooted variant.  Real arithmetic is `ℝ`, not axiomatized.

  See `../../Theorem6.lean` for the self-contained standalone variant
  (axiomatizes 5 ordered-field facts).  This variant discharges those
  axioms against `Mathlib.Data.Real.Basic`.

  Informal statement (QIQT_Foundations_Paper §7.6 / QIQT_Math §9A):

    For a branch decomposition {(p̃_k, ω_{k,R})} of a global state
    relative to a region R, with

        D_k := χ_R(ω_{k,R}),     D̄ := χ_R(ω̄_R),
        I   := I_Hol^R,          C  := C(R) = A(∂R)/(4 ℓ_P²),

    Donald's identity says  Σ_k p̃_k D_k = D̄ + I.  Combined with the
    holographic bound (each D_k ≤ C, hence Σ p̃_k D_k ≤ C) and D̄ ≥ 0,
    we get  I ≤ C.  Chained with Holevo, Fano and an experimental
    slack: H_ε ≤ (C − I_0 + η_0) + η_def.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith

namespace QIQTH
namespace Theorem6

/- ── Branch decomposition data ───────────────────────────────────── -/

/-- Data of a branch decomposition relative to a region R, packaging
    exactly the quantities Theorem 6's inner chain consumes. -/
structure BranchData where
  /-- Σ_k p̃_k · χ_R(ω_{k,R}) — weighted single-branch relative entropy. -/
  S      : ℝ
  /-- χ_R(ω̄_R) — mixed-state relative entropy. -/
  D_bar  : ℝ
  /-- I_Hol^R — Holographic mutual information. -/
  I      : ℝ
  /-- C(R) = A(∂R)/(4 ℓ_P²) — holographic capacity. -/
  C      : ℝ
  /-- **Donald's identity**:  Σ p̃_k D_k = D̄ + I. -/
  donald          : S = D_bar + I
  /-- **Holographic bound** applied branchwise plus Σ p̃_k = 1:
      Σ p̃_k D_k ≤ C. -/
  sum_le_capacity : S ≤ C
  /-- Relative entropy is non-negative. -/
  D_bar_nonneg    : (0 : ℝ) ≤ D_bar

namespace BranchData

variable (B : BranchData)

/-- **Donald-bound lemma.**
    Donald's identity, the branchwise holographic bound, and
    non-negativity of the mixed-state relative entropy together
    imply that the Holographic mutual information is bounded by
    the holographic capacity:  I_Hol^R ≤ C(R).

    All five "axioms" of the standalone variant — `le_trans`,
    `add_le_add_right`, `sub_le_self_of_nonneg`, `eq_sub_of_sum`,
    `le_refl` — are now Mathlib theorems automatically applied. -/
theorem holevo_le_capacity : B.I ≤ B.C := by
  have hI : B.I = B.S - B.D_bar := by linarith [B.donald]
  rw [hI]
  linarith [B.D_bar_nonneg, B.sum_le_capacity]

end BranchData

/- ── Outer chain ─────────────────────────────────────────────────── -/

/-- **QIQT-H Theorem 6 — Effective Macroscopic Definiteness (inner-chain form).**

    Given a branch decomposition `B`, an "experimental slack"
    `B.I ≤ (C − I_0) + η_0`, a Holevo accessibility bound
    `I_acc ≤ B.I`, and a Fano-style bound `H_ε ≤ I_acc + η_def`,
    conclude  H_ε ≤ (C(R) − I_0) + η_0 + η_def. -/
theorem effective_definiteness
    (B : BranchData)
    (H_eps I_acc I_0 eta_0 eta_def : ℝ)
    (acc_le      : I_acc ≤ B.I)
    (fano_le     : H_eps ≤ I_acc + eta_def)
    (capacity_le : B.I ≤ (B.C - I_0) + eta_0) :
    H_eps ≤ ((B.C - I_0) + eta_0) + eta_def := by
  linarith

end Theorem6
end QIQTH
