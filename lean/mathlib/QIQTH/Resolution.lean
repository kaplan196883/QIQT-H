/-
  QIQT-H Resolution — Lemma 1 + Theorem 3, Mathlib-rooted variant.
  ------------------------------------------------------------------
  Mathlib-rooted variant carries the *continuous* form:
      ε(R) = (1 : ℝ) / 2^Q > 0
  rather than the discrete `numBins Q > 0` of the standalone variant.

  See `../../Resolution.lean` for the standalone version.

  Informal statements:

    LEMMA 1 (QIQT_Foundations_Paper §5.1).
        Under (FQ), formal amplitudes within precision ε(R) of a
        value k ∈ {0, 1} are physically equivalent to k.

    THEOREM 3 (QIQT_Foundations_Paper §7.2).
        Under (FQ), the per-run wave function in any bounded region R
        has a finite physical resolution floor ε(R) > 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

namespace QIQTH
namespace Resolution

/- ── Continuous precision threshold from FQ information bound ────── -/

/-- Continuous-form resolution threshold induced by an FQ information
    bound `Q` (bits):  ε(Q) := (1/2)^Q. -/
noncomputable def eps (Q : ℕ) : ℝ := (1 / 2 : ℝ) ^ Q

/-- **Theorem 3 (positive resolution floor — continuous form).**

    For any finite information bound `Q : ℕ`, the FQ-induced resolution
    threshold is strictly positive. -/
theorem eps_pos (Q : ℕ) : 0 < eps Q := by
  unfold eps
  positivity

/-- The threshold is at most 1 — amplitudes are always comparable. -/
theorem eps_le_one (Q : ℕ) : eps Q ≤ 1 := by
  unfold eps
  exact pow_le_one₀ (by norm_num) (by norm_num)

/- ── FQ region structure with continuous tolerance ──────────────── -/

/-- An (FQ)-constrained region with a continuous-precision tolerance
    interpretation.
    Amplitudes are real-valued (think of `|amplitude|` or a real-part
    cross-section in the paper); the FQ floor `eps Q` is the minimum
    distinguishable difference. -/
structure FQRegion where
  /-- Information bound Q_R in bits — finite by (FQ). -/
  Q : ℕ

namespace FQRegion

variable (R : FQRegion)

/-- The resolution threshold induced by R's FQ bound. -/
noncomputable def epsR : ℝ := eps R.Q

/-- The threshold is positive (a corollary of Theorem 3). -/
theorem epsR_pos : 0 < R.epsR := eps_pos R.Q

/-- *Physical equivalence* (tolerance form):  formal amplitudes within
    `epsR` of each other are FQ-indistinguishable. -/
def physEq (x y : ℝ) : Prop := |x - y| < R.epsR

/-- A formal amplitude is *physically zero* iff it is within `epsR` of 0. -/
def isPhysZero (x : ℝ) : Prop := |x| < R.epsR

/-- A formal amplitude is *physically one* iff it is within `epsR` of 1. -/
def isPhysOne (x : ℝ) : Prop := |x - 1| < R.epsR

/-- **Lemma 1 (near-extreme indistinguishability) — zero side, continuous form.**

    A formal amplitude `x` with `|x| < ε(R)` is physically equivalent
    to the value `0` itself (where the value 0 is trivially within
    `ε(R)` of itself).

    The continuous form: amplitudes within ε(R) of 0 are physically
    equivalent to 0. -/
theorem lemma1_zero (x : ℝ) (hx : R.isPhysZero x) : R.physEq x 0 := by
  unfold physEq isPhysZero at *
  simpa using hx

/-- **Lemma 1 — one side, continuous form.** -/
theorem lemma1_one (x : ℝ) (hx : R.isPhysOne x) : R.physEq x 1 := by
  unfold physEq isPhysOne at *
  exact hx

/-- `physEq` is reflexive. -/
theorem physEq_refl (x : ℝ) : R.physEq x x := by
  unfold physEq
  simpa using R.epsR_pos

/-- `physEq` is symmetric. -/
theorem physEq_symm {x y : ℝ} (h : R.physEq x y) : R.physEq y x := by
  unfold physEq at *
  rw [abs_sub_comm]
  exact h

/- `physEq` is **not** transitive in general — it is a tolerance
   pre-relation, not an equivalence relation.  This is faithful to
   the paper: FQ-equivalence is the (continuous) `≈_ε` relation, not
   a true equivalence.  (For an equivalence-relation formalization,
   use the discrete-bin standalone variant.) -/

end FQRegion

end Resolution
end QIQTH
