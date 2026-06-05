/-
# One-site Born bridge (prize step C2)

The no-collapse core (`CoreNoCollapse.FinPVM`) already has the record weights
`weight ψ r = ‖E r ψ‖²` and proves they sum to one.  To JOIN with the Born layer we need
the *calibration* fact: these weights are exactly the values of the prepared state's
effect-valuation on the PVM effects — i.e. the single-trial probability of a pointer value
is the Born value `⟪ψ, E r ψ⟫`.

This file proves that one-site bridge for the canonical **vector-state** valuation
`ν_ψ(E) = Re⟪ψ, E ψ⟫`: for a PVM projection `E r` (self-adjoint idempotent),
`ν_ψ(E r) = ‖E r ψ‖² = weight ψ r` (`vectorState_eq_weight`).  Packaged as a genuine
probability vector `bornVec ψ` (nonneg, sums to one) it plugs directly into
`BornTypicalityFinite`/`BornMeasureUniqueness` as the single-trial law `p`.

(Per GPT-5.5-pro's C2: this is the MVP one-site law with `ν = vectorState ψ`; identifying
`vectorState ψ` with the UNIQUE effect-Gleason valuation `tr(ρ_ψ ·)` of `EffectGleason` is a
separate uniqueness step, deferred — the operator-side weights are what the ensemble join
C3/C4 consumes.)  Axiom-free (standard three only). -/
import QIQTH.CoreNoCollapse
import Mathlib.Tactic

namespace QIQTH.OneSiteBorn

open CoreNoCollapse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **vector-state effect valuation** of a prepared state `ψ`: `ν_ψ(E) = Re⟪ψ, E ψ⟫`. -/
noncomputable def vectorState (ψ : H) (E : H →L[ℂ] H) : ℝ := RCLike.re (inner ℂ ψ (E ψ))

variable (M : FinPVM H)

/-- **One-site Born bridge.**  On a PVM projection the vector-state valuation equals the
    Born weight: `ν_ψ(E r) = ‖E r ψ‖² = weight ψ r`.  (Self-adjoint + idempotent ⇒
    `⟪ψ, E r ψ⟫ = ⟪E r ψ, E r ψ⟫ = ‖E r ψ‖²`.) -/
theorem vectorState_eq_weight (ψ : H) (r : M.Rec) :
    vectorState ψ (M.E r) = M.weight ψ r := by
  have hadj : ContinuousLinearMap.adjoint (M.E r) = M.E r := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact M.selfadj r
  have hidem : M.E r (M.E r ψ) = M.E r ψ := by
    rw [← ContinuousLinearMap.mul_apply, M.idem r]
  have key : inner ℂ ψ (M.E r ψ) = (inner ℂ (M.E r ψ) (M.E r ψ) : ℂ) :=
    calc inner ℂ ψ (M.E r ψ)
        = inner ℂ ψ (M.E r (M.E r ψ)) := by rw [hidem]
      _ = inner ℂ (ContinuousLinearMap.adjoint (M.E r) ψ) (M.E r ψ) :=
          (ContinuousLinearMap.adjoint_inner_left (M.E r) (M.E r ψ) ψ).symm
      _ = inner ℂ (M.E r ψ) (M.E r ψ) := by rw [hadj]
  unfold vectorState FinPVM.weight
  rw [key]
  exact inner_self_eq_norm_sq (M.E r ψ)

/-- The **Born probability vector** of a prepared state over a finite PVM. -/
noncomputable def bornVec (ψ : H) : M.Rec → ℝ := fun r => M.weight ψ r

theorem bornVec_eq_vectorState (ψ : H) (r : M.Rec) :
    bornVec M ψ r = vectorState ψ (M.E r) :=
  (vectorState_eq_weight M ψ r).symm

theorem bornVec_nonneg (ψ : H) (r : M.Rec) : 0 ≤ bornVec M ψ r :=
  sq_nonneg _

theorem bornVec_sum (ψ : H) (hψ : ‖ψ‖ = 1) : ∑ r, bornVec M ψ r = 1 :=
  M.weight_sum_eq_one ψ hψ

end QIQTH.OneSiteBorn
