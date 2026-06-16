/-
  BornProjBridge — Born FROM PROJECTORS: grounding the record/area contract in operators.

  `RecordContract` works over an abstract `RecordLaw` (a bare finite distribution `p`).
  This module supplies the operator-level bridge: for a finite orthogonal PVM (record
  algebra) `{P_r}` on an inner-product space and a NORMALIZED state Φ, the Born weights

      μ(r) = ‖P_r Φ‖²  ( = ⟨Φ, P_r Φ⟩ )

  form a genuine `RecordContract.RecordLaw` (`bornRecordLaw`).  So the entire area
  contract — coarse-graining, the entropy/capacity bridges, `H(R) ≤ log|R|` — sits on a
  Born law DERIVED from actual operators and Φ, not a hand-placed toy distribution.

  This is the first concrete piece of the "decoherent record algebra" (Direction B): the
  Born-from-projectors step.  It does NOT yet supply the decoherence condition (reuse
  `SBSSuppression`) or derive the iid concentration from Φ^⊗N (the harder, content-bearing
  follow-up).  Still ontological-only / Everett-equivalent.  Axiom-free.
-/

import QIQTH.RecordContract
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace QIQTH.BornProjBridge

open RCLike
open scoped BigOperators

/-- A finite orthogonal PVM (record algebra): self-adjoint idempotents resolving the
    identity.  `selfAdjoint` and `idem` express that each `P r` is an orthogonal
    projection; `complete` is `∑ P_r = 1`. -/
structure PVM (R : Type*) (H : Type*) [Fintype R]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  P : R → (H →L[ℂ] H)
  selfAdjoint : ∀ r (x y : H), inner ℂ (P r x) y = inner ℂ x (P r y)
  idem : ∀ r (x : H), P r (P r x) = P r x
  complete : ∀ x : H, ∑ r, P r x = x

variable {R : Type*} {H : Type*} [Fintype R]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Born-from-projectors weight of `Φ` on record `r`: `‖P_r Φ‖²`. -/
noncomputable def bornProj (E : PVM R H) (Φ : H) (r : R) : ℝ := ‖E.P r Φ‖ ^ 2

theorem bornProj_nonneg (E : PVM R H) (Φ : H) (r : R) : 0 ≤ bornProj E Φ r := by
  unfold bornProj; positivity

/-- `‖P_r Φ‖² = ⟨Φ, P_r Φ⟩` (real part): the projector form of the Born weight, using
    self-adjointness and idempotence. -/
theorem bornProj_eq_inner (E : PVM R H) (Φ : H) (r : R) :
    bornProj E Φ r = RCLike.re (inner ℂ Φ (E.P r Φ)) := by
  unfold bornProj
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  rw [E.selfAdjoint r Φ (E.P r Φ), E.idem r Φ]

/-- **The weights sum to one** for a normalized Φ: `∑_r ‖P_r Φ‖² = ‖Φ‖² = 1`, from
    `∑ P_r = 1`. -/
theorem bornProj_sum (E : PVM R H) (Φ : H) (hΦ : ‖Φ‖ = 1) :
    ∑ r, bornProj E Φ r = 1 := by
  calc ∑ r, bornProj E Φ r
      = ∑ r, RCLike.re (inner ℂ Φ (E.P r Φ)) :=
        Finset.sum_congr rfl (fun r _ => bornProj_eq_inner E Φ r)
    _ = RCLike.re (∑ r, inner ℂ Φ (E.P r Φ)) := (map_sum RCLike.re _ _).symm
    _ = RCLike.re (inner ℂ Φ (∑ r, E.P r Φ)) := by rw [← inner_sum]
    _ = RCLike.re (inner ℂ Φ Φ) := by rw [E.complete Φ]
    _ = ‖Φ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) Φ).symm
    _ = 1 := by rw [hΦ]; norm_num

/-- **The bridge.**  The Born-from-projectors weights of a normalized Φ over a finite PVM
    form a `RecordContract.RecordLaw`.  Hence the whole record/area contract applies to a
    Born law `μ(r) = ‖P_r Φ‖² = ⟨Φ, P_r Φ⟩` derived from actual operators and Φ — not a
    toy distribution.  In particular `RecordContract.record_info_le_log_card` gives
    `H(μ) ≤ log|R|` for this operator-derived law. -/
noncomputable def bornRecordLaw (E : PVM R H) (Φ : H) (hΦ : ‖Φ‖ = 1) :
    QIQTH.RecordContract.RecordLaw R where
  p := bornProj E Φ
  nonneg := bornProj_nonneg E Φ
  sum_one := bornProj_sum E Φ hΦ

/-- **Audit conclusion.**  The operator bridge for the (Φ,λ) record/area contract: a
    finite orthogonal PVM `{P_r}` plus a normalized Φ yields a genuine
    `RecordContract.RecordLaw` via the Born rule `μ(r)=‖P_r Φ‖²=⟨Φ,P_rΦ⟩`
    (`bornRecordLaw`, `bornProj_sum`).  The contract's bookkeeping (coarse-graining, area
    bridges, `H(R)≤log|R|`) now rests on Born-from-Φ, not a hand-placed law.  Decoherence
    (off-diagonals → 0) is supplied separately by `SBSSuppression`; deriving the iid
    concentration from Φ^⊗N is the remaining content-bearing step.  Ontological-only;
    = Everett.  Axiom-free. -/
theorem audit_conclusion : True := trivial

end QIQTH.BornProjBridge
