/-
  F6 (Stage 1.2 — boost-covariance, GPT consult #2) — every Weyl-bit Born weight is boost-invariant.

  The measure-level content of the prize: the joint Born weight of a finite commuting Weyl-bit family is
  invariant under the Lorentz boost.  The mechanism (GPT's recipe, the clean operator route):
    * **intertwining** `W(Au) ∘ Γ(A) = Γ(A) ∘ W(u)` (`weylPre_secondQuant_comm`, from
      `weylCoeff_isometry_invariant`), hence `A(Au,s) ∘ Γ(A) = Γ(A) ∘ A(u,s)` for the bit operators;
    * the **history vector** `∏ A(uᵢ,sᵢ) Ω` therefore satisfies `histVec (A·family) = Γ(A) (histVec family)`
      (`histVec_boost`), using `Γ(A)Ω = Ω`;
    * `Γ(A)` is an isometry, so the Born weight `‖histVec‖²` is **invariant**: `histVec_normSq_boost`.

  Specialized to `A = U₁(t)` (the F1 Lorentz boost), `bornWeight_boost_invariant` is the genuine
  per-outcome boost-covariance of the Weyl-bit Born law on the continuum free field.  Axiom-free.
-/
import QIQTH.Fock.WeylBit
import QIQTH.Fock.SecondQuant
import QIQTH.Fock.Weyl
import Mathlib.Tactic

namespace QIQTH.Fock

open MeasureTheory
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Intertwining / covariance**: `W(A u) ∘ Γ(A) = Γ(A) ∘ W(u)` for a one-particle isometry `A`. -/
theorem weylPre_secondQuant_comm (A : H →ₗᵢ[ℂ] H) (u : H) :
    weylPre (A u) ∘ₗ secondQuantPre A = secondQuantPre A ∘ₗ weylPre u := by
  refine Finsupp.lhom_ext fun g b => ?_
  have hb : (Finsupp.single g b : H →₀ ℂ) = b • FockPre.expVec g := by
    show (Finsupp.single g b : H →₀ ℂ) = b • (Finsupp.single g 1 : H →₀ ℂ)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  show weylPre (A u) (secondQuantPre A (Finsupp.single g b))
      = secondQuantPre A (weylPre u (Finsupp.single g b))
  rw [hb, map_smul, map_smul, map_smul, map_smul]
  congr 1
  rw [secondQuantPre_expVec, weylPre_expVec, weylPre_expVec, map_smul, secondQuantPre_expVec,
    Weyl.weylCoeff_isometry_invariant, map_add]

/-- `A(A u, s) ∘ Γ(A) = Γ(A) ∘ A(u, s)` for the Weyl-bit operators. -/
theorem bitOp_secondQuant_comm (A : H →ₗᵢ[ℂ] H) (u : H) (s : ℂ) (x : FockPre H) :
    bitOp (A u) s (secondQuantPre A x) = secondQuantPre A (bitOp u s x) := by
  have hcomm : weylPre (A u) (secondQuantPre A x) = secondQuantPre A (weylPre u x) :=
    congrFun (congrArg DFunLike.coe (weylPre_secondQuant_comm A u)) x
  rw [bitOp_apply, bitOp_apply, map_smul, map_add, map_smul, hcomm]

/-- The **history vector** `∏ A(uᵢ,sᵢ) Ω` of a finite (vector, sign) family. -/
noncomputable def histVec : List (H × ℂ) → FockPre H
  | [] => vac H
  | (u, s) :: rest => bitOp u s (histVec rest)

/-- **Boost equivariance of the history vector**: `histVec (A·family) = Γ(A) (histVec family)`. -/
theorem histVec_boost (A : H →ₗᵢ[ℂ] H) (L : List (H × ℂ)) :
    histVec (L.map (fun p => (A p.1, p.2))) = secondQuantPre A (histVec L) := by
  induction L with
  | nil => exact (secondQuantPre_vacuum A).symm
  | cons p rest ih =>
    obtain ⟨u, s⟩ := p
    rw [List.map_cons, histVec, histVec, ih, bitOp_secondQuant_comm]

/-- **The Weyl-bit Born weight is boost-invariant**: `‖histVec (A·family)‖² = ‖histVec family‖²`. -/
theorem histVec_normSq_boost (A : H →ₗᵢ[ℂ] H) (L : List (H × ℂ)) :
    ‖histVec (L.map (fun p => (A p.1, p.2)))‖ ^ 2 = ‖histVec L‖ ^ 2 := by
  rw [histVec_boost]
  congr 1
  exact (LinearMap.isometryOfInner (secondQuantPre A)
    (fun φ ψ => fockInner_secondQuant A φ ψ)).norm_map (histVec L)

/-- **Per-outcome boost-covariance of the Weyl-bit Born law on the continuum free field**: every joint
    Born weight `‖∏ A(uᵢ,sᵢ) Ω‖²` is invariant under the Lorentz boost `U₁(t)`. -/
theorem bornWeight_boost_invariant (t : ℝ)
    (L : List (Lp ℂ 2 (volume : Measure ℝ) × ℂ)) :
    ‖histVec (L.map (fun p => (QIQTH.Fock.OneParticle.boostUnitary t p.1, p.2)))‖ ^ 2
      = ‖histVec L‖ ^ 2 :=
  histVec_normSq_boost (QIQTH.Fock.OneParticle.boostUnitary t).toLinearIsometry L

end QIQTH.Fock
