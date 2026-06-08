/-
  F6 (Stage 1.1, GPT-5.5-pro consult #2) — the Weyl-BIT and the norm-square Born law.

  Per the GPT review, the joint Born law of commuting Weyl bits is realized as a **norm-square** on the
  pre-Fock space, which makes positivity FREE and needs no `ContinuousLinearMap` bundling.  For a sign
  `s = ±1` the bit operator is `A(u,s) = (I + s·W(u))/2` (`bitOp`); since `W(u)* = W(−u)`, the bit effect
  `E(u,s) = A(u,s)* A(u,s)`, so the joint Born weight `P(s) = ‖∏ A(uᵢ,sᵢ) Ω‖² ≥ 0` automatically.

  This module builds the foundation + the two-bit law:
    * `bit_normSq_sum` — `‖A(u,1)ψ‖² + ‖A(u,−1)ψ‖² = ‖ψ‖²` (the isometry/parallelogram identity; the
      engine of normalization and projectivity);
    * `norm_vac_sq` — `‖Ω‖² = 1`;
    * `two_bit_normalization` — the four two-bit Born weights sum to 1.

  Positivity is just `sq_nonneg _`.  Axiom-free.
-/
import QIQTH.Fock.WeylOp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace QIQTH.Fock

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The **Weyl-bit operator** `A(u,s) = (I + s·W(u))/2` on the pre-Fock space (`s = ±1`). -/
noncomputable def bitOp (u : H) (s : ℂ) : FockPre H →ₗ[ℂ] FockPre H :=
  (1 / 2 : ℂ) • (LinearMap.id + s • weylPre u)

theorem bitOp_apply (u : H) (s : ℂ) (ψ : FockPre H) :
    bitOp u s ψ = (1 / 2 : ℂ) • (ψ + s • weylPre u ψ) := by
  simp [bitOp, LinearMap.smul_apply, LinearMap.add_apply]

/-- `W(u)` preserves the pre-Fock norm. -/
theorem norm_weylPre (u : H) (ψ : FockPre H) : ‖weylPre u ψ‖ = ‖ψ‖ :=
  (weylₗᵢ u).norm_map ψ

/-- **The normalization identity** `‖A(u,1)ψ‖² + ‖A(u,−1)ψ‖² = ‖ψ‖²` — from the parallelogram law and
    `W(u)` isometric.  The engine of normalization (Σ = 1) and projectivity. -/
theorem bit_normSq_sum (u : H) (ψ : FockPre H) :
    ‖bitOp u 1 ψ‖ ^ 2 + ‖bitOp u (-1) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have h1 : ‖bitOp u 1 ψ‖ ^ 2 = (1 / 4) * ‖ψ + weylPre u ψ‖ ^ 2 := by
    rw [bitOp_apply, one_smul, norm_smul, hhalf]; ring
  have h2 : ‖bitOp u (-1) ψ‖ ^ 2 = (1 / 4) * ‖ψ - weylPre u ψ‖ ^ 2 := by
    rw [bitOp_apply, neg_one_smul, ← sub_eq_add_neg, norm_smul, hhalf]; ring
  rw [h1, h2,
    show (1 / 4) * ‖ψ + weylPre u ψ‖ ^ 2 + (1 / 4) * ‖ψ - weylPre u ψ‖ ^ 2
        = (1 / 4) * (‖ψ + weylPre u ψ‖ ^ 2 + ‖ψ - weylPre u ψ‖ ^ 2) from by ring,
    parallelogram_law_with_norm ℂ ψ (weylPre u ψ), norm_weylPre]
  ring

/-- The pre-vacuum `Ω = e(0)`. -/
noncomputable def vac (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : FockPre H :=
  FockPre.expVec 0

/-- `‖Ω‖² = 1`. -/
theorem norm_vac_sq : ‖vac H‖ ^ 2 = 1 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  show RCLike.re (fockInner (FockPre.expVec (0 : H)) (FockPre.expVec 0)) = 1
  rw [FockPre.inner_expVec, inner_zero_left, Complex.exp_zero]
  simp

/-- **Positivity is free**: every Born weight is a norm-square. -/
theorem bit_born_nonneg (u v : H) (s s' : ℂ) :
    0 ≤ ‖bitOp u s (bitOp v s' (vac H))‖ ^ 2 := sq_nonneg _

/-- **Two-bit normalization**: the four joint Born weights sum to 1. -/
theorem two_bit_normalization (u v : H) :
    ‖bitOp u 1 (bitOp v 1 (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v 1 (vac H))‖ ^ 2
      + ‖bitOp u 1 (bitOp v (-1) (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v (-1) (vac H))‖ ^ 2 = 1 := by
  rw [show ‖bitOp u 1 (bitOp v 1 (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v 1 (vac H))‖ ^ 2
        + ‖bitOp u 1 (bitOp v (-1) (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v (-1) (vac H))‖ ^ 2
      = (‖bitOp u 1 (bitOp v 1 (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v 1 (vac H))‖ ^ 2)
        + (‖bitOp u 1 (bitOp v (-1) (vac H))‖ ^ 2 + ‖bitOp u (-1) (bitOp v (-1) (vac H))‖ ^ 2) from by ring,
    bit_normSq_sum u (bitOp v 1 (vac H)), bit_normSq_sum u (bitOp v (-1) (vac H)),
    bit_normSq_sum v (vac H), norm_vac_sq]

end QIQTH.Fock
