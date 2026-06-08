/-
  B.0 — the Weyl-bit EFFECTS: the norm-square Born weights are genuine vacuum-state POVM expectations.

  GPT consult #2 made positivity FREE by representing the Born weight as a norm-square `‖A(u,s)Ω‖²`.
  This module closes the operational loop: that norm-square IS the vacuum expectation `⟪Ω, E(u,s) Ω⟫` of a
  genuine POSITIVE effect operator `E(u,s) = A(u,s)* A(u,s)`, where the adjoint is computed from the Weyl
  unitarity `W(u)* = W(−u)` (`fockInner_weyl_adjoint`).  So the Weyl-bit Born weights are not merely
  nonnegative numbers we defined — they are the Born probabilities of an actual two-outcome POVM
  `{E(u,+1), E(u,−1)}` measured in the quasifree vacuum state.  Axiom-free.
-/
import QIQTH.Fock.WeylBit
import QIQTH.Fock.WeylBitMeasure
import Mathlib.Tactic

namespace QIQTH.Fock

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The pre-Fock inner product is `fockInner` on the underlying finsupps. -/
theorem fockPre_inner_eq (φ ψ : FockPre H) : ⟪φ, ψ⟫_ℂ = fockInner φ ψ := rfl

/-- **`W(u)* = W(−u)` at the inner-product level**: `⟪W(u)φ, ψ⟫ = ⟪φ, W(−u)ψ⟫`. -/
theorem weylPre_adjoint_inner (u : H) (φ ψ : FockPre H) :
    ⟪weylPre u φ, ψ⟫_ℂ = ⟪φ, weylPre (-u) ψ⟫_ℂ := by
  rw [fockPre_inner_eq, fockPre_inner_eq]
  exact fockInner_weyl_adjoint u φ ψ

/-- The **adjoint Weyl-bit operator** `A(u,s)* = (I + s̄·W(−u))/2`. -/
noncomputable def bitAdj (u : H) (s : ℂ) : FockPre H →ₗ[ℂ] FockPre H :=
  (1 / 2 : ℂ) • (LinearMap.id + (starRingEnd ℂ s) • weylPre (-u))

theorem bitAdj_apply (u : H) (s : ℂ) (ψ : FockPre H) :
    bitAdj u s ψ = (1 / 2 : ℂ) • (ψ + (starRingEnd ℂ s) • weylPre (-u) ψ) := by
  simp [bitAdj, LinearMap.smul_apply, LinearMap.add_apply]

/-- **`A(u,s)` and `A(u,s)*` are adjoint** with respect to the Fock inner product:
    `⟪A(u,s)φ, ψ⟫ = ⟪φ, A(u,s)* ψ⟫`.  (Uses `W(u)* = W(−u)` and conjugate-(bi)linearity.) -/
theorem bitOp_adjoint_inner (u : H) (s : ℂ) (φ ψ : FockPre H) :
    ⟪bitOp u s φ, ψ⟫_ℂ = ⟪φ, bitAdj u s ψ⟫_ℂ := by
  rw [bitOp_apply, bitAdj_apply, inner_smul_left, inner_add_left, inner_smul_left,
    weylPre_adjoint_inner, inner_smul_right, inner_add_right, inner_smul_right]
  simp only [map_div₀, map_one, map_ofNat]

/-- The **Weyl-bit EFFECT** `E(u,s) = A(u,s)* A(u,s)` — a positive operator (manifestly `T*T`). -/
noncomputable def effOp (u : H) (s : ℂ) : FockPre H →ₗ[ℂ] FockPre H := bitAdj u s ∘ₗ bitOp u s

/-- **The Born weight is the expectation of the effect**: `⟪ψ, E(u,s) ψ⟫ = ‖A(u,s) ψ‖²` (real, ≥ 0).
    The norm-square Born weight is literally the quantum expectation value of the positive effect
    `E(u,s) = A(u,s)* A(u,s)` in the state `ψ`. -/
theorem bit_effect_expectation (u : H) (s : ℂ) (ψ : FockPre H) :
    RCLike.re ⟪ψ, effOp u s ψ⟫_ℂ = ‖bitOp u s ψ‖ ^ 2 := by
  show RCLike.re ⟪ψ, bitAdj u s (bitOp u s ψ)⟫_ℂ = _
  rw [← bitOp_adjoint_inner u s ψ (bitOp u s ψ)]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (bitOp u s ψ)

/-- **The effect is positive**: `0 ≤ ⟪ψ, E(u,s) ψ⟫` for every `ψ` (it is a norm-square). -/
theorem effOp_nonneg (u : H) (s : ℂ) (ψ : FockPre H) :
    0 ≤ RCLike.re ⟪ψ, effOp u s ψ⟫_ℂ := by
  rw [bit_effect_expectation]; positivity

/-- **The single-mode Weyl-bit Born weight is a genuine vacuum-state POVM expectation**:
    `bornWeight u {i} σ = ⟪Ω, E(u_i, ±) Ω⟫`.  The Born probability of the two-outcome POVM
    `{E(u_i,+1), E(u_i,−1)}` measured in the quasifree vacuum. -/
theorem bornWeight_singleton_eq_effect {ι : Type*} [DecidableEq ι] (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (i : ι)
    (σ : ∀ j : ({i} : Finset ι), Bool) :
    bornWeight u hiso {i} σ
      = RCLike.re ⟪vac H, effOp (u i) (sgn (σ ⟨i, Finset.mem_singleton_self i⟩)) (vac H)⟫_ℂ := by
  rw [bit_effect_expectation, bornWeight,
    bornVecTot_erase u hiso (signExt {i} σ) (Finset.mem_singleton_self i),
    Finset.erase_singleton, bornVecTot_empty]
  have hs : (signExt ({i} : Finset ι) σ) i = sgn (σ ⟨i, Finset.mem_singleton_self i⟩) := by
    rw [signExt, dif_pos (Finset.mem_singleton_self i)]
  rw [hs]

end QIQTH.Fock
