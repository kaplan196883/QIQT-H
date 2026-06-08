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

/-- **POVM completeness for the two-outcome Weyl-bit measurement**: `E(u,+1) + E(u,−1) = I`.  Together
    with positivity (`effOp_nonneg`), `{E(u,+1), E(u,−1)}` is a genuine operator-valued POVM (the resolution
    of identity uses `W(−u) W(u) = I`, `weylPre_neg_cancel`). -/
theorem effOp_sum_eq_id (u : H) : effOp u 1 + effOp u (-1) = LinearMap.id := by
  ext ψ
  simp only [LinearMap.add_apply, LinearMap.id_apply, effOp, LinearMap.comp_apply, bitAdj_apply,
    bitOp_apply, map_smul, map_add, weylPre_neg_cancel, map_one, map_neg, smul_add, smul_smul]
  module

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

/-! ### B.0.3 — the JOINT effect: the full multi-mode Born weight is a vacuum POVM expectation -/

/-- The adjoint Weyl bits **commute** under isotropy (microcausality), so their order-independent product
    is well-defined. -/
theorem bitAdj_comm (u v : H) (s s' : ℂ) (huv : Complex.im ⟪u, v⟫_ℂ = 0) (ψ : FockPre H) :
    bitAdj u s (bitAdj v s' ψ) = bitAdj v s' (bitAdj u s ψ) := by
  have hw : weylPre (-u) (weylPre (-v) ψ) = weylPre (-v) (weylPre (-u) ψ) :=
    congrFun (congrArg DFunLike.coe (weyl_microcausality (-u) (-v) (by
      rw [inner_neg_neg]; exact huv))) ψ
  simp only [bitAdj_apply, map_smul, map_add, smul_add, smul_smul]
  rw [hw]
  module

theorem bitAdj_commute {ι : Type*} {u : ι → H}
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) {i j : ι} (hij : i ≠ j) (s s' : ℂ) :
    Commute (bitAdj (u i) s) (bitAdj (u j) s') := by
  show bitAdj (u i) s * bitAdj (u j) s' = bitAdj (u j) s' * bitAdj (u i) s
  ext ψ
  exact bitAdj_comm (u i) (u j) s s' (hiso i j hij) ψ

variable {ι : Type*} [DecidableEq ι]

/-- **The product adjoint** `∏_{i∈J} A(uᵢ,sᵢ)*` (order-independent `noncommProd` of the adjoint bits). -/
noncomputable def bornAdjOp (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (s : ι → ℂ) (J : Finset ι) : FockPre H →ₗ[ℂ] FockPre H :=
  J.noncommProd (fun i => bitAdj (u i) (s i)) (fun i _ j _ hij => bitAdj_commute hiso hij (s i) (s j))

theorem bornAdjOp_insert (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (s : ι → ℂ) {a : ι} {J : Finset ι} (ha : a ∉ J) (ψ : FockPre H) :
    bornAdjOp u hiso s (insert a J) ψ = bitAdj (u a) (s a) (bornAdjOp u hiso s J ψ) := by
  rw [bornAdjOp, bornAdjOp, Finset.noncommProd_insert_of_notMem _ _ _ _ ha]; rfl

/-- **The history vector pairs against the product adjoint**: `⟪∏A(uᵢ,sᵢ) Ω, ψ⟫ = ⟪Ω, ∏A(uᵢ,sᵢ)* ψ⟫`.
    By induction on `J`, peeling one bit with `bitOp_adjoint_inner` and commuting the head adjoint
    `A(uₐ,sₐ)*` through the rest (`bitAdj_commute`, from microcausality). -/
theorem bornVecTot_adjoint_inner (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (s : ι → ℂ) (J : Finset ι) :
    ∀ ψ : FockPre H, ⟪bornVecTot u hiso s J, ψ⟫_ℂ = ⟪vac H, bornAdjOp u hiso s J ψ⟫_ℂ := by
  classical
  induction J using Finset.induction with
  | empty => intro ψ; simp [bornVecTot_empty, bornAdjOp, Finset.noncommProd_empty]
  | @insert a J' ha ih =>
    intro ψ
    rw [bornVecTot_insert u hiso s ha, bitOp_adjoint_inner, ih, bornAdjOp_insert u hiso s ha]
    congr 1
    have hcomm : Commute (bitAdj (u a) (s a)) (bornAdjOp u hiso s J') :=
      Finset.noncommProd_commute _ _ _ _ fun j hj =>
        bitAdj_commute hiso (by rintro rfl; exact ha hj) (s a) (s j)
    exact (congrFun (congrArg DFunLike.coe hcomm) ψ).symm

/-- **THE JOINT POVM expectation (B.0):** the full multi-mode Weyl-bit Born weight
    `bornWeight u J σ = ⟪Ω, E_σ Ω⟫`, where `E_σ = (∏_{i∈J} A(uᵢ,σᵢ))* (∏_{i∈J} A(uᵢ,σᵢ))` is the positive
    JOINT effect of the outcome `σ` on the commuting context `J`.  So every joint Born weight on the
    continuum free field is a genuine vacuum-state expectation of a positive bounded effect — the
    operational reading of the σ-additive boost-covariant prize measure μ∞. -/
theorem bornWeight_eq_joint_effect (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight u hiso J σ
      = RCLike.re ⟪vac H,
          bornAdjOp u hiso (signExt J σ) J (bornVecTot u hiso (signExt J σ) J)⟫_ℂ := by
  rw [bornWeight, ← inner_self_eq_norm_sq (𝕜 := ℂ),
    bornVecTot_adjoint_inner u hiso (signExt J σ) J (bornVecTot u hiso (signExt J σ) J)]

end QIQTH.Fock
