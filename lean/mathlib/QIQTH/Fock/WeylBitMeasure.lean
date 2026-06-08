/-
  F6 (Stage 1.3) — the σ-additive boost-covariant typicality measure μ∞ on the Weyl-bit history space.

  Assembles the four proven ingredients (positivity, normalization, projectivity, boost-covariance) +
  the abelian structure (`bitOp_comm`) into the literal `μ∞.map(boost) = μ∞`, via the existing
  `EffectStateNet`/`KolmogorovFiniteFiber` machinery with `A = ℝ`, `ω = id`, `E = bornWeight`.

  The Born weight of a finite commuting context `J` with outcome `σ` is the norm-square
  `‖∏_{i∈J} A(uᵢ, σᵢ) Ω‖²`, where the product is the order-independent `Finset.noncommProd` of the
  (commuting) bit operators.  This module builds the bit-operator commutation in the endomorphism
  monoid, the history vector `bornVecTot`, and its `insert` composition law — the foundation for the
  `total` (normalization) and `coarse` (marginalization) obligations.  Axiom-free.
-/
import QIQTH.Fock.WeylBit
import QIQTH.Fock.WeylBitProcess
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace

variable {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Weyl bit operators **commute in the endomorphism monoid** when the modes are symplectically
    orthogonal (`Im⟪uᵢ,uⱼ⟫ = 0`). -/
theorem bitOp_commute {u : ι → H} (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {i j : ι} (hij : i ≠ j) (s s' : ℂ) :
    Commute (bitOp (u i) s) (bitOp (u j) s') := by
  show bitOp (u i) s * bitOp (u j) s' = bitOp (u j) s' * bitOp (u i) s
  ext ψ
  show bitOp (u i) s (bitOp (u j) s' ψ) = bitOp (u j) s' (bitOp (u i) s ψ)
  exact bitOp_comm (u i) (u j) s s' (hiso i j hij) ψ

/-- The Weyl-bit **history vector** over a finite commuting context `J` with sign assignment `s`:
    the order-independent product `∏_{i∈J} A(uᵢ, sᵢ)` (a `Finset.noncommProd`) applied to the vacuum. -/
noncomputable def bornVecTot (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (s : ι → ℂ) (J : Finset ι) : FockPre H :=
  (J.noncommProd (fun i => bitOp (u i) (s i))
    (fun i _ j _ hij => bitOp_commute hiso hij (s i) (s j))) (vac H)

@[simp] theorem bornVecTot_empty (u : ι → H) (hiso) (s : ι → ℂ) :
    bornVecTot u hiso s ∅ = vac H := by
  simp [bornVecTot]

/-- **Insert composition**: adding a mode prepends its bit (outermost). -/
theorem bornVecTot_insert (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (s : ι → ℂ) {a : ι} {J : Finset ι} (ha : a ∉ J) :
    bornVecTot u hiso s (insert a J) = bitOp (u a) (s a) (bornVecTot u hiso s J) := by
  rw [bornVecTot, bornVecTot,
    Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
  rfl

/-- ±1 from a Boolean sign. -/
def sgn (b : Bool) : ℂ := if b then 1 else -1

/-- Extend a context-restricted sign assignment to a total `ι → ℂ` (`1` off the context). -/
noncomputable def signExt (J : Finset ι) (σ : ∀ j : J, Bool) (i : ι) : ℂ :=
  if h : i ∈ J then sgn (σ ⟨i, h⟩) else 1

/-- `bornVecTot` depends only on the signs on `J`. -/
theorem bornVecTot_congr (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {s₁ s₂ : ι → ℂ} {J : Finset ι} (h : ∀ i ∈ J, s₁ i = s₂ i) :
    bornVecTot u hiso s₁ J = bornVecTot u hiso s₂ J := by
  rw [bornVecTot, bornVecTot]
  congr 1
  exact Finset.noncommProd_congr rfl (fun i hi => by rw [h i hi]) _

/-- The **Weyl-bit Born weight** of a finite commuting context `J` with outcome `σ`:
    `‖∏_{i∈J} A(uᵢ, σᵢ) Ω‖²`. -/
noncomputable def bornWeight (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (J : Finset ι) (σ : ∀ j : J, Bool) : ℝ :=
  ‖bornVecTot u hiso (signExt J σ) J‖ ^ 2

/-- The Born weight on a context `J = insert a J'` factors a bit off the head:
    `bornWeight (insert a J') σ = ‖A(uₐ, σₐ) (∏_{J'} A Ω)‖²`. -/
theorem bornWeight_insert (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {a : ι} {J' : Finset ι} (ha : a ∉ J') (σ : ∀ j : (insert a J' : Finset ι), Bool) :
    bornWeight u hiso (insert a J') σ
      = ‖bitOp (u a) (sgn (σ ⟨a, Finset.mem_insert_self a J'⟩))
          (bornVecTot u hiso (signExt J' (fun j => σ ⟨j.1, Finset.mem_insert_of_mem j.2⟩)) J')‖ ^ 2 := by
  have h1 : signExt (insert a J') σ a = sgn (σ ⟨a, Finset.mem_insert_self a J'⟩) := by
    rw [signExt, dif_pos (Finset.mem_insert_self a J')]
  have h2 : bornVecTot u hiso (signExt (insert a J') σ) J'
      = bornVecTot u hiso (signExt J' (fun j => σ ⟨j.1, Finset.mem_insert_of_mem j.2⟩)) J' := by
    refine bornVecTot_congr u hiso fun i hi => ?_
    have hi' : i ∈ insert a J' := Finset.mem_insert_of_mem hi
    rw [signExt, signExt, dif_pos hi, dif_pos hi']
  rw [bornWeight, bornVecTot_insert u hiso _ ha, h1, h2]

/-- The all-`σ` Born-weight sum over an empty context is 1. -/
theorem bornWeight_total_empty (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) :
    ∑ σ : (∀ j : (∅ : Finset ι), Bool), bornWeight u hiso ∅ σ = 1 := by
  simp [bornWeight, bornVecTot_empty, norm_vac_sq]

/-- The explicit splitting equivalence `(∀ j ∈ insert a J', Bool) ≃ Bool × (∀ j ∈ J', Bool)`,
    forward map `σ ↦ (σ a, σ↾J')`.  An explicit *forward* map keeps the sum-reindexing term in
    terms of projections (no `e.symm` unfolding), which is what makes `bornWeight_total` go through. -/
def insertBoolSplit {a : ι} {J' : Finset ι} (ha : a ∉ J') :
    (∀ j : (insert a J' : Finset ι), Bool) ≃ Bool × (∀ j : J', Bool) where
  toFun σ := (σ ⟨a, Finset.mem_insert_self a J'⟩,
    fun j => σ ⟨j.1, Finset.mem_insert_of_mem j.2⟩)
  invFun p j := if h : (j : ι) = a then p.1
    else p.2 ⟨j.1, (Finset.mem_insert.mp j.2).resolve_left h⟩
  left_inv σ := by
    funext j
    dsimp only
    by_cases h : (j : ι) = a
    · rw [dif_pos h]; congr 1; exact Subtype.ext h.symm
    · rw [dif_neg h]
  right_inv p := by
    obtain ⟨b, τ⟩ := p
    refine Prod.ext ?_ ?_
    · dsimp only; rw [dif_pos rfl]
    · funext j
      dsimp only
      have hj : (j : ι) ≠ a := fun h => ha (h ▸ j.2)
      rw [dif_neg hj]

/-- **Normalization over a Finset context**: the Born weights of all outcomes sum to 1. -/
theorem bornWeight_total (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (J : Finset ι) : ∑ σ : (∀ j : J, Bool), bornWeight u hiso J σ = 1 := by
  classical
  induction J using Finset.induction with
  | empty => exact bornWeight_total_empty u hiso
  | @insert a J' ha ih =>
    rw [Fintype.sum_equiv (insertBoolSplit ha) (fun σ => bornWeight u hiso (insert a J') σ)
        (fun p => ‖bitOp (u a) (sgn p.1) (bornVecTot u hiso (signExt J' p.2) J')‖ ^ 2)
        (fun σ => bornWeight_insert u hiso ha σ),
      Fintype.sum_prod_type, Finset.sum_comm, ← ih]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fintype.sum_bool]
    simp only [sgn, Bool.false_eq_true, reduceIte]
    rw [bornWeight, bit_normSq_sum]

/-- **Projectivity (single-mode marginal)**: summing the *free* bit at a head mode `a ∉ J'` over its two
    values collapses the Born weight on `insert a J'` to the Born weight on `J'`.  This is `bit_normSq_sum`
    transported to the Finset-context Born weight — the inductive step for the general coarse-graining
    consistency of the joint Born law. -/
theorem bornWeight_marginal (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {a : ι} {J' : Finset ι} (ha : a ∉ J') (y : ∀ j : J', Bool) :
    ∑ b : Bool, bornWeight u hiso (insert a J') ((insertBoolSplit ha).symm (b, y))
      = bornWeight u hiso J' y := by
  have key : ∀ b : Bool, bornWeight u hiso (insert a J') ((insertBoolSplit ha).symm (b, y))
      = ‖bitOp (u a) (sgn b) (bornVecTot u hiso (signExt J' y) J')‖ ^ 2 := by
    intro b
    have hsplit := (insertBoolSplit ha).apply_symm_apply (b, y)
    have hb : (insertBoolSplit ha).symm (b, y) ⟨a, Finset.mem_insert_self a J'⟩ = b :=
      congrArg Prod.fst hsplit
    have hy : (fun j : J' => (insertBoolSplit ha).symm (b, y) ⟨j.1, Finset.mem_insert_of_mem j.2⟩) = y :=
      congrArg Prod.snd hsplit
    rw [bornWeight_insert u hiso ha, hb, hy]
  simp_rw [key, Fintype.sum_bool, sgn, Bool.false_eq_true, reduceIte]
  rw [bornWeight, bit_normSq_sum]

end QIQTH.Fock
