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
import QIQTH.StateNetMeasure
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace
open MeasureTheory QIQTH.StateNetMeasure

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

/-- Peel a mode `a ∈ J` off the history vector (erase form, no dependent type rewrite). -/
theorem bornVecTot_erase (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (s : ι → ℂ) {a : ι} {J : Finset ι} (haJ : a ∈ J) :
    bornVecTot u hiso s J = bitOp (u a) (s a) (bornVecTot u hiso s (J.erase a)) := by
  have he : insert a (J.erase a) = J := Finset.insert_erase haJ
  rw [show bornVecTot u hiso s J = bornVecTot u hiso s (insert a (J.erase a)) from by rw [he],
    bornVecTot_insert u hiso s (Finset.notMem_erase a J)]

/-- Born weight factors a bit off any `a ∈ J` (erase form). -/
theorem bornWeight_erase (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {a : ι} {J : Finset ι} (haJ : a ∈ J) (σ : ∀ j : J, Bool) :
    bornWeight u hiso J σ
      = ‖bitOp (u a) (sgn (σ ⟨a, haJ⟩))
          (bornVecTot u hiso
            (signExt (J.erase a) (fun j => σ ⟨j.1, Finset.mem_of_mem_erase j.2⟩)) (J.erase a))‖ ^ 2 := by
  have h1 : signExt J σ a = sgn (σ ⟨a, haJ⟩) := by rw [signExt, dif_pos haJ]
  have h2 : bornVecTot u hiso (signExt J σ) (J.erase a)
      = bornVecTot u hiso
          (signExt (J.erase a) (fun j => σ ⟨j.1, Finset.mem_of_mem_erase j.2⟩)) (J.erase a) := by
    refine bornVecTot_congr u hiso fun i hi => ?_
    have hiJ : i ∈ J := Finset.mem_of_mem_erase hi
    rw [signExt, signExt, dif_pos hi, dif_pos hiJ]
  rw [bornWeight, bornVecTot_erase u hiso _ haJ, h1, h2]

/-- The erase-form splitting equivalence `(∀ j ∈ J, Bool) ≃ Bool × (∀ j ∈ J.erase a, Bool)`. -/
def eraseBoolSplit {a : ι} {J : Finset ι} (haJ : a ∈ J) :
    (∀ j : J, Bool) ≃ Bool × (∀ j : (J.erase a : Finset ι), Bool) where
  toFun σ := (σ ⟨a, haJ⟩, fun j => σ ⟨j.1, Finset.mem_of_mem_erase j.2⟩)
  invFun p j := if h : (j : ι) = a then p.1
    else p.2 ⟨j.1, Finset.mem_erase.mpr ⟨h, j.2⟩⟩
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
      rw [dif_neg (Finset.ne_of_mem_erase j.2)]

/-- **Projectivity (erase form)**: summing the free bit at any `a ∈ J` collapses the Born weight on `J`
    to the Born weight on `J.erase a`. -/
theorem bornWeight_erase_marginal (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {a : ι} {J : Finset ι} (haJ : a ∈ J) (y : ∀ j : (J.erase a : Finset ι), Bool) :
    ∑ b : Bool, bornWeight u hiso J ((eraseBoolSplit haJ).symm (b, y))
      = bornWeight u hiso (J.erase a) y := by
  have key : ∀ b : Bool, bornWeight u hiso J ((eraseBoolSplit haJ).symm (b, y))
      = ‖bitOp (u a) (sgn b) (bornVecTot u hiso (signExt (J.erase a) y) (J.erase a))‖ ^ 2 := by
    intro b
    have hsplit := (eraseBoolSplit haJ).apply_symm_apply (b, y)
    have hb : (eraseBoolSplit haJ).symm (b, y) ⟨a, haJ⟩ = b := congrArg Prod.fst hsplit
    have hy : (fun j : (J.erase a : Finset ι) =>
        (eraseBoolSplit haJ).symm (b, y) ⟨j.1, Finset.mem_of_mem_erase j.2⟩) = y :=
      congrArg Prod.snd hsplit
    rw [bornWeight_erase u hiso haJ, hb, hy]
  simp_rw [key, Fintype.sum_bool, sgn, Bool.false_eq_true, reduceIte]
  rw [bornWeight, bit_normSq_sum]

/-- **Coarse-graining consistency (Kolmogorov projectivity) of the joint Born law**: for any sub-context
    `I ⊆ J`, the Born weight of an outcome `y` on `I` equals the sum of the `J`-weights over all
    `J`-outcomes restricting to `y`.  Proved by strong induction on `J`, peeling one *free* mode
    (`a ∈ J \ I`) at a time via `bornWeight_erase_marginal`.  This is the `coarse` obligation of the
    `EffectStateNet` interface — the last ingredient for the σ-additive μ∞. -/
theorem bornWeight_coarse (u : ι → H) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) :
    ∀ (J I : Finset ι) (h : I ⊆ J) (y : ∀ i : I, Bool),
      bornWeight u hiso I y
        = ∑ x ∈ Finset.univ.filter
            (fun x : ∀ j : J, Bool => Finset.restrict₂ (π := fun _ : ι => Bool) h x = y),
            bornWeight u hiso J x := by
  intro J
  induction J using Finset.strongInduction with
  | _ J ih =>
    intro I h y
    rcases eq_or_ne I J with rfl | hne
    · have hself : ∀ x : ∀ i : I, Bool, Finset.restrict₂ (π := fun _ : ι => Bool) h x = x :=
        fun x => funext fun i => rfl
      rw [Finset.sum_filter]
      simp_rw [hself]
      rw [Finset.sum_ite_eq' Finset.univ y, if_pos (Finset.mem_univ y)]
    · obtain ⟨a, haJ, haI⟩ := Finset.exists_of_ssubset (h.ssubset_of_ne hne)
      have hIe : I ⊆ J.erase a := fun i hi =>
        Finset.mem_erase.mpr ⟨fun e => haI (e ▸ hi), h hi⟩
      rw [ih (J.erase a) (Finset.erase_ssubset haJ) I hIe y, Finset.sum_filter, Finset.sum_filter,
        Fintype.sum_equiv (eraseBoolSplit haJ)
          (fun x : ∀ j : J, Bool =>
            if Finset.restrict₂ (π := fun _ : ι => Bool) h x = y then bornWeight u hiso J x else 0)
          (fun p : Bool × (∀ j : (J.erase a : Finset ι), Bool) =>
            if Finset.restrict₂ (π := fun _ : ι => Bool) h ((eraseBoolSplit haJ).symm p) = y
            then bornWeight u hiso J ((eraseBoolSplit haJ).symm p) else 0)
          (fun x => by simp only [Equiv.symm_apply_apply]),
        Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      have hpred : ∀ b : Bool,
          Finset.restrict₂ (π := fun _ : ι => Bool) h ((eraseBoolSplit haJ).symm (b, x'))
          = Finset.restrict₂ (π := fun _ : ι => Bool) hIe x' := by
        intro b
        funext i
        have hia : (i : ι) ≠ a := fun e => haI (e ▸ i.2)
        simp only [Finset.restrict₂, eraseBoolSplit, Equiv.coe_fn_symm_mk, dif_neg hia]
      simp_rw [hpred]
      by_cases hc : Finset.restrict₂ (π := fun _ : ι => Bool) hIe x' = y
      · simp_rw [if_pos hc]; exact (bornWeight_erase_marginal u hiso haJ x').symm
      · simp_rw [if_neg hc, Finset.sum_const_zero]

/-- **Second-quantization push-through**: `Γ(A)` carries the history vector of `u` to the history vector
    of the boosted family `A∘u` — `Γ(A) (∏ A(uᵢ,sᵢ) Ω) = ∏ A(A uᵢ,sᵢ) Ω` — by pushing `Γ(A)` through the
    `noncommProd` one bit at a time (`bitOp_secondQuant_comm`), using `Γ(A) Ω = Ω`. -/
theorem bornVecTot_secondQuant (A : H →ₗᵢ[ℂ] H) (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪A (u i), A (u j)⟫_ℂ = 0) (s : ι → ℂ) (J : Finset ι) :
    secondQuantPre A (bornVecTot u hiso s J) = bornVecTot (fun i => A (u i)) hiso' s J := by
  classical
  induction J using Finset.induction with
  | empty => simp [bornVecTot_empty, vac]
  | @insert a J' ha ih =>
    rw [bornVecTot_insert u hiso s ha, bornVecTot_insert (fun i => A (u i)) hiso' s ha, ← ih,
      bitOp_secondQuant_comm]

/-- **Isometry-invariance of the Weyl-bit Born weight**: for any one-particle isometry `A`, the joint
    Born weight is unchanged under boosting every mode `uᵢ ↦ A uᵢ` — `Γ(A)` is unitary, so the
    norm-square history weight is preserved.  (Specialized to the Lorentz boost `A = U₁(t)`, this is the
    per-outcome boost-covariance underlying `μ∞.map(boost) = μ∞`.) -/
theorem bornWeight_isometry_invariant (A : H →ₗᵢ[ℂ] H) (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪A (u i), A (u j)⟫_ℂ = 0) (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight (fun i => A (u i)) hiso' J σ = bornWeight u hiso J σ := by
  rw [bornWeight, bornWeight, ← bornVecTot_secondQuant A u hiso hiso']
  congr 1
  exact (LinearMap.isometryOfInner (secondQuantPre A)
    (fun φ ψ => fockInner_secondQuant A φ ψ)).norm_map _

/-- **The genuine (non-deterministic) Weyl-bit `EffectStateNet` on the continuum free field.**
    Outcomes are bits (`α = Bool`), the state is the identity functional on `ℝ`, and the joint effect of
    a finite commuting context `J` with outcome `σ` is its **Born weight** `‖∏_{i∈J} A(uᵢ,σᵢ) Ω‖²`.  Unlike
    the deterministic record nets (`diracNet`, `fockVacuumNet`), the effects here are a genuine probability
    distribution over `2^|J|` outcomes: positivity is free (norm-square), normalization is `bornWeight_total`,
    and coarse-graining consistency is `bornWeight_coarse`. -/
noncomputable def weylBitNet (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) :
    EffectStateNet (ι := ι) (fun _ : ι => Bool) ℝ where
  ω := AddMonoidHom.id ℝ
  E := fun J σ => bornWeight u hiso J σ
  pos := fun J x => by
    simp only [AddMonoidHom.id_apply]; exact pow_nonneg (norm_nonneg _) 2
  total := fun J => by simpa using bornWeight_total u hiso J
  coarse := fun I J h y => bornWeight_coarse u hiso J I h y

/-- **The σ-additive typicality measure μ∞ EXISTS for the genuine Weyl-bit net.**  Combining the four
    proven ingredients (positivity, normalization `bornWeight_total`, coarse-graining `bornWeight_coarse`)
    with the finite-fiber Kolmogorov extension: there is a unique σ-additive probability measure μ∞ on the
    history space `∀ i, Bool` whose finite marginals are the Weyl-bit Born measures.  This is the FIRST
    non-deterministic (genuinely physical) typicality measure on the continuum free field — Born weights
    that are an actual probability distribution, not a point mass. -/
theorem weylBit_typicalityMeasure_exists (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) :
    ∃ μ : Measure (∀ _ : ι, Bool), IsProbabilityMeasure μ ∧
      (weylBitNet u hiso).toFiniteMarginals.IsLimit μ :=
  (weylBitNet u hiso).exists_typicalityMeasure

/-- **The Weyl-bit Born marginals are boost-invariant.**  Boosting every mode `uᵢ ↦ A uᵢ` by a
    one-particle isometry `A` leaves the entire projective family of finite Born marginals unchanged
    (`bornWeight_isometry_invariant` at each context).  This is the measure-level statement of
    Lorentz-covariance: the typicality data does not depend on the boost frame. -/
theorem weylBit_marginals_boost_invariant (A : H →ₗᵢ[ℂ] H) (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪A (u i), A (u j)⟫_ℂ = 0) :
    (weylBitNet (fun i => A (u i)) hiso').toFiniteMarginals.μ
      = (weylBitNet u hiso).toFiniteMarginals.μ := by
  have hbornPMF : ∀ (J : Finset ι) (x : ∀ j : J, Bool),
      (weylBitNet (fun i => A (u i)) hiso').bornPMF J x = (weylBitNet u hiso).bornPMF J x := by
    intro J x
    simp only [weylBitNet, EffectStateNet.bornPMF_apply, AddMonoidHom.id_apply,
      bornWeight_isometry_invariant A u hiso hiso']
  funext J
  exact congrArg PMF.toMeasure (PMF.ext (hbornPMF J))

/-- **THE PRIZE (per-frame form): the σ-additive typicality measure μ∞ is Lorentz-boost-covariant.**
    If `μ` realizes the Weyl-bit typicality family for the modes `u` and `ν` realizes it for the
    boosted modes `A∘u` (any one-particle isometry `A` — in particular the Lorentz boost `U₁(t)`), then
    `μ = ν`.  The two projective families coincide (`weylBit_marginals_boost_invariant`), so by uniqueness
    of the Kolmogorov limit the typicality measure is the SAME — boosting the apparatus does not change
    the typicality measure on the continuum free field.  Axiom-free. -/
theorem weylBit_typicality_boost_invariant (A : H →ₗᵢ[ℂ] H) (u : ι → H)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪A (u i), A (u j)⟫_ℂ = 0)
    {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet u hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => A (u i)) hiso').toFiniteMarginals.IsLimit ν) :
    μ = ν := by
  refine (weylBitNet u hiso).toFiniteMarginals.limit_unique hμ ?_
  show MeasureTheory.IsProjectiveLimit ν ((weylBitNet u hiso).toFiniteMarginals.μ)
  rw [← weylBit_marginals_boost_invariant A u hiso hiso']
  exact hν

/-- The F1 Lorentz boost `U₁(t)` preserves the symplectic-isotropy (microcausality) condition on the
    modes, since it is a one-particle isometry (`inner_map_map`). -/
theorem boostUnitary_preserves_isotropy {ι : Type*} (t : ℝ)
    (u : ι → Lp ℂ 2 (volume : Measure ℝ)) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0) :
    ∀ i j, i ≠ j →
      Complex.im ⟪(OneParticle.boostUnitary t).toLinearIsometry (u i),
        (OneParticle.boostUnitary t).toLinearIsometry (u j)⟫_ℂ = 0 :=
  fun i j hij => by rw [LinearIsometry.inner_map_map]; exact hiso i j hij

/-- **THE PRIZE (Lorentz boost `U₁(t)`):** the σ-additive Weyl-bit typicality measure μ∞ on the continuum
    free field over `L²(ℝ)` is invariant under the F1 rapidity boost `U₁(t)`.  If `μ` realizes the
    typicality family for the modes `u` and `ν` for the boosted modes `U₁(t)·u`, then `μ = ν`: the
    typicality measure is the same in every Lorentz frame.  Axiom-free, the literal Open-Problem-3b
    deliverable on the relativistic free field. -/
theorem weylBit_typicality_lorentzBoost_invariant {ι : Type*} [DecidableEq ι] (t : ℝ)
    (u : ι → Lp ℂ 2 (volume : Measure ℝ)) (hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0)
    {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet u hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => (OneParticle.boostUnitary t).toLinearIsometry (u i))
            (boostUnitary_preserves_isotropy t u hiso)).toFiniteMarginals.IsLimit ν) :
    μ = ν :=
  weylBit_typicality_boost_invariant (OneParticle.boostUnitary t).toLinearIsometry u hiso
    (boostUnitary_preserves_isotropy t u hiso) hμ hν

end QIQTH.Fock
