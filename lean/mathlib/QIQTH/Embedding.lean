/-
  THE EMBEDDING (THE_EMBEDDING_PLAN.md) — the matter-side dictionary: the N-mode truncated
  free-field diamond algebra IS a counted record corner.

  KEY OBSERVATION (binding): the keystone's microstate space `Micro L C = (e : C) → Fin (D e)` IS a
  multi-mode truncated Fock basis (joint occupation numbers `n_k < D_k`). No new Hilbert space is
  built — this file gives the already-counted `DiamondAlg` its FIELD structure and the mode↔link
  dictionary semantics. Transport, not construction; capacity is a constraint, NOT a generator;
  the cutoff→continuum limit is THE wall, never claimed.

  EM1 — the mode dictionary aliases:
  • `ModeAssignment` — mode labels with per-mode level cutoffs (the matter-side data);
  • `toLinkDims` — the dictionary map: A LINK IS A FIELD MODE, its dimension the mode's cutoff;
  • `FieldMicro`/`TruncatedFockBasis`/`FieldDiamondAlg` — the field-side readings of the keystone
    objects, with the rfl dictionary theorems (the identification is DEFINITIONAL);
  • CAPSTONE `truncated_field_diamond_entropy` — the keystone count READ as the truncated field
    diamond's entropy: `S(maxMixed) = Σ_k log D_k = A_τ(C)/4G`.
  Axiom-free, std-3.
-/
import Mathlib
import QIQTH.Keystone
import QIQTH.CornerConstruction

namespace QIQTH.Embedding

open QIQTH.Keystone
open scoped Matrix

variable {M : Type*} [DecidableEq M]

/-- **The mode assignment of a truncated field diamond** — mode labels with per-mode truncation
    cutoffs (`n_k` levels for mode `k`). NAMED finite data per the binding verdict: which modes
    belong to the diamond and how deep they are cut off is carried, never constructed from the
    continuum (the localization map stays the wall). -/
structure ModeAssignment (M : Type*) where
  /-- the truncation cutoff (level count) of each mode -/
  cutoff : M → ℕ
  /-- every mode carries at least one level -/
  cutoff_pos : ∀ k, 0 < cutoff k

/-- **The dictionary map**: a LINK is a FIELD MODE; the link dimension is the mode's cutoff. -/
def ModeAssignment.toLinkDims (A : ModeAssignment M) : LinkDims M :=
  ⟨A.cutoff, A.cutoff_pos⟩

@[simp] theorem ModeAssignment.toLinkDims_D (A : ModeAssignment M) (k : M) :
    A.toLinkDims.D k = A.cutoff k := rfl

/-- **The truncated Fock basis** of the diamond's mode set `C`: joint occupation numbers
    `n_k < D_k` — DEFINITIONALLY the keystone's microstate space. -/
abbrev FieldMicro (A : ModeAssignment M) (C : Finset M) : Type _ :=
  Micro A.toLinkDims C

/-- Alias: the occupation basis. -/
abbrev TruncatedFockBasis (A : ModeAssignment M) (C : Finset M) : Type _ :=
  FieldMicro A C

/-- **The truncated field diamond algebra** — the full matrix algebra on the occupation basis;
    DEFINITIONALLY the keystone's counted `DiamondAlg`. -/
abbrev FieldDiamondAlg (A : ModeAssignment M) (C : Finset M) : Type _ :=
  DiamondAlg A.toLinkDims C

/-- The dictionary is definitional: the truncated Fock basis IS the keystone microstate space. -/
theorem fieldMicro_eq_micro (A : ModeAssignment M) (C : Finset M) :
    FieldMicro A C = Micro A.toLinkDims C := rfl

/-- The dictionary is definitional: the field diamond algebra IS the counted diamond algebra. -/
theorem fieldDiamondAlg_eq_diamondAlg (A : ModeAssignment M) (C : Finset M) :
    FieldDiamondAlg A C = DiamondAlg A.toLinkDims C := rfl

/-- An occupation state is literally a choice of level below each mode's cutoff. -/
theorem fieldMicro_occupation (A : ModeAssignment M) (C : Finset M) :
    FieldMicro A C = ((k : C) → Fin (A.cutoff k.val)) := rfl

/-- **The truncated field diamond's state count**: `#(occupation basis) = Π_k D_k` — the keystone
    count read on the field side. -/
theorem card_truncatedFockBasis (A : ModeAssignment M) (C : Finset M) :
    Fintype.card (TruncatedFockBasis A C) = ∏ k ∈ C, A.cutoff k :=
  card_micro A.toLinkDims C

/-- **EM1 CAPSTONE — the count READS as the truncated field diamond's entropy:** the maximal
    entropy of the N-mode truncated free-field diamond algebra equals the sum of the per-mode
    log-cutoffs equals the trace-induced area over `4G` — the keystone theorem with LINKS = MODES.
    (The keystone capstone applied verbatim through the dictionary; nothing new is proved — that
    definitional transparency IS the point.) -/
theorem truncated_field_diamond_entropy (A : ModeAssignment M) (C : Finset M)
    {G : ℝ} (hG : G ≠ 0) :
    QIQTH.QuantumEntropy.vonNeumannEntropy (maxMixed_isDensity (ι := FieldMicro A C))
      = inducedScreenAreaTau A.toLinkDims G C / (4 * G) :=
  K2a_count_capstone A.toLinkDims C hG

/-! ## EM2 — the coordinate operator embedding

The direct-entry `modeOp` (per the binding verdict — NEVER Kronecker induction): a single-mode
matrix `A` acts on fiber `k`, delta elsewhere. The transport package (`modeOp_one/mul/add/smul/star`
+ injectivity) makes every single-mode truncated-oscillator theorem transportable into the diamond
algebra without ever unfolding the single-mode operators. -/

section ModeOp

variable (L : LinkDims M) (C : Finset M)

/-- Agreement off mode `k`: two occupation states that can differ only in the `k`-th fiber. -/
def sameOff (k : C) (m n : Micro L C) : Prop :=
  ∀ j : C, j ≠ k → m j = n j

instance (k : C) (m n : Micro L C) : Decidable (sameOff L C k m n) :=
  inferInstanceAs (Decidable (∀ j : C, j ≠ k → m j = n j))

theorem sameOff_refl (k : C) (m : Micro L C) : sameOff L C k m m := fun _ _ => rfl

theorem sameOff_symm {k : C} {m n : Micro L C} (h : sameOff L C k m n) :
    sameOff L C k n m := fun j hj => (h j hj).symm

theorem sameOff_trans {k : C} {m p n : Micro L C} (h1 : sameOff L C k m p)
    (h2 : sameOff L C k p n) : sameOff L C k m n :=
  fun j hj => (h1 j hj).trans (h2 j hj)

/-- The default (vacuum) occupation state. -/
def zeroMicro : Micro L C := fun e => ⟨0, L.hD e.val⟩

/-- Update the occupation of mode `k` (the dependent-update helper — casts hidden here, per the
    binding trap list). -/
def updMode (k : C) (m : Micro L C) (i : Fin (L.D k.val)) : Micro L C :=
  Function.update m k i

@[simp] theorem updMode_self (k : C) (m : Micro L C) (i : Fin (L.D k.val)) :
    updMode L C k m i k = i :=
  Function.update_self ..

theorem updMode_of_ne {k j : C} (hj : j ≠ k) (m : Micro L C) (i : Fin (L.D k.val)) :
    updMode L C k m i j = m j :=
  Function.update_of_ne hj ..

theorem sameOff_updMode (k : C) (m : Micro L C) (i : Fin (L.D k.val)) :
    sameOff L C k m (updMode L C k m i) :=
  fun j hj => (updMode_of_ne L C hj m i).symm

theorem eq_updMode_of_sameOff {k : C} {m p : Micro L C} (h : sameOff L C k m p) :
    p = updMode L C k m (p k) := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [updMode_self]
  · rw [updMode_of_ne L C hj]
    exact (h j hj).symm

theorem updMode_injective (k : C) (m : Micro L C) :
    Function.Injective (updMode L C k m) := fun i i' h => by
  have h2 := congrFun h k
  rwa [updMode_self, updMode_self] at h2

/-- **The fiber-sum lemma** (the reusable engine of EM2): a function vanishing off the
    `sameOff k m` fiber sums over the whole microstate space as a sum over the `k`-th occupation. -/
theorem sum_mode_fiber (k : C) (m : Micro L C) (f : Micro L C → ℂ)
    (hf : ∀ p, ¬ sameOff L C k m p → f p = 0) :
    (∑ p : Micro L C, f p) = ∑ i : Fin (L.D k.val), f (updMode L C k m i) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := updMode L C k m)
      (f := f) (fun x _ y _ h => updMode_injective L C k m h)]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro p _ hp
  refine hf p fun hs => hp ?_
  rw [Finset.mem_image]
  exact ⟨p k, Finset.mem_univ _, (eq_updMode_of_sameOff L C hs).symm⟩

/-- **The coordinate operator embedding**: `A` acting on the `k`-th fiber, delta elsewhere. -/
def modeOp (k : C) (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    DiamondAlg L C :=
  Matrix.of fun m n => if sameOff L C k m n then A (m k) (n k) else 0

theorem modeOp_apply (k : C) (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ)
    (m n : Micro L C) :
    modeOp L C k A m n = if sameOff L C k m n then A (m k) (n k) else 0 := rfl

/-- The embedding is unital. -/
theorem modeOp_one (k : C) : modeOp L C k 1 = 1 := by
  ext m n
  rw [modeOp_apply, Matrix.one_apply]
  by_cases h : sameOff L C k m n
  · rw [if_pos h, Matrix.one_apply]
    by_cases hk : m k = n k
    · rw [if_pos hk, if_pos]
      funext j
      by_cases hj : j = k
      · subst hj; exact hk
      · exact h j hj
    · rw [if_neg hk, if_neg fun hmn => hk (by rw [hmn])]
  · rw [if_neg h, Matrix.one_apply, if_neg fun hmn => h fun j _ => by rw [hmn]]

/-- The embedding is additive. -/
theorem modeOp_add (k : C) (A B : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k (A + B) = modeOp L C k A + modeOp L C k B := by
  ext m n
  simp only [modeOp_apply, Matrix.add_apply]
  by_cases h : sameOff L C k m n <;> simp [h]

/-- The embedding is ℂ-homogeneous. -/
theorem modeOp_smul (k : C) (c : ℂ) (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k (c • A) = c • modeOp L C k A := by
  ext m n
  simp only [modeOp_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : sameOff L C k m n <;> simp [h]

/-- The embedding is a ⋆-map: adjoints transport. -/
theorem modeOp_star (k : C) (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k Aᴴ = (modeOp L C k A)ᴴ := by
  ext m n
  rw [modeOp_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, modeOp_apply]
  by_cases h : sameOff L C k m n
  · rw [if_pos h, if_pos (sameOff_symm L C h)]
  · rw [if_neg h, if_neg fun h' => h (sameOff_symm L C h'), star_zero]

/-- **The embedding is multiplicative** (the crux — via the fiber-sum lemma; the single-mode
    product becomes the diamond product with all other fibers frozen). -/
theorem modeOp_mul (k : C) (A B : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k (A * B) = modeOp L C k A * modeOp L C k B := by
  ext m n
  by_cases h : sameOff L C k m n
  · have lhs : modeOp L C k (A * B) m n = ∑ i, A (m k) i * B i (n k) := by
      rw [modeOp_apply, if_pos h, Matrix.mul_apply]
    have rhs : (modeOp L C k A * modeOp L C k B) m n
        = ∑ i, A (m k) i * B i (n k) := by
      rw [Matrix.mul_apply,
        sum_mode_fiber L C k m (fun p => modeOp L C k A m p * modeOp L C k B p n)
          (fun p hp => by
            show modeOp L C k A m p * modeOp L C k B p n = 0
            rw [modeOp_apply, if_neg hp, zero_mul])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [modeOp_apply, modeOp_apply, if_pos (sameOff_updMode L C k m i),
        if_pos (sameOff_trans L C (sameOff_symm L C (sameOff_updMode L C k m i)) h),
        updMode_self]
    rw [lhs, rhs]
  · have lhs : modeOp L C k (A * B) m n = 0 := by rw [modeOp_apply, if_neg h]
    have rhs : (modeOp L C k A * modeOp L C k B) m n = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun p _ => ?_
      show modeOp L C k A m p * modeOp L C k B p n = 0
      by_cases hmp : sameOff L C k m p
      · rw [modeOp_apply L C k B, if_neg fun hpn => h (sameOff_trans L C hmp hpn), mul_zero]
      · rw [modeOp_apply L C k A, if_neg hmp, zero_mul]
    rw [lhs, rhs]

/-- **EM2 CAPSTONE — the embedding is injective**: distinct single-mode operators stay distinct in
    the diamond algebra (each truncated oscillator algebra genuinely EMBEDS). -/
theorem modeOp_injective (k : C) :
    Function.Injective (modeOp L C k) := by
  intro A B hAB
  ext i i'
  set m := updMode L C k (zeroMicro L C) i with hm
  set n := updMode L C k m i' with hn
  have h2 : modeOp L C k A m n = modeOp L C k B m n := by rw [hAB]
  rw [modeOp_apply, modeOp_apply, if_pos (sameOff_updMode L C k m i'),
    if_pos (sameOff_updMode L C k m i')] at h2
  simpa [hm, hn] using h2

end ModeOp

/-! ## EM3 — the per-mode oscillator structure

`a_k := modeOp k (lowering D_k)` — the held single-mode truncated-oscillator theorems TRANSPORTED
through the EM2 package (never unfolding `lowering`, per the binding verdict): the honest defect
`[a_k, a_k†] = 1 − D_k·P_top,k`, the number operator with its finite spectrum reading, and the
ladder relations `[N_k, a_k] = −a_k`, `[N_k, a_k†] = a_k†`. -/

section PerMode

variable (L : LinkDims M) (C : Finset M)

theorem modeOp_sub (k : C) (A B : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k (A - B) = modeOp L C k A - modeOp L C k B := by
  ext m n
  simp only [modeOp_apply, Matrix.sub_apply]
  by_cases h : sameOff L C k m n <;> simp [h]

theorem modeOp_neg (k : C) (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    modeOp L C k (-A) = -(modeOp L C k A) := by
  ext m n
  simp only [modeOp_apply, Matrix.neg_apply]
  by_cases h : sameOff L C k m n <;> simp [h]

/-- **The `k`-th mode annihilation operator** on the field diamond algebra. -/
noncomputable def modeLowering (k : C) : DiamondAlg L C :=
  modeOp L C k (QIQTH.CornerConstruction.lowering (L.D k.val))

/-- **The `k`-th mode number operator** (occupation of mode `k`). -/
noncomputable def numberOp (k : C) : DiamondAlg L C :=
  modeOp L C k (Matrix.diagonal fun i => ((i : ℕ) : ℂ))

/-- **The `k`-th mode truncation-site projector** — the single level where the defect lives. -/
noncomputable def topProjMode (k : C) : DiamondAlg L C :=
  modeOp L C k (QIQTH.CornerConstruction.topProjector (L.D k.val))

/-- `N_k = a_k† a_k` — the number operator is the transported single-mode identity. -/
theorem raising_mul_lowering (k : C) :
    (modeLowering L C k)ᴴ * modeLowering L C k = numberOp L C k := by
  rw [modeLowering, ← modeOp_star, ← modeOp_mul,
    QIQTH.CornerConstruction.conjTranspose_lowering_mul, numberOp]

/-- **EM3 CAPSTONE — the honest truncation defect, per mode:** `[a_k, a_k†] = 1 − D_k·P_top,k` —
    the held single-mode theorem transported through the embedding (never re-proved). Exact CCR is
    permanently impossible in finite dimension; the defect is stated, not hidden. -/
theorem mode_ladder_commutator (k : C) :
    modeLowering L C k * (modeLowering L C k)ᴴ - (modeLowering L C k)ᴴ * modeLowering L C k
      = 1 - (L.D k.val : ℂ) • topProjMode L C k := by
  rw [modeLowering, ← modeOp_star, ← modeOp_mul, ← modeOp_mul, ← modeOp_sub,
    QIQTH.CornerConstruction.truncated_ladder_commutator', modeOp_sub, modeOp_one, modeOp_smul,
    topProjMode]

/-- The number operator is diagonal in the occupation basis, with entry `n_k` — the finite
    spectrum reading (no analytic spectrum API, per the binding verdict). -/
theorem numberOp_apply_diag (k : C) (m n : Micro L C) :
    numberOp L C k m n = if m = n then ((m k : ℕ) : ℂ) else 0 := by
  rw [numberOp, modeOp_apply]
  by_cases h : sameOff L C k m n
  · rw [if_pos h, Matrix.diagonal_apply]
    by_cases hk : m k = n k
    · rw [if_pos hk, if_pos (show m = n by
        funext j
        by_cases hj : j = k
        · subst hj; exact hk
        · exact h j hj)]
    · rw [if_neg hk, if_neg fun hmn => hk (by rw [hmn])]
  · rw [if_neg h, if_neg fun hmn => h fun j _ => by rw [hmn]]

/-- **The occupation (pointer-basis) projector** `|m⟩⟨m|`. -/
noncomputable def occupationProj (m : Micro L C) : DiamondAlg L C :=
  Matrix.diagonal (fun p => if p = m then 1 else 0)

/-- **The joint-eigenbasis fact**: every occupation projector is an `N_k`-eigenprojector with
    eigenvalue `n_k = m k` — "the spectrum of `N_k` is `{0, …, D_k − 1}`" in its honest finite
    form. -/
theorem occupationProj_joint_eigen (k : C) (m : Micro L C) :
    numberOp L C k * occupationProj L C m = ((m k : ℕ) : ℂ) • occupationProj L C m := by
  ext p q
  rw [occupationProj, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases hq : q = m
  · rw [if_pos hq, mul_one, numberOp_apply_diag]
    by_cases hp : p = q
    · rw [if_pos hp, if_pos hp, if_pos (hp.trans hq), smul_eq_mul, mul_one, hp, hq]
    · rw [if_neg hp, if_neg hp, smul_zero]
  · rw [if_neg hq, mul_zero]
    by_cases hp : p = q
    · rw [if_pos hp, if_neg (hp ▸ hq), smul_zero]
    · rw [if_neg hp, smul_zero]

/-- The number operator is self-adjoint (real occupation numbers). -/
theorem numberOp_selfAdjoint (k : C) : (numberOp L C k)ᴴ = numberOp L C k := by
  rw [numberOp, ← modeOp_star]
  congr 1
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- The single-mode ladder relation `[N, a] = −a` (proved once at the single-mode level). -/
theorem number_comm_lowering (N : ℕ) :
    Matrix.diagonal (fun i : Fin N => ((i : ℕ) : ℂ)) * QIQTH.CornerConstruction.lowering N
        - QIQTH.CornerConstruction.lowering N * Matrix.diagonal (fun i : Fin N => ((i : ℕ) : ℂ))
      = -(QIQTH.CornerConstruction.lowering N) := by
  ext i j
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply,
    QIQTH.CornerConstruction.lowering]
  simp only [Matrix.of_apply]
  by_cases hij : (i : ℕ) + 1 = (j : ℕ)
  · rw [if_pos hij]
    have hj : ((j : ℕ) : ℂ) = ((i : ℕ) : ℂ) + 1 := by exact_mod_cast hij.symm
    rw [hj]
    ring
  · rw [if_neg hij]
    ring

/-- **The ladder relation transported**: `[N_k, a_k] = −a_k` — the annihilator lowers the
    occupation of its own mode. -/
theorem numberOp_comm_modeLowering (k : C) :
    numberOp L C k * modeLowering L C k - modeLowering L C k * numberOp L C k
      = -(modeLowering L C k) := by
  rw [numberOp, modeLowering, ← modeOp_mul, ← modeOp_mul, ← modeOp_sub, number_comm_lowering,
    modeOp_neg]

/-- `[N_k, a_k†] = a_k†` — the creator raises the occupation (by adjoints, no re-proof). -/
theorem numberOp_comm_modeRaising (k : C) :
    numberOp L C k * (modeLowering L C k)ᴴ - (modeLowering L C k)ᴴ * numberOp L C k
      = (modeLowering L C k)ᴴ := by
  have h := congrArg Matrix.conjTranspose (numberOp_comm_modeLowering L C k)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_neg, numberOp_selfAdjoint] at h
  rw [← neg_sub, h, neg_neg]

end PerMode

/-! ## EM4 — the cross-mode algebra

ONE generic theorem (per the binding verdict): coordinate operators at DIFFERENT modes commute
(`modeOp_commute_of_ne`, via the two-coordinate "same outside {k,j}" helper) — every cross-mode
commutator (ladders, adjoints, number operators) is a corollary, never re-proved. NOTE the honest
scope: different-mode pi-ladders COMMUTE — this is the bosonic sector; fermionic CAR needs the held
graded/FreeFieldCorner layer (cut, per the verdict). -/

section CrossMode

variable (L : LinkDims M) (C : Finset M)

/-- Agreement off the pair `{k, j}`. -/
def sameOff2 (k j : C) (m n : Micro L C) : Prop :=
  ∀ l : C, l ≠ k → l ≠ j → m l = n l

instance (k j : C) (m n : Micro L C) : Decidable (sameOff2 L C k j m n) :=
  inferInstanceAs (Decidable (∀ l : C, l ≠ k → l ≠ j → m l = n l))

/-- **The two-coordinate product entry**: for `k ≠ j`, the product of coordinate operators acts on
    the two fibers independently, delta elsewhere. -/
theorem modeOp_mul_apply_of_ne {k j : C} (hkj : k ≠ j)
    (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ)
    (B : Matrix (Fin (L.D j.val)) (Fin (L.D j.val)) ℂ) (m n : Micro L C) :
    (modeOp L C k A * modeOp L C j B) m n
      = if sameOff2 L C k j m n then A (m k) (n k) * B (m j) (n j) else 0 := by
  rw [Matrix.mul_apply,
    sum_mode_fiber L C k m (fun p => modeOp L C k A m p * modeOp L C j B p n)
      (fun p hp => by
        show modeOp L C k A m p * modeOp L C j B p n = 0
        rw [modeOp_apply, if_neg hp, zero_mul])]
  by_cases h2 : sameOff2 L C k j m n
  · rw [if_pos h2, Finset.sum_eq_single_of_mem (n k) (Finset.mem_univ _) ?h0]
    · show modeOp L C k A m (updMode L C k m (n k)) * modeOp L C j B (updMode L C k m (n k)) n
        = A (m k) (n k) * B (m j) (n j)
      rw [modeOp_apply, if_pos (sameOff_updMode L C k m (n k)), updMode_self,
        modeOp_apply L C j B,
        if_pos (show sameOff L C j (updMode L C k m (n k)) n from fun l hl => by
          by_cases hlk : l = k
          · subst hlk; rw [updMode_self]
          · rw [updMode_of_ne L C hlk]; exact h2 l hlk hl),
        updMode_of_ne L C hkj.symm]
    case h0 =>
      intro i _ hi
      show modeOp L C k A m (updMode L C k m i) * modeOp L C j B (updMode L C k m i) n = 0
      rw [modeOp_apply L C j B,
        if_neg (show ¬ sameOff L C j (updMode L C k m i) n from fun hs => by
          have hk := hs k hkj
          rw [updMode_self] at hk
          exact hi hk),
        mul_zero]
  · rw [if_neg h2]
    refine Finset.sum_eq_zero fun i _ => ?_
    show modeOp L C k A m (updMode L C k m i) * modeOp L C j B (updMode L C k m i) n = 0
    rw [modeOp_apply L C j B,
      if_neg (show ¬ sameOff L C j (updMode L C k m i) n from fun hs =>
        h2 fun l hlk hlj => by
          have hl := hs l hlj
          rwa [updMode_of_ne L C hlk] at hl),
      mul_zero]

/-- **EM4 CAPSTONE — the ONE generic cross-mode commutativity theorem:** coordinate operators at
    different modes commute. Every cross-mode commutator below is a corollary. -/
theorem modeOp_commute_of_ne {k j : C} (hkj : k ≠ j)
    (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ)
    (B : Matrix (Fin (L.D j.val)) (Fin (L.D j.val)) ℂ) :
    modeOp L C k A * modeOp L C j B = modeOp L C j B * modeOp L C k A := by
  ext m n
  rw [modeOp_mul_apply_of_ne L C hkj A B m n, modeOp_mul_apply_of_ne L C hkj.symm B A m n]
  have hiff : sameOff2 L C k j m n ↔ sameOff2 L C j k m n :=
    ⟨fun h l h1 h2 => h l h2 h1, fun h l h1 h2 => h l h2 h1⟩
  by_cases h2 : sameOff2 L C k j m n
  · rw [if_pos h2, if_pos (hiff.mp h2), mul_comm]
  · rw [if_neg h2, if_neg fun h => h2 (hiff.mpr h)]

/-- `[a_k, a_j] = 0` for `k ≠ j`. -/
theorem cross_lowering_commutator (k j : C) (hkj : k ≠ j) :
    modeLowering L C k * modeLowering L C j - modeLowering L C j * modeLowering L C k = 0 := by
  rw [modeLowering, modeLowering, modeOp_commute_of_ne L C hkj, sub_self]

/-- `[a_k, a_j†] = 0` for `k ≠ j` — the bosonic cross-mode independence (the honest scope:
    pi-fiber ladders commute; fermionic CAR needs the held graded layer, cut per the verdict). -/
theorem cross_ladder_commutator (k j : C) (hkj : k ≠ j) :
    modeLowering L C k * (modeLowering L C j)ᴴ
      - (modeLowering L C j)ᴴ * modeLowering L C k = 0 := by
  rw [modeLowering, modeLowering, ← modeOp_star, modeOp_commute_of_ne L C hkj, sub_self]

/-- `[N_k, a_j] = 0` for `k ≠ j` — occupations of other modes are untouched. -/
theorem cross_number_commutator (k j : C) (hkj : k ≠ j) :
    numberOp L C k * modeLowering L C j - modeLowering L C j * numberOp L C k = 0 := by
  rw [numberOp, modeLowering, modeOp_commute_of_ne L C hkj, sub_self]

end CrossMode

/-! ## EM5 — records and the counted corner

Records ARE occupation pointer-basis subsets (the theorem, not a slogan): the occupation projectors
are orthogonal, self-adjoint, resolve the identity, and every keystone record projector is their
sum; the record trace runs through the constructed τ₀ (the keystone clock window); and the field
dictionary transports into a capacity-bounded ambient corner with the HONEST identity `P = VVᴴ`
(never global 1, per the binding verdict). -/

section Records

variable (L : LinkDims M) (C : Finset M)

theorem occupationProj_star (m : Micro L C) :
    (occupationProj L C m)ᴴ = occupationProj L C m := by
  rw [occupationProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  by_cases h : p = m <;> simp [h]

theorem occupationProj_mul_self (m : Micro L C) :
    occupationProj L C m * occupationProj L C m = occupationProj L C m := by
  rw [occupationProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  by_cases h : p = m <;> simp [h]

theorem occupationProj_orthogonal {m m' : Micro L C} (h : m ≠ m') :
    occupationProj L C m * occupationProj L C m' = 0 := by
  rw [occupationProj, occupationProj, Matrix.diagonal_mul_diagonal]
  ext p q
  rw [Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases hpq : p = q
  · rw [if_pos hpq]
    by_cases h1 : p = m
    · rw [if_pos h1, if_neg fun h2 => h (h1.symm.trans h2), mul_zero]
    · rw [if_neg h1, zero_mul]
  · rw [if_neg hpq]

/-- **The occupation projectors resolve the identity** — the pointer basis is complete. -/
theorem sum_occupationProj_eq_one :
    (∑ m : Micro L C, occupationProj L C m) = 1 := by
  ext p q
  rw [Matrix.sum_apply, Matrix.one_apply]
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    simp only [occupationProj, Matrix.diagonal_apply_eq]
    rw [Finset.sum_ite_eq]
    simp
  · rw [if_neg hpq]
    exact Finset.sum_eq_zero fun m _ => by
      rw [occupationProj, Matrix.diagonal_apply_ne _ hpq]

/-- **EM5 CAPSTONE — records ARE occupation pointer-basis subsets:** every keystone record
    projector is the sum of the occupation projectors of its microstates. -/
theorem recordProj_eq_sum_occupationProj (R : Finset (Micro L C)) :
    recordProj L C R = ∑ m ∈ R, occupationProj L C m := by
  ext p q
  rw [recordProj, Matrix.sum_apply]
  by_cases hpq : p = q
  · subst hpq
    rw [Matrix.diagonal_apply_eq]
    simp only [occupationProj, Matrix.diagonal_apply_eq]
    rw [Finset.sum_ite_eq]
  · rw [Matrix.diagonal_apply_ne _ hpq]
    exact (Finset.sum_eq_zero fun m _ => by
      rw [occupationProj, Matrix.diagonal_apply_ne _ hpq]).symm

/-- Each occupation record counts exactly one microstate: `τ(|m⟩⟨m|) = 1`. -/
theorem tauCount_occupationProj (m : Micro L C) :
    tauCount L C (occupationProj L C m) = 1 := by
  rw [show tauCount L C (occupationProj L C m) = Matrix.trace (occupationProj L C m) from rfl,
    occupationProj, Matrix.trace_diagonal, Finset.sum_ite_eq']
  simp

/-- **The field record trace through the constructed τ₀** (the keystone clock window, links =
    modes): `τ₀(π(P_R)·q_{N_C}(L)) = |R|` — the truncated field diamond's records are counted by
    the crossed-product trace. -/
theorem field_record_tau0 (A : ModeAssignment M) (C : Finset M)
    (R : Finset (FieldMicro A C)) :
    QIQTH.TypeIITrace.tauMonomial (uniformState A.toLinkDims C)
        (recordProj A.toLinkDims C R) 0 (flatClock (NC A.toLinkDims C))
      = (R.card : ℂ) :=
  tau0_recordProj_eq_card A.toLinkDims C R

/-- **The corner transport with the honest `P`** — encoding the field dictionary into a
    capacity-bounded ambient corner (isometry `V`, `P = VVᴴ`), the per-mode defect commutator
    becomes `[ι_V(a_k), ι_V(a_k)†] = P − D_k·ι_V(P_top,k)`: the corner UNIT is `P`, never the
    ambient 1 (per the binding verdict). -/
theorem encoded_mode_ladder_commutator {d𝓗 : Type*} [Fintype d𝓗] [DecidableEq d𝓗]
    (V : Matrix d𝓗 (Micro L C) ℂ) (hV : Vᴴ * V = 1) (k : C) :
    QIQTH.CornerConstruction.encode V (modeLowering L C k)
        * (QIQTH.CornerConstruction.encode V (modeLowering L C k))ᴴ
      - (QIQTH.CornerConstruction.encode V (modeLowering L C k))ᴴ
        * QIQTH.CornerConstruction.encode V (modeLowering L C k)
      = QIQTH.CornerConstruction.codeProjector V
        - (L.D k.val : ℂ) • QIQTH.CornerConstruction.encode V (topProjMode L C k) := by
  rw [← QIQTH.CornerConstruction.encode_conjTranspose, ← QIQTH.CornerConstruction.encode_mul V hV,
    ← QIQTH.CornerConstruction.encode_mul V hV, ← QIQTH.CornerConstruction.encode_sub,
    mode_ladder_commutator, QIQTH.CornerConstruction.encode_sub,
    QIQTH.CornerConstruction.encode_smul]
  congr 1
  rw [QIQTH.CornerConstruction.encode, Matrix.mul_one]
  rfl

end Records

/-! ## EM6 — capacity and local areas

CAPACITY IS A CONSTRAINT, NOT A GENERATOR (binding phrasing): the FQ bound selects the
admissible/saturating subtype of cutoff assignments — the bound is a HYPOTHESIS implying the
entropy bound; saturation gives equality for a CHOSEN assignment; existence of exact integer
saturation for arbitrary external real area is never claimed (cut). Each mode occupies the local
area `4G·log D_k`; the local areas reassemble the trace-induced screen area. -/

section Capacity

variable (A : ModeAssignment M) (C : Finset M)

/-- **The capacity bound** — the FQ constraint on a mode assignment: the total log-cutoff fits in
    the area, `Σ_k log D_k ≤ Area/4G`. A constraint selecting admissible assignments. -/
def capacityBound (Area G : ℝ) : Prop :=
  ∑ k ∈ C, Real.log (A.cutoff k) ≤ Area / (4 * G)

/-- The field diamond's maximal entropy IS the total log-cutoff. -/
theorem field_entropy_eq_sum_log :
    QIQTH.QuantumEntropy.vonNeumannEntropy (maxMixed_isDensity (ι := FieldMicro A C))
      = ∑ k ∈ C, Real.log (A.cutoff k) := by
  rw [vonNeumannEntropy_maxMixed, card_micro, log_NC_eq_cutTau, cutTau]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **EM6 CAPSTONE — capacity CONSTRAINS the field entropy:** an admissible mode assignment's
    diamond entropy is area-bounded, `S(maxMixed) ≤ Area/4G` — the FQ postulate as a hypothesis,
    the entropy bound as its consequence. -/
theorem field_entropy_le_area_of_capacity {Area G : ℝ} (h : capacityBound A C Area G) :
    QIQTH.QuantumEntropy.vonNeumannEntropy (maxMixed_isDensity (ι := FieldMicro A C))
      ≤ Area / (4 * G) := by
  rw [field_entropy_eq_sum_log]
  exact h

/-- **Saturation gives equality for the CHOSEN assignment** — never existence of integer
    saturation for arbitrary external real area (cut, per the verdict). -/
theorem field_entropy_eq_area_of_saturation {Area G : ℝ}
    (h : ∑ k ∈ C, Real.log (A.cutoff k) = Area / (4 * G)) :
    QIQTH.QuantumEntropy.vonNeumannEntropy (maxMixed_isDensity (ι := FieldMicro A C))
      = Area / (4 * G) := by
  rw [field_entropy_eq_sum_log]
  exact h

/-- **The local mode area**: each mode occupies `4G·log D_k` of screen area. -/
noncomputable def localModeArea (G : ℝ) (k : M) : ℝ :=
  4 * G * Real.log (A.cutoff k)

/-- **The local mode areas reassemble the trace-induced screen area** — the per-mode reading of
    the keystone's `A_τ(C)`. -/
theorem sum_localModeArea (G : ℝ) :
    ∑ k ∈ C, localModeArea A G k = inducedScreenAreaTau A.toLinkDims G C := by
  rw [inducedScreenAreaTau, cutTau, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **The mode-count area bound** (the qubit-cutoff restatement): a diamond of two-level modes
    admissible under the capacity carries at most `Area/(4G·log 2)` modes —
    `|C|·log 2 ≤ Area/4G`. -/
theorem mode_count_le_area_of_qubit_capacity {Area G : ℝ}
    (hcut : ∀ k ∈ C, A.cutoff k = 2) (h : capacityBound A C Area G) :
    (C.card : ℝ) * Real.log 2 ≤ Area / (4 * G) := by
  have hsum : ∑ k ∈ C, Real.log (A.cutoff k) = (C.card : ℝ) * Real.log 2 := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hcut k hk] : ∀ k ∈ C,
      Real.log (A.cutoff k) = Real.log ((2 : ℕ) : ℝ)), Finset.sum_const, nsmul_eq_mul]
    norm_num
  rw [← hsum]
  exact h

end Capacity

end QIQTH.Embedding
