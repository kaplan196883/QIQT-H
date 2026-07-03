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

end QIQTH.Embedding
