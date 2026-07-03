/-
  THE TOWER T7 (THE_TOWER_PLAN.md) — the finite operator tower: `cornerEmbed`.

  The honest finite shadow of the ITPFI refinement tower: for nested corners C ⊆ C′ the
  inclusion ι : DiamondAlg C → DiamondAlg C′ (act on the C-modes, identity on the complement) is
    • a unital ⋆-homomorphism    (cornerEmbed_one/_mul/_star/_add/_smul),
    • mode-compatible            (cornerEmbed_modeOp — the C-mode operators go to THE SAME
                                  mode operators upstairs),
    • state-compatible           (cornerEmbed_stateOf — φ_{C′} ∘ ι = φ_C, the operator form of
                                  DY4's Gibbs-marginal consistency),
    • MODULAR-FLOW EQUIVARIANT   (cornerEmbed_sigmaDiag — σ_s^{C′} ∘ ι = ι ∘ σ_s^C, via the
                                  kappaOf eigen-law: the Gibbs log-weight difference of two
                                  configurations agreeing off C is computed inside C).

  ⚠ HONEST SCOPE (binding verdict): this is a FAMILY OF FINITE-DIMENSIONAL MAPS only. No
  inductive limit, no weak closure, no infinite tensor product, and no von Neumann algebra is
  constructed; no type is claimed. This exhibits exactly the state-compatible modular-equivariant
  tower data that Araki–Woods 1968 would classify — the classification itself is never performed
  here.
-/
import Mathlib
import QIQTH.Dynamics
import QIQTH.FiniteCornerEigen

namespace QIQTH.Tower

open QIQTH.Keystone QIQTH.Embedding QIQTH.Dynamics QIQTH.FiniteModularTheory
open scoped Matrix

variable {M : Type*} [DecidableEq M] (L : LinkDims M) (C C' : Finset M)

/-- Two big-corner occupations agree OUTSIDE the sub-corner `C`. -/
def sameOffSub (m n : Micro L C') : Prop :=
  ∀ j : C', j.val ∉ C → m j = n j

instance (m n : Micro L C') : Decidable (sameOffSub L C C' m n) :=
  inferInstanceAs (Decidable (∀ j : C', j.val ∉ C → m j = n j))

theorem sameOffSub_refl (m : Micro L C') : sameOffSub L C C' m m := fun _ _ => rfl

theorem sameOffSub_symm {m n : Micro L C'} (h : sameOffSub L C C' m n) :
    sameOffSub L C C' n m := fun j hj => (h j hj).symm

theorem sameOffSub_trans {m p n : Micro L C'} (h1 : sameOffSub L C C' m p)
    (h2 : sameOffSub L C C' p n) : sameOffSub L C C' m n :=
  fun j hj => (h1 j hj).trans (h2 j hj)

/-- Overwrite a big-corner occupation on the sub-corner `C` by a `C`-occupation. -/
def updOn (m : Micro L C') (r : Micro L C) : Micro L C' :=
  fun j => if h : j.val ∈ C then r ⟨j.val, h⟩ else m j

theorem restrict_updOn (hCC : C ⊆ C') (m : Micro L C') (r : Micro L C) :
    restrictMicro L C' C hCC (updOn L C C' m r) = r := by
  funext j
  simp only [restrictMicro, updOn, dif_pos j.2]

theorem sameOffSub_updOn (m : Micro L C') (r : Micro L C) :
    sameOffSub L C C' m (updOn L C C' m r) := by
  intro j hj
  simp only [updOn, dif_neg hj]

theorem eq_updOn_of_sameOffSub (hCC : C ⊆ C') {m p : Micro L C'}
    (h : sameOffSub L C C' m p) :
    p = updOn L C C' m (restrictMicro L C' C hCC p) := by
  funext j
  by_cases hj : j.val ∈ C
  · simp only [updOn, dif_pos hj, restrictMicro]
  · simp only [updOn, dif_neg hj]
    exact (h j hj).symm

theorem updOn_injective (hCC : C ⊆ C') (m : Micro L C') :
    Function.Injective (updOn L C C' m) := by
  intro r r' h
  funext j
  have hj := congrFun h ⟨j.val, hCC j.2⟩
  simpa only [updOn, dif_pos j.2] using hj

/-- **The corner embedding**: act by `A` on the `C`-modes, identity on the complement — the
    finite refinement-tower inclusion `DiamondAlg C → DiamondAlg C′`. -/
def cornerEmbed (hCC : C ⊆ C') (A : DiamondAlg L C) : DiamondAlg L C' :=
  Matrix.of fun m n =>
    if sameOffSub L C C' m n
    then A (restrictMicro L C' C hCC m) (restrictMicro L C' C hCC n) else 0

theorem cornerEmbed_apply (hCC : C ⊆ C') (A : DiamondAlg L C) (m n : Micro L C') :
    cornerEmbed L C C' hCC A m n
      = if sameOffSub L C C' m n
        then A (restrictMicro L C' C hCC m) (restrictMicro L C' C hCC n) else 0 := rfl

/-- The embedding is UNITAL. -/
theorem cornerEmbed_one (hCC : C ⊆ C') : cornerEmbed L C C' hCC 1 = 1 := by
  ext m n
  rw [cornerEmbed_apply, Matrix.one_apply]
  by_cases h : sameOffSub L C C' m n
  · rw [if_pos h, Matrix.one_apply]
    by_cases hres : restrictMicro L C' C hCC m = restrictMicro L C' C hCC n
    · rw [if_pos hres, if_pos]
      funext j
      by_cases hj : j.val ∈ C
      · exact congrFun hres ⟨j.val, hj⟩
      · exact h j hj
    · rw [if_neg hres, if_neg fun hmn => hres (by rw [hmn])]
  · rw [if_neg h, Matrix.one_apply, if_neg fun hmn => h fun j _ => by rw [hmn]]

/-- The embedding is additive. -/
theorem cornerEmbed_add (hCC : C ⊆ C') (A B : DiamondAlg L C) :
    cornerEmbed L C C' hCC (A + B) = cornerEmbed L C C' hCC A + cornerEmbed L C C' hCC B := by
  ext m n
  simp only [cornerEmbed_apply, Matrix.add_apply]
  by_cases h : sameOffSub L C C' m n <;> simp [h]

/-- The embedding is ℂ-homogeneous. -/
theorem cornerEmbed_smul (hCC : C ⊆ C') (c : ℂ) (A : DiamondAlg L C) :
    cornerEmbed L C C' hCC (c • A) = c • cornerEmbed L C C' hCC A := by
  ext m n
  simp only [cornerEmbed_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : sameOffSub L C C' m n <;> simp [h]

/-- The embedding is a ⋆-map. -/
theorem cornerEmbed_star (hCC : C ⊆ C') (A : DiamondAlg L C) :
    cornerEmbed L C C' hCC Aᴴ = (cornerEmbed L C C' hCC A)ᴴ := by
  ext m n
  rw [Matrix.conjTranspose_apply, cornerEmbed_apply, cornerEmbed_apply,
    Matrix.conjTranspose_apply]
  by_cases h : sameOffSub L C C' m n
  · rw [if_pos h, if_pos (sameOffSub_symm L C C' h)]
  · rw [if_neg h, if_neg fun h' => h (sameOffSub_symm L C C' h'), star_zero]

/-- The embedding is MULTIPLICATIVE (with unitality and the ⋆-law: a unital ⋆-homomorphism) —
    the intermediate index sums over big-corner occupations collapse to the sub-corner fiber. -/
theorem cornerEmbed_mul (hCC : C ⊆ C') (A B : DiamondAlg L C) :
    cornerEmbed L C C' hCC (A * B) = cornerEmbed L C C' hCC A * cornerEmbed L C C' hCC B := by
  classical
  ext m n
  rw [cornerEmbed_apply, Matrix.mul_apply]
  by_cases hmn : sameOffSub L C C' m n
  · rw [if_pos hmn, Matrix.mul_apply]
    have hzero : ∀ p ∈ Finset.univ,
        p ∉ Finset.univ.image (updOn L C C' m) →
        cornerEmbed L C C' hCC A m p * cornerEmbed L C C' hCC B p n = 0 := by
      intro p _ hp
      have hnot : ¬ sameOffSub L C C' m p := by
        intro hsame
        apply hp
        rw [Finset.mem_image]
        exact ⟨restrictMicro L C' C hCC p, Finset.mem_univ _,
          (eq_updOn_of_sameOffSub L C C' hCC hsame).symm⟩
      rw [cornerEmbed_apply, if_neg hnot, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero,
      Finset.sum_image fun r _ r' _ h => updOn_injective L C C' hCC m h]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 : sameOffSub L C C' m (updOn L C C' m r) := sameOffSub_updOn L C C' m r
    have h2 : sameOffSub L C C' (updOn L C C' m r) n :=
      sameOffSub_trans L C C' (sameOffSub_symm L C C' h1) hmn
    rw [cornerEmbed_apply, cornerEmbed_apply, if_pos h1, if_pos h2,
      restrict_updOn L C C' hCC]
  · rw [if_neg hmn]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    simp only [cornerEmbed_apply]
    by_cases h1 : sameOffSub L C C' m p
    · rw [if_neg fun h2 => hmn (sameOffSub_trans L C C' h1 h2), mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **Mode compatibility**: the `C`-mode operators are carried to THE SAME mode operators of the
    big corner — the tower inclusions respect the field content. -/
theorem cornerEmbed_modeOp (hCC : C ⊆ C') (k : C)
    (A : Matrix (Fin (L.D k.val)) (Fin (L.D k.val)) ℂ) :
    cornerEmbed L C C' hCC (modeOp L C k A) = modeOp L C' ⟨k.val, hCC k.2⟩ A := by
  ext m n
  rw [cornerEmbed_apply, modeOp_apply, modeOp_apply]
  by_cases h : sameOffSub L C C' m n
  · rw [if_pos h]
    by_cases hk : sameOff L C k (restrictMicro L C' C hCC m) (restrictMicro L C' C hCC n)
    · have hlift : sameOff L C' ⟨k.val, hCC k.2⟩ m n := by
        intro j hj
        by_cases hjC : j.val ∈ C
        · exact hk ⟨j.val, hjC⟩
            fun he => hj (Subtype.ext (show j.val = k.val from congrArg Subtype.val he))
        · exact h j hjC
      rw [if_pos hk, if_pos hlift]
      rfl
    · rw [if_neg hk, if_neg]
      intro hcontra
      apply hk
      intro j hjk
      exact hcontra ⟨j.val, hCC j.2⟩
        fun he => hjk (Subtype.ext (Subtype.mk_eq_mk.mp he))
  · rw [if_neg h, if_neg]
    intro hcontra
    apply h
    intro j hjC
    refine hcontra j fun he => hjC ?_
    rw [show j.val = k.val from congrArg Subtype.val he]
    exact k.2

/-- The energy DIFFERENCE of two configurations agreeing off `C` is computed inside `C`
    (the complement contributions cancel termwise). -/
theorem energy_sub_of_sameOffSub (hCC : C ⊆ C') (ω : M → ℝ) {m n : Micro L C'}
    (h : sameOffSub L C C' m n) :
    energy L C' ω m - energy L C' ω n
      = energy L C ω (restrictMicro L C' C hCC m)
        - energy L C ω (restrictMicro L C' C hCC n) := by
  classical
  set F : M → ℝ := fun v =>
    if hv : v ∈ C' then ω v * (((m ⟨v, hv⟩ : ℕ) : ℝ) - ((n ⟨v, hv⟩ : ℕ) : ℝ)) else 0 with hF
  have hC' : energy L C' ω m - energy L C' ω n = ∑ v ∈ C', F v := by
    rw [energy, energy, ← Finset.sum_sub_distrib, ← Finset.sum_coe_sort C' F]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, dif_pos k.2]
    ring
  have hC : energy L C ω (restrictMicro L C' C hCC m)
      - energy L C ω (restrictMicro L C' C hCC n) = ∑ v ∈ C, F v := by
    rw [energy, energy, ← Finset.sum_sub_distrib, ← Finset.sum_coe_sort C F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hF, dif_pos (hCC j.2), restrictMicro]
    ring
  rw [hC', hC]
  refine (Finset.sum_subset hCC fun v hv hvC => ?_).symm
  simp only [hF, dif_pos hv]
  rw [h ⟨v, hv⟩ hvC, sub_self, mul_zero]

/-- **The kappaOf eigen-law of the tower**: the Gibbs log-weight difference of two big-corner
    configurations agreeing off `C` equals the sub-corner's own log-weight difference — the
    partition functions cancel and the complement energies cancel. This is what makes the
    modular flows of the tower compatible. -/
theorem kappaOf_gibbsWeight_of_sameOffSub (hCC : C ⊆ C') (ω : M → ℝ) (β : ℝ)
    {m n : Micro L C'} (h : sameOffSub L C C' m n) :
    QIQTH.TypeIITrace.kappaOf (gibbsWeight L C' ω β) m n
      = QIQTH.TypeIITrace.kappaOf (gibbsWeight L C ω β)
          (restrictMicro L C' C hCC m) (restrictMicro L C' C hCC n) := by
  rw [QIQTH.TypeIITrace.kappaOf, QIQTH.TypeIITrace.kappaOf,
    log_gibbsWeight, log_gibbsWeight, log_gibbsWeight, log_gibbsWeight]
  linear_combination (-β) * energy_sub_of_sameOffSub L C C' hCC ω h

/-- Trace against a diagonal density picks out the weighted diagonal. -/
theorem trace_diagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ)
    (X : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.diagonal d * X) = ∑ i, d i * X i i := by
  rw [Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-- **State compatibility**: the big corner's Gibbs state restricts to the sub-corner's Gibbs
    state through the embedding — `φ_{C′} ∘ ι = φ_C`. This is the OPERATOR form of DY4's
    marginal consistency (the same consistency that fed the T5 Kolmogorov extension). -/
theorem cornerEmbed_stateOf (hCC : C ⊆ C') (ω : M → ℝ) (β : ℝ) (A : DiamondAlg L C) :
    stateOf (gibbsDensity L C' ω β) (cornerEmbed L C C' hCC A)
      = stateOf (gibbsDensity L C ω β) A := by
  classical
  rw [stateOf, stateOf, gibbsDensity, gibbsDensity, trace_diagonal_mul, trace_diagonal_mul]
  rw [← Finset.sum_fiberwise Finset.univ (restrictMicro L C' C hCC)
    (fun m => ((gibbsWeight L C' ω β m : ℝ) : ℂ) * cornerEmbed L C C' hCC A m m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hterm : ∀ p ∈ Finset.univ.filter
      (fun p : Micro L C' => restrictMicro L C' C hCC p = r),
      ((gibbsWeight L C' ω β p : ℝ) : ℂ) * cornerEmbed L C C' hCC A p p
      = ((gibbsWeight L C' ω β p : ℝ) : ℂ) * A r r := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [cornerEmbed_apply, if_pos (sameOffSub_refl L C C' p), hp.2]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  rw [← marginal_gibbsWeight L C' ω C hCC β r, marginalWeight]
  push_cast
  rfl

/-- **T7 CAPSTONE — MODULAR-FLOW EQUIVARIANCE**: the tower inclusions intertwine the Gibbs
    modular flows — `σ_s^{C′} ∘ ι = ι ∘ σ_s^C` — via the kappaOf eigen-law (the phase of an
    entry is the log-weight difference, which is computed inside the sub-corner). Together with
    unitality, multiplicativity, the ⋆-law, mode compatibility and state compatibility this is
    the state-compatible modular-equivariant finite refinement tower: exactly the ITPFI tower
    DATA, as a family of finite-dimensional maps — no algebra limit is constructed and no type
    is claimed (Araki–Woods 1968 classification: CITED at T3, never proved). -/
theorem cornerEmbed_sigmaDiag (hCC : C ⊆ C') (ω : M → ℝ) (β s : ℝ) (A : DiamondAlg L C) :
    sigmaDiag (fun p => gibbsWeight L C' ω β p) s (cornerEmbed L C C' hCC A)
      = cornerEmbed L C C' hCC (sigmaDiag (fun r => gibbsWeight L C ω β r) s A) := by
  ext m n
  rw [sigmaDiag_entry L C' (fun p => gibbsWeight L C' ω β p)
    (fun p => gibbsWeight_pos L C' ω β p) s (cornerEmbed L C C' hCC A) m n,
    cornerEmbed_apply, cornerEmbed_apply]
  by_cases h : sameOffSub L C C' m n
  · rw [if_pos h, if_pos h, sigmaDiag_entry L C (fun r => gibbsWeight L C ω β r)
      (fun r => gibbsWeight_pos L C ω β r) s A]
    have hkappa := kappaOf_gibbsWeight_of_sameOffSub L C C' hCC ω β h
    rw [QIQTH.TypeIITrace.kappaOf, QIQTH.TypeIITrace.kappaOf] at hkappa
    rw [hkappa]
  · rw [if_neg h, if_neg h, mul_zero]

end QIQTH.Tower
