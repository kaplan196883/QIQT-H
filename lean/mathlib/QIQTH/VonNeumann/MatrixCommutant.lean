/-
  THE CLOSURE C5 (THE_CLOSURE_PLAN.md) — the two minimal matrix-commutant lemmas.

  Per the binding verdict, `(diag A)′ ≅ Mₙ(A′)` is NEVER proved — only the two directional facts
  the density argument consumes, both through the frozen C4 interface (`coordIncl`/`coordProj`/
  `diagCLM`; the PiLp synonym is never unfolded here):

  • ENTRIES  (`entry_mem_centralizer`): an operator commuting with the diagonal algebra has all
    its `π i ∘ S ∘ ι j` entries in the commutant A′.
  • ASSEMBLY (`commute_diag_of_entries`): an element of the bicommutant A″, amplified diagonally,
    commutes with every operator whose entries lie in A′ (entrywise extensionality).

  Together: `diag_mem_bicommutant` — T ∈ A″ ⟹ diag T ∈ (diag A)″ — the amplification step that
  turns C3's single-vector density into C6's n-vector density. `diagAlg` is the image of A under
  the diagonal ⋆-algebra homomorphism. No density statement, no SOT/WOT here.
-/
import Mathlib
import QIQTH.VonNeumann.Amplification

namespace QIQTH.VonNeumann

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n : ℕ}

/-- `diagCLM 0 = 0`. -/
theorem diagCLM_zero : diagCLM (n := n) (0 : H →L[ℂ] H) = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine PiLp.ext fun j => ?_
  rw [diagCLM_apply]
  rfl

/-- The diagonal embedding as a ⋆-algebra homomorphism. -/
noncomputable def diagHom (n : ℕ) :
    (H →L[ℂ] H) →⋆ₐ[ℂ]
      (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) where
  toFun := diagCLM
  map_one' := diagCLM_one
  map_mul' := diagCLM_mul
  map_zero' := diagCLM_zero
  map_add' := diagCLM_add
  commutes' := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      diagCLM_smul, diagCLM_one]
  map_star' := fun a => (star_diagCLM a).symm

theorem diagHom_apply (a : H →L[ℂ] H) : diagHom (H := H) n a = diagCLM a := rfl

/-- The diagonal image of a star-subalgebra. -/
noncomputable def diagAlg (A : StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) :
    StarSubalgebra ℂ (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :=
  StarSubalgebra.map (diagHom n) A

theorem diagAlg_coe (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (diagAlg A n : Set (PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)))
      = diagCLM '' (A : Set (H →L[ℂ] H)) := rfl

theorem diagCLM_mem_diagAlg {A : StarSubalgebra ℂ (H →L[ℂ] H)} {a : H →L[ℂ] H}
    (ha : a ∈ A) : diagCLM (n := n) a ∈ diagAlg A n :=
  ⟨a, ha, rfl⟩

/-- **ENTRIES**: an operator commuting with the diagonal image of `A` has all its
    `π i ∘ S ∘ ι j` entries in the commutant `A′`. -/
theorem entry_mem_centralizer {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {S : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)}
    (hS : S ∈ Set.centralizer (diagCLM '' (A : Set (H →L[ℂ] H)))) (i j : Fin n) :
    coordProj i ∘L S ∘L coordIncl j ∈ Set.centralizer (A : Set (H →L[ℂ] H)) := by
  intro a ha
  have hcomm : diagCLM a * S = S * diagCLM a := hS (diagCLM a) ⟨a, ha, rfl⟩
  refine ContinuousLinearMap.ext fun x => ?_
  have h5 : ∀ w : PiLp 2 (fun _ : Fin n => H), a (coordProj i w) = coordProj i (diagCLM a w) := by
    intro w
    have h := congrArg (fun (T : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H) => T w)
      (coordProj_comp_diagCLM a i)
    simp only [ContinuousLinearMap.comp_apply] at h
    exact h.symm
  have h6 : diagCLM a (coordIncl j x) = coordIncl j (a x) := by
    have h := congrArg (fun (T : H →L[ℂ] PiLp 2 (fun _ : Fin n => H)) => T x)
      (diagCLM_comp_coordIncl a j)
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hSa : diagCLM a (S (coordIncl j x)) = S (diagCLM a (coordIncl j x)) := by
    have h := congrArg
      (fun (T : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) =>
        T (coordIncl j x)) hcomm
    simpa only [ContinuousLinearMap.mul_apply] using h
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  rw [h5, hSa, h6]

/-- **ASSEMBLY**: a bicommutant element, amplified diagonally, commutes with every operator
    whose entries lie in the commutant (entrywise extensionality through the C4 interface). -/
theorem commute_diag_of_entries {A : StarSubalgebra ℂ (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    {S : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)}
    (hent : ∀ i j, coordProj i ∘L S ∘L coordIncl j
      ∈ Set.centralizer (A : Set (H →L[ℂ] H))) :
    diagCLM T * S = S * diagCLM T := by
  refine clm_ext_of_entries fun i j => ?_
  have hE : (coordProj i ∘L S ∘L coordIncl j) * T = T * (coordProj i ∘L S ∘L coordIncl j) :=
    hT (coordProj i ∘L S ∘L coordIncl j) (hent i j)
  refine ContinuousLinearMap.ext fun x => ?_
  have h5 : ∀ w : PiLp 2 (fun _ : Fin n => H), T (coordProj i w) = coordProj i (diagCLM T w) := by
    intro w
    have h := congrArg (fun (F : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H) => F w)
      (coordProj_comp_diagCLM T i)
    simp only [ContinuousLinearMap.comp_apply] at h
    exact h.symm
  have h6 : diagCLM T (coordIncl j x) = coordIncl j (T x) := by
    have h := congrArg (fun (F : H →L[ℂ] PiLp 2 (fun _ : Fin n => H)) => F x)
      (diagCLM_comp_coordIncl T j)
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hEx : coordProj i (S (coordIncl j (T x))) = T (coordProj i (S (coordIncl j x))) := by
    have h := congrArg (fun (F : H →L[ℂ] H) => F x) hE
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using h
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply]
  rw [← h5, h6, hEx]

/-- **C5 CAPSTONE — the amplification of the bicommutant**: `T ∈ A″ ⟹ diag T ∈ (diag A)″`. -/
theorem diag_mem_bicommutant {A : StarSubalgebra ℂ (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) :
    diagCLM (n := n) T
      ∈ Set.centralizer (Set.centralizer ((diagAlg A n : Set _))) := by
  intro S hS
  have hS' : S ∈ Set.centralizer (diagCLM '' (A : Set (H →L[ℂ] H))) := by
    rwa [← diagAlg_coe]
  have hent := fun i j => entry_mem_centralizer hS' i j
  exact (commute_diag_of_entries hT hent).symm

end QIQTH.VonNeumann
