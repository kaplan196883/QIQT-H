/-
  THE CLOSURE C10 (THE_CLOSURE_PLAN.md, STRETCH) — the weak-operator-topology closure.

  The one theorem whose name may say "WOT" (binding verdict), proved wholly inside Mathlib's
  type copy `H →WOT[ℂ] H` about images under `ofCLM`:

      closure (ofCLM '' A) = ofCLM '' A″.

  ⊆ : for each fixed `s ∈ A′` the equalizer `{W | ofCLM s * W = W * ofCLM s}` is WOT-closed
      (`continuous_dual_apply` + `isClosed_eq`; T3 from `SeparatingDual ℂ H`, automatic for a
      Hilbert space) and contains the image of A — so the closure commutes with all of A′.
  ⊇ : SOT approximability (C7) beats every basic WOT neighborhood — a seminorm-ball
      `(s.sup (seminormFamily)).ball 0 r` is defeated by the C6 approximant on the tuple of the
      ball's vectors with margin `r/(Σ‖y‖ + 1)`.

  Together with C7 this identifies the WOT closure of a unital ⋆-subalgebra with its SOT
  closure and its bicommutant — the full classical statement. Only SEPARATE continuity of
  multiplication is used (the WOT copy is a semitopological ring; joint continuity is false).
-/
import Mathlib
import QIQTH.VonNeumann.Bicommutant

set_option maxHeartbeats 1000000

namespace QIQTH.VonNeumann

open ContinuousLinearMapWOT Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- SOT approximability defeats every basic WOT neighborhood: the image of an SOT-approximable
    operator lies in the WOT closure of the image of the algebra. -/
theorem ofCLM_mem_wotClosure_of_sotApprox {A : Set (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : SOTApprox A T) :
    (ofCLM T : H →WOT[ℂ] H) ∈ closure (ofCLM '' A) := by
  classical
  have h0 : (𝓝 (0 : H →WOT[ℂ] H)).HasBasis
      (· ∈ (seminormFamily (RingHom.id ℂ) H H).basisSets) id := hasBasis_seminorms
  have hmap := h0.map (fun W : H →WOT[ℂ] H => ofCLM T + W)
  have heq : Filter.map (fun W : H →WOT[ℂ] H => ofCLM T + W) (𝓝 0) = 𝓝 (ofCLM T) := by
    simpa using (Homeomorph.addLeft (ofCLM T : H →WOT[ℂ] H)).map_nhds_eq 0
  rw [heq] at hmap
  rw [mem_closure_iff_nhds_basis hmap]
  intro U hU
  rw [SeminormFamily.basisSets_iff] at hU
  obtain ⟨s, r, hr, rfl⟩ := hU
  set B : ℝ := ∑ q ∈ s, ‖q.2‖ with hB
  have hB0 : (0 : ℝ) ≤ B := Finset.sum_nonneg fun q _ => norm_nonneg _
  set δ : ℝ := r / (B + 1) with hδ
  have hδ0 : 0 < δ := div_pos hr (by linarith)
  obtain ⟨a, ha, hclose⟩ := hT s.card
    (fun i => ((s.equivFin.symm i : ↥s) : H × StrongDual ℂ H).1) δ hδ0
  refine ⟨ofCLM a, ⟨a, ha, rfl⟩, ⟨ofCLM a - ofCLM T, ?_, by abel⟩⟩
  show ofCLM a - ofCLM T ∈ (s.sup (seminormFamily (RingHom.id ℂ) H H)).ball 0 r
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt hr ?_
  rintro ⟨x, y⟩ hq
  show ‖y ((ofCLM a - ofCLM T : H →WOT[ℂ] H) x)‖ < r
  have hvec : (ofCLM a - ofCLM T : H →WOT[ℂ] H) x = a x - T x := by
    rw [← ofCLM_sub, ofCLM_apply]
    rfl
  rw [hvec]
  have hi := hclose (s.equivFin ⟨(x, y), hq⟩)
  have hξ : ((s.equivFin.symm (s.equivFin ⟨(x, y), hq⟩) : ↥s) : H × StrongDual ℂ H).1 = x := by
    rw [Equiv.symm_apply_apply]
  rw [hξ] at hi
  have hyB : ‖y‖ ≤ B := by
    rw [hB]
    exact Finset.single_le_sum (f := fun q : H × StrongDual ℂ H => ‖q.2‖)
      (fun q _ => norm_nonneg _) hq
  calc ‖y (a x - T x)‖ ≤ ‖y‖ * ‖a x - T x‖ := y.le_opNorm _
    _ ≤ B * ‖a x - T x‖ := mul_le_mul_of_nonneg_right hyB (norm_nonneg _)
    _ ≤ B * δ := by
        rw [norm_sub_rev] at hi
        exact mul_le_mul_of_nonneg_left hi.le hB0
    _ < r := by
        have h1 : B * δ < (B + 1) * δ := mul_lt_mul_of_pos_right (by linarith) hδ0
        have h2 : (B + 1) * δ = r := by
          rw [hδ, mul_div_cancel₀ _ (by linarith : (B + 1 : ℝ) ≠ 0)]
        linarith

/-- A WOT-limit of algebra elements commutes with the commutant: the ⊆ half. Only SEPARATE
    continuity of multiplication is used. -/
theorem toCLM_mem_bicommutant_of_mem_wotClosure {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    {W : H →WOT[ℂ] H} (hW : W ∈ closure (ofCLM '' (A : Set (H →L[ℂ] H)))) :
    toCLM W ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
  intro s hs
  have hf : Continuous fun V : H →WOT[ℂ] H => ofCLM s * V := by
    apply continuous_of_dual_apply_continuous
    intro x y
    have hkey : (fun V : H →WOT[ℂ] H => y ((ofCLM s * V) x))
        = fun V : H →WOT[ℂ] H => (y.comp s) (V x) := by
      funext V
      simp [mul_apply, ofCLM_apply]
    rw [hkey]
    exact continuous_dual_apply x (y.comp s)
  have hg : Continuous fun V : H →WOT[ℂ] H => V * ofCLM s := by
    apply continuous_of_dual_apply_continuous
    intro x y
    have hkey : (fun V : H →WOT[ℂ] H => y ((V * ofCLM s) x))
        = fun V : H →WOT[ℂ] H => y (V (s x)) := by
      funext V
      simp [mul_apply, ofCLM_apply]
    rw [hkey]
    exact continuous_dual_apply (s x) y
  have hclosed : IsClosed {V : H →WOT[ℂ] H | ofCLM s * V = V * ofCLM s} :=
    isClosed_eq hf hg
  have himg : ofCLM '' (A : Set (H →L[ℂ] H))
      ⊆ {V : H →WOT[ℂ] H | ofCLM s * V = V * ofCLM s} := by
    rintro _ ⟨a, ha, rfl⟩
    show ofCLM s * ofCLM a = ofCLM a * ofCLM s
    rw [← ofCLM_mul, ← ofCLM_mul, (hs a ha).symm]
  have hWcomm : ofCLM s * W = W * ofCLM s := closure_minimal himg hclosed hW
  have := congrArg toCLM hWcomm
  simpa only [toCLM_mul, toCLM_ofCLM] using this

/-- **C10 CAPSTONE — the WOT closure IS the bicommutant** (in the type copy, about `ofCLM`
    images): `closure (ofCLM '' A) = ofCLM '' A″`. With C7, the WOT closure, the SOT closure,
    and the double centralizer of a unital ⋆-subalgebra all coincide — the full classical
    double-commutant statement. -/
theorem wotClosure_image_eq_image_bicommutant (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    closure (ofCLM '' (A : Set (H →L[ℂ] H)) : Set (H →WOT[ℂ] H))
      = ofCLM '' (Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) := by
  apply Set.Subset.antisymm
  · intro W hW
    exact ⟨toCLM W, toCLM_mem_bicommutant_of_mem_wotClosure hW, ofCLM_toCLM W⟩
  · rintro _ ⟨T, hT, rfl⟩
    exact ofCLM_mem_wotClosure_of_sotApprox
      ((mem_centralizer_centralizer_iff_sotApprox A T).mp hT)

end QIQTH.VonNeumann
