/-
  THE CLOSURE C9 (THE_CLOSURE_PLAN.md) — downstream payoff (i): the directed-union limit
  von Neumann algebra (the refinement-tower limit, in its honest form).

  For a DIRECTED family of unital ⋆-subalgebras `Aᵢ ⊆ B(H)` on ONE Hilbert space, the union is
  itself a unital ⋆-subalgebra (`unionStarSubalgebra` — directedness closes products and sums),
  and `limitVN := generatedBy (⋃ i, Aᵢ)` is its von Neumann algebra, with C7's density theorem
  giving the concrete membership characterization: `T ∈ limitVN ↔ SOTApprox (⋃ i, Aᵢ) T`.

  ⚠ SCOPE BANNER (binding verdict): the project's `DiamondAlg` refinement tower (THE TOWER T7,
  `cornerEmbed`) has NO common Hilbert-space representation yet — the corner algebras live on
  DIFFERENT finite spaces, related by embeddings, not inside one B(H). This increment packages
  the limit for ANY HYPOTHESIZED common representation (a directed family of subalgebras of one
  B(H) — e.g. the image of the tower under a future GNS representation of the compatible tower
  state). The instantiation with the tower itself awaits the DEFERRED tower-GNS campaign
  (infinite tensor products / the GNS of the T5 tower state). No ITPFI factor is constructed
  here; no type is classified; the continuum is not done.
-/
import Mathlib
import QIQTH.VonNeumann.Bicommutant

namespace QIQTH.VonNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} (A : ι → StarSubalgebra ℂ (H →L[ℂ] H))

/-- The union of a DIRECTED family of ⋆-subalgebras is a ⋆-subalgebra (directedness closes the
    binary operations; unitality from any index). -/
def unionStarSubalgebra [Nonempty ι] (hdir : Directed (· ≤ ·) A) :
    StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := ⋃ i, (A i : Set (H →L[ℂ] H))
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_iUnion] at hx hy ⊢
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, mul_mem (hik hi) (hjk hj)⟩
  add_mem' := by
    intro x y hx hy
    rw [Set.mem_iUnion] at hx hy ⊢
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, add_mem (hik hi) (hjk hj)⟩
  one_mem' := Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, one_mem _⟩
  zero_mem' := Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, zero_mem _⟩
  algebraMap_mem' := fun r =>
    Set.mem_iUnion.mpr ⟨Classical.arbitrary ι, algebraMap_mem _ r⟩
  star_mem' := by
    intro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, star_mem hi⟩

theorem unionStarSubalgebra_coe [Nonempty ι] (hdir : Directed (· ≤ ·) A) :
    (unionStarSubalgebra A hdir : Set (H →L[ℂ] H))
      = ⋃ i, (A i : Set (H →L[ℂ] H)) := rfl

/-- **The limit von Neumann algebra of a directed family** — the refinement-tower limit for any
    hypothesized common representation. -/
noncomputable def limitVN [Nonempty ι] (hdir : Directed (· ≤ ·) A) : VonNeumannAlgebra H :=
  generatedBy (⋃ i, (A i : Set (H →L[ℂ] H)))

/-- Every stage of the family lies in the limit. -/
theorem stage_subset_limitVN [Nonempty ι] (hdir : Directed (· ≤ ·) A) (i : ι) :
    (A i : Set (H →L[ℂ] H)) ⊆ (limitVN A hdir : Set (H →L[ℂ] H)) := fun _ hx =>
  subset_generatedBy _ (Set.mem_iUnion.mpr ⟨i, hx⟩)

/-- **C9 CAPSTONE — the membership characterization of the limit**: an operator lies in the
    limit von Neumann algebra iff it is SOT-approximable from the union of the stages
    (C7's density theorem for the union ⋆-subalgebra; the union's ⋆-closure collapses the
    star-union in `generatedBy`). -/
theorem mem_limitVN_iff [Nonempty ι] (hdir : Directed (· ≤ ·) A) (T : H →L[ℂ] H) :
    T ∈ limitVN A hdir ↔ SOTApprox (⋃ i, (A i : Set (H →L[ℂ] H))) T := by
  have hstar : ∀ a ∈ (⋃ i, (A i : Set (H →L[ℂ] H))),
      star a ∈ ⋃ i, (A i : Set (H →L[ℂ] H)) := by
    intro a ha
    rw [Set.mem_iUnion] at ha ⊢
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, star_mem hi⟩
  have hcoe : (limitVN A hdir : Set (H →L[ℂ] H))
      = Set.centralizer (Set.centralizer (⋃ i, (A i : Set (H →L[ℂ] H)))) :=
    generatedBy_coe_of_starClosed hstar
  constructor
  · intro hT
    have hmem : T ∈ (limitVN A hdir : Set (H →L[ℂ] H)) := hT
    rw [hcoe] at hmem
    exact (mem_centralizer_centralizer_iff_sotApprox (unionStarSubalgebra A hdir) T).mp hmem
  · intro hT
    show T ∈ (limitVN A hdir : Set (H →L[ℂ] H))
    rw [hcoe]
    exact (mem_centralizer_centralizer_iff_sotApprox (unionStarSubalgebra A hdir) T).mpr hT

end QIQTH.VonNeumann
