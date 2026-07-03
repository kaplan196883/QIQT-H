/-
  THE CLOSURE C6 (THE_CLOSURE_PLAN.md) — n-vector density: the amplification pays off.

  `T ∈ A″` is norm-approximable by ONE element of `A` uniformly over any finite tuple of
  vectors: stack the tuple into `Hⁿ = PiLp 2`, amplify the bicommutant membership diagonally
  (C5's `diag_mem_bicommutant`), run the single-vector density (C3) for `diagAlg A n` on the
  stacked vector — an orbit element is `diagCLM a v`, whose `i`-th coordinate is `a (ξ i)` —
  and pull the estimate back coordinatewise (`norm_coord_le`).

  This is the quantifier shape of the binding verdict's `SOTApprox` (ONE `a` uniform over the
  whole tuple — the load-bearing point; C7 names the predicate and proves the iff). No SOT/WOT,
  no bicommutant statement here.
-/
import Mathlib
import QIQTH.VonNeumann.DensityOne
import QIQTH.VonNeumann.MatrixCommutant

namespace QIQTH.VonNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **C6 CAPSTONE — n-vector density**: an element of the double centralizer is norm-approximable
    by a SINGLE element of the algebra, uniformly over any finite tuple of vectors. -/
theorem bicommutant_sotApprox {A : StarSubalgebra ℂ (H →L[ℂ] H)} {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (n : ℕ) (ξ : Fin n → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ∀ i, ‖T (ξ i) - a (ξ i)‖ < ε := by
  set v : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 ξ with hv
  have hdiagT := diag_mem_bicommutant (n := n) hT
  obtain ⟨b, hb, hclose⟩ := bicommutant_apply_approx (diagAlg A n) hdiagT v hε
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨a, ha, fun i => ?_⟩
  have hcoord : (diagCLM T v - diagCLM a v) i = T (ξ i) - a (ξ i) := by
    rw [PiLp.sub_apply, diagCLM_apply, diagCLM_apply]
  calc ‖T (ξ i) - a (ξ i)‖ = ‖(diagCLM T v - diagCLM a v) i‖ := by rw [hcoord]
    _ ≤ ‖diagCLM T v - diagCLM a v‖ := norm_coord_le _ i
    _ < ε := hclose

end QIQTH.VonNeumann
