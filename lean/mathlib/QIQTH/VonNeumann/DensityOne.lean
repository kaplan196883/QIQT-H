/-
  THE CLOSURE C3 (THE_CLOSURE_PLAN.md) — single-vector density: `T ∈ A″ ⟹ Tξ ∈ cl(Aξ)`.

  The heart of the double-commutant theorem in its one-vector form: the cyclic-subspace
  projection P lies in A′ (C1), an element of the bicommutant commutes with it, and — THE
  UNITALITY USE — ξ itself lies in its own orbit closure (ξ = 1ξ), so Pξ = ξ and
  Tξ = T(Pξ) = P(Tξ) lands in the closed orbit.

  ⚠ UNITALITY IS LOAD-BEARING (counterexample): take A = {0}, the zero (non-unital) subalgebra.
  Its commutant is everything, so A″ = B(H) ∋ 1, but cl(Aξ) = {0} — the conclusion 1·ξ ∈ {0} is
  FALSE for ξ ≠ 0. The step that dies without 1 ∈ A is exactly ξ = Pξ: the vector need not lie
  in its own orbit closure. (In Lean the unitality rides in `StarSubalgebra`, which extends
  `Subalgebra` and hence contains 1 — this is where that hypothesis lives.)

  Single vector only — the n-vector version (C6) needs the amplification (C4–C5); no SOT/WOT,
  no bicommutant statement here.
-/
import Mathlib
import QIQTH.VonNeumann.InvariantProjection

namespace QIQTH.VonNeumann

open Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : StarSubalgebra ℂ (H →L[ℂ] H))

/-- **C3 CAPSTONE — single-vector density**: an element of the double centralizer maps every
    vector into that vector's closed orbit. `P := P_{cl(Aξ)} ∈ A′` (C1), `T` commutes with `P`,
    and `Pξ = ξ` by unitality, so `Tξ = T(Pξ) = P(Tξ) ∈ cl(Aξ)`. -/
theorem bicommutant_apply_mem_orbitClosure {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) (ξ : H) :
    T ξ ∈ orbitClosure A ξ := by
  set P : H →L[ℂ] H := (orbitClosure A ξ).starProjection with hP
  have hPmem : P ∈ Set.centralizer (A : Set (H →L[ℂ] H)) :=
    starProjection_orbitClosure_mem_centralizer A ξ
  have hcomm : P * T = T * P := hT P hPmem
  have hfix : P ξ = ξ :=
    Submodule.starProjection_eq_self_iff.mpr (self_mem_orbitClosure A ξ)
  have : T ξ = P (T ξ) := by
    conv_lhs => rw [← hfix]
    calc T (P ξ) = (T * P) ξ := rfl
      _ = (P * T) ξ := by rw [hcomm]
      _ = P (T ξ) := rfl
  rw [this]
  exact Submodule.starProjection_apply_mem (orbitClosure A ξ) (T ξ)

/-- The ε-form (what C6 consumes): an element of the double centralizer is norm-approximable
    at any single vector by elements of the algebra. -/
theorem bicommutant_apply_approx {T : H →L[ℂ] H}
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H)))) (ξ : H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ A, ‖T ξ - a ξ‖ < ε := by
  have hmem : T ξ ∈ closure ((orbitSubmodule A ξ : Set H)) := by
    have h1 := bicommutant_apply_mem_orbitClosure A hT ξ
    rw [← Submodule.topologicalClosure_coe]
    exact h1
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hdist⟩ := hmem ε hε
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨a, ha, by rwa [← dist_eq_norm]⟩

end QIQTH.VonNeumann
