/-
  ContinuumSelection — Stage 3 of CONTINUUM_LAMBDA_ROADMAP.md.

  The selection event in the continuum.  The point: λ's selection event needs
  only the finite *record* structure (a finite spectral pointer family — a finite
  coarse-graining of the Type III₁ algebra), NOT finiteness of the algebra.  So
  the inverse-CDF constructor of `SelectionEvent.lean` applies verbatim to the
  continuum modular Born weights of `NaturalConeBorn.lean` — the selection event
  is *Type-blind*.

  For a finite measurable partition `{sᵢ}` of the modular spectrum and a unit
  state `ξ`, with continuum Born weights `pᵢ = bornWeight (modular PVM) ξ sᵢ`:

    * `continuum_selects_exists_unique` — EXACTLY ONE record per actuality seed
      `s ∈ [0,1)` (totality + uniqueness), driven by the *continuum* Born weights;
    * `continuum_volume_selects` — the uniform seed measure of record `k` equals
      its continuum Born weight `pₖ` (the selection realizes the continuum Born
      frequencies).

  Axiom-free.  This closes the conceptual loop: the records λ selects are a finite
  family, even when the algebra is Type III₁; the selection event lives on that
  finite structure and is identical to the finite case.
-/

import QIQTH.NaturalConeBorn
import QIQTH.SelectionEvent

namespace QIQTH.ContinuumSelection

open QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem QIQTH.NaturalConeBorn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuum Born weights of a finite spectral partition `s : Fin n → …`,
    packaged as a function `ℕ → ℝ` (extended by `∅ ↦ 0`) for the inverse-CDF
    `SelectionEvent` constructor. -/
noncomputable def contWeights (S : StandardSubspace H) (ξ : H) {n : ℕ}
    (s : Fin n → Set (spectrum ℝ (rvdRC S))) (j : ℕ) : ℝ :=
  bornWeight (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)) ξ
    (if h : j < n then s ⟨j, h⟩ else ∅)

theorem contWeights_nonneg (S : StandardSubspace H) (ξ : H) {n : ℕ}
    (s : Fin n → Set (spectrum ℝ (rvdRC S))) (j : ℕ) : 0 ≤ contWeights S ξ s j :=
  bornWeight_nonneg _ _ _

/-- The continuum Born weights over the partition sum to one (unit state). -/
theorem contWeights_sum (S : StandardSubspace H) (ξ : H) (hξ : ‖ξ‖ = 1) {n : ℕ}
    (s : Fin n → Set (spectrum ℝ (rvdRC S))) (hmeas : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s)) (hcover : ⋃ i, s i = Set.univ) :
    ∑ j ∈ Finset.range n, contWeights S ξ s j = 1 := by
  rw [← Fin.sum_univ_eq_sum_range (contWeights S ξ s) n]
  have hpt : ∀ i : Fin n, contWeights S ξ s i.val
      = bornWeight (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)) ξ (s i) := by
    intro i
    unfold contWeights
    rw [dif_pos i.isLt, Fin.eta]
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  exact modBornWeights_sum_unit S ξ hξ s hmeas hdisj hcover

/-- **The continuum selection event: exactly one record per seed.**  Driven by
    the continuum modular Born weights, every actuality seed `seed ∈ [0,1)`
    selects a UNIQUE record `k < n` — the single-world consistency (totality +
    uniqueness), Type-blind. -/
theorem continuum_selects_exists_unique (S : StandardSubspace H) (ξ : H)
    (hξ : ‖ξ‖ = 1) {n : ℕ} (hn : 0 < n) (s : Fin n → Set (spectrum ℝ (rvdRC S)))
    (hmeas : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : ⋃ i, s i = Set.univ) {seed : ℝ} (hseed0 : 0 ≤ seed) (hseed1 : seed < 1) :
    ∃! k, k < n ∧ SelectionEvent.selects (contWeights S ξ s) seed k :=
  SelectionEvent.selects_exists_unique (contWeights_nonneg S ξ s) hn
    (contWeights_sum S ξ hξ s hmeas hdisj hcover) hseed0 hseed1

/-- **The continuum selection realizes Born.**  The Lebesgue measure of the seeds
    selecting record `k` equals its continuum Born weight `pₖ` — the uniform
    actuality-seed measure pushes to the continuum Born frequencies. -/
theorem continuum_volume_selects (S : StandardSubspace H) (ξ : H) {n : ℕ}
    (s : Fin n → Set (spectrum ℝ (rvdRC S))) (k : ℕ) :
    MeasureTheory.volume {seed : ℝ | SelectionEvent.selects (contWeights S ξ s) seed k}
      = ENNReal.ofReal (contWeights S ξ s k) :=
  SelectionEvent.volume_selects (contWeights S ξ s) k

/-- **Audit conclusion (Stage 3).**  The continuum selection event — exactly one
    record per seed, realizing the continuum Born weights — built by reusing the
    inverse-CDF `SelectionEvent` constructor on the Stage-2 continuum Born rule.
    NO project axioms.  The selection event needs only the finite *record*
    structure, not finiteness of the algebra: it is Type-blind.  Remaining: Stage
    4 (the Type III₁ classification boundary, cited). -/
theorem audit_conclusion : True := trivial

end QIQTH.ContinuumSelection
