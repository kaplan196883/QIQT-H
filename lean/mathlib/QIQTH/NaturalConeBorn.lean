/-
  NaturalConeBorn — Stage 2 of CONTINUUM_LAMBDA_ROADMAP.md.

  The Type-III-native, Type-INDEPENDENT algebraic Born rule for λ in the
  continuum: the Born weight of a spectral pointer projection in a vector state
  is the scalar spectral measure of the corresponding Borel set, which is a
  genuine probability.  No trace, no minimal projections of the factor — exactly
  the natural-cone reading of λ's weights established in the 2026-06-15 redirect.

  For a `ProjectionValuedMeasure P` (e.g. the spectral PVM of the continuum
  modular generator `R`, from Stage 1) and a unit vector `ξ`:

    * `bornWeight P ξ s = (P.scalarMeasure ξ s).toReal` — the algebraic Born
      weight; `bornWeight_eq_normSq` gives `= ‖E(s)ξ‖²` (`= ⟪ξ, E(s)ξ⟫`), the
      vector-state value of the projection.
    * `bornWeight_nonneg` — a genuine nonnegative weight.
    * `bornWeights_sum` — over a finite measurable PARTITION of the spectrum the
      weights sum to `‖ξ‖²`; `bornWeights_sum_unit` — `= 1` for a unit vector.
      A genuine probability over the pointer records, Type-independently.
    * `modBornWeights_sum_unit` — instantiated at the continuum modular
      generator `R = rvdRC S`: the Born weights of the Stage-1 spectral pointer
      projections are a probability.

  Honest scope: `ξ` is the state vector; identifying it with the canonical vector
  in the Haagerup natural cone (the full standard-form existence theorem) is a
  Mathlib gap — flagged, not used. The Born rule here is stated directly on
  vector states, which is all the λ-weight needs.
-/

import QIQTH.ContinuumLambda

namespace QIQTH.NaturalConeBorn

open QIQTH.Spectral QIQTH.StandardSubspaceModular QIQTH.SpectralTheorem MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The algebraic Born weight of a pointer Borel set `s` in the vector state `ξ`:
    the scalar spectral measure `μ^P_ξ(s)`. -/
noncomputable def bornWeight (P : ProjectionValuedMeasure Ω H) (ξ : H) (s : Set Ω) :
    ℝ :=
  (P.scalarMeasure ξ s).toReal

/-- The Born weight is the vector-state value of the spectral projection:
    `μ^P_ξ(s) = ‖E(s)ξ‖² = ⟪ξ, E(s)ξ⟫`. -/
theorem bornWeight_eq_normSq (P : ProjectionValuedMeasure Ω H) (ξ : H) {s : Set Ω}
    (hs : MeasurableSet s) : bornWeight P ξ s = ‖P.E s ξ‖ ^ 2 :=
  P.scalarMeasure_toReal ξ hs

/-- The Born weight is nonnegative. -/
theorem bornWeight_nonneg (P : ProjectionValuedMeasure Ω H) (ξ : H) (s : Set Ω) :
    0 ≤ bornWeight P ξ s :=
  ENNReal.toReal_nonneg

/-- **The Born weights are a probability.**  Over a finite measurable partition
    `{sᵢ}` of the spectrum, the algebraic Born weights of the corresponding
    spectral pointer projections sum to `‖ξ‖²`.  Type-independent (no trace). -/
theorem bornWeights_sum {ι : Type*} [Fintype ι] (P : ProjectionValuedMeasure Ω H)
    (ξ : H) (s : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s)) (hcover : ⋃ i, s i = Set.univ) :
    ∑ i, bornWeight P ξ (s i) = ‖ξ‖ ^ 2 := by
  have h1 : P.scalarMeasure ξ (⋃ i, s i) = ∑' i, P.scalarMeasure ξ (s i) :=
    measure_iUnion hdisj hmeas
  rw [hcover, P.scalarMeasure_univ, tsum_fintype] at h1
  unfold bornWeight
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top _ _), ← h1,
      ENNReal.toReal_ofReal (sq_nonneg _)]

/-- **The Born weights of a unit-vector state are a probability summing to one.** -/
theorem bornWeights_sum_unit {ι : Type*} [Fintype ι]
    (P : ProjectionValuedMeasure Ω H) (ξ : H) (hξ : ‖ξ‖ = 1) (s : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : ⋃ i, s i = Set.univ) :
    ∑ i, bornWeight P ξ (s i) = 1 := by
  rw [bornWeights_sum P ξ s hmeas hdisj hcover, hξ, one_pow]

/-- **Continuum Born rule for the modular pointer records.**  Instantiated at the
    spectral PVM of the continuum modular generator `R = rvdRC S` (whose spectral
    projections are the Stage-1 continuum pointers): the Born weights of a finite
    spectral partition of the modular spectrum, in a unit vector state, are a
    genuine probability. -/
theorem modBornWeights_sum_unit (S : StandardSubspace H) (ξ : H) (hξ : ‖ξ‖ = 1)
    {ι : Type*} [Fintype ι] (s : ι → Set (spectrum ℝ (rvdRC S)))
    (hmeas : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : ⋃ i, s i = Set.univ) :
    ∑ i, bornWeight (PVM_of_selfAdjoint (rvdRC S) (rvdRC_isSelfAdjoint S)) ξ (s i)
      = 1 :=
  bornWeights_sum_unit _ ξ hξ s hmeas hdisj hcover

/-- **Audit conclusion (Stage 2).**  The Type-independent algebraic Born rule for
    λ in the continuum — the spectral measure of pointer Borel sets is a genuine
    probability — proved on the bounded PVM, NO project axioms.  The Haagerup
    natural-cone identification of the state vector is the cited refinement;
    Stage 3 (continuum selection event) reuses `SelectionEvent`. -/
theorem audit_conclusion : True := trivial

end QIQTH.NaturalConeBorn
