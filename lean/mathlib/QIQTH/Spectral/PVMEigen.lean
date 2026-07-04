/-
  THE RESOLVENT campaign, increment R3: the PVM EIGENVECTOR / ATOM CALCULUS —
  an abstract, reusable supplement to the project's spectral tower
  (`PVM_of_selfAdjoint` → `borelFC`), absent from both the project and Mathlib.

  Contents (all axiom-free):

  (a) FINITE ADDITIVITY + COMPLEMENT on a genuine `ProjectionValuedMeasure`
      (the structure carries only σ-additivity `hasSum_iUnion`; the finite laws
      are derived from it here): `E_union_disjoint` (`E(s∪t) = E s + E t`),
      `E_add_compl` (`E s + E sᶜ = 1`), `E_compl` (`E sᶜ = 1 − E s`).

  (b) THE GENERIC OPERATOR SPECTRAL THEOREM `T = ∫ λ dE(λ)` at operator level:
      `eq_borelFC : T = borelFC T ha (coord)` for EVERY bounded self-adjoint `T`
      (de-specializing `rvdRC_eq_borelFC` of StandardSubspaceModularFlow.lean,
      whose proof was already generic: `scalarMeasure = specMeasure` bridge +
      `re_inner_T_eq_integral` + polarization + self-adjoint realness).

  (c) THE KERNEL ATOM: `E({0}) = 0` for INJECTIVE self-adjoint `T`
      (`E_zero_atom_of_injective`).  Kernel triviality does NOT kill the atom
      automatically; the multiplicative symbol identity `coord · 𝟙_{coord=0} = 0`
      does: `T ∘ E({0}) = borelFC(0) = 0`, then injectivity.

  (d) EIGENVECTOR LOCALIZATION + the FC-eigenvector capstone:
      `E_far_of_eigenvector` (`Tx = r·x ⟹ E(s)x = 0` for `s` ε-far from `r`,
      by the inverse-symbol trick `𝟙_s(ω)·(ω−r)⁻¹ · (coord−r) = 𝟙_s`),
      `mem_spectrum_of_eigenvector` (an eigenvalue lies in the ℝ-spectrum),
      `E_eigenvector_atom` (`E({r})x = x`, by the disjointed-annulus
      decomposition of `{ω ≠ r}` + σ-additivity), and
      `borelFC_apply_eigenvector` (`f(T) x = f(r) • x` for every bounded
      measurable `f` — the bounded Borel FC acts on eigenvectors by evaluation).

  Consumed by R5/R6 of THE_RESOLVENT_PLAN.md (`U_t Ω = Ω`, `E({0}) = 0` for the
  tower resolvent, `R = ∫ λ dE`).  Imports only Mathlib + the Spectral tower;
  NO TowerGNS imports.  Adds NO axioms.
-/
import QIQTH.Spectral.SpectralTheorem
import Mathlib.Tactic

/-! ### (a) Finite additivity and complement on a `ProjectionValuedMeasure` -/

namespace QIQTH
namespace Spectral
namespace ProjectionValuedMeasure

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (P : ProjectionValuedMeasure Ω H)

/-- **Finite additivity** of a genuine PVM on two disjoint measurable sets:
    `E(s ∪ t) = E s + E t`.  Derived from the σ-additivity field `hasSum_iUnion`
    on the eventually-empty sequence `(s, t, ∅, ∅, …)`: the strong sum of that
    family is on the one hand `E(s ∪ t)x` (σ-additivity), on the other the finite
    sum `E s x + E t x` (all later terms vanish by `E ∅ = 0`); limits are unique. -/
theorem E_union_disjoint {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hd : Disjoint s t) : P.E (s ∪ t) = P.E s + P.E t := by
  classical
  refine ContinuousLinearMap.ext fun x => ?_
  set A : ℕ → Set Ω := fun n => if n = 0 then s else if n = 1 then t else ∅ with hAdef
  have hA0 : A 0 = s := by simp [hAdef]
  have hA1 : A 1 = t := by simp [hAdef]
  have hA2 : ∀ n, 2 ≤ n → A n = ∅ := fun n hn => by
    simp only [hAdef]
    rw [if_neg (by omega), if_neg (by omega)]
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by
    by_cases h0 : n = 0
    · rw [h0, hA0]; exact hs
    by_cases h1 : n = 1
    · rw [h1, hA1]; exact ht
    · rw [hA2 n (by omega)]; exact MeasurableSet.empty
  have hApd : Pairwise fun m n => Disjoint (A m) (A n) := by
    intro m n hmn
    by_cases hm2 : 2 ≤ m
    · rw [hA2 m hm2]; exact Set.empty_disjoint _
    by_cases hn2 : 2 ≤ n
    · rw [hA2 n hn2]; exact Set.disjoint_empty _
    have hm2' : m < 2 := by omega
    have hn2' : n < 2 := by omega
    interval_cases m <;> interval_cases n
    · exact absurd rfl hmn
    · rw [hA0, hA1]; exact hd
    · rw [hA1, hA0]; exact hd.symm
    · exact absurd rfl hmn
  have hAU : (⋃ n, A n) = s ∪ t := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun n => ?_
      by_cases h0 : n = 0
      · rw [h0, hA0]; exact Set.subset_union_left
      by_cases h1 : n = 1
      · rw [h1, hA1]; exact Set.subset_union_right
      · rw [hA2 n (by omega)]; exact Set.empty_subset _
    · refine Set.union_subset ?_ ?_
      · intro a ha
        exact Set.mem_iUnion.mpr ⟨0, by rw [hA0]; exact ha⟩
      · intro a ha
        exact Set.mem_iUnion.mpr ⟨1, by rw [hA1]; exact ha⟩
  have hsum := P.hasSum_iUnion hAm hApd x
  rw [hAU] at hsum
  have hfin : HasSum (fun n => P.E (A n) x) (∑ n ∈ Finset.range 2, P.E (A n) x) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    have h2 : 2 ≤ n := by
      by_contra hlt
      exact hn (Finset.mem_range.mpr (by omega))
    rw [hA2 n h2, P.E_empty, ContinuousLinearMap.zero_apply]
  have hval : ∑ n ∈ Finset.range 2, P.E (A n) x = P.E s x + P.E t x := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hA0, hA1]
  rw [ContinuousLinearMap.add_apply, ← hval]
  exact hsum.unique hfin

/-- **Resolution of identity on a measurable set and its complement:**
    `E s + E sᶜ = 1`. -/
theorem E_add_compl {s : Set Ω} (hs : MeasurableSet s) : P.E s + P.E sᶜ = 1 := by
  rw [← P.E_union_disjoint hs hs.compl disjoint_compl_right, Set.union_compl_self,
    P.E_univ]

/-- **Complementation** on a genuine PVM (previously only on `PVContent`, whose
    finite-additivity FIELD a `ProjectionValuedMeasure` does not carry):
    `E sᶜ = 1 − E s` for measurable `s`. -/
theorem E_compl {s : Set Ω} (hs : MeasurableSet s) : P.E sᶜ = 1 - P.E s := by
  have h := P.E_add_compl hs
  rw [← h]; abel

/-- Vector form of complementation: `E sᶜ x = x − E s x`. -/
theorem E_compl_apply {s : Set Ω} (hs : MeasurableSet s) (x : H) :
    P.E sᶜ x = x - P.E s x := by
  rw [P.E_compl hs, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]

end ProjectionValuedMeasure
end Spectral
end QIQTH

/-! ### (b) The generic operator spectral theorem `T = ∫ λ dE` -/

namespace QIQTH.SpectralTheorem

open QIQTH.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H)

set_option maxHeartbeats 1000000 in
/-- **`scalarMeasure(PVM_of_selfAdjoint) = specMeasure`**, for EVERY bounded
    self-adjoint `T` (the generic form of the bridge proved for the RvD operator in
    StandardSubspaceModularFlow.lean): the PVM's scalar measure `μ_x(s) = ‖E(s)x‖²`
    agrees with the Riesz–Markov spectral measure, connecting the bounded-Borel-FC
    layer (`diagInt`/`bilinDiag`) to `re_inner_T_eq_integral`. -/
theorem pvmScalarMeasure_eq_specMeasure (ha : IsSelfAdjoint T) (x : H) :
    (PVM_of_selfAdjoint T ha).scalarMeasure x = specMeasure T ha x := by
  apply MeasureTheory.Measure.ext
  intro s hs
  have hErfl : (PVM_of_selfAdjoint T ha).E s = specProj T ha s := rfl
  have hidem : specProj T ha s * specProj T ha s = specProj T ha s := by
    have h := specProj_inter T ha hs hs
    rw [Set.inter_self] at h
    exact h.symm
  have hi : specProj T ha s (specProj T ha s x) = specProj T ha s x := by
    have := DFunLike.congr_fun hidem x
    rwa [ContinuousLinearMap.mul_apply] at this
  have hadj : ContinuousLinearMap.adjoint (specProj T ha s) = specProj T ha s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact (specProj_isSelfAdjoint T ha s).star_eq
  have hee : inner ℂ (specProj T ha s x) (specProj T ha s x)
      = inner ℂ (specProj T ha s x) x := by
    have h := ContinuousLinearMap.adjoint_inner_right (specProj T ha s) (specProj T ha s x) x
    rw [hadj, hi] at h
    exact h
  have hnorm : ‖specProj T ha s x‖ ^ 2 = qForm T ha s x := by
    rw [← reApplyInnerSelf_specProj T ha s x, ContinuousLinearMap.reApplyInnerSelf_apply,
        ← inner_self_eq_norm_sq (𝕜 := ℂ), hee]
  rw [(PVM_of_selfAdjoint T ha).scalarMeasure_apply x hs, hErfl, hnorm, qForm,
      MeasureTheory.measureReal_def,
      ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top (specMeasure T ha x) s)]

/-- The coordinate symbol `λ ↦ λ` on `σ(T)` — the integrand of `T = ∫ λ dE`. -/
noncomputable def specCoordFn : spectrum ℝ T → ℂ :=
  fun ω => ((ω : ℝ) : ℂ)

omit [CompleteSpace H] in
theorem specCoordFn_measurable : Measurable (specCoordFn T) :=
  Complex.continuous_ofReal.measurable.comp measurable_subtype_coe

omit [CompleteSpace H] in
/-- The canonical nonnegativity of the coordinate bound (kept as a NAMED constant so
    every `borelFC`-of-coordinate below is literally the same term). -/
theorem specCoordFn_bound_nonneg : (0 : ℝ) ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem specCoordFn_norm_le (ω : spectrum ℝ T) :
    ‖specCoordFn T ω‖ ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ := by
  rw [specCoordFn, Complex.norm_real]
  exact spectrum.norm_le_norm_mul_of_mem ω.2

/-- `borelFC` depends only on the symbol, not on the measurability/bound proofs
    (QIQTH-layer wrapper of `boundedFC_congr`). -/
theorem borelFC_congr_fun (ha : IsSelfAdjoint T) {f f' : spectrum ℝ T → ℂ}
    {Cf Cf' : ℝ} (hf : Measurable f) (hCf0 : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hf' : Measurable f') (hCf0' : 0 ≤ Cf') (hCf' : ∀ ω, ‖f' ω‖ ≤ Cf') (h : f = f') :
    borelFC T ha hf hCf0 hCf = borelFC T ha hf' hCf0' hCf' :=
  (PVM_of_selfAdjoint T ha).boundedFC_congr hf hCf0 hCf hf' hCf0' hCf' h

/-- **`diagInt(coord) z = ⟪z, T z⟫`** for every bounded self-adjoint `T` — the
    diagonal of `T = ∫ λ dE` (the `scalarMeasure = specMeasure` bridge +
    `re_inner_T_eq_integral` + self-adjoint realness of `⟪z, T z⟫`). -/
theorem diagInt_specCoordFn (ha : IsSelfAdjoint T) (z : H) :
    (PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) z = inner ℂ z (T z) := by
  rw [show (PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) z
        = ∫ ω, ((ω : ℝ) : ℂ) ∂((PVM_of_selfAdjoint T ha).scalarMeasure z)
      from rfl, pvmScalarMeasure_eq_specMeasure,
      show (∫ ω, ((ω : ℝ) : ℂ) ∂(specMeasure T ha z))
        = (((∫ ω, (ω : ℝ) ∂(specMeasure T ha z)) : ℝ) : ℂ)
      from integral_ofReal, re_inner_T_eq_integral]
  have hreal : (starRingEnd ℂ) (inner ℂ z (T z)) = inner ℂ z (T z) := by
    rw [inner_conj_symm]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha) z z
  exact Complex.conj_eq_iff_re.mp hreal

/-- **The generic operator spectral theorem: `T = borelFC(coord) = ∫ λ dE(λ)`** for
    every bounded self-adjoint `T` on a complex Hilbert space — the operator-level
    reconstruction of `T` from its own projection-valued measure, via polarization
    of `diagInt_specCoordFn` (de-specializing `rvdRC_eq_borelFC`). -/
theorem eq_borelFC (ha : IsSelfAdjoint T) :
    T = borelFC T ha (specCoordFn_measurable T) (specCoordFn_bound_nonneg T)
      (specCoordFn_norm_le T) := by
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [inner_borelFC,
      show (PVM_of_selfAdjoint T ha).bilinDiag (specCoordFn T) x y
        = 4⁻¹ * ((PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) (x + y)
          - (PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) (x - y)
          + Complex.I *
              (PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) (Complex.I • x + y)
          - Complex.I *
              (PVM_of_selfAdjoint T ha).diagInt (specCoordFn T) (Complex.I • x - y))
      from rfl,
      diagInt_specCoordFn, diagInt_specCoordFn, diagInt_specCoordFn, diagInt_specCoordFn]
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-! ### (c) The kernel atom: `E({0}) = 0` for injective self-adjoint `T` -/

/-- **THE KERNEL ATOM LEMMA.**  If the bounded self-adjoint `T` is injective, its
    PVM carries NO spectral weight at the point `0`: `E({0}) = 0` (with `{0}` the
    fiber `Subtype.val ⁻¹' {0}` in `σ(T)`).  Kernel triviality does not kill the
    atom automatically — the proof is multiplicative: the symbol product
    `coord · 𝟙_{coord = 0}` VANISHES identically, so by `T = ∫ λ dE` (b) and
    `borelFC_mul`, `T ∘ E({0}) = borelFC(0) = 0`; injectivity then forces
    `E({0})x = 0` for every `x`. -/
theorem E_zero_atom_of_injective (ha : IsSelfAdjoint T) (hinj : Function.Injective T) :
    (PVM_of_selfAdjoint T ha).E (Subtype.val ⁻¹' ({0} : Set ℝ)) = 0 := by
  classical
  set s₀ : Set (spectrum ℝ T) := Subtype.val ⁻¹' ({0} : Set ℝ) with hs₀def
  have hs₀ : MeasurableSet s₀ := measurable_subtype_coe (measurableSet_singleton 0)
  have hindm : Measurable (s₀.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs₀
  have hpm : Measurable (fun ω => specCoordFn T ω * s₀.indicator (fun _ => (1 : ℂ)) ω) :=
    (specCoordFn_measurable T).mul hindm
  have hpb : ∀ ω, ‖specCoordFn T ω * s₀.indicator (fun _ => (1 : ℂ)) ω‖
      ≤ (‖T‖ * ‖(1 : H →L[ℂ] H)‖) * 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (specCoordFn_norm_le T ω)
      (ProjectionValuedMeasure.norm_indicatorOne_le s₀ ω) (norm_nonneg _)
      (specCoordFn_bound_nonneg T)
  -- the symbol product vanishes identically
  have hkey : (fun ω => specCoordFn T ω * s₀.indicator (fun _ => (1 : ℂ)) ω)
      = fun _ => (0 : ℂ) := by
    funext ω
    by_cases hω : ω ∈ s₀
    · have hv : ((ω : ℝ) : ℂ) = 0 := by
        have h0 : (ω : ℝ) = 0 := hω
        rw [h0, Complex.ofReal_zero]
      rw [show specCoordFn T ω = ((ω : ℝ) : ℂ) from rfl, hv, zero_mul]
    · rw [Set.indicator_of_notMem hω, mul_zero]
  -- borelFC of the vanishing product is 0
  have hzero : borelFC T ha hpm (mul_nonneg (specCoordFn_bound_nonneg T) zero_le_one) hpb
      = 0 := by
    have h1 : borelFC T ha hpm (mul_nonneg (specCoordFn_bound_nonneg T) zero_le_one) hpb
        = borelFC T ha (f := fun _ => (0 : ℂ)) measurable_const (norm_nonneg (0 : ℂ))
            (fun _ => le_rfl) :=
      borelFC_congr_fun T ha hpm _ hpb measurable_const (norm_nonneg (0 : ℂ))
        (fun _ => le_rfl) hkey
    rw [h1, borelFC_const T ha 0, zero_smul]
  -- multiplicativity: `T ∘ E({0}) = 0`
  have hmul : borelFC T ha hpm (mul_nonneg (specCoordFn_bound_nonneg T) zero_le_one) hpb
      = borelFC T ha (specCoordFn_measurable T) (specCoordFn_bound_nonneg T)
          (specCoordFn_norm_le T)
        * borelFC T ha hindm zero_le_one (ProjectionValuedMeasure.norm_indicatorOne_le s₀) :=
    borelFC_mul T ha (specCoordFn_measurable T) (specCoordFn_bound_nonneg T)
      (specCoordFn_norm_le T) hindm zero_le_one
      (ProjectionValuedMeasure.norm_indicatorOne_le s₀)
      hpm (mul_nonneg (specCoordFn_bound_nonneg T) zero_le_one) hpb
  have hTE : T * (PVM_of_selfAdjoint T ha).E s₀ = 0 := by
    have h2 := hmul.symm.trans hzero
    rwa [← eq_borelFC T ha, borelFC_indicator T ha hs₀] at h2
  -- injectivity kills the projection
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.zero_apply]
  have hx := DFunLike.congr_fun hTE x
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] at hx
  exact hinj (hx.trans (map_zero T).symm)

/-! ### (d) Eigenvector localization and the FC-eigenvector capstone -/

/-- **Eigenvector localization (the far lemma).**  If `T x = r • x` and the
    measurable set `s ⊆ σ(T)` stays at distance `≥ ε > 0` from `r`, then
    `E(s) x = 0`.  Inverse-symbol trick: `h := 𝟙_s(ω) · (ω − r)⁻¹` is bounded by
    `ε⁻¹` and satisfies `h · (coord − r) = 𝟙_s` pointwise, so
    `E(s) = borelFC(h) ∘ (T − r·1)` — and `(T − r·1) x = 0`. -/
theorem E_far_of_eigenvector (ha : IsSelfAdjoint T) {r : ℝ} {x : H}
    (hTx : T x = (r : ℂ) • x) {s : Set (spectrum ℝ T)} (hs : MeasurableSet s)
    {ε : ℝ} (hε : 0 < ε) (hfar : ∀ ω ∈ s, ε ≤ |(ω : ℝ) - r|) :
    (PVM_of_selfAdjoint T ha).E s x = 0 := by
  classical
  -- the inverse symbol
  set h : spectrum ℝ T → ℂ := s.indicator (fun ω => ((((ω : ℝ) - r)⁻¹ : ℝ) : ℂ)) with hhdef
  have hhm : Measurable h :=
    (Complex.measurable_ofReal.comp
      ((measurable_subtype_coe.sub measurable_const).inv)).indicator hs
  have hC0h : (0 : ℝ) ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have hhb : ∀ ω, ‖h ω‖ ≤ ε⁻¹ := by
    intro ω
    by_cases hω : ω ∈ s
    · rw [hhdef, Set.indicator_of_mem hω, Complex.norm_real, Real.norm_eq_abs, abs_inv]
      exact inv_anti₀ hε (hfar ω hω)
    · rw [hhdef, Set.indicator_of_notMem hω, norm_zero]
      exact hC0h
  -- the affine symbol `coord − r`
  have hgm : Measurable (fun ω => specCoordFn T ω + (-(r : ℂ))) :=
    (specCoordFn_measurable T).add measurable_const
  have hC0g : (0 : ℝ) ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ + ‖(-(r : ℂ))‖ :=
    add_nonneg (specCoordFn_bound_nonneg T) (norm_nonneg _)
  have hgb : ∀ ω, ‖specCoordFn T ω + (-(r : ℂ))‖
      ≤ ‖T‖ * ‖(1 : H →L[ℂ] H)‖ + ‖(-(r : ℂ))‖ :=
    fun ω => (norm_add_le _ _).trans (add_le_add (specCoordFn_norm_le T ω) le_rfl)
  -- the product symbol
  have hpm : Measurable (fun ω => h ω * (specCoordFn T ω + (-(r : ℂ)))) := hhm.mul hgm
  have hC0p : (0 : ℝ) ≤ ε⁻¹ * (‖T‖ * ‖(1 : H →L[ℂ] H)‖ + ‖(-(r : ℂ))‖) :=
    mul_nonneg hC0h hC0g
  have hpb : ∀ ω, ‖h ω * (specCoordFn T ω + (-(r : ℂ)))‖
      ≤ ε⁻¹ * (‖T‖ * ‖(1 : H →L[ℂ] H)‖ + ‖(-(r : ℂ))‖) := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hhb ω) (hgb ω) (norm_nonneg _) hC0h
  -- pointwise: `h · (coord − r) = 𝟙_s`
  have hkey : (fun ω => h ω * (specCoordFn T ω + (-(r : ℂ))))
      = s.indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ s
    · rw [hhdef, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hne : (ω : ℝ) - r ≠ 0 := by
        intro h0
        have hf := hfar ω hω
        rw [h0, abs_zero] at hf
        linarith
      have hcast : specCoordFn T ω + (-(r : ℂ)) = (((ω : ℝ) - r : ℝ) : ℂ) := by
        rw [show specCoordFn T ω = ((ω : ℝ) : ℂ) from rfl]
        push_cast
        ring
      rw [hcast, ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one]
    · rw [hhdef, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
  -- operator identity: `E(s) = borelFC(h) ∘ borelFC(coord − r)`
  have hEs : (PVM_of_selfAdjoint T ha).E s
      = borelFC T ha hhm hC0h hhb * borelFC T ha hgm hC0g hgb := by
    have h1 : borelFC T ha hpm hC0p hpb
        = borelFC T ha hhm hC0h hhb * borelFC T ha hgm hC0g hgb :=
      borelFC_mul T ha hhm hC0h hhb hgm hC0g hgb hpm hC0p hpb
    have h2 : borelFC T ha hpm hC0p hpb = (PVM_of_selfAdjoint T ha).E s := by
      have hcongr : borelFC T ha hpm hC0p hpb
          = borelFC T ha (measurable_const.indicator hs) zero_le_one
              (ProjectionValuedMeasure.norm_indicatorOne_le s) :=
        borelFC_congr_fun T ha hpm hC0p hpb (measurable_const.indicator hs) zero_le_one
          (ProjectionValuedMeasure.norm_indicatorOne_le s) hkey
      rw [hcongr]
      exact borelFC_indicator T ha hs
    rw [← h2, h1]
  -- `borelFC(coord − r) x = 0` since `x` is an `r`-eigenvector
  have hgx : borelFC T ha hgm hC0g hgb x = 0 := by
    have hAdd : borelFC T ha hgm hC0g hgb
        = borelFC T ha (specCoordFn_measurable T) (specCoordFn_bound_nonneg T)
            (specCoordFn_norm_le T)
          + borelFC T ha (f := fun _ : spectrum ℝ T => (-(r : ℂ))) measurable_const
              (norm_nonneg (-(r : ℂ))) (fun _ => le_rfl) :=
      (PVM_of_selfAdjoint T ha).boundedFC_add (specCoordFn_measurable T) measurable_const
        (specCoordFn_bound_nonneg T) (norm_nonneg (-(r : ℂ))) (specCoordFn_norm_le T)
        (fun _ => le_rfl)
    rw [hAdd, ContinuousLinearMap.add_apply, ← eq_borelFC T ha, borelFC_const T ha (-(r : ℂ)),
      hTx, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, ← add_smul,
      add_neg_cancel, zero_smul]
  calc (PVM_of_selfAdjoint T ha).E s x
      = (borelFC T ha hhm hC0h hhb) ((borelFC T ha hgm hC0g hgb) x) := by
        rw [hEs, ContinuousLinearMap.mul_apply]
    _ = (borelFC T ha hhm hC0h hhb) 0 := by rw [hgx]
    _ = 0 := map_zero _

omit [CompleteSpace H] in
/-- An eigenvalue of a bounded operator lies in its ℝ-spectrum: if `T x = r • x`
    with `x ≠ 0`, then `r ∈ spectrum ℝ T` (a unit `algebraMap r − T` would force
    `x = 0`). -/
theorem mem_spectrum_of_eigenvector {r : ℝ} {x : H} (hx : x ≠ 0)
    (hTx : T x = (r : ℂ) • x) : r ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  intro hu
  apply hx
  have hBx : (algebraMap ℝ (H →L[ℂ] H) r - T) x = 0 := by
    rw [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hTx,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact sub_eq_zero_of_eq rfl
  obtain ⟨u, hu_eq⟩ := hu
  have hunit : (↑u⁻¹ : H →L[ℂ] H) * (algebraMap ℝ (H →L[ℂ] H) r - T) = 1 := by
    rw [← hu_eq]
    exact u.inv_mul
  calc x = ((↑u⁻¹ : H →L[ℂ] H) * (algebraMap ℝ (H →L[ℂ] H) r - T)) x := by
        rw [hunit, ContinuousLinearMap.one_apply]
    _ = (↑u⁻¹ : H →L[ℂ] H) ((algebraMap ℝ (H →L[ℂ] H) r - T) x) := by
        rw [ContinuousLinearMap.mul_apply]
    _ = 0 := by rw [hBx, map_zero]

/-- **THE EIGENVECTOR ATOM.**  An eigenvector is entirely carried by the spectral
    atom at its eigenvalue: `T x = r • x  ⟹  E({r}) x = x`.  Proof: the complement
    `{ω ≠ r}` is the disjointified union of the annuli `{|ω − r| ≥ 1/(n+1)}`, each
    of which carries none of `x` by the far lemma; σ-additivity (`hasSum_iUnion`)
    sums the zeros, and complementation (a) returns the atom.  (No `x ≠ 0` and no
    `r ∈ σ(T)` needed: for `r ∉ σ(T)` the fiber is empty and `x = 0` is forced.) -/
theorem E_eigenvector_atom (ha : IsSelfAdjoint T) {r : ℝ} {x : H}
    (hTx : T x = (r : ℂ) • x) :
    (PVM_of_selfAdjoint T ha).E (Subtype.val ⁻¹' ({r} : Set ℝ)) x = x := by
  classical
  set s₀ : Set (spectrum ℝ T) := Subtype.val ⁻¹' ({r} : Set ℝ) with hs₀def
  have hs₀ : MeasurableSet s₀ := measurable_subtype_coe (measurableSet_singleton r)
  -- the annuli
  set B : ℕ → Set (spectrum ℝ T) := fun n => {ω | 1 / (n + 1 : ℝ) ≤ |(ω : ℝ) - r|}
    with hBdef
  have hsubm : Measurable (fun ω : spectrum ℝ T => |(ω : ℝ) - r|) :=
    continuous_abs.measurable.comp (measurable_subtype_coe.sub measurable_const)
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_le measurable_const hsubm
  have hAm : ∀ n, MeasurableSet (disjointed B n) := MeasurableSet.disjointed hBm
  have hApd : Pairwise fun m n => Disjoint (disjointed B m) (disjointed B n) :=
    disjoint_disjointed B
  -- each disjointified annulus is far from `r`, so carries none of `x`
  have hzero : ∀ n, (PVM_of_selfAdjoint T ha).E (disjointed B n) x = 0 := by
    intro n
    refine E_far_of_eigenvector T ha hTx (hAm n) (ε := 1 / (n + 1 : ℝ)) (by positivity) ?_
    intro ω hω
    exact disjointed_subset B n hω
  -- σ-additivity over the disjointified annuli
  have hsum := (PVM_of_selfAdjoint T ha).hasSum_iUnion hAm hApd x
  have hU : (⋃ n, disjointed B n) = s₀ᶜ := by
    rw [iUnion_disjointed]
    ext ω
    simp only [Set.mem_iUnion, Set.mem_compl_iff, hs₀def, Set.mem_preimage,
      Set.mem_singleton_iff, hBdef, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩ heq
      rw [heq, sub_self, abs_zero] at hn
      have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    · intro hne
      have hpos : 0 < |(ω : ℝ) - r| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, hn.le⟩
  rw [hU] at hsum
  -- the complement of the atom carries none of `x`
  have hcompl0 : (PVM_of_selfAdjoint T ha).E s₀ᶜ x = 0 := by
    have hz : HasSum (fun n : ℕ => (PVM_of_selfAdjoint T ha).E (disjointed B n) x) 0 := by
      have hfe : (fun n : ℕ => (PVM_of_selfAdjoint T ha).E (disjointed B n) x)
          = fun _ => 0 := funext hzero
      rw [hfe]
      exact hasSum_zero
    exact (hz.unique hsum).symm
  -- complementation returns the atom
  have hEc := (PVM_of_selfAdjoint T ha).E_compl_apply hs₀ x
  rw [hcompl0] at hEc
  exact (sub_eq_zero.mp hEc.symm).symm

/-- **CAPSTONE: the bounded Borel functional calculus acts on eigenvectors by
    evaluation.**  For every bounded measurable `f : σ(T) → ℂ` and every
    eigenvector `T x = r • x` (with `r ∈ σ(T)`, e.g. from
    `mem_spectrum_of_eigenvector` when `x ≠ 0`):

        `f(T) x = f(r) • x`.

    Proof: `f · 𝟙_{{r}} = f(r) · 𝟙_{{r}}` pointwise; apply `borelFC`, use
    multiplicativity and the eigenvector atom `E({r}) x = x` on both ends. -/
theorem borelFC_apply_eigenvector (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℂ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C)
    {r : ℝ} (hr : r ∈ spectrum ℝ T) {x : H} (hTx : T x = (r : ℂ) • x) :
    borelFC T ha hf hC0 hC x = f ⟨r, hr⟩ • x := by
  classical
  set s₀ : Set (spectrum ℝ T) := Subtype.val ⁻¹' ({r} : Set ℝ) with hs₀def
  have hs₀ : MeasurableSet s₀ := measurable_subtype_coe (measurableSet_singleton r)
  have hatom : (PVM_of_selfAdjoint T ha).E s₀ x = x := E_eigenvector_atom T ha hTx
  have hindm : Measurable (s₀.indicator (fun _ => (1 : ℂ))) := measurable_const.indicator hs₀
  have hpm : Measurable (fun ω => f ω * s₀.indicator (fun _ => (1 : ℂ)) ω) := hf.mul hindm
  have hpb : ∀ ω, ‖f ω * s₀.indicator (fun _ => (1 : ℂ)) ω‖ ≤ C * 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hC ω) (ProjectionValuedMeasure.norm_indicatorOne_le s₀ ω)
      (norm_nonneg _) hC0
  -- pointwise: `f · 𝟙_{{r}} = f(r) · 𝟙_{{r}}`
  have hkey : (fun ω => f ω * s₀.indicator (fun _ => (1 : ℂ)) ω)
      = fun ω => f ⟨r, hr⟩ * s₀.indicator (fun _ => (1 : ℂ)) ω := by
    funext ω
    by_cases hω : ω ∈ s₀
    · have hωr : ω = ⟨r, hr⟩ := Subtype.ext hω
      rw [hωr]
    · rw [Set.indicator_of_notMem hω, mul_zero, mul_zero]
  have hsm : Measurable (fun ω => f ⟨r, hr⟩ * s₀.indicator (fun _ => (1 : ℂ)) ω) :=
    hindm.const_mul _
  have hsb : ∀ ω, ‖f ⟨r, hr⟩ * s₀.indicator (fun _ => (1 : ℂ)) ω‖
      ≤ ‖f ⟨r, hr⟩‖ * 1 := fun ω => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ProjectionValuedMeasure.norm_indicatorOne_le s₀ ω)
      (norm_nonneg _)
  -- operator identities
  have h1 : borelFC T ha hpm (mul_nonneg hC0 zero_le_one) hpb
      = borelFC T ha hf hC0 hC
        * borelFC T ha hindm zero_le_one (ProjectionValuedMeasure.norm_indicatorOne_le s₀) :=
    borelFC_mul T ha hf hC0 hC hindm zero_le_one
      (ProjectionValuedMeasure.norm_indicatorOne_le s₀)
      hpm (mul_nonneg hC0 zero_le_one) hpb
  have h2 : borelFC T ha hpm (mul_nonneg hC0 zero_le_one) hpb
      = borelFC T ha hsm (mul_nonneg (norm_nonneg _) zero_le_one) hsb :=
    borelFC_congr_fun T ha hpm (mul_nonneg hC0 zero_le_one) hpb hsm
      (mul_nonneg (norm_nonneg _) zero_le_one) hsb hkey
  have h3 : borelFC T ha hsm (mul_nonneg (norm_nonneg _) zero_le_one) hsb
      = f ⟨r, hr⟩ • borelFC T ha hindm zero_le_one
          (ProjectionValuedMeasure.norm_indicatorOne_le s₀) :=
    (PVM_of_selfAdjoint T ha).boundedFC_smul (f ⟨r, hr⟩) hindm zero_le_one
      (ProjectionValuedMeasure.norm_indicatorOne_le s₀)
  have hind : borelFC T ha hindm zero_le_one (ProjectionValuedMeasure.norm_indicatorOne_le s₀)
      = (PVM_of_selfAdjoint T ha).E s₀ := borelFC_indicator T ha hs₀
  calc borelFC T ha hf hC0 hC x
      = borelFC T ha hf hC0 hC ((PVM_of_selfAdjoint T ha).E s₀ x) := by rw [hatom]
    _ = (borelFC T ha hf hC0 hC
          * borelFC T ha hindm zero_le_one
              (ProjectionValuedMeasure.norm_indicatorOne_le s₀)) x := by
        rw [ContinuousLinearMap.mul_apply, hind]
    _ = (f ⟨r, hr⟩ • borelFC T ha hindm zero_le_one
          (ProjectionValuedMeasure.norm_indicatorOne_le s₀)) x := by
        rw [← h1, h2, h3]
    _ = f ⟨r, hr⟩ • ((PVM_of_selfAdjoint T ha).E s₀ x) := by
        rw [ContinuousLinearMap.smul_apply, hind]
    _ = f ⟨r, hr⟩ • x := by rw [hatom]

end QIQTH.SpectralTheorem
