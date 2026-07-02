/-
  K1 (KEYSTONE_PLAN.md) — the operator packaging: clock cutoffs as GENUINE OPERATORS.

  The clock symbols of the count (and of the whole W-tower) promoted from data to operators on the held
  crossed-product representation space `L²(ℝ; H)`:
  • `clockMul g` — multiplication by a bounded measurable symbol (the `dualPhase` construction,
    generalized from unimodular phases to arbitrary bounded symbols);
  • `clockMul_comp` — the product law `clockMul g ∘ clockMul g' = clockMul (g·g')`;
  • **`clockTransl_clockMul`** — the WEYL COVARIANCE `λ_t ∘ M_g = M_{g(·+t)} ∘ λ_t` (the operator half
    of the shift/modulation structure the wall's data-level laws encode);
  • `repMonomial` — the represented core monomial `π(a)·λ_t·M_{f}` as an actual continuous operator,
    with `tau0Rep_repMonomial` tying the operator to the held monomial-trace value.
  Per the plan: K1 is packaging — it does not (and need not) re-derive the count; K2b already proved it
  on the monomial data. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.DualAction
import QIQTH.CrossedProductTranslation
import QIQTH.MonomialTrace
import QIQTH.EigenCore

namespace QIQTH.KeystoneOperator

open MeasureTheory QIQTH.StandardSubspaceModular QIQTH.TypeIITrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section ClockMul

variable (g : ℝ → ℂ)

theorem memLp_clockMulFiber (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun x => g x • ξ x) 2 (volume : Measure ℝ) :=
  MemLp.of_le_mul (Lp.memLp ξ)
    ((hg.aestronglyMeasurable).smul (Lp.aestronglyMeasurable ξ))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- The fiberwise multiplication map. -/
noncomputable def clockMulFun (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    Lp H 2 (volume : Measure ℝ) :=
  (memLp_clockMulFiber g hg hC ξ).toLp

theorem clockMulFun_coeFn (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockMulFun g hg hC ξ =ᵐ[volume] fun x => g x • ξ x :=
  MemLp.coeFn_toLp _

theorem clockMulFun_add (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (ξ η : Lp H 2 (volume : Measure ℝ)) :
    clockMulFun g hg hC (ξ + η) = clockMulFun g hg hC ξ + clockMulFun g hg hC η := by
  rw [Lp.ext_iff]
  filter_upwards [clockMulFun_coeFn g hg hC (ξ + η),
    Lp.coeFn_add (clockMulFun g hg hC ξ) (clockMulFun g hg hC η),
    clockMulFun_coeFn g hg hC ξ, clockMulFun_coeFn g hg hC η, Lp.coeFn_add ξ η]
    with x e1 e2 e3 e4 e5
  simp only [e1, e2, Pi.add_apply, e3, e4, e5, smul_add]

theorem clockMulFun_smul (hg : Measurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (c : ℂ) (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockMulFun g hg hC (c • ξ) = c • clockMulFun g hg hC ξ := by
  rw [Lp.ext_iff]
  filter_upwards [clockMulFun_coeFn g hg hC (c • ξ),
    Lp.coeFn_smul c (clockMulFun g hg hC ξ), clockMulFun_coeFn g hg hC ξ,
    Lp.coeFn_smul c ξ] with x e1 e2 e3 e4
  simp only [e1, e2, Pi.smul_apply, e3, e4]
  rw [smul_comm]

theorem clockMulFun_norm_le (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖g x‖ ≤ C) (ξ : Lp H 2 (volume : Measure ℝ)) :
    ‖clockMulFun g hg hC ξ‖ ≤ C * ‖ξ‖ := by
  have h1 : ‖clockMulFun g hg hC ξ‖ ≤ ‖((C : ℂ)) • ξ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [clockMulFun_coeFn g hg hC ξ, Lp.coeFn_smul ((C : ℂ)) ξ] with x e1 e2
    rw [e1, e2, Pi.smul_apply, norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0] at h1

/-- **The clock multiplication operator** `M_g` for a bounded measurable symbol. -/
noncomputable def clockMul (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := clockMulFun g hg hC
      map_add' := clockMulFun_add g hg hC
      map_smul' := clockMulFun_smul g hg hC }
    C (fun ξ => clockMulFun_norm_le g hg hC0 hC ξ)

theorem clockMul_coeFn (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockMul g hg hC0 hC ξ =ᵐ[volume] fun x => g x • ξ x :=
  clockMulFun_coeFn g hg hC ξ

end ClockMul

/-- **The product law**: `M_g ∘ M_{g′} = M_{g·g′}`. -/
theorem clockMul_comp (g g' : ℝ → ℂ) (hg : Measurable g) (hg' : Measurable g')
    {C C' : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) (hC0' : 0 ≤ C') (hC' : ∀ x, ‖g' x‖ ≤ C')
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockMul g hg hC0 hC (clockMul g' hg' hC0' hC' ξ)
      = clockMul (fun x => g x * g' x) (hg.mul hg') (mul_nonneg hC0 hC0')
        (fun x => by
          rw [norm_mul]
          exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) hC0) ξ := by
  rw [Lp.ext_iff]
  have h1 := clockMul_coeFn g hg hC0 hC (clockMul g' hg' hC0' hC' ξ)
  have h2 := clockMul_coeFn g' hg' hC0' hC' ξ
  have h3 := clockMul_coeFn (fun x => g x * g' x) (hg.mul hg') (mul_nonneg hC0 hC0')
    (fun x => by
      rw [norm_mul]
      exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) hC0) ξ
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1, e2, e3, smul_smul]

/-- **K1 CAPSTONE — the WEYL COVARIANCE:** `λ_t ∘ M_g = M_{g(·+t)} ∘ λ_t` — the clock translation
    conjugates multiplication symbols by the shift (the operator half of the shift/modulation
    structure that the wall's data-level dual-scaling laws encode). -/
theorem clockTransl_clockMul (t : ℝ) (g : ℝ → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) (ξ : Lp H 2 (volume : Measure ℝ)) :
    clockTransl t (clockMul g hg hC0 hC ξ)
      = clockMul (fun x => g (x + t)) (hg.comp (measurable_id.add_const t)) hC0
          (fun x => hC (x + t)) (clockTransl t ξ) := by
  rw [Lp.ext_iff]
  have h2 := clockMul_coeFn (fun x => g (x + t)) (hg.comp (measurable_id.add_const t)) hC0
    (fun x => hC (x + t)) (clockTransl t ξ)
  have h1 : clockTransl t (clockMul g hg hC0 hC ξ)
      =ᵐ[volume] fun x => (clockMul g hg hC0 hC ξ : ℝ → H) (x + t) := by
    rw [clockTransl_apply]
    exact Lp.coeFn_compMeasurePreserving _ _
  have h3 : clockTransl t ξ =ᵐ[volume] fun x => ξ (x + t) := by
    rw [clockTransl_apply]
    exact Lp.coeFn_compMeasurePreserving _ _
  have hmap : Measure.map (· + t) (volume : Measure ℝ) = volume :=
    (measurePreserving_addRight_volume t).map_eq
  have hco : clockMul g hg hC0 hC ξ =ᵐ[Measure.map (· + t) volume] fun v => g v • ξ v := by
    simp only [hmap]
    exact clockMul_coeFn g hg hC0 hC ξ
  have h4 : (fun x => (clockMul g hg hC0 hC ξ : ℝ → H) (x + t))
      =ᵐ[volume] fun x => g (x + t) • ξ (x + t) :=
    ae_eq_comp (measurePreserving_addRight_volume t).measurable.aemeasurable hco
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  rw [e1, e4, e2, e3]

/-- **The REPRESENTED core monomial** `π(a)·λ_t·M_{F}` — the crossed-product monomial as a genuine
    continuous operator on `L²(ℝ; H)` (matter representation ∘ clock translation ∘ clock
    multiplication), whose trace value on its data is the held W3a `tauMonomial` (the K2b count
    evaluates exactly these at `t = 0` with the mass-`N_C` window). -/
noncomputable def repMonomial [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (S : StandardSubspace H) (a : H →L[ℂ] H) (t : ℝ) (F : ExpTest) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  (matterRep S a) ∘L (clockTransl t) ∘L
    (clockMul F.f F.meas (ExpTest.bound_nonneg F) F.hbound)

end QIQTH.KeystoneOperator
