/-
  Phase 1.3 of the Tomita–Takesaki roadmap (TOMITA_TAKESAKI_ROADMAP.md):
  the BOUNDED SPECTRAL THEOREM — constructing a projection-valued measure from a
  bounded self-adjoint operator `T : H →L[ℂ] H` (`PVM_of_selfAdjoint`).

  Now reachable on Mathlib v4.30 (both earlier-feared blockers are absent):
    • `cfc` works on `T` — `CStarAlgebra (H →L[ℂ] H)` is a registered instance
      (`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`);
    • the Riesz–Markov REPRESENTATION theorem exists
      (`MeasureTheory.RealRMK.integral_rieszMeasure`);
    • multiplicativity of the bounded-Borel FC is proved (`Spectral/PVM.lean`,
      `boundedFC_mul`), giving the PVM laws.

  Construction roadmap: scalar measure `μ_x := rieszMeasure (f ↦ re ⟪x, cfc f x⟫)`
  → polarize → `E(B)` via the Riesz form → `ProjectionValuedMeasure` laws → `∫ id dE = T`.

  STATUS (scalar foundation COMPLETE, axiom-free):
    • `re_inner_cfc_nonneg`     — positivity bridge `0 ≤ re ⟪x, f(T) x⟫` for `f ≥ 0`.
    • `specFunctional`/`specPLM`— the positive functional `Λ_x : C_c(σ(T),ℝ) →ₚ[ℝ] ℝ`.
    • `specMeasure` (`μ_x`)     — its Riesz–Markov measure, finite, with
      `integral_specMeasure : ∫ f dμ_x = re ⟪x, f(T) x⟫` and `specMeasure_real_univ`
      (`μ_x(univ) = ‖x‖²`, scalar-level `E(univ)=1`) and `specMeasure_real_le`
      (`μ_x(B) ≤ ‖x‖²`).
    • `inner_cfcHom_polarization` — the off-diagonal complex bridge: `⟪f(T) x, y⟫` is the
      complex-polarized combination of the scalar integrals `∫ f dμ_z`.

  NEXT (the projection `E(B)`): the subtle step is sesquilinearity of `(x,y) ↦ μ_{x,y}(B)`
  for fixed Borel `B`.  Because the `rieszMeasure` content is NONLINEAR in the vector, this
  does NOT follow by polarizing the real measures; it requires UNIQUENESS of the representing
  (complex) measure (`RealRMK.rieszMeasure_integralPositiveLinearMap`): `f ↦ ⟪x, f(T) y⟫` is
  sesquilinear, so the representing complex measures combine sesquilinearly, hence so does
  `μ_{x,y}(B)`.  Then bound (via `specMeasure_real_le`) + `continuousLinearMapOfBilin`
  (`Analysis/InnerProductSpace/Dual.lean`) gives `E(B)`; multiplicativity (`boundedFC_mul`
  in `Spectral/PVM.lean`) gives `E(B)²=E(B)`, and assembly gives `ProjectionValuedMeasure`.

  This file begins with a validation that `cfc` fires on a self-adjoint `B(H)` operator.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Tactic

namespace QIQTH.SpectralTheorem

open scoped ComplexInnerProductSpace CompactlySupported NNReal ENNReal
open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Validation:** the continuous functional calculus fires on a bounded self-adjoint
    operator on a complex Hilbert space — `cfc id T = T`.  (Confirms the `cfc` instance
    resolves via `CStarAlgebra (H →L[ℂ] H)`, the entry point for the spectral theorem.) -/
example (T : H →L[ℂ] H) (_hT : IsSelfAdjoint T) : cfc (id : ℝ → ℝ) T = T := cfc_id ℝ T

/-! ### Scalar spectral measure: the positivity bridge

The scalar spectral measure `μ_x` is the Riesz–Markov measure of the positive linear
functional `Λ_x : C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ`, `f ↦ re ⟪x, f(T) x⟫`.  Positivity of
`Λ_x` is the first ingredient: if `f ≥ 0` on the spectrum, then `f(T) ≥ 0` in the C\*-order
of `B(H)` (by `cfc_nonneg`), hence `re ⟪x, f(T) x⟫ ≥ 0` (since the C\*-order on `B(H)`
coincides with the Loewner / `IsPositive` order). -/

open RCLike in
/-- **Positivity bridge.**  If `f ≥ 0` on the spectrum of `T`, then `re ⟪x, f(T) x⟫ ≥ 0`.
    This is the positivity of the scalar functional `Λ_x f = re ⟪x, cfc f T x⟫`, the seed of
    the scalar spectral measure `μ_x`. -/
theorem re_inner_cfc_nonneg (T : H →L[ℂ] H) (x : H)
    {f : ℝ → ℝ} (hf : ∀ r ∈ spectrum ℝ T, 0 ≤ f r) :
    0 ≤ re ⟪x, cfc f T x⟫ :=
  let hpos : (0 : H →L[ℂ] H) ≤ cfc f T := cfc_nonneg hf
  ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos).re_inner_nonneg_right x

/-! ### The scalar spectral functional `Λ_x` and the scalar spectral measure `μ_x`

For a fixed vector `x`, `Λ_x : C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ`, `f ↦ re ⟪x, f(T) x⟫`, is a
positive linear functional (the `cfcHom` star-algebra hom makes it linear; the positivity
bridge makes it positive).  Its Riesz–Markov measure is the scalar spectral measure `μ_x`,
with defining property `∫ f dμ_x = re ⟪x, f(T) x⟫`. -/

variable (T : H →L[ℂ] H)

open RCLike in
/-- The scalar spectral functional as an ℝ-linear map on compactly-supported continuous
    functions on the spectrum: `f ↦ re ⟪x, f(T) x⟫`, where `f(T) := cfcHom ha f`. -/
noncomputable def specFunctional (ha : IsSelfAdjoint T) (x : H) :
    C_c(spectrum ℝ T, ℝ) →ₗ[ℝ] ℝ where
  toFun f := re ⟪x, cfcHom ha f.toContinuousMap x⟫
  map_add' f g := by
    have h : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := by
      ext a; simp
    rw [h, map_add, ContinuousLinearMap.add_apply, inner_add_right, map_add]
  map_smul' c f := by
    have h : (c • f).toContinuousMap = c • f.toContinuousMap := by
      ext a; simp
    rw [h, map_smul, ContinuousLinearMap.smul_apply, real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_right, smul_re, RingHom.id_apply, smul_eq_mul]

open RCLike in
/-- The scalar spectral functional bundled as a **positive** linear functional
    `Λ_x : C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ`. -/
noncomputable def specPLM (ha : IsSelfAdjoint T) (x : H) :
    C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (specFunctional T ha x) fun f hf0 => by
    have hle : (0 : C(spectrum ℝ T, ℝ)) ≤ f.toContinuousMap := by
      intro a; simpa using CompactlySupportedContinuousMap.le_def.mp hf0 a
    have hpos : (0 : H →L[ℂ] H) ≤ cfcHom ha f.toContinuousMap :=
      (cfcHom_nonneg_iff ha).mpr hle
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hpos).re_inner_nonneg_right x

/-- The **scalar spectral measure** `μ_x` of a self-adjoint `T` at a vector `x`: the
    Riesz–Markov measure of the positive functional `Λ_x = specPLM`. -/
noncomputable def specMeasure (ha : IsSelfAdjoint T) (x : H) :
    MeasureTheory.Measure (spectrum ℝ T) :=
  RealRMK.rieszMeasure (specPLM T ha x)

open RCLike in
/-- **Defining property of the scalar spectral measure** (Riesz–Markov representation):
    `∫ f dμ_x = re ⟪x, f(T) x⟫` for every `f ∈ C_c(spectrum ℝ T, ℝ)`. -/
theorem integral_specMeasure (ha : IsSelfAdjoint T) (x : H) (f : C_c(spectrum ℝ T, ℝ)) :
    ∫ s, f s ∂(specMeasure T ha x) = re ⟪x, cfcHom ha f.toContinuousMap x⟫ :=
  RealRMK.integral_rieszMeasure (specPLM T ha x) f

/-- `μ_x` is a finite measure (the spectrum is compact). -/
instance (ha : IsSelfAdjoint T) (x : H) :
    MeasureTheory.IsFiniteMeasure (specMeasure T ha x) := by
  unfold specMeasure; infer_instance

open RCLike MeasureTheory in
/-- **Total mass of the scalar spectral measure** — the scalar-level `E(univ) = 1`:
    `μ_x(univ) = ‖x‖²` (as a real number), since `1(T) = 1` and `re ⟪x, x⟫ = ‖x‖²`. -/
theorem specMeasure_real_univ (ha : IsSelfAdjoint T) (x : H) :
    (specMeasure T ha x).real Set.univ = ‖x‖ ^ 2 := by
  have key := integral_specMeasure T ha x ⟨1, HasCompactSupport.of_compactSpace 1⟩
  have hint : ∫ s, (⟨1, HasCompactSupport.of_compactSpace 1⟩ : C_c(spectrum ℝ T, ℝ)) s
      ∂(specMeasure T ha x) = (specMeasure T ha x).real Set.univ := by
    simp [integral_const]
  rw [hint] at key
  rw [key, show ((⟨1, HasCompactSupport.of_compactSpace 1⟩ : C_c(spectrum ℝ T, ℝ)).toContinuousMap)
        = (1 : C(spectrum ℝ T, ℝ)) from rfl, map_one, ContinuousLinearMap.one_apply,
      inner_self_eq_norm_sq]

/-! ### Off-diagonal: the complex polarization bridge

The full complex inner product `⟪f(T) x, y⟫` is determined by the (positive, real) scalar
measures `μ_z` via the complex polarization identity: writing `f(T) := cfcHom ha f` (which is
self-adjoint, as `f` is real-valued), each diagonal term `⟪f(T) z, z⟫` is real and equals
`∫ f dμ_z`.  This is the bridge that lets the projection `E(B)` be defined from the scalar
measures: replacing `∫ f dμ_z` by `μ_z(B)` gives the sesquilinear form `⟪E(B) x, y⟫`. -/

open RCLike MeasureTheory in
/-- **Complex polarization bridge.**  For real `f`, the off-diagonal `⟪f(T) x, y⟫` is the
    complex-polarized combination of the diagonal scalar integrals `∫ f dμ_z`. -/
theorem inner_cfcHom_polarization (ha : IsSelfAdjoint T) (f : C_c(spectrum ℝ T, ℝ)) (x y : H) :
    ⟪cfcHom ha f.toContinuousMap x, y⟫
      = ((↑(∫ s, f s ∂(specMeasure T ha (x + y))) : ℂ)
          - (↑(∫ s, f s ∂(specMeasure T ha (x - y))) : ℂ)
          - Complex.I * (↑(∫ s, f s ∂(specMeasure T ha (x + Complex.I • y))) : ℂ)
          + Complex.I * (↑(∫ s, f s ∂(specMeasure T ha (x - Complex.I • y))) : ℂ)) / 4 := by
  -- `f(T)` is self-adjoint (f is real-valued, so `star f = f`).
  have hSA : IsSelfAdjoint (cfcHom ha f.toContinuousMap) := by
    rw [isSelfAdjoint_iff, ← map_star, star_trivial]
  have hsym : LinearMap.IsSymmetric ((cfcHom ha f.toContinuousMap : H →L[ℂ] H) : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSA
  -- Each diagonal term `⟪f(T) z, z⟫` is real and equals `∫ f dμ_z`.
  have diag : ∀ z : H, ⟪cfcHom ha f.toContinuousMap z, z⟫
      = ((∫ s, f s ∂(specMeasure T ha z) : ℝ) : ℂ) := fun z => by
    rw [integral_specMeasure, inner_re_symm, ← ContinuousLinearMap.reApplyInnerSelf_apply]
    exact (hsym.coe_reApplyInnerSelf_apply z).symm
  have hpol := inner_map_polarization'
    ((cfcHom ha f.toContinuousMap : H →L[ℂ] H) : H →ₗ[ℂ] H) x y
  simp only [ContinuousLinearMap.coe_coe] at hpol
  rw [hpol, diag, diag, diag, diag]

/-- **Per-set bound** for the scalar spectral measure: `μ_z(B) ≤ ‖z‖²` for every set `B`
    (monotonicity against the total mass `μ_z(univ) = ‖z‖²`).  This feeds the operator-norm
    bound on the spectral projections `E(B)`. -/
theorem specMeasure_real_le (ha : IsSelfAdjoint T) (z : H) (B : Set (spectrum ℝ T)) :
    (specMeasure T ha z).real B ≤ ‖z‖ ^ 2 := by
  rw [← specMeasure_real_univ T ha z]
  exact MeasureTheory.measureReal_mono (Set.subset_univ B)

/-! ### Polarized-measure layer (toward the spectral projection `E(B)`)

The scalar measures are determined by their `C_c`-integrals (`μ` is regular, being finite on a
compact metric space), so algebraic identities for the quadratic form `z ↦ re ⟪z, f(T) z⟫`
transport to identities between the *positive* measures `μ_z` via Riesz–Markov uniqueness
(`Measure.ext_of_integral_eq_on_compactlySupported`).  These are the load-bearing identities
that make the polarized form `(x,y) ↦ μ_{x,y}(B)` sesquilinear — bypassing the need for any
complex-measure API. -/

open RCLike MeasureTheory in
/-- **Scaling law** of the scalar spectral measure: `μ_{c•x} = ‖c‖² · μ_x`. -/
theorem specMeasure_smul (ha : IsSelfAdjoint T) (c : ℂ) (x : H) :
    specMeasure T ha (c • x) = (‖c‖₊ ^ 2 : ℝ≥0∞) • specMeasure T ha x := by
  haveI : IsFiniteMeasure ((‖c‖₊ ^ 2 : ℝ≥0∞) • specMeasure T ha x) :=
    Measure.smul_finite _ (by simp)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_specMeasure, integral_smul_measure, integral_specMeasure, smul_eq_mul,
    map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  congr 1

open RCLike MeasureTheory in
/-- **Parallelogram law** of the scalar spectral measure:
    `μ_{x+y} + μ_{x−y} = 2·μ_x + 2·μ_y` (the cross terms of the quadratic form cancel).
    Holds for any operator; the engine for sesquilinearity of the polarized form. -/
theorem specMeasure_parallelogram (ha : IsSelfAdjoint T) (x y : H) :
    specMeasure T ha (x + y) + specMeasure T ha (x - y)
      = (2 : ℝ≥0∞) • specMeasure T ha x + (2 : ℝ≥0∞) • specMeasure T ha y := by
  haveI : IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha x) := Measure.smul_finite _ (by simp)
  haveI : IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha y) := Measure.smul_finite _ (by simp)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_smul_measure, integral_smul_measure,
      integral_specMeasure, integral_specMeasure, integral_specMeasure, integral_specMeasure]
  simp only [ENNReal.toReal_ofNat, smul_eq_mul, map_add, map_sub, inner_add_left,
    inner_add_right, inner_sub_left, inner_sub_right]
  ring

open RCLike MeasureTheory in
/-- **Additivity engine** (measure level): the second-difference identity
    `μ_{x+a+b} + μ_{x−a} + μ_{x−b} = μ_{x−a−b} + μ_{x+a} + μ_{x+b}` (both sides expand to
    `3q(x)+2q(a)+2q(b)+g(a,b)` for the quadratic form `q` and its symmetric bilinear part `g`).
    Applied with `(a,b)=(y₁,y₂)` and `(a,b)=(I·y₁, I·y₂)` it yields additivity of the polarized
    spectral form in `y`. -/
theorem specMeasure_add (ha : IsSelfAdjoint T) (x a b : H) :
    specMeasure T ha (x + a + b) + specMeasure T ha (x - a) + specMeasure T ha (x - b)
      = specMeasure T ha (x - a - b) + specMeasure T ha (x + a) + specMeasure T ha (x + b) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_specMeasure, integral_specMeasure, integral_specMeasure,
      integral_specMeasure, integral_specMeasure, integral_specMeasure]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-! ### The diagonal quadratic form `q_s` and the polarized bilinear form `b_s`

`q_s(z) := μ_z(s)` is a nonnegative real quadratic form; `b_s(u,v) := ¼(q_s(u+v) − q_s(u−v))`
is its (symmetric, biadditive) polarization, with `b_s(u,u) = q_s(u)`.  Because `q_s ≥ 0`, the
form satisfies Cauchy–Schwarz, which delivers boundedness, continuity, and hence ℝ-linearity. -/

/-- The diagonal quadratic form `q_s(z) = μ_z(s)` (real, nonnegative). -/
noncomputable def qForm (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (z : H) : ℝ :=
  (specMeasure T ha z).real s

lemma qForm_nonneg (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (z : H) :
    0 ≤ qForm T ha s z := MeasureTheory.measureReal_nonneg

/-- `μ_0 = 0` (the zero vector gives the zero measure). -/
lemma specMeasure_zero (ha : IsSelfAdjoint T) : specMeasure T ha 0 = 0 := by
  have h := specMeasure_smul T ha 0 0
  simpa using h

lemma qForm_zero (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) :
    qForm T ha s 0 = 0 := by
  rw [qForm, specMeasure_zero]; rfl

lemma qForm_smul (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (c : ℂ) (z : H) :
    qForm T ha s (c • z) = ‖c‖ ^ 2 * qForm T ha s z := by
  rw [qForm, specMeasure_smul, MeasureTheory.measureReal_ennreal_smul_apply, qForm]
  congr 1

lemma qForm_neg (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (z : H) :
    qForm T ha s (-z) = qForm T ha s z := by
  have h := qForm_smul T ha s (-1) z
  simpa using h

lemma qForm_parallelogram (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    qForm T ha s (x + y) + qForm T ha s (x - y)
      = 2 * qForm T ha s x + 2 * qForm T ha s y := by
  haveI : MeasureTheory.IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha x) :=
    MeasureTheory.Measure.smul_finite _ (by simp)
  haveI : MeasureTheory.IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha y) :=
    MeasureTheory.Measure.smul_finite _ (by simp)
  unfold qForm
  rw [← MeasureTheory.measureReal_add_apply, specMeasure_parallelogram,
    MeasureTheory.measureReal_add_apply, MeasureTheory.measureReal_ennreal_smul_apply,
    MeasureTheory.measureReal_ennreal_smul_apply, ENNReal.toReal_ofNat]

lemma qForm_add (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x a b : H) :
    qForm T ha s (x + a + b) + qForm T ha s (x - a) + qForm T ha s (x - b)
      = qForm T ha s (x - a - b) + qForm T ha s (x + a) + qForm T ha s (x + b) := by
  unfold qForm
  rw [← MeasureTheory.measureReal_add_apply, ← MeasureTheory.measureReal_add_apply,
    specMeasure_add, MeasureTheory.measureReal_add_apply, MeasureTheory.measureReal_add_apply]

/-- The polarized bilinear form `b_s(u,v) = ¼(q_s(u+v) − q_s(u−v))`. -/
noncomputable def bForm (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) : ℝ :=
  (qForm T ha s (u + v) - qForm T ha s (u - v)) / 4

/-- Expansion identity: `q_s(p+q) = q_s(p) + q_s(q) + 2 b_s(p,q)` (from the parallelogram law). -/
lemma qForm_add_expand (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (p q : H) :
    qForm T ha s (p + q) = qForm T ha s p + qForm T ha s q + 2 * bForm T ha s p q := by
  unfold bForm
  have hpar := qForm_parallelogram T ha s p q
  linarith

/-- `b_s(u,u) = q_s(u)`. -/
lemma bForm_self (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u : H) :
    bForm T ha s u u = qForm T ha s u := by
  unfold bForm
  rw [sub_self, qForm_zero, show u + u = (2 : ℂ) • u by rw [two_smul], qForm_smul]
  simp
  ring

/-- `b_s` is symmetric. -/
lemma bForm_comm (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) :
    bForm T ha s u v = bForm T ha s v u := by
  unfold bForm
  rw [add_comm u v, show u - v = -(v - u) by abel, qForm_neg]

/-- `b_s` is additive in its right argument. -/
lemma bForm_add_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v w : H) :
    bForm T ha s u (v + w) = bForm T ha s u v + bForm T ha s u w := by
  have h := qForm_add T ha s u v w
  unfold bForm
  rw [show u + (v + w) = u + v + w by abel, show u - (v + w) = u - v - w by abel]
  linarith

/-- `b_s` is additive in its left argument. -/
lemma bForm_add_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v w : H) :
    bForm T ha s (u + v) w = bForm T ha s u w + bForm T ha s v w := by
  rw [bForm_comm, bForm_add_right, bForm_comm T ha s w u, bForm_comm T ha s w v]

/-- Real-scalar version of the scaling law: `q_s(r•z) = r²·q_s(z)`. -/
lemma qForm_real_smul (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (r : ℝ) (z : H) :
    qForm T ha s (r • z) = r ^ 2 * qForm T ha s z := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), qForm_smul, RCLike.norm_ofReal, sq_abs]

lemma bForm_zero_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u : H) :
    bForm T ha s u 0 = 0 := by
  unfold bForm; simp

/-- `b_s(u, ·)` bundled as an additive homomorphism (used for ℚ-homogeneity in Cauchy–Schwarz). -/
noncomputable def bFormRight (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u : H) : H →+ ℝ where
  toFun w := bForm T ha s u w
  map_zero' := bForm_zero_right T ha s u
  map_add' := bForm_add_right T ha s u

/-- **Cauchy–Schwarz** for the spectral form: `b_s(u,v)² ≤ q_s(u)·q_s(v)`.
    Because `q_s ≥ 0`, the quadratic `t ↦ q_s(u + t•v) = q_s(v)·t² + 2 b_s(u,v)·t + q_s(u)` is
    nonnegative on `ℚ` (hence on `ℝ` by density), so its discriminant is `≤ 0`. -/
lemma bForm_sq_le (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) :
    bForm T ha s u v ^ 2 ≤ qForm T ha s u * qForm T ha s v := by
  -- ℚ-homogeneity of `b_s(u, ·)`
  have hq : ∀ q : ℚ, bForm T ha s u ((q : ℝ) • v) = (q : ℝ) * bForm T ha s u v := by
    intro q
    have h := map_ratCast_smul (bFormRight T ha s u) ℝ ℝ q v
    simpa [bFormRight, smul_eq_mul] using h
  -- nonnegativity of the quadratic at rational points
  have hpoly : ∀ q : ℚ,
      0 ≤ qForm T ha s v * ((q : ℝ) * (q : ℝ)) + 2 * bForm T ha s u v * (q : ℝ)
        + qForm T ha s u := by
    intro q
    have hexp := qForm_add_expand T ha s u ((q : ℝ) • v)
    rw [hq q, qForm_real_smul] at hexp
    have hnn := qForm_nonneg T ha s (u + (q : ℝ) • v)
    rw [hexp] at hnn
    nlinarith [hnn]
  -- extend to all reals by density of ℚ
  have hreal : ∀ t : ℝ,
      0 ≤ qForm T ha s v * (t * t) + 2 * bForm T ha s u v * t + qForm T ha s u := by
    intro t
    refine Rat.denseRange_cast.induction_on t ?_ hpoly
    exact isClosed_le continuous_const (by fun_prop)
  -- discriminant ≤ 0
  have hd := discrim_le_zero (a := qForm T ha s v) (b := 2 * bForm T ha s u v)
    (c := qForm T ha s u) (fun x => by nlinarith [hreal x])
  unfold discrim at hd
  nlinarith [hd]

/-- `b_s` is subtractive in its right argument. -/
lemma bForm_sub_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v w : H) :
    bForm T ha s u (v - w) = bForm T ha s u v - bForm T ha s u w := by
  have h : bForm T ha s u v = bForm T ha s u (v - w) + bForm T ha s u w := by
    rw [← bForm_add_right, sub_add_cancel]
  linarith

/-- **Boundedness** of the spectral form: `|b_s(u,v)| ≤ ‖u‖·‖v‖` (from Cauchy–Schwarz and
    `q_s(z) ≤ ‖z‖²`). -/
lemma bForm_abs_le (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) :
    |bForm T ha s u v| ≤ ‖u‖ * ‖v‖ := by
  have hcs := bForm_sq_le T ha s u v
  have hu : qForm T ha s u ≤ ‖u‖ ^ 2 := specMeasure_real_le T ha u s
  have hv : qForm T ha s v ≤ ‖v‖ ^ 2 := specMeasure_real_le T ha v s
  have h2 : bForm T ha s u v ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [hcs, hu, hv, qForm_nonneg T ha s u, qForm_nonneg T ha s v,
      norm_nonneg u, norm_nonneg v]
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt (bForm T ha s u v ^ 2) ≤ Real.sqrt ((‖u‖ * ‖v‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖u‖ * ‖v‖ := Real.sqrt_sq (by positivity)

/-- `b_s(u, ·)` is continuous (Lipschitz with constant `‖u‖`). -/
lemma bForm_continuous_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u : H) :
    Continuous (fun v => bForm T ha s u v) := by
  refine LipschitzWith.continuous (K := ‖u‖₊) (LipschitzWith.of_dist_le_mul fun v w => ?_)
  rw [Real.dist_eq, ← bForm_sub_right]
  refine (bForm_abs_le T ha s u (v - w)).trans ?_
  rw [coe_nnnorm, dist_eq_norm]

/-- **ℝ-homogeneity** of `b_s(u, ·)` (continuity + `map_real_smul`). -/
lemma bForm_real_smul_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u : H)
    (r : ℝ) (v : H) : bForm T ha s u (r • v) = r * bForm T ha s u v := by
  have h := map_real_smul (bFormRight T ha s u) (bForm_continuous_right T ha s u) r v
  simpa [bFormRight, smul_eq_mul] using h

lemma bForm_neg_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) :
    bForm T ha s u (-v) = - bForm T ha s u v := by
  have h := bForm_real_smul_right T ha s u (-1) v
  simpa using h

/-- `b_s` is invariant under simultaneous multiplication by `i`: `b_s(I•u, I•v) = b_s(u,v)`
    (from the `i`-invariance `q_s(I•z) = q_s(z)`). -/
lemma bForm_I_smul (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u v : H) :
    bForm T ha s (Complex.I • u) (Complex.I • v) = bForm T ha s u v := by
  unfold bForm
  rw [← smul_add, ← smul_sub, qForm_smul, qForm_smul, Complex.norm_I]
  ring

/-- The `i`-twist: `b_s(I•x, y) = − b_s(x, I•y)`. -/
lemma bForm_I_comm (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    bForm T ha s (Complex.I • x) y = - bForm T ha s x (Complex.I • y) := by
  have key := bForm_I_smul T ha s x (-(Complex.I • y))
  rw [show Complex.I • (-(Complex.I • y)) = y by
        rw [smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg],
      bForm_neg_right] at key
  exact key

/-- The complex spectral form `c_s(x,y) = b_s(x,y) − i·b_s(x, I•y)`; its Riesz representation
    will be the spectral projection `E(s)`, with `⟪E(s) x, y⟫ = c_s(x,y)`. -/
noncomputable def cForm (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) : ℂ :=
  (bForm T ha s x y : ℂ) - Complex.I * (bForm T ha s x (Complex.I • y) : ℂ)

lemma cForm_add_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y z : H) :
    cForm T ha s x (y + z) = cForm T ha s x y + cForm T ha s x z := by
  unfold cForm
  rw [bForm_add_right, smul_add, bForm_add_right]
  push_cast
  ring

lemma cForm_real_smul_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) (r : ℝ)
    (y : H) : cForm T ha s x (r • y) = (r : ℂ) * cForm T ha s x y := by
  unfold cForm
  rw [bForm_real_smul_right, show Complex.I • (r • y) = r • (Complex.I • y) by
        rw [smul_comm], bForm_real_smul_right]
  push_cast
  ring

/-- The `i`-twist for the complex form: `c_s(x, I•y) = i·c_s(x,y)`. -/
lemma cForm_I_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    cForm T ha s x (Complex.I • y) = Complex.I * cForm T ha s x y := by
  unfold cForm
  rw [show Complex.I • (Complex.I • y) = -y by
        rw [smul_smul, Complex.I_mul_I, neg_one_smul], bForm_neg_right]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **ℂ-homogeneity** of `c_s(x, ·)`: `c_s(x, c•y) = c·c_s(x,y)` (combine ℝ-homogeneity, the
    i-twist, and additivity, decomposing `c = c.re + c.im·i`). -/
lemma cForm_smul_right (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) (c : ℂ) (y : H) :
    cForm T ha s x (c • y) = c * cForm T ha s x y := by
  have h0 : ((c.re : ℝ) : ℂ) • y + ((c.im : ℝ) : ℂ) • (Complex.I • y) = c • y := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  have hc : (c.re : ℝ) • y + (c.im : ℝ) • (Complex.I • y) = c • y := by
    rw [← h0]; congr 1 <;> exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  rw [← hc, cForm_add_right, cForm_real_smul_right, cForm_real_smul_right, cForm_I_right]
  conv_rhs => rw [← Complex.re_add_im c]
  push_cast
  ring

/-- ℝ-homogeneity in the left argument: `b_s(r•u, v) = r·b_s(u,v)`. -/
lemma bForm_real_smul_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (r : ℝ) (u v : H) :
    bForm T ha s (r • u) v = r * bForm T ha s u v := by
  rw [bForm_comm, bForm_real_smul_right, bForm_comm T ha s v u]

/-- `c_s` is additive in its left argument. -/
lemma cForm_add_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x x' y : H) :
    cForm T ha s (x + x') y = cForm T ha s x y + cForm T ha s x' y := by
  unfold cForm
  rw [bForm_add_left, bForm_add_left]
  push_cast
  ring

/-- ℝ-homogeneity of `c_s` in the left argument. -/
lemma cForm_real_smul_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (r : ℝ) (x y : H) :
    cForm T ha s (r • x) y = (r : ℂ) * cForm T ha s x y := by
  unfold cForm
  rw [bForm_real_smul_left, bForm_real_smul_left]
  push_cast
  ring

/-- The `i`-twist in the left argument: `c_s(I•x, y) = conj(i)·c_s(x,y) = −i·c_s(x,y)`. -/
lemma cForm_I_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    cForm T ha s (Complex.I • x) y = -Complex.I * cForm T ha s x y := by
  unfold cForm
  rw [bForm_I_comm, bForm_I_smul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Conjugate-linearity** of `c_s` in the left argument: `c_s(c•x, y) = conj(c)·c_s(x,y)`. -/
lemma cForm_conj_smul_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (c : ℂ) (x y : H) :
    cForm T ha s (c • x) y = (starRingEnd ℂ) c * cForm T ha s x y := by
  have h0 : ((c.re : ℝ) : ℂ) • x + ((c.im : ℝ) : ℂ) • (Complex.I • x) = c • x := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  have hc : (c.re : ℝ) • x + (c.im : ℝ) • (Complex.I • x) = c • x := by
    rw [← h0]; congr 1 <;> exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm
  rw [← hc, cForm_add_left, cForm_real_smul_left, cForm_real_smul_left, cForm_I_left]
  conv_rhs => rw [← Complex.re_add_im ((starRingEnd ℂ) c), Complex.conj_re, Complex.conj_im]
  push_cast
  ring

/-- **Norm bound**: `‖c_s(x,y)‖ ≤ 2·‖x‖·‖y‖`. -/
lemma cForm_norm_le (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    ‖cForm T ha s x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
  unfold cForm
  have hb1 : ‖((bForm T ha s x y : ℝ) : ℂ)‖ ≤ ‖x‖ * ‖y‖ := by
    rw [Complex.norm_real]; exact bForm_abs_le T ha s x y
  have hb2 : ‖Complex.I * ((bForm T ha s x (Complex.I • y) : ℝ) : ℂ)‖ ≤ ‖x‖ * ‖y‖ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
    refine (bForm_abs_le T ha s x (Complex.I • y)).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
  calc ‖((bForm T ha s x y : ℝ) : ℂ) - Complex.I * ((bForm T ha s x (Complex.I • y) : ℝ) : ℂ)‖
      ≤ ‖((bForm T ha s x y : ℝ) : ℂ)‖ + ‖Complex.I * ((bForm T ha s x (Complex.I • y) : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖x‖ * ‖y‖ := add_le_add hb1 hb2
    _ = 2 * ‖x‖ * ‖y‖ := by ring

/-- `c_s(x, ·)` bundled as a continuous ℂ-linear functional `H →L[ℂ] ℂ`. -/
noncomputable def cFormCLM (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun y => cForm T ha s x y
      map_add' := cForm_add_right T ha s x
      map_smul' := fun c y => by
        simp only [RingHom.id_apply, smul_eq_mul]; exact cForm_smul_right T ha s x c y }
    (2 * ‖x‖) (fun y => cForm_norm_le T ha s x y)

@[simp] lemma cFormCLM_apply (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    cFormCLM T ha s x y = cForm T ha s x y := rfl

lemma cFormCLM_norm_le (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) :
    ‖cFormCLM T ha s x‖ ≤ 2 * ‖x‖ := by
  unfold cFormCLM
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The **spectral projection** `E(s) : H →L[ℂ] H`, obtained by Riesz-representing the bounded
    sesquilinear form `c_s` (`⟪E(s) x, y⟫ = c_s(x,y)`). -/
noncomputable def specProj (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin
    (LinearMap.mkContinuous
      ({ toFun := fun x => cFormCLM T ha s x
         map_add' := fun x x' => by
           ext y
           simp only [ContinuousLinearMap.add_apply, cFormCLM_apply]
           exact cForm_add_left T ha s x x' y
         map_smul' := fun c x => by
           ext y
           simp only [ContinuousLinearMap.smul_apply, cFormCLM_apply, smul_eq_mul]
           exact cForm_conj_smul_left T ha s c x y } :
        H →ₛₗ[starRingEnd ℂ] (H →L[ℂ] ℂ))
      2 (fun x => cFormCLM_norm_le T ha s x))

/-- **Defining identity of the spectral projection**: `⟪E(s) x, y⟫ = c_s(x,y)`. -/
lemma inner_specProj (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    ⟪specProj T ha s x, y⟫ = cForm T ha s x y := by
  rw [specProj, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- `c_∅ = 0`. -/
lemma cForm_empty (ha : IsSelfAdjoint T) (x y : H) : cForm T ha ∅ x y = 0 := by
  unfold cForm bForm qForm
  simp

/-- `E(∅) = 0`. -/
lemma specProj_empty (ha : IsSelfAdjoint T) : specProj T ha ∅ = 0 := by
  ext x
  rw [ContinuousLinearMap.zero_apply, ← inner_self_eq_zero (𝕜 := ℂ), inner_specProj, cForm_empty]

/-- **Hermitian symmetry** of the form: `conj(c_s(y,x)) = c_s(x,y)`. -/
lemma cForm_hermitian (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x y : H) :
    (starRingEnd ℂ) (cForm T ha s y x) = cForm T ha s x y := by
  unfold cForm
  simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [bForm_comm T ha s y x, bForm_comm T ha s y (Complex.I • x), bForm_I_comm]
  push_cast
  ring

/-- `E(s)` is self-adjoint. -/
lemma specProj_isSelfAdjoint (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) :
    IsSelfAdjoint (specProj T ha s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_specProj, ← inner_conj_symm, inner_specProj, cForm_hermitian]

/-- `q_univ(z) = ‖z‖²`. -/
lemma qForm_univ (ha : IsSelfAdjoint T) (z : H) :
    qForm T ha Set.univ z = ‖z‖ ^ 2 := specMeasure_real_univ T ha z

/-- `b_univ(x,y) = re ⟪x,y⟫` (polarization of the norm). -/
lemma bForm_univ (ha : IsSelfAdjoint T) (x y : H) :
    bForm T ha Set.univ x y = RCLike.re (inner ℂ x y) := by
  unfold bForm
  rw [qForm_univ, qForm_univ, @norm_add_sq ℂ, @norm_sub_sq ℂ]
  ring

/-- `c_univ(x,y) = ⟪x,y⟫`. -/
lemma cForm_univ (ha : IsSelfAdjoint T) (x y : H) :
    cForm T ha Set.univ x y = inner ℂ x y := by
  unfold cForm
  rw [bForm_univ, bForm_univ, inner_smul_right,
    show RCLike.re (inner ℂ x y) = (inner ℂ x y).re from rfl,
    show RCLike.re (Complex.I * inner ℂ x y) = (Complex.I * inner ℂ x y).re from rfl,
    Complex.mul_re]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  conv_rhs => rw [← Complex.re_add_im (inner ℂ x y)]
  push_cast
  ring

/-- `E(univ) = 1`. -/
lemma specProj_univ (ha : IsSelfAdjoint T) : specProj T ha Set.univ = 1 := by
  ext x
  refine ext_inner_right ℂ (fun y => ?_)
  rw [inner_specProj, cForm_univ, ContinuousLinearMap.one_apply]

/-- The diagonal of the spectral form is the (real, nonnegative) quadratic form:
    `re ⟪E(s) x, x⟫ = q_s(x)`. -/
lemma reApplyInnerSelf_specProj (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) :
    (specProj T ha s).reApplyInnerSelf x = qForm T ha s x := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_specProj]
  unfold cForm
  rw [bForm_self]
  show (((qForm T ha s x : ℝ) : ℂ) -
    Complex.I * ((bForm T ha s x (Complex.I • x) : ℝ) : ℂ)).re = qForm T ha s x
  simp [Complex.sub_re, Complex.mul_re]

/-- `E(s)` is a positive operator. -/
lemma specProj_isPositive (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) :
    (specProj T ha s).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨specProj_isSelfAdjoint T ha s, fun x => ?_⟩
  rw [reApplyInnerSelf_specProj]
  exact qForm_nonneg T ha s x

/-- Finite additivity of the diagonal form on disjoint sets. -/
lemma qForm_union (ha : IsSelfAdjoint T) {s t : Set (spectrum ℝ T)} (hd : Disjoint s t)
    (hmt : MeasurableSet t) (z : H) :
    qForm T ha (s ∪ t) z = qForm T ha s z + qForm T ha t z :=
  MeasureTheory.measureReal_union hd hmt

/-- Finite additivity of the complex form on disjoint sets. -/
lemma cForm_union_disjoint (ha : IsSelfAdjoint T) {s t : Set (spectrum ℝ T)} (hd : Disjoint s t)
    (hmt : MeasurableSet t) (x y : H) :
    cForm T ha (s ∪ t) x y = cForm T ha s x y + cForm T ha t x y := by
  unfold cForm bForm
  rw [qForm_union T ha hd hmt, qForm_union T ha hd hmt, qForm_union T ha hd hmt,
    qForm_union T ha hd hmt]
  push_cast
  ring

/-- **Finite additivity** of the spectral projection on disjoint measurable sets:
    `E(s ∪ t) = E(s) + E(t)`. -/
lemma specProj_union_disjoint (ha : IsSelfAdjoint T) {s t : Set (spectrum ℝ T)} (hd : Disjoint s t)
    (hmt : MeasurableSet t) :
    specProj T ha (s ∪ t) = specProj T ha s + specProj T ha t := by
  ext x
  refine ext_inner_right ℂ (fun y => ?_)
  rw [inner_specProj, cForm_union_disjoint T ha hd hmt, ContinuousLinearMap.add_apply,
    inner_add_left, inner_specProj, inner_specProj]

/-- `E(s) ≤ 1` (the spectral projection is a contraction in the Loewner order): `1 − E(s)` is
    positive since `re ⟪(1−E(s)) x, x⟫ = ‖x‖² − q_s(x) ≥ 0`. -/
lemma specProj_le_one (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) :
    specProj T ha s ≤ 1 := by
  rw [ContinuousLinearMap.le_def]
  have hsa : IsSelfAdjoint (1 - specProj T ha s) := by
    show star (1 - specProj T ha s) = _
    rw [star_sub, star_one, (specProj_isSelfAdjoint T ha s).star_eq]
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsa, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, map_sub,
    ← ContinuousLinearMap.reApplyInnerSelf_apply, reApplyInnerSelf_specProj,
    inner_self_eq_norm_sq]
  have hle : qForm T ha s x ≤ ‖x‖ ^ 2 := specMeasure_real_le T ha x s
  linarith

/-- **Effect estimate**: for the positive contraction `E(s)`, `‖E(s) x‖² ≤ q_s(x)`.
    (From `E(s)² ≤ E(s)`, i.e. `E(s)·(1−E(s)) ≥ 0` for commuting positives.) -/
lemma norm_specProj_sq_le (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (x : H) :
    ‖specProj T ha s x‖ ^ 2 ≤ qForm T ha s x := by
  set A := specProj T ha s with hA
  have hpos : (0 : H →L[ℂ] H) ≤ A :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (specProj_isPositive T ha s)
  have h1mA : (0 : H →L[ℂ] H) ≤ 1 - A := by
    rw [sub_nonneg]; exact specProj_le_one T ha s
  have hcomm : Commute A (1 - A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hAsq : (0 : H →L[ℂ] H) ≤ A - A * A := by
    have h := Commute.mul_nonneg hpos h1mA hcomm
    rwa [mul_sub, mul_one] at h
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (specProj_isSelfAdjoint T ha s)
  have key := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hAsq).2 x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.sub_apply,
    inner_sub_left, map_sub] at key
  have hAA : RCLike.re ⟪(A * A) x, x⟫ = ‖A x‖ ^ 2 := by
    rw [ContinuousLinearMap.mul_apply, show (⟪A (A x), x⟫ : ℂ) = ⟪A x, A x⟫ from hsym (A x) x,
      inner_self_eq_norm_sq]
  rw [hAA, ← ContinuousLinearMap.reApplyInnerSelf_apply, reApplyInnerSelf_specProj] at key
  linarith

/-- Finite (`Finset`) additivity of the spectral projection over pairwise-disjoint measurable
    sets: `∑ n ∈ F, E(A n) = E(⋃ n ∈ F, A n)`. -/
lemma specProj_finset_sum (ha : IsSelfAdjoint T) {A : ℕ → Set (spectrum ℝ T)}
    (hm : ∀ n, MeasurableSet (A n)) (hd : Pairwise (fun m n => Disjoint (A m) (A n)))
    (F : Finset ℕ) :
    ∑ n ∈ F, specProj T ha (A n) = specProj T ha (⋃ n ∈ F, A n) := by
  induction F using Finset.induction with
  | empty => simp [specProj_empty]
  | @insert a F haF ih =>
    have hdisj : Disjoint (A a) (⋃ n ∈ F, A n) := by
      simp only [Set.disjoint_iUnion_right]
      exact fun n hn => hd (fun h => haF (h ▸ hn))
    have hmu : MeasurableSet (⋃ n ∈ F, A n) :=
      MeasurableSet.biUnion F.countable_toSet (fun n _ => hm n)
    rw [Finset.sum_insert haF, ih, Finset.set_biUnion_insert,
      specProj_union_disjoint T ha hdisj hmu]

/-- **σ-additivity** of the spectral projection (strong/SOT): for pairwise-disjoint measurable
    `A`, `HasSum (fun n => E(A n) x) (E(⋃ n, A n) x)`.  Proved by a norm-tail estimate:
    `‖∑_{n∈s} E(A n) x − E(⋃A) x‖² ≤ q_{(⋃A)∖(⋃_s)}(x) = q_{⋃A}(x) − ∑_{n∈s} q_{A n}(x) → 0`
    (effect estimate + scalar measure σ-additivity). -/
lemma specProj_hasSum (ha : IsSelfAdjoint T) {A : ℕ → Set (spectrum ℝ T)}
    (hm : ∀ n, MeasurableSet (A n)) (hd : Pairwise (fun m n => Disjoint (A m) (A n))) (x : H) :
    HasSum (fun n => specProj T ha (A n) x) (specProj T ha (⋃ n, A n) x) := by
  set U := ⋃ n, A n with hU
  have hmU : MeasurableSet U := MeasurableSet.iUnion hm
  have hsum_ne : (∑' n, (specMeasure T ha x) (A n)) ≠ ∞ := by
    rw [← MeasureTheory.measure_iUnion (μ := specMeasure T ha x) hd hm]
    exact MeasureTheory.measure_ne_top _ _
  have hval : qForm T ha U x = ∑' n, qForm T ha (A n) x := by
    show ((specMeasure T ha x) U).toReal = _
    rw [MeasureTheory.measure_iUnion (μ := specMeasure T ha x) hd hm,
      ENNReal.tsum_toReal_eq (fun n => MeasureTheory.measure_ne_top _ _)]
    rfl
  have hscalar : HasSum (fun n => qForm T ha (A n) x) (qForm T ha U x) := by
    rw [hval]; exact ENNReal.hasSum_toReal hsum_ne
  have hbound : ∀ s : Finset ℕ,
      ‖(∑ n ∈ s, specProj T ha (A n) x) - specProj T ha U x‖
        ≤ Real.sqrt (qForm T ha U x - ∑ n ∈ s, qForm T ha (A n) x) := by
    intro s
    have hsub : (⋃ n ∈ s, A n) ⊆ U :=
      Set.iUnion_subset fun n => Set.iUnion_subset fun _ => Set.subset_iUnion A n
    have hms : MeasurableSet (⋃ n ∈ s, A n) :=
      MeasurableSet.biUnion s.countable_toSet (fun n _ => hm n)
    have hsumeq : ∑ n ∈ s, specProj T ha (A n) x = specProj T ha (⋃ n ∈ s, A n) x := by
      rw [← ContinuousLinearMap.sum_apply, specProj_finset_sum T ha hm hd s]
    have hUeq : specProj T ha U =
        specProj T ha (⋃ n ∈ s, A n) + specProj T ha (U \ (⋃ n ∈ s, A n)) := by
      rw [← specProj_union_disjoint T ha Set.disjoint_sdiff_right (hmU.diff hms)]
      rw [Set.union_diff_cancel hsub]
    have hdiff : (∑ n ∈ s, specProj T ha (A n) x) - specProj T ha U x
        = - specProj T ha (U \ (⋃ n ∈ s, A n)) x := by
      rw [hsumeq, hUeq]; simp
    have hq : qForm T ha (U \ (⋃ n ∈ s, A n)) x
        = qForm T ha U x - ∑ n ∈ s, qForm T ha (A n) x := by
      unfold qForm
      rw [MeasureTheory.measureReal_diff hsub hms,
        ← MeasureTheory.measureReal_biUnion_finset (fun m _ n _ hmn => hd hmn) (fun n _ => hm n)]
    rw [hdiff, norm_neg, ← hq, ← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (norm_specProj_sq_le T ha (U \ (⋃ n ∈ s, A n)) x)
  have htend0 : Tendsto
      (fun s : Finset ℕ => Real.sqrt (qForm T ha U x - ∑ n ∈ s, qForm T ha (A n) x))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun s : Finset ℕ => qForm T ha U x - ∑ n ∈ s, qForm T ha (A n) x)
        atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := qForm T ha U x)).sub hscalar
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa using this
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  exact squeeze_zero (fun s => norm_nonneg _) hbound htend0

/-! ### Toward `E_inter` (the projection property): the `cfcHom`-multiplicativity engine

`E(s∩t) = E(s)·E(t)` is the remaining `ProjectionValuedMeasure` field — the bounded Borel
functional calculus bridge.  Its non-circular content comes from `cfcHom` being an algebra
homomorphism, transported to indicators via a (weak/dominated-convergence) monotone-class
argument.  The core algebraic mechanism is that `g(T)·h(T)·g(T) = (h·g²)(T)`: -/

/-- **`cfcHom`-conjugation engine**: `⟪g(T) z, h(T) (g(T) z)⟫ = ⟪z, (h·g²)(T) z⟫` for continuous
    real `g, h`.  (Self-adjointness of `g(T)` moves one factor across; `cfcHom`'s multiplicativity
    collapses `g·h·g = h·g²`.)  This is the seed of the bounded-Borel-FC multiplicativity. -/
lemma inner_cfcHom_conj (ha : IsSelfAdjoint T) (g h : C(spectrum ℝ T, ℝ)) (z : H) :
    inner ℂ (cfcHom ha g z) (cfcHom ha h (cfcHom ha g z))
      = inner ℂ z (cfcHom ha (h * g ^ 2) z) := by
  have hsa : IsSelfAdjoint (cfcHom ha g) := by
    rw [isSelfAdjoint_iff, ← map_star, star_trivial]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  rw [show cfcHom ha h (cfcHom ha g z) = cfcHom ha (h * g) z by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul]]
  rw [show (⟪cfcHom ha g z, cfcHom ha (h * g) z⟫ : ℂ)
        = ⟪z, cfcHom ha g (cfcHom ha (h * g) z)⟫ from hsym z _]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul]
  congr 2
  ring

/-! ### The `f`-weighted quadratic form `q_f(z) := ∫ f dμ_z` (toward `Φ(f)`)

To build the bounded Borel functional calculus `Φ(f)` (with `Φ(𝟙_s)=E(s)`, `Φ(continuous)=cfcHom`)
we replace `q_s(z)=μ_z(s)` by `q_f(z)=∫ f dμ_z` for bounded measurable `f`.  The whole `q`-engine
descends from the *measure* identities (`specMeasure_smul/parallelogram/add`), so it transfers by
integrating `f` against them. -/

open MeasureTheory in
/-- The `f`-weighted diagonal quadratic form `q_f(z) := ∫ f dμ_z`. -/
noncomputable def qfForm (ha : IsSelfAdjoint T) (f : spectrum ℝ T → ℝ) (z : H) : ℝ :=
  ∫ ω, f ω ∂(specMeasure T ha z)

open MeasureTheory in
/-- A bounded measurable `f` is integrable against every (finite) scalar spectral measure. -/
lemma qf_integrable (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ ω, |f ω| ≤ M) (μ : Measure (spectrum ℝ T)) [IsFiniteMeasure μ] :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfb ω)

open MeasureTheory in
/-- `q_f` is nonnegative for `f ≥ 0`. -/
lemma qfForm_nonneg (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (z : H) :
    0 ≤ qfForm T ha f z :=
  integral_nonneg hf0

open MeasureTheory in
/-- Scaling law for `q_f`: `q_f(c•z) = ‖c‖²·q_f(z)`. -/
lemma qfForm_smul (ha : IsSelfAdjoint T) (f : spectrum ℝ T → ℝ) (c : ℂ) (z : H) :
    qfForm T ha f (c • z) = ‖c‖ ^ 2 * qfForm T ha f z := by
  unfold qfForm
  rw [specMeasure_smul, integral_smul_measure, smul_eq_mul]
  congr 1

open MeasureTheory in
/-- Parallelogram law for `q_f`. -/
lemma qfForm_parallelogram (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℝ} (hf : Measurable f)
    {M : ℝ} (hfb : ∀ ω, |f ω| ≤ M) (x y : H) :
    qfForm T ha f (x + y) + qfForm T ha f (x - y)
      = 2 * qfForm T ha f x + 2 * qfForm T ha f y := by
  haveI : IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha x) := Measure.smul_finite _ (by simp)
  haveI : IsFiniteMeasure ((2 : ℝ≥0∞) • specMeasure T ha y) := Measure.smul_finite _ (by simp)
  unfold qfForm
  rw [← integral_add_measure (qf_integrable T ha hf hfb _) (qf_integrable T ha hf hfb _),
    specMeasure_parallelogram, integral_add_measure (qf_integrable T ha hf hfb _)
      (qf_integrable T ha hf hfb _), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofNat, smul_eq_mul, smul_eq_mul]

open MeasureTheory in
/-- The additivity engine for `q_f`. -/
lemma qfForm_add (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℝ} (hf : Measurable f) {M : ℝ}
    (hfb : ∀ ω, |f ω| ≤ M) (x a b : H) :
    qfForm T ha f (x + a + b) + qfForm T ha f (x - a) + qfForm T ha f (x - b)
      = qfForm T ha f (x - a - b) + qfForm T ha f (x + a) + qfForm T ha f (x + b) := by
  unfold qfForm
  rw [← integral_add_measure (qf_integrable T ha hf hfb _) (qf_integrable T ha hf hfb _),
    ← integral_add_measure (qf_integrable T ha hf hfb _) (qf_integrable T ha hf hfb _),
    specMeasure_add, integral_add_measure (qf_integrable T ha hf hfb _)
      (qf_integrable T ha hf hfb _), integral_add_measure (qf_integrable T ha hf hfb _)
      (qf_integrable T ha hf hfb _)]

end QIQTH.SpectralTheorem
