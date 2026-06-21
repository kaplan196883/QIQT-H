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

  COMPLETE (Layer 1, axiom-free): the spectral projection `specProj` (`E(s)`) is Riesz-represented
  from the bounded sesquilinear form `c_s` (built via the Cauchy–Schwarz/Jordan–von Neumann
  kernel `bForm_sq_le`), shown to be a σ-additive normalized POVM, then PROJECTION-valued via
  `specProj_inter` (`E(s∩t)=E(s)·E(t)`, the bounded-Borel-FC bridge through `cfcHom`
  multiplicativity + Riesz–Markov uniqueness — no monotone operator convergence needed).
  `PVM_of_selfAdjoint` assembles the `ProjectionValuedMeasure`; `re_inner_T_eq_integral`
  recovers `T = ∫ λ dE(λ)` on the diagonal.  This is the keystone unlocking the bounded Borel
  functional calculus (`Spectral/PVM.lean`), hence `Δ^{it}` and the modular tower.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported
import QIQTH.Spectral.PVM
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

/-- **`cfcHom`-multiplicativity in the inner product**: `⟪g(T)x, h(T)y⟫ = ⟪x, (g·h)(T)y⟫`
    (self-adjointness of `g(T)` + `cfcHom` is an algebra hom).  This is the clean engine for the
    off-diagonal measure identity `ν_{g(T)x,y} = g·ν_{x,y}` that yields `E_inter` directly. -/
lemma inner_cfcHom_mul (ha : IsSelfAdjoint T) (g h : C(spectrum ℝ T, ℝ)) (x y : H) :
    inner ℂ (cfcHom ha g x) (cfcHom ha h y) = inner ℂ x (cfcHom ha (g * h) y) := by
  have hsa : IsSelfAdjoint (cfcHom ha g) := by
    rw [isSelfAdjoint_iff, ← map_star, star_trivial]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  rw [show (⟪cfcHom ha g x, cfcHom ha h y⟫ : ℂ) = ⟪x, cfcHom ha g (cfcHom ha h y)⟫
        from hsym x _, ← ContinuousLinearMap.mul_apply, ← map_mul]

open RCLike MeasureTheory in
/-- Bridge: the scalar-measure integral of a *continuous* `h` is `re ⟪z, h(T) z⟫` (the `C_c`
    version `integral_specMeasure` specialised via `HasCompactSupport.of_compactSpace`). -/
lemma integral_specMeasure_cont (ha : IsSelfAdjoint T) (z : H) (h : C(spectrum ℝ T, ℝ)) :
    ∫ ω, h ω ∂(specMeasure T ha z) = re ⟪z, cfcHom ha h z⟫ := by
  have hk := integral_specMeasure T ha z ⟨h, HasCompactSupport.of_compactSpace h⟩
  simpa using hk

open RCLike MeasureTheory in
/-- **Off-diagonal engine** (integral form): for continuous `g, h` and any vectors `x, v`,
    `(∫h dμ_{g(T)x+v} − ∫h dμ_{g(T)x−v}) = (∫(h·g) dμ_{x+v} − ∫(h·g) dμ_{x−v})`.
    Both sides equal `4·re⟪x, (h·g)(T) v⟫` (polarization + `inner_cfcHom_mul`). -/
lemma specMeasure_engine (ha : IsSelfAdjoint T) (g h : C(spectrum ℝ T, ℝ)) (x v : H) :
    (∫ ω, h ω ∂(specMeasure T ha (cfcHom ha g x + v)))
        - (∫ ω, h ω ∂(specMeasure T ha (cfcHom ha g x - v)))
      = (∫ ω, (h * g) ω ∂(specMeasure T ha (x + v)))
        - (∫ ω, (h * g) ω ∂(specMeasure T ha (x - v))) := by
  have key1 : (⟪cfcHom ha g x, cfcHom ha h v⟫ : ℂ) = ⟪x, cfcHom ha (h * g) v⟫ := by
    rw [inner_cfcHom_mul, mul_comm g h]
  have key2 : cfcHom ha h (cfcHom ha g x) = cfcHom ha (h * g) x := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_comm h g]
  rw [integral_specMeasure_cont, integral_specMeasure_cont, integral_specMeasure_cont,
    integral_specMeasure_cont]
  simp only [map_add, map_sub, key2, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [key1]
  ring

open RCLike MeasureTheory in
/-- **Engine, measure form** (`g ≥ 0`): `μ_{g(T)x+v} + (μ_{x−v}·g) = μ_{g(T)x−v} + (μ_{x+v}·g)`,
    where `·g` is `withDensity (ENNReal.ofReal ∘ g)`.  Lifts `specMeasure_engine` to a measure
    identity by Riesz–Markov uniqueness. -/
lemma specMeasure_engine_measure (ha : IsSelfAdjoint T) (g : C(spectrum ℝ T, ℝ))
    (hg0 : ∀ ω, 0 ≤ g ω) (x v : H) :
    specMeasure T ha (cfcHom ha g x + v)
        + (specMeasure T ha (x - v)).withDensity (fun ω => ENNReal.ofReal (g ω))
      = specMeasure T ha (cfcHom ha g x - v)
        + (specMeasure T ha (x + v)).withDensity (fun ω => ENNReal.ofReal (g ω)) := by
  have hρmeas : Measurable (fun ω => ENNReal.ofReal (g ω)) :=
    ENNReal.measurable_ofReal.comp g.continuous.measurable
  have hρlt : ∀ z : H, ∀ᵐ ω ∂(specMeasure T ha z), (fun ω => ENNReal.ofReal (g ω)) ω < ∞ :=
    fun z => ae_of_all _ fun ω => ENNReal.ofReal_lt_top
  have hfin : ∀ z : H, (∫⁻ ω, ENNReal.ofReal (g ω) ∂(specMeasure T ha z)) ≠ ∞ := by
    intro z
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal ‖g‖) fun ω => ?_) ?_)
    · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (g.norm_coe_le_norm ω))
    · rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  haveI : IsFiniteMeasure ((specMeasure T ha (x - v)).withDensity (fun ω => ENNReal.ofReal (g ω))) :=
    isFiniteMeasure_withDensity (hfin _)
  haveI : IsFiniteMeasure ((specMeasure T ha (x + v)).withDensity (fun ω => ENNReal.ofReal (g ω))) :=
    isFiniteMeasure_withDensity (hfin _)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_withDensity_eq_integral_toReal_smul hρmeas (hρlt _),
      integral_withDensity_eq_integral_toReal_smul hρmeas (hρlt _)]
  have hconv : ∀ z : H, ∫ ω, (ENNReal.ofReal (g ω)).toReal • f ω ∂(specMeasure T ha z)
      = ∫ ω, (f.toContinuousMap * g) ω ∂(specMeasure T ha z) := by
    intro z
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (hg0 ω), smul_eq_mul]
    simp [mul_comm]
  rw [hconv, hconv]
  have heng := specMeasure_engine T ha g f.toContinuousMap x v
  simp only [CompactlySupportedContinuousMap.coe_toContinuousMap] at heng ⊢
  linarith

open RCLike MeasureTheory in
/-- `withDensity`-to-`setIntegral` bridge: `((μ_z)·g).real s = ∫_s g dμ_z` for `g ≥ 0`. -/
lemma withDensity_real_setIntegral (ha : IsSelfAdjoint T) (g : C(spectrum ℝ T, ℝ))
    (hg0 : ∀ ω, 0 ≤ g ω) (z : H) {s : Set (spectrum ℝ T)} (hs : MeasurableSet s) :
    ((specMeasure T ha z).withDensity (fun ω => ENNReal.ofReal (g ω))).real s
      = ∫ ω in s, g ω ∂(specMeasure T ha z) := by
  rw [Measure.real, withDensity_apply _ hs,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0)
      (Continuous.aestronglyMeasurable (by fun_prop))]

open RCLike MeasureTheory in
/-- **Set-level engine** for `g ≥ 0`: `q_s(g(T)x+v) − q_s(g(T)x−v) = ∫_s g dμ_{x+v} − ∫_s g dμ_{x−v}`
    (the `.real`-at-`s` evaluation of `specMeasure_engine_measure`). -/
lemma specMeasure_setEngine_nonneg (ha : IsSelfAdjoint T) (g : C(spectrum ℝ T, ℝ))
    (hg0 : ∀ ω, 0 ≤ g ω) (x v : H) {s : Set (spectrum ℝ T)} (hs : MeasurableSet s) :
    (specMeasure T ha (cfcHom ha g x + v)).real s
        - (specMeasure T ha (cfcHom ha g x - v)).real s
      = (∫ ω in s, g ω ∂(specMeasure T ha (x + v)))
        - (∫ ω in s, g ω ∂(specMeasure T ha (x - v))) := by
  have hfin : ∀ z : H, (∫⁻ ω, ENNReal.ofReal (g ω) ∂(specMeasure T ha z)) ≠ ∞ := by
    intro z
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal ‖g‖) fun ω => ?_) ?_)
    · exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (g.norm_coe_le_norm ω))
    · rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  haveI : IsFiniteMeasure ((specMeasure T ha (x - v)).withDensity (fun ω => ENNReal.ofReal (g ω))) :=
    isFiniteMeasure_withDensity (hfin _)
  haveI : IsFiniteMeasure ((specMeasure T ha (x + v)).withDensity (fun ω => ENNReal.ofReal (g ω))) :=
    isFiniteMeasure_withDensity (hfin _)
  have h := specMeasure_engine_measure T ha g hg0 x v
  apply_fun (fun μ => MeasureTheory.Measure.real μ s) at h
  rw [measureReal_add_apply, measureReal_add_apply,
    withDensity_real_setIntegral T ha g hg0 _ hs, withDensity_real_setIntegral T ha g hg0 _ hs] at h
  linarith

/-- `b_s` is subtractive in its left argument. -/
lemma bForm_sub_left (ha : IsSelfAdjoint T) (s : Set (spectrum ℝ T)) (u w v : H) :
    bForm T ha s (u - w) v = bForm T ha s u v - bForm T ha s w v := by
  rw [bForm_comm, bForm_comm T ha s u v, bForm_comm T ha s w v, bForm_sub_right]

open RCLike MeasureTheory in
/-- **Set-level engine** (general continuous `g`): `q_s(g(T)x+v) − q_s(g(T)x−v) =
    ∫_s g dμ_{x+v} − ∫_s g dμ_{x−v}`.  Both sides are linear in `g`; extend the `g≥0` case by
    `g = (g+‖g‖) − ‖g‖`. -/
lemma specMeasure_setEngine (ha : IsSelfAdjoint T) (g : C(spectrum ℝ T, ℝ)) (x v : H)
    {s : Set (spectrum ℝ T)} (hs : MeasurableSet s) :
    (specMeasure T ha (cfcHom ha g x + v)).real s
        - (specMeasure T ha (cfcHom ha g x - v)).real s
      = (∫ ω in s, g ω ∂(specMeasure T ha (x + v)))
        - (∫ ω in s, g ω ∂(specMeasure T ha (x - v))) := by
  have hLHS : ∀ g' : C(spectrum ℝ T, ℝ),
      (specMeasure T ha (cfcHom ha g' x + v)).real s
          - (specMeasure T ha (cfcHom ha g' x - v)).real s
        = 4 * bForm T ha s (cfcHom ha g' x) v := by
    intro g'; unfold bForm qForm; ring
  set cC : C(spectrum ℝ T, ℝ) := ContinuousMap.const _ ‖g‖ with hcC
  set gC : C(spectrum ℝ T, ℝ) := g + cC with hgC
  have hgC0 : ∀ ω, 0 ≤ gC ω := by
    intro ω
    have hb := g.norm_coe_le_norm ω
    rw [Real.norm_eq_abs] at hb
    simp only [hgC, hcC, ContinuousMap.add_apply, ContinuousMap.const_apply]
    have := (abs_le.mp hb).1
    linarith
  have hcC0 : ∀ ω, 0 ≤ cC ω := fun ω => by
    simp only [hcC, ContinuousMap.const_apply]; exact norm_nonneg g
  have e1 := specMeasure_setEngine_nonneg T ha gC hgC0 x v hs
  have e2 := specMeasure_setEngine_nonneg T ha cC hcC0 x v hs
  rw [hLHS] at e1 e2
  have hcfc : cfcHom ha g x = cfcHom ha gC x - cfcHom ha cC x := by
    rw [hgC, map_add, ContinuousLinearMap.add_apply]; abel
  rw [hLHS, hcfc, bForm_sub_left, mul_sub, e1, e2]
  have hadd : ∀ z : H, ∫ ω in s, gC ω ∂(specMeasure T ha z)
      = (∫ ω in s, g ω ∂(specMeasure T ha z)) + ∫ ω in s, cC ω ∂(specMeasure T ha z) := by
    intro z
    rw [hgC]
    simp only [ContinuousMap.add_apply]
    exact integral_add
      ((g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).restrict)
      ((cC.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).restrict)
  rw [hadd, hadd]
  ring

open RCLike in
/-- **Diagonal–`E(s)` identity**: `re ⟪x, h(T)(E(s)v)⟫ = b_s(h(T)x, v)` for continuous `h`.
    (Move `h(T)` and `E(s)` across by self-adjointness; the imaginary part of `c_s` drops under `re`.) -/
lemma re_inner_cfcHom_specProj (ha : IsSelfAdjoint T) (h : C(spectrum ℝ T, ℝ))
    (s : Set (spectrum ℝ T)) (x v : H) :
    re ⟪x, cfcHom ha h (specProj T ha s v)⟫ = bForm T ha s (cfcHom ha h x) v := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (show IsSelfAdjoint (cfcHom ha h) by rw [isSelfAdjoint_iff, ← map_star, star_trivial])
  have hEsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (specProj_isSelfAdjoint T ha s)
  rw [show (⟪x, cfcHom ha h (specProj T ha s v)⟫ : ℂ)
        = ⟪cfcHom ha h x, specProj T ha s v⟫ from (hsym x _).symm,
    show (⟪cfcHom ha h x, specProj T ha s v⟫ : ℂ)
        = ⟪specProj T ha s (cfcHom ha h x), v⟫ from (hEsym _ v).symm,
    inner_specProj]
  show (((bForm T ha s (cfcHom ha h x) v : ℝ) : ℂ)
    - Complex.I * ((bForm T ha s (cfcHom ha h x) (Complex.I • v) : ℝ) : ℂ)).re = _
  simp [Complex.sub_re, Complex.mul_re]

open RCLike MeasureTheory in
/-- Polarization at the scalar-measure level: `∫f dμ_{w+u} − ∫f dμ_{w−u} = 4·re⟪w, f(T)u⟫`. -/
lemma integral_specMeasure_polarization (ha : IsSelfAdjoint T) (f : C(spectrum ℝ T, ℝ)) (w u : H) :
    (∫ ω, f ω ∂(specMeasure T ha (w + u))) - (∫ ω, f ω ∂(specMeasure T ha (w - u)))
      = 4 * re ⟪w, cfcHom ha f u⟫ := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (show IsSelfAdjoint (cfcHom ha f) by rw [isSelfAdjoint_iff, ← map_star, star_trivial])
  have hcross : re ⟪u, cfcHom ha f w⟫ = re ⟪w, cfcHom ha f u⟫ := by
    rw [show (⟪u, cfcHom ha f w⟫ : ℂ) = ⟪cfcHom ha f u, w⟫ from (hsym u w).symm, inner_re_symm]
  rw [integral_specMeasure_cont, integral_specMeasure_cont]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [hcross]
  ring

open RCLike MeasureTheory in
/-- **Final measure identity**: `μ_{x+E(s)v} + (μ_{x−v})↾s = μ_{x−E(s)v} + (μ_{x+v})↾s`.
    Proved by Riesz–Markov uniqueness: the test against continuous `f` reduces, via the
    polarization + `re_inner_cfcHom_specProj` + `specMeasure_setEngine`, to an identity that holds. -/
lemma specProj_engine_measure (ha : IsSelfAdjoint T) {s : Set (spectrum ℝ T)} (hs : MeasurableSet s)
    (x v : H) :
    specMeasure T ha (x + specProj T ha s v) + (specMeasure T ha (x - v)).restrict s
      = specMeasure T ha (x - specProj T ha s v) + (specMeasure T ha (x + v)).restrict s := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f),
      integral_add_measure (CompactlySupportedContinuousMap.integrable f)
        (CompactlySupportedContinuousMap.integrable f)]
  have hpol := integral_specMeasure_polarization T ha f.toContinuousMap x (specProj T ha s v)
  rw [re_inner_cfcHom_specProj] at hpol
  have hset := specMeasure_setEngine T ha f.toContinuousMap x v hs
  have h4b : 4 * bForm T ha s (cfcHom ha f.toContinuousMap x) v
      = (specMeasure T ha (cfcHom ha f.toContinuousMap x + v)).real s
        - (specMeasure T ha (cfcHom ha f.toContinuousMap x - v)).real s := by
    unfold bForm qForm; ring
  simp only [CompactlySupportedContinuousMap.coe_toContinuousMap] at hpol hset h4b
  rw [h4b] at hpol
  -- hpol : ∫f dμ_{x+E(s)v} − ∫f dμ_{x−E(s)v} = (.real diff) ; hset : (.real diff) = ∫_s f dμ_{x+v} − ∫_s f dμ_{x−v}
  linarith [hpol, hset]

open MeasureTheory in
/-- **The intersection identity at the form level**: `b_t(x, E(s)v) = b_{s∩t}(x, v)`
    (evaluate `specProj_engine_measure` at `t` via `.real`). -/
lemma bForm_specProj (ha : IsSelfAdjoint T) {s t : Set (spectrum ℝ T)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (x v : H) :
    bForm T ha t x (specProj T ha s v) = bForm T ha (s ∩ t) x v := by
  have h := specProj_engine_measure T ha hs x v
  apply_fun (fun μ => MeasureTheory.Measure.real μ t) at h
  rw [measureReal_add_apply, measureReal_add_apply, measureReal_restrict_apply ht,
    measureReal_restrict_apply ht, Set.inter_comm t s] at h
  unfold bForm qForm
  linarith [h]

/-- **`E_inter`**: `E(s∩t) = E(s)·E(t)` — the projection / multiplicativity property, the final
    `ProjectionValuedMeasure` field.  `E(s)·E(t)` tested against `⟪·x,y⟫` is `c_t(x,E(s)y)`, which
    equals `c_{s∩t}(x,y)` by `bForm_specProj` (using `E(s)` ℂ-linear for the imaginary part). -/
lemma specProj_inter (ha : IsSelfAdjoint T) {s t : Set (spectrum ℝ T)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    specProj T ha (s ∩ t) = specProj T ha s * specProj T ha t := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [inner_specProj, ContinuousLinearMap.mul_apply]
  have hEsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (specProj_isSelfAdjoint T ha s)
  rw [show (⟪specProj T ha s (specProj T ha t x), y⟫ : ℂ)
        = ⟪specProj T ha t x, specProj T ha s y⟫ from hEsym _ y, inner_specProj]
  unfold cForm
  rw [show Complex.I • specProj T ha s y = specProj T ha s (Complex.I • y)
        from (map_smul (specProj T ha s) Complex.I y).symm,
    bForm_specProj T ha hs ht, bForm_specProj T ha hs ht]

/-- **The bounded spectral theorem (PVM form)**: every bounded self-adjoint `T : H →L[ℂ] H`
    induces a projection-valued measure on `spectrum ℝ T`, with `E(s) = specProj`.  All structure
    fields are the lemmas proved above; `isIdem` is `E_inter` at `s = t`. -/
noncomputable def PVM_of_selfAdjoint (ha : IsSelfAdjoint T) :
    QIQTH.Spectral.ProjectionValuedMeasure (spectrum ℝ T) H where
  E := specProj T ha
  isSA := fun s _ => specProj_isSelfAdjoint T ha s
  isIdem := fun s hs => by
    have h := specProj_inter T ha hs hs
    rw [Set.inter_self] at h
    exact h.symm
  E_empty := specProj_empty T ha
  E_univ := specProj_univ T ha
  E_inter := fun s t hs ht => specProj_inter T ha hs ht
  hasSum_iUnion := fun hm hd x => specProj_hasSum T ha hm hd x

open RCLike MeasureTheory in
/-- **Spectral representation of `T` (diagonal form)**: `∫_{σ(T)} λ dμ_x(λ) = re ⟪x, T x⟫`.
    Since `μ_x` is the scalar spectral measure of the `PVM_of_selfAdjoint` (`μ_x(s) = ⟪E(s)x,x⟫`),
    this is the statement `T = ∫ λ dE(λ)` tested on the diagonal — `T` recovered from its PVM. -/
theorem re_inner_T_eq_integral (ha : IsSelfAdjoint T) (x : H) :
    ∫ ω, (ω : ℝ) ∂(specMeasure T ha x) = re ⟪x, T x⟫ := by
  have h := integral_specMeasure T ha x
    ⟨(ContinuousMap.id ℝ).restrict (spectrum ℝ T), HasCompactSupport.of_compactSpace _⟩
  rw [show ((⟨(ContinuousMap.id ℝ).restrict (spectrum ℝ T), HasCompactSupport.of_compactSpace _⟩ :
        C_c(spectrum ℝ T, ℝ)).toContinuousMap) = (ContinuousMap.id ℝ).restrict (spectrum ℝ T)
      from rfl, cfcHom_id] at h
  exact h

/-! ### Layer 2 kickoff — the bounded Borel functional calculus of `T`

With `PVM_of_selfAdjoint` in hand, `PVM.lean`'s `boundedFC` (proved a unital `*`-algebra hom)
instantiates to the **bounded Borel functional calculus of `T`**: a bounded measurable
`f : σ(T) → ℂ` (including discontinuous functions like the modular `λ ↦ ((2−λ)/λ)^{it}`) maps to
an operator `f(T)`, multiplicatively.  This is the gateway to `Δ^{it}` and the continuum modular
flow that continuous `cfc` cannot reach. -/

/-- The **bounded Borel functional calculus** of a bounded self-adjoint `T`: `f(T)` for bounded
    measurable `f : σ(T) → ℂ`. -/
noncomputable def borelFC (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℂ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C) : H →L[ℂ] H :=
  (PVM_of_selfAdjoint T ha).boundedFC hf hC0 hC

/-- Defining property: `⟪x, f(T) y⟫ = B_f(x,y)` (the polarized scalar-measure form). -/
theorem inner_borelFC (ha : IsSelfAdjoint T) {f : spectrum ℝ T → ℂ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖f ω‖ ≤ C) (x y : H) :
    inner ℂ x (borelFC T ha hf hC0 hC y) = (PVM_of_selfAdjoint T ha).bilinDiag f x y :=
  (PVM_of_selfAdjoint T ha).inner_boundedFC hf hC0 hC x y

/-- **Multiplicativity** of the bounded Borel FC: `(f·g)(T) = f(T)·g(T)`. -/
theorem borelFC_mul (ha : IsSelfAdjoint T) {f g : spectrum ℝ T → ℂ} {Cf Cg Cp : ℝ}
    (hf : Measurable f) (hC0f : 0 ≤ Cf) (hCf : ∀ ω, ‖f ω‖ ≤ Cf)
    (hg : Measurable g) (hC0g : 0 ≤ Cg) (hCg : ∀ ω, ‖g ω‖ ≤ Cg)
    (hfp : Measurable (fun ω => f ω * g ω)) (hC0p : 0 ≤ Cp) (hCp : ∀ ω, ‖f ω * g ω‖ ≤ Cp) :
    borelFC T ha hfp hC0p hCp = borelFC T ha hf hC0f hCf * borelFC T ha hg hC0g hCg :=
  (PVM_of_selfAdjoint T ha).boundedFC_mul hf hC0f hCf hg hC0g hCg hfp hC0p hCp

/-- The bounded Borel FC is **unital**: `(fun _ => 1)(T) = 1`. -/
theorem borelFC_one (ha : IsSelfAdjoint T) :
    borelFC T ha (f := fun _ => (1 : ℂ)) measurable_const (norm_nonneg 1) (fun _ => le_rfl)
      = 1 := by
  rw [borelFC, (PVM_of_selfAdjoint T ha).boundedFC_const]
  simp

/-- **Constant rule** `(fun _ => c)(T) = c·1` — the QIQTH-layer wrapper of `boundedFC_const`. -/
theorem borelFC_const (ha : IsSelfAdjoint T) (c : ℂ) :
    borelFC T ha (f := fun _ => c) measurable_const (norm_nonneg c) (fun _ => le_rfl)
      = c • (1 : H →L[ℂ] H) :=
  (PVM_of_selfAdjoint T ha).boundedFC_const c

/-- **Indicator rule** `𝟙_s(T) = E s` — the QIQTH-layer wrapper of `boundedFC_indicator`: the bounded
    Borel FC of a level-set indicator is the corresponding spectral projection of the PVM. -/
theorem borelFC_indicator (ha : IsSelfAdjoint T) {s : Set (spectrum ℝ T)} (hs : MeasurableSet s) :
    borelFC T ha (f := s.indicator (fun _ => (1 : ℂ))) (measurable_const.indicator hs)
        zero_le_one (QIQTH.Spectral.ProjectionValuedMeasure.norm_indicatorOne_le s)
      = (PVM_of_selfAdjoint T ha).E s :=
  (PVM_of_selfAdjoint T ha).boundedFC_indicator hs

/-! ### Layer 2 — the continuum modular flow `U(t) = exp(it·A) = Δ^{it}`

The one-parameter unitary group generated by a bounded self-adjoint `A` (with `Δ = exp A`, so
`U(t) = Δ^{it}`): the continuum analog of `FiniteModularTheory.sigmaDiag`.  Group law from
commuting exponentials; unitarity from self-adjointness via `star_exp`. -/

/-- `U(t) = exp(it·A)`, the modular unitary flow with self-adjoint generator `A`. -/
noncomputable def modFlow (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp (((t : ℂ) * Complex.I) • A)

@[simp] theorem modFlow_zero (A : H →L[ℂ] H) : modFlow A 0 = 1 := by
  simp [modFlow]

/-- **One-parameter group law**: `U(s+t) = U(s)·U(t)`. -/
theorem modFlow_add (A : H →L[ℂ] H) (s t : ℝ) :
    modFlow A (s + t) = modFlow A s * modFlow A t := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [modFlow, modFlow, modFlow,
    ← NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)]
  congr 1
  push_cast
  rw [← add_smul]
  ring_nf

/-- Adjoint of the flow: `U(t)⋆ = U(−t)` (uses `A` self-adjoint). -/
theorem modFlow_star (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (modFlow A t) = modFlow A (-t) := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [modFlow, modFlow, NormedSpace.star_exp, star_smul, hA.star_eq]
  congr 2
  rw [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Unitarity**: `U(t)⋆·U(t) = 1` (and hence `U(t)` is a unitary; `U(t)·U(t)⋆ = 1` symmetrically). -/
theorem modFlow_unitary (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (modFlow A t) * modFlow A t = 1 := by
  rw [modFlow_star A hA, ← modFlow_add, neg_add_cancel, modFlow_zero]

/-- **Strong (norm) continuity**: `t ↦ U(t)` is continuous — so `U` is a strongly-continuous
    one-parameter unitary group (the bounded-generator Stone's theorem). -/
theorem modFlow_continuous (A : H →L[ℂ] H) : Continuous (modFlow A) := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous.comp (by fun_prop)

/-- **Generator fixes the vector ⇒ the flow fixes it.**  If the generator annihilates `ξ`
(`A ξ = 0`) then `U(t) ξ = ξ` for every `t`.  This is the infinitesimal form of the Tomita–Takesaki
invariance of the cyclic separating vector: writing `Δ = exp A`, `A Ω = 0` gives `Δ^{it} Ω = Ω`.
Proof: expand `exp((it)A) = ∑ ((it)A)ⁿ/n!`, evaluate at `ξ` (evaluation is a continuous linear map,
so it commutes with the sum); every `n ≥ 1` term kills `ξ` since `((it)A) ξ = (it)(A ξ) = 0`, leaving
the `n = 0` term `ξ`. -/
theorem modFlow_apply_eq_self_of_generator (A : H →L[ℂ] H) {ξ : H} (hAξ : A ξ = 0) (t : ℝ) :
    modFlow A t ξ = ξ := by
  set B : H →L[ℂ] H := ((t : ℂ) * Complex.I) • A with hBdef
  have hBξ : B ξ = 0 := by rw [hBdef, ContinuousLinearMap.smul_apply, hAξ, smul_zero]
  have hpow : ∀ n : ℕ, (B ^ (n + 1)) ξ = 0 := by
    intro n; rw [pow_succ, ContinuousLinearMap.mul_apply, hBξ, map_zero]
  have happ : modFlow A t ξ = (ContinuousLinearMap.apply ℂ H ξ) (NormedSpace.exp B) :=
    (ContinuousLinearMap.apply_apply ξ _).symm
  rw [happ]
  simp only [NormedSpace.exp_eq_tsum ℂ]
  rw [ContinuousLinearMap.map_tsum _ (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)]
  simp only [map_smul, ContinuousLinearMap.apply_apply]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hpow m, smul_zero]

/-! ### Layer 2 — the modular automorphism group `σ_t(x) = U(t)·x·U(t)⁻¹`

Conjugation by the modular flow gives a one-parameter group of `*`-automorphisms — the continuum
modular automorphism group, generalizing `FiniteModularTheory.modAut`. -/

/-- The modular automorphism `σ_t(x) = U(t)·x·U(t)⁻¹ = U(t)·x·U(−t)`. -/
noncomputable def modAut (A : H →L[ℂ] H) (t : ℝ) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  modFlow A t * x * modFlow A (-t)

@[simp] theorem modAut_zero (A : H →L[ℂ] H) (x : H →L[ℂ] H) : modAut A 0 x = x := by
  rw [modAut, neg_zero, modFlow_zero, mul_one, one_mul]

/-- **One-parameter group law**: `σ_s ∘ σ_t = σ_{s+t}`. -/
theorem modAut_comp (A : H →L[ℂ] H) (s t : ℝ) (x : H →L[ℂ] H) :
    modAut A s (modAut A t x) = modAut A (s + t) x := by
  rw [modAut, modAut, modAut, modFlow_add, show -(s + t) = -t + -s by ring, modFlow_add]
  simp only [mul_assoc]

/-- `σ_t(1) = 1`. -/
@[simp] theorem modAut_one (A : H →L[ℂ] H) (t : ℝ) : modAut A t 1 = 1 := by
  rw [modAut, mul_one, ← modFlow_add, add_neg_cancel, modFlow_zero]

/-- **Multiplicativity**: `σ_t(x·y) = σ_t(x)·σ_t(y)` (conjugation by a unitary). -/
theorem modAut_mul (A : H →L[ℂ] H) (t : ℝ) (x y : H →L[ℂ] H) :
    modAut A t (x * y) = modAut A t x * modAut A t y := by
  have h1 : modFlow A (-t) * modFlow A t = 1 := by
    rw [← modFlow_add, neg_add_cancel, modFlow_zero]
  simp only [modAut, mul_assoc]
  rw [← mul_assoc (modFlow A (-t)) (modFlow A t), h1, one_mul]

/-- **`*`-compatibility**: `σ_t(x⋆) = σ_t(x)⋆` (uses `A` self-adjoint). -/
theorem modAut_star (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : H →L[ℂ] H) :
    star (modAut A t x) = modAut A t (star x) := by
  rw [modAut, modAut, star_mul, star_mul, modFlow_star A hA, modFlow_star A hA, neg_neg,
    mul_assoc]

/-! ### Layer 2 — modular invariance of the state `ω_ξ(x) = ⟪ξ, x ξ⟫`

The continuum generalization of `FiniteModularTheory.modAut_stateOf_invariant`: the modular flow
`σ_t` preserves the GNS vector state of any vector fixed by the flow.  In Tomita–Takesaki the cyclic
separating vector `Ω` satisfies `Δ^{it} Ω = Ω` (it generates the state and is annihilated by the
modular generator), so `ω_Ω ∘ σ_t = ω_Ω` is exactly the invariance of the modular state.  This is
the first *state-coupled* (genuinely modular) continuum theorem; it rides on `modFlow_star`
(`U(t)⋆ = U(−t)`), no analytic-continuation machinery. -/

/-- The GNS **vector state** `ω_ξ(x) = ⟪ξ, x ξ⟫` induced by a vector `ξ` (a state when `‖ξ‖ = 1`). -/
noncomputable def vectorState (ξ : H) (x : H →L[ℂ] H) : ℂ := inner ℂ ξ (x ξ)

/-- **Modular invariance of the state.**  If `ξ` is fixed by the modular flow
(`modFlow A (−t) ξ = ξ` — the continuum form of the Tomita–Takesaki axiom `Δ^{it} Ω = Ω`), then the
modular automorphism `σ_t` preserves its vector state: `ω_ξ(σ_t x) = ω_ξ(x)`.  Generalizes
`FiniteModularTheory.modAut_stateOf_invariant` from the finite trace state to the continuum.
Proof: `⟪ξ, U(t) x U(−t) ξ⟫ = ⟪U(t)⋆ ξ, x U(−t) ξ⟫ = ⟪U(−t) ξ, x U(−t) ξ⟫ = ⟪ξ, x ξ⟫`, using
`U(t)⋆ = U(−t)` (`modFlow_star`) and the fixed-vector hypothesis. -/
theorem modAut_vectorState_invariant (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ)
    {ξ : H} (hξ : modFlow A (-t) ξ = ξ) (x : H →L[ℂ] H) :
    vectorState ξ (modAut A t x) = vectorState ξ x := by
  have hadj : ContinuousLinearMap.adjoint (modFlow A t) = modFlow A (-t) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact modFlow_star A hA t
  unfold vectorState modAut
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ← ContinuousLinearMap.adjoint_inner_left, hadj, hξ]

/-- **Modular invariance from the generator.**  If the generator annihilates `ξ` (`A ξ = 0` — i.e.
`ξ` is in the kernel of the modular generator, the infinitesimal `Δ^{it} ξ = ξ`), then the modular
automorphism preserves its vector state: `ω_ξ(σ_t x) = ω_ξ(x)`.  Combines
`modFlow_apply_eq_self_of_generator` with `modAut_vectorState_invariant`; the directly checkable form
of the continuum modular-invariance theorem. -/
theorem modAut_vectorState_invariant_of_generator (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ)
    {ξ : H} (hAξ : A ξ = 0) (x : H →L[ℂ] H) :
    vectorState ξ (modAut A t x) = vectorState ξ x :=
  modAut_vectorState_invariant A hA t (modFlow_apply_eq_self_of_generator A hAξ (-t)) x

/-! ### Layer 2 — the complex-time (entire-analytic) modular flow `U(z) = Δ^{iz}`

Because the generator `A` is **bounded**, `exp((z·i)·A)` converges for *every* complex `z`: every
algebra element is *entire* analytic for the modular flow.  This is exactly the analytic-element
theory that is the hard ingredient of the *unbounded* Tomita–Takesaki theory (there σ_z is only
defined on a dense set of analytic vectors) — and which the bounded/Type-I case gets for free.  We
build the complex-time flow `modFlowC`/`modAutC`, recover the real unitary flow on `ℝ`, and identify
the imaginary-time conjugation `σ_{-i}` with conjugation by the modular operator `Δ = exp A`.

HONEST SCOPE: this is the analytic *infrastructure*.  The KMS *identity*
`ω(x · σ_{-i} y) = ω(y · x)` itself holds only when `Δ` is the genuine modular operator of a pair
`(M, Ω)` (Tomita's theorem) — it is FALSE for an arbitrary self-adjoint generator — so it is NOT
claimed here; it stays gated on the Phase-3 modular-operator construction. -/

/-- Complex-time modular flow `U(z) = exp((z·i)·A) = Δ^{iz}`, entire in `z` (bounded generator). -/
noncomputable def modFlowC (A : H →L[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  NormedSpace.exp ((z * Complex.I) • A)

/-- On the real axis the complex-time flow is the unitary `modFlow`. -/
@[simp] theorem modFlowC_ofReal (A : H →L[ℂ] H) (t : ℝ) :
    modFlowC A (t : ℂ) = modFlow A t := rfl

@[simp] theorem modFlowC_zero (A : H →L[ℂ] H) : modFlowC A 0 = 1 := by
  simp [modFlowC]

/-- **Complex one-parameter group law**: `U(w+z) = U(w)·U(z)` for all `w, z ∈ ℂ`. -/
theorem modFlowC_add (A : H →L[ℂ] H) (w z : ℂ) :
    modFlowC A (w + z) = modFlowC A w * modFlowC A z := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [modFlowC, modFlowC, modFlowC,
    ← NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left _).smul_right _)]
  congr 1
  rw [← add_smul, ← add_mul]

/-- The complex-time flow is **entire** (continuous on all of `ℂ`). -/
theorem modFlowC_continuous (A : H →L[ℂ] H) : Continuous (modFlowC A) := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous.comp (by fun_prop)

/-- The **modular operator** `Δ = exp A` (so `U(z) = Δ^{iz}` and `U(-i) = Δ`). -/
noncomputable def modDelta (A : H →L[ℂ] H) : H →L[ℂ] H := NormedSpace.exp A

/-- `Δ · exp(-A) = 1` — `exp(-A)` is the inverse `Δ⁻¹`. -/
theorem modDelta_mul_expNeg (A : H →L[ℂ] H) : modDelta A * NormedSpace.exp (-A) = 1 := by
  haveI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [modDelta, ← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_right), add_neg_cancel,
    NormedSpace.exp_zero]

/-- At imaginary time `z = -i`: `U(-i) = Δ`. -/
@[simp] theorem modFlowC_neg_I (A : H →L[ℂ] H) : modFlowC A (-Complex.I) = modDelta A := by
  rw [modFlowC, modDelta,
    show ((-Complex.I) * Complex.I) = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I]; ring, one_smul]

/-- At imaginary time `z = i`: `U(i) = Δ⁻¹ = exp(-A)`. -/
@[simp] theorem modFlowC_I (A : H →L[ℂ] H) : modFlowC A Complex.I = NormedSpace.exp (-A) := by
  rw [modFlowC, show (Complex.I * Complex.I) = (-1 : ℂ) by rw [Complex.I_mul_I], neg_one_smul]

/-- The complex-time modular automorphism `σ_z(x) = U(z)·x·U(-z)`. -/
noncomputable def modAutC (A : H →L[ℂ] H) (z : ℂ) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  modFlowC A z * x * modFlowC A (-z)

/-- On the real axis `σ_z` is the `*`-automorphism `modAut`. -/
@[simp] theorem modAutC_ofReal (A : H →L[ℂ] H) (t : ℝ) (x : H →L[ℂ] H) :
    modAutC A (t : ℂ) x = modAut A t x := by
  unfold modAutC modAut
  rw [modFlowC_ofReal, show (-(t : ℂ)) = ((-t : ℝ) : ℂ) by push_cast; ring, modFlowC_ofReal]

/-- `σ_0 = id`. -/
@[simp] theorem modAutC_zero (A : H →L[ℂ] H) (x : H →L[ℂ] H) : modAutC A 0 x = x := by
  rw [modAutC, neg_zero, modFlowC_zero, mul_one, one_mul]

/-- **Complex group law**: `σ_w ∘ σ_z = σ_{w+z}` for all `w, z ∈ ℂ` (the analytic continuation
    of the modular automorphism group to complex time). -/
theorem modAutC_comp (A : H →L[ℂ] H) (w z : ℂ) (x : H →L[ℂ] H) :
    modAutC A w (modAutC A z x) = modAutC A (w + z) x := by
  rw [modAutC, modAutC, modAutC, modFlowC_add, show -(w + z) = -z + -w by ring, modFlowC_add]
  simp only [mul_assoc]

/-- `σ_z(x·y) = σ_z(x)·σ_z(y)` (algebra homomorphism for every complex time). -/
theorem modAutC_mul (A : H →L[ℂ] H) (z : ℂ) (x y : H →L[ℂ] H) :
    modAutC A z (x * y) = modAutC A z x * modAutC A z y := by
  have h1 : modFlowC A (-z) * modFlowC A z = 1 := by
    rw [← modFlowC_add, neg_add_cancel, modFlowC_zero]
  simp only [modAutC, mul_assoc]
  rw [← mul_assoc (modFlowC A (-z)) (modFlowC A z), h1, one_mul]

/-- **Imaginary-time modular conjugation = conjugation by Δ.**  At `z = -i` the complex modular flow
    is conjugation by the modular operator `Δ = exp A`: `σ_{-i}(x) = Δ · x · Δ⁻¹` (`Δ⁻¹ = exp(-A)`,
    `modDelta_mul_expNeg`).  This is the conjugation the KMS condition relates to `xy ↦ yx` — the
    analytic ingredient, *entire* here because `A` is bounded.  (The KMS identity itself needs Δ to
    be the genuine modular operator of `(M, Ω)`; see the section header.) -/
theorem modAutC_neg_I (A : H →L[ℂ] H) (x : H →L[ℂ] H) :
    modAutC A (-Complex.I) x = modDelta A * x * NormedSpace.exp (-A) := by
  rw [modAutC, modFlowC_neg_I, neg_neg, modFlowC_I]

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
