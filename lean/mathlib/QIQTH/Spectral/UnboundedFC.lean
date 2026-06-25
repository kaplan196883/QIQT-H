/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Stone, Phase 1 (M1) — the unbounded functional calculus `∫ f dE` on a PVM

`STONE_THEOREM_PLAN.md` Phase 1 / `P4_TO_GR_MASTER_PLAN.md` M1.  The keystone that makes the modular
Hamiltonian `K = ∫ log(r/(2−r)) dE_R` a genuine self-adjoint operator (Phase 2) — built on the EXISTING
`ProjectionValuedMeasure` substrate (`scalarMeasure`, `boundedFC`), no general Stone theorem, no Cayley.

This file delivers the **domain**: for a real Borel symbol `f`, the set of vectors with finite spectral
energy `∫ f² dμ_x < ∞` is a `ℂ`-submodule `fcDomain P f` of `H` — the natural domain `D(∫ f dE)` of the
(unbounded) self-adjoint operator.  The operator on this domain, its symmetry and self-adjointness, and the
exponential law `exp(it ∫f dE) = ∫ e^{itf} dE` are the subsequent Phase-1/2 increments.

Axiom-free.  Uses the spectral scaling `μ_{c·x} = ‖c‖²·μ_x` and the parallelogram identity
`μ_{x+y} + μ_{x−y} = 2μ_x + 2μ_y` already proved in `QIQTH/Spectral/PVM.lean`.
-/
import QIQTH.Spectral.PVM
import Mathlib.MeasureTheory.Function.L2Space

namespace QIQTH.Spectral.ProjectionValuedMeasure

open MeasureTheory
open scoped ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : ProjectionValuedMeasure Ω H)

/-- The **spectral energy** `∫ f² dμ_x ∈ ℝ≥0∞` of a vector `x` against a real Borel symbol `f`
    (`μ_x = P.scalarMeasure x`).  Finite energy is the defining condition of the FC domain. -/
noncomputable def fcEnergy (f : Ω → ℝ) (x : H) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x)

/-- The scalar spectral measure of `0` is the zero measure (`E s 0 = 0`). -/
theorem scalarMeasure_zero : P.scalarMeasure (0 : H) = 0 := by
  have h := P.scalarMeasure_smul (0 : ℂ) (0 : H)
  simpa using h

@[simp] theorem fcEnergy_zero (f : Ω → ℝ) : P.fcEnergy f (0 : H) = 0 := by
  rw [fcEnergy, P.scalarMeasure_zero, lintegral_zero_measure]

/-- **Homogeneity of the energy:** `‖c‖²` scales out (`μ_{c·x} = ‖c‖²·μ_x`). -/
theorem fcEnergy_smul (f : Ω → ℝ) (c : ℂ) (x : H) :
    P.fcEnergy f (c • x) = ENNReal.ofReal (‖c‖ ^ 2) * P.fcEnergy f x := by
  rw [fcEnergy, fcEnergy, P.scalarMeasure_smul, lintegral_smul_measure, smul_eq_mul]

/-- **Sub-additivity of the energy** (the parallelogram bound `μ_{x+y} ≤ 2μ_x + 2μ_y`):
    `∫ f² dμ_{x+y} ≤ 2∫ f² dμ_x + 2∫ f² dμ_y`. -/
theorem fcEnergy_add_le (f : Ω → ℝ) (x y : H) :
    P.fcEnergy f (x + y) ≤ 2 * P.fcEnergy f x + 2 * P.fcEnergy f y := by
  unfold fcEnergy
  have hpar := P.scalarMeasure_parallelogram_measure x y
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y))
      ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y))
        + ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x - y)) := le_self_add
    _ = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure (x + y) + P.scalarMeasure (x - y)) := by
        rw [lintegral_add_measure]
    _ = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2)
        ∂((2 : ℝ≥0∞) • P.scalarMeasure x + (2 : ℝ≥0∞) • P.scalarMeasure y) := by
        rw [hpar]
    _ = 2 * (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x))
        + 2 * (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure y)) := by
        rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
          smul_eq_mul, smul_eq_mul]

/-- **The domain of `∫ f dE`** — the vectors of finite spectral energy — as a `ℂ`-submodule of `H`.
    `0` has zero energy; energy is sub-additive (parallelogram) and `‖c‖²`-homogeneous, so the
    finite-energy set is closed under `+` and `•`.  This is the natural (dense) domain `D(∫ f dE)` of the
    unbounded self-adjoint operator built in the next increment. -/
noncomputable def fcDomain (f : Ω → ℝ) : Submodule ℂ H where
  carrier := {x | P.fcEnergy f x ≠ ⊤}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at *
    refine ne_top_of_le_ne_top ?_ (P.fcEnergy_add_le f x y)
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (by simp) hx, ENNReal.mul_ne_top (by simp) hy⟩
  smul_mem' := fun c {x} hx => by
    simp only [Set.mem_setOf_eq] at *
    rw [P.fcEnergy_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx

@[simp] theorem mem_fcDomain {f : Ω → ℝ} {x : H} :
    x ∈ P.fcDomain f ↔ P.fcEnergy f x ≠ ⊤ := Iff.rfl

/-- **A bounded symbol has full domain.**  If `|f| ≤ C` then every vector has finite energy
    (`∫ f² dμ_x ≤ C²‖x‖²`), so `x ∈ fcDomain f`.  (This is why `K = ∫ log(r/(2−r)) dE_R` is genuinely
    *unbounded* — its domain is proper precisely because `log` is unbounded, not bounded.) -/
theorem mem_fcDomain_of_bounded {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) (x : H) :
    x ∈ P.fcDomain f := by
  rw [mem_fcDomain]
  have hpt : ∀ ω, ENNReal.ofReal (f ω ^ 2) ≤ ENNReal.ofReal (C ^ 2) := fun ω =>
    ENNReal.ofReal_le_ofReal (by nlinarith [hC ω, abs_nonneg (f ω), sq_abs (f ω)])
  have hbound : P.fcEnergy f x ≤ ENNReal.ofReal (C ^ 2) * P.scalarMeasure x Set.univ := by
    rw [fcEnergy]
    calc ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂(P.scalarMeasure x)
        ≤ ∫⁻ _, ENNReal.ofReal (C ^ 2) ∂(P.scalarMeasure x) := lintegral_mono hpt
      _ = ENNReal.ofReal (C ^ 2) * P.scalarMeasure x Set.univ := by rw [lintegral_const]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (by rw [P.scalarMeasure_univ]; exact ENNReal.ofReal_ne_top)) hbound

/-- **A bounded symbol's FC domain is all of `H`** — the consistency bridge to the bounded functional
    calculus `boundedFC` (where the operator is total). -/
theorem fcDomain_eq_top_of_bounded {f : Ω → ℝ} {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    P.fcDomain f = ⊤ :=
  Submodule.eq_top_iff'.mpr (P.mem_fcDomain_of_bounded hC)

/-- **The FC domain is the `L²(μ_x)` condition.**  For a measurable symbol `f`, a vector `x` lies in the
    domain of `∫ f dE` iff `f` is square-integrable against the scalar spectral measure `μ_x`, i.e.
    `f ∈ L²(μ_x)`.  This is the structural bridge that opens Mathlib's `L²`/integrability machinery
    (Cauchy–Schwarz, `f·g ∈ L¹` for `g ∈ L²`) for the construction of the operator `∫ f dE` on this
    domain (the Riesz representation of `y ↦ ∫ f dμ_{x,y}`). -/
theorem mem_fcDomain_iff_integrable_sq {f : Ω → ℝ} (hf : Measurable f) (x : H) :
    x ∈ P.fcDomain f ↔ Integrable (fun ω => f ω ^ 2) (P.scalarMeasure x) := by
  have hnn : 0 ≤ᵐ[P.scalarMeasure x] (fun ω => f ω ^ 2) :=
    Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  rw [mem_fcDomain, fcEnergy, ← lt_top_iff_ne_top,
    ← MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
  exact ⟨fun h => ⟨(hf.pow_const 2).aestronglyMeasurable, h⟩, fun h => h.2⟩

/-- **On the domain, the symbol itself is integrable** (`f ∈ L¹(μ_x)`).  Since `μ_x` is a *finite*
    measure and `f ∈ L²(μ_x)` on the domain, `L² ⊆ L¹` gives `f ∈ L¹` — so the diagonal expectation
    `⟨x, (∫f dE) x⟩ = ∫ f dμ_x` converges.  (This is the first-law/JLMS expectation value and the
    integrability prerequisite for the operator's matrix elements.) -/
theorem integrable_of_mem_fcDomain {f : Ω → ℝ} (hf : Measurable f) {x : H}
    (hx : x ∈ P.fcDomain f) : Integrable f (P.scalarMeasure x) := by
  have h2 : MemLp f 2 (P.scalarMeasure x) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      ((P.mem_fcDomain_iff_integrable_sq hf x).mp hx)
  exact memLp_one_iff_integrable.mp (h2.mono_exponent (by norm_num))

/-- **A real (`f̄ = f`) bounded symbol gives a self-adjoint operator.**  Via `inner_boundedFC` and the
    symbol-conjugation symmetry `conj B_f(y,x) = B_{f̄}(x,y)` of the polarized form.  This is the symmetry
    seed for the (real) modular Hamiltonian `K`, and the first half of the norm identity
    `‖boundedFC g x‖² = ∫ |g|² dμ_x` underlying the truncation construction of `∫ f dE`. -/
theorem boundedFC_isSelfAdjoint {f : Ω → ℂ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖f ω‖ ≤ C) (hreal : ∀ ω, (starRingEnd ℂ) (f ω) = f ω) :
    IsSelfAdjoint (P.boundedFC hf hC0 hC) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [P.inner_boundedFC hf hC0 hC x y, ← inner_conj_symm, P.inner_boundedFC hf hC0 hC y x,
    P.bilinDiag_conj_symm f x y, show (fun ω => (starRingEnd ℂ) (f ω)) = f from funext hreal]

/-- **The diagonal of the polarized form is the original functional:** `B_g(x,x) = D_g(x) = ∫ g dμ_x`.
    The defining property of the Jordan–von Neumann polarization (mirrors `inner_self` for `‖·‖²`); via
    `diagInt`'s homogeneity `D_g(c·x) = ‖c‖² D_g(x)`.  This is the diagonal expectation `⟨x,(∫g dE)x⟩`. -/
theorem bilinDiag_self (g : Ω → ℂ) (x : H) : P.bilinDiag g x x = P.diagInt g x := by
  have hz : P.diagInt g (x - x) = 0 := by
    rw [sub_self]; simp only [diagInt, P.scalarMeasure_zero, MeasureTheory.integral_zero_measure]
  have h2 : P.diagInt g (x + x) = ((‖(2 : ℂ)‖ ^ 2 : ℝ) : ℂ) * P.diagInt g x := by
    rw [← two_smul ℂ x, P.diagInt_smul]
  have hI1 : P.diagInt g (Complex.I • x + x)
      = ((‖Complex.I + 1‖ ^ 2 : ℝ) : ℂ) * P.diagInt g x := by
    rw [show Complex.I • x + x = (Complex.I + 1) • x by rw [add_smul, one_smul], P.diagInt_smul]
  have hI2 : P.diagInt g (Complex.I • x - x)
      = ((‖Complex.I - 1‖ ^ 2 : ℝ) : ℂ) * P.diagInt g x := by
    rw [show Complex.I • x - x = (Complex.I - 1) • x by rw [sub_smul, one_smul], P.diagInt_smul]
  have key : ∀ z : ℂ, (‖z‖ ^ 2 : ℝ) = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have n2 : (‖(2 : ℂ)‖ ^ 2 : ℝ) = 4 := by
    rw [key]; norm_num
  have nI1 : (‖Complex.I + 1‖ ^ 2 : ℝ) = 2 := by
    rw [key]; norm_num [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
  have nI2 : (‖Complex.I - 1‖ ^ 2 : ℝ) = 2 := by
    rw [key]; norm_num [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
  simp only [bilinDiag, hz, h2, hI1, hI2, n2, nI1, nI2]
  push_cast
  ring

/-- **The diagonal expectation of the operator:** `⟨x, (∫h dE) x⟩ = ∫ h dμ_x`.  Immediate from
    `inner_boundedFC` (`⟨x, boundedFC h y⟩ = B_h(x,y)`) and the polarization diagonal `bilinDiag_self`.
    This is the JLMS first-law expectation value `⟨K⟩` at the bounded level. -/
theorem inner_boundedFC_self {h : Ω → ℂ} (hh : Measurable h) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖h ω‖ ≤ C) (x : H) :
    inner ℂ x (P.boundedFC hh hC0 hC x) = ∫ ω, h ω ∂(P.scalarMeasure x) := by
  rw [P.inner_boundedFC hh hC0 hC x x, P.bilinDiag_self, diagInt]

/-- **The adjoint of `boundedFC g` is `boundedFC ḡ`** (the bounded functional calculus is a `*`-hom):
    `(boundedFC g)† = boundedFC (conj ∘ g)`.  From `inner_boundedFC` + the symbol-conjugation symmetry
    `bilinDiag_conj_symm` and `conj (conj z) = z`.  Combined with `boundedFC_mul` this gives the norm
    identity `‖boundedFC g x‖² = ∫ |g|² dμ_x` driving the truncation construction. -/
theorem boundedFC_adjoint {g : Ω → ℂ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ContinuousLinearMap.adjoint (P.boundedFC hg hC0 hC)
      = P.boundedFC (by fun_prop : Measurable fun ω => (starRingEnd ℂ) (g ω)) hC0
          (fun ω => (Complex.norm_conj (g ω)).le.trans (hC ω)) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [P.inner_boundedFC hg hC0 hC x y, ← inner_conj_symm, P.inner_boundedFC _ _ _ y x,
    P.bilinDiag_conj_symm,
    show (fun ω => (starRingEnd ℂ) ((starRingEnd ℂ) (g ω))) = g from
      funext fun ω => Complex.conj_conj (g ω)]

/-- **`T† T = boundedFC(ḡ·g)`** for `T = boundedFC g`: composing the operator with its adjoint gives the
    FC of `|g|²`.  From `boundedFC_adjoint` + `boundedFC_mul` (the bounded FC is a `*`-algebra hom).  The
    diagonal of this is `‖T x‖² = ∫ |g|² dμ_x` (the norm identity). -/
theorem boundedFC_adjoint_mul_self {g : Ω → ℂ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖g ω‖ ≤ C) :
    ContinuousLinearMap.adjoint (P.boundedFC hg hC0 hC) * P.boundedFC hg hC0 hC
      = P.boundedFC (f := fun ω => (starRingEnd ℂ) (g ω) * g ω) (by fun_prop)
          (mul_nonneg hC0 hC0)
          (fun ω => by rw [norm_mul, Complex.norm_conj]
                       exact mul_le_mul (hC ω) (hC ω) (norm_nonneg _) hC0) := by
  rw [P.boundedFC_adjoint hg hC0 hC,
    ← P.boundedFC_mul (by fun_prop) hC0 (fun ω => (Complex.norm_conj (g ω)).le.trans (hC ω))
      hg hC0 hC (by fun_prop) (mul_nonneg hC0 hC0)
      (fun ω => by rw [norm_mul, Complex.norm_conj]
                   exact mul_le_mul (hC ω) (hC ω) (norm_nonneg _) hC0)]

/-- **The norm identity** `‖boundedFC g x‖² = ∫ |g|² dμ_x` — the diagonal of `T†T = boundedFC(|g|²)`.
    This converts the truncation `L²`-convergence into operator-image Cauchy-ness, defining `∫ f dE`. -/
theorem norm_boundedFC_sq {g : Ω → ℂ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, ‖g ω‖ ≤ C) (x : H) :
    ‖P.boundedFC hg hC0 hC x‖ ^ 2 = ∫ ω, ‖g ω‖ ^ 2 ∂(P.scalarMeasure x) := by
  have hgint : ∀ ω, (starRingEnd ℂ) (g ω) * g ω = ((‖g ω‖ ^ 2 : ℝ) : ℂ) := fun ω => by
    rw [mul_comm, RCLike.mul_conj]; norm_cast
  have hkey : inner ℂ (P.boundedFC hg hC0 hC x) (P.boundedFC hg hC0 hC x)
      = ∫ ω, (starRingEnd ℂ) (g ω) * g ω ∂(P.scalarMeasure x) := by
    rw [show inner ℂ (P.boundedFC hg hC0 hC x) (P.boundedFC hg hC0 hC x)
          = inner ℂ x ((ContinuousLinearMap.adjoint (P.boundedFC hg hC0 hC)
            * P.boundedFC hg hC0 hC) x) by
          rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right],
      P.boundedFC_adjoint_mul_self hg hC0 hC, P.inner_boundedFC_self _ _ _ x]
  have hkey2 : inner ℂ (P.boundedFC hg hC0 hC x) (P.boundedFC hg hC0 hC x)
      = ((∫ ω, ‖g ω‖ ^ 2 ∂(P.scalarMeasure x) : ℝ) : ℂ) := by
    rw [hkey, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hgint)]
    exact integral_ofReal
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hkey2]
  simp

/-- `boundedFC` is symbol-subtractive: `boundedFC(f−g) = boundedFC f − boundedFC g` (from `boundedFC_add`
    via `(f−g)+g = f`). -/
theorem boundedFC_sub {f g : Ω → ℂ} (hf : Measurable f) {Cf : ℝ} (hCf0 : 0 ≤ Cf)
    (hCf : ∀ ω, ‖f ω‖ ≤ Cf) (hg : Measurable g) {Cg : ℝ} (hCg0 : 0 ≤ Cg) (hCg : ∀ ω, ‖g ω‖ ≤ Cg) :
    P.boundedFC (hf.sub hg) (add_nonneg hCf0 hCg0)
        (fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω)))
      = P.boundedFC hf hCf0 hCf - P.boundedFC hg hCg0 hCg := by
  have hadd := P.boundedFC_add (hf.sub hg) hg (add_nonneg hCf0 hCg0) hCg0
    (fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω))) hCg
  rw [P.boundedFC_congr _ _ _ hf hCf0 hCf (by funext ω; ring)] at hadd
  rw [hadd]; abel

/-- **The difference-norm identity** `‖boundedFC g₁ x − boundedFC g₂ x‖² = ∫ |g₁−g₂|² dμ_x` — the concrete
    bound that makes `boundedFC(fₙ)x` a Cauchy sequence (from `boundedFC_sub` + the norm identity). -/
theorem norm_boundedFC_sub_sq {g₁ g₂ : Ω → ℂ} (h₁ : Measurable g₁) {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ ω, ‖g₁ ω‖ ≤ C₁) (h₂ : Measurable g₂) {C₂ : ℝ} (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ ω, ‖g₂ ω‖ ≤ C₂) (x : H) :
    ‖P.boundedFC h₁ hC₁0 hC₁ x - P.boundedFC h₂ hC₂0 hC₂ x‖ ^ 2
      = ∫ ω, ‖g₁ ω - g₂ ω‖ ^ 2 ∂(P.scalarMeasure x) := by
  rw [← ContinuousLinearMap.sub_apply, ← P.boundedFC_sub h₁ hC₁0 hC₁ h₂ hC₂0 hC₂,
    P.norm_boundedFC_sq]

/-! ### Bounded truncations of the symbol (the operator's `L²`-Cauchy engine)

The unbounded operator `∫ f dE` is built as the strong limit `Kx := limₙ boundedFC(fₙ) x` over the bounded
truncations `fₙ = f · 𝟙_{|f|≤n}`.  The key analytic fact, proved here, is that on the domain the truncations
converge to `f` in `L²(μ_x)`: `∫ |f − fₙ|² dμ_x → 0`.  Combined with the norm identity
`‖boundedFC g x‖² = ∫ |g|² dμ_x` (next increment, from `boundedFC_isSelfAdjoint` + `boundedFC_mul`), this makes
`boundedFC(fₙ) x` a Cauchy sequence, whose limit is the operator. -/

/-- The bounded truncation `fₙ = f · 𝟙_{|f| ≤ n}`. -/
noncomputable def fcTrunc (f : Ω → ℝ) (n : ℕ) : Ω → ℝ := {ω | |f ω| ≤ n}.indicator f

theorem fcTrunc_abs_le (f : Ω → ℝ) (n : ℕ) (ω : Ω) : |fcTrunc f n ω| ≤ n := by
  unfold fcTrunc
  by_cases h : ω ∈ {ω | |f ω| ≤ (n : ℝ)}
  · rw [Set.indicator_of_mem h]; exact h
  · rw [Set.indicator_of_notMem h]; simp

theorem fcTrunc_measurable {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) : Measurable (fcTrunc f n) :=
  hf.indicator (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const)

theorem fcTrunc_tendsto (f : Ω → ℝ) (ω : Ω) :
    Filter.Tendsto (fun n => fcTrunc f n ω) Filter.atTop (nhds (f ω)) := by
  have hev : (fun n => fcTrunc f n ω) =ᶠ[Filter.atTop] (fun _ => f ω) := by
    obtain ⟨N, hN⟩ := exists_nat_ge |f ω|
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hmem : ω ∈ {ω | |f ω| ≤ (n : ℝ)} := hN.trans (by exact_mod_cast hn)
    simp only [fcTrunc, Set.indicator_of_mem hmem]
  exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

theorem fcTrunc_sub_sq_le (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    (f ω - fcTrunc f n ω) ^ 2 ≤ (f ω) ^ 2 := by
  unfold fcTrunc
  by_cases h : ω ∈ {ω | |f ω| ≤ (n : ℝ)}
  · rw [Set.indicator_of_mem h]; simp [sq_nonneg]
  · rw [Set.indicator_of_notMem h]; simp

/-- The Cauchy integrand bound `(fₘ − fₙ)² ≤ 2(f − fₘ)² + 2(f − fₙ)²` (the parallelogram-type estimate
    `(b−a)² ≤ 2a² + 2b²`), so the truncation `L²`-convergence controls `‖boundedFC(fₘ)x − boundedFC(fₙ)x‖²`. -/
theorem fcTrunc_diff_sq_le (f : Ω → ℝ) (n m : ℕ) (ω : Ω) :
    (fcTrunc f m ω - fcTrunc f n ω) ^ 2
      ≤ 2 * (f ω - fcTrunc f m ω) ^ 2 + 2 * (f ω - fcTrunc f n ω) ^ 2 := by
  nlinarith [sq_nonneg ((f ω - fcTrunc f m ω) + (f ω - fcTrunc f n ω))]

theorem fcTrunc_abs_le_abs (f : Ω → ℝ) (n : ℕ) (ω : Ω) : |fcTrunc f n ω| ≤ |f ω| := by
  simp only [fcTrunc]
  by_cases h : ω ∈ {ω | |f ω| ≤ (n : ℝ)}
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; simp [abs_nonneg]

/-- **The `L¹` tail-convergence on the domain:** `∫ fcTrunc f n dμ_x → ∫ f dμ_x` (Bochner, real).  Dominated
    convergence (`|fcTrunc f n| ≤ |f| ∈ L¹`, `fcTrunc f n → f` ptwise).  This gives the operator's diagonal
    expectation `⟨x,(∫f dE)x⟩ = ∫ f dμ_x` — the operator-level first law `⟨K⟩ = ∫ kFn dμ`. -/
theorem fcTrunc_integral_tendsto {f : Ω → ℝ} (hf : Measurable f) {x : H} (hx : x ∈ P.fcDomain f) :
    Filter.Tendsto (fun n => ∫ ω, fcTrunc f n ω ∂(P.scalarMeasure x)) Filter.atTop
      (nhds (∫ ω, f ω ∂(P.scalarMeasure x))) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω => |f ω|)
    (fun n => (fcTrunc_measurable hf n).aestronglyMeasurable)
    ((P.integrable_of_mem_fcDomain hf hx).abs)
    (fun n => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact fcTrunc_abs_le_abs f n ω)
    (Filter.Eventually.of_forall fun ω => fcTrunc_tendsto f ω)

/-- **On the domain, the truncations converge to `f` in `L²(μ_x)`:** `∫ |f − fₙ|² dμ_x → 0`.  Dominated
    convergence — the integrand `→ 0` pointwise and is dominated by `f²`, which is `μ_x`-integrable
    exactly because `x` lies in the FC domain. -/
theorem fcTrunc_lintegral_sub_sq_tendsto {f : Ω → ℝ} (hf : Measurable f) {x : H}
    (hx : x ∈ P.fcDomain f) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x))
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, (fun ω => ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2))
      ≤ᵐ[P.scalarMeasure x] (fun ω => ENNReal.ofReal ((f ω) ^ 2)) := fun n =>
    Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_le_ofReal (fcTrunc_sub_sq_le f n ω))
  have hmeas : ∀ n, Measurable (fun ω => ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2)) := fun n =>
    ENNReal.measurable_ofReal.comp ((hf.sub (fcTrunc_measurable hf n)).pow_const 2)
  have hfin : ∫⁻ ω, ENNReal.ofReal ((f ω) ^ 2) ∂(P.scalarMeasure x) ≠ ⊤ := (P.mem_fcDomain).mp hx
  have hlim : ∀ᵐ ω ∂(P.scalarMeasure x),
      Filter.Tendsto (fun n => ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2)) Filter.atTop (nhds 0) := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have : Filter.Tendsto (fun n => (f ω - fcTrunc f n ω) ^ 2) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun n => f ω - fcTrunc f n ω) Filter.atTop (nhds 0) := by
        have := (tendsto_const_nhds (x := f ω)).sub (fcTrunc_tendsto f ω)
        simpa using this
      simpa using h0.pow 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp this
    simpa using this
  have := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (fun ω => ENNReal.ofReal ((f ω) ^ 2)) hmeas hbound hfin hlim
  simpa using this

/-- **The Bochner form** of the truncation `L²`-convergence: `∫ |f − fₙ|² dμ_x → 0` (real integral).
    From the `lintegral` version (`fcTrunc_lintegral_sub_sq_tendsto`) via `∫ g = (∫⁻ ofReal g).toReal`
    (nonnegative integrand) + continuity of `ENNReal.toReal` at `0`. -/
theorem fcTrunc_integral_sub_sq_tendsto {f : Ω → ℝ} (hf : Measurable f) {x : H}
    (hx : x ∈ P.fcDomain f) :
    Filter.Tendsto (fun n => ∫ ω, (f ω - fcTrunc f n ω) ^ 2 ∂(P.scalarMeasure x))
      Filter.atTop (nhds 0) := by
  have heq : ∀ n, ∫ ω, (f ω - fcTrunc f n ω) ^ 2 ∂(P.scalarMeasure x)
      = (∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)).toReal := fun n =>
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      ((hf.sub (fcTrunc_measurable hf n)).pow_const 2).aestronglyMeasurable
  have htoReal : Filter.Tendsto
      (fun n => (∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)).toReal)
      Filter.atTop (nhds (0 : ℝ≥0∞).toReal) :=
    (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (P.fcTrunc_lintegral_sub_sq_tendsto hf hx)
  simp only [ENNReal.toReal_zero] at htoReal
  exact htoReal.congr (fun n => (heq n).symm)

/-- The **`lintegral` Cauchy bound** (ℝ≥0∞, no Bochner `Integrable` — avoids the `whnf` blowup):
    `∫⁻ ofReal((fcTrunc m − fcTrunc n)²) ≤ 2∫⁻ ofReal((f−fcTrunc m)²) + 2∫⁻ ofReal((f−fcTrunc n)²)`.
    The spectral integrals over `scalarMeasure` elaborate cleanly at the `lintegral` level. -/
theorem fcTrunc_diff_lintegral_le {f : Ω → ℝ} (hf : Measurable f) (x : H) (n m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((fcTrunc f m ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)
      ≤ 2 * ∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f m ω) ^ 2) ∂(P.scalarMeasure x)
        + 2 * ∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x) := by
  have hmm : Measurable (fun ω => ENNReal.ofReal ((f ω - fcTrunc f m ω) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hf.sub (fcTrunc_measurable hf m)).pow_const 2)
  have hmn : Measurable (fun ω => ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hf.sub (fcTrunc_measurable hf n)).pow_const 2)
  rw [← MeasureTheory.lintegral_const_mul _ hmm, ← MeasureTheory.lintegral_const_mul _ hmn,
    ← MeasureTheory.lintegral_add_left (hmm.const_mul 2)]
  refine MeasureTheory.lintegral_mono fun ω => ?_
  have heq : (2 : ℝ≥0∞) * ENNReal.ofReal ((f ω - fcTrunc f m ω) ^ 2)
      + 2 * ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2)
      = ENNReal.ofReal (2 * (f ω - fcTrunc f m ω) ^ 2 + 2 * (f ω - fcTrunc f n ω) ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp [ENNReal.ofReal_ofNat]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (fcTrunc_diff_sq_le f n m ω)

/-- **The approximating operator sequence** `uₙ x := boundedFC(fₙ) x` (with `fₙ` the bounded ℂ-truncation
    of `f`).  Its strong limit (once shown Cauchy) is the unbounded operator `∫ f dE` applied to `x`. -/
noncomputable def fcSeq {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) (x : H) : H :=
  P.boundedFC (Complex.continuous_ofReal.measurable.comp (fcTrunc_measurable hf n)) n.cast_nonneg
    (fun ω => (Complex.norm_real (fcTrunc f n ω)).le.trans
      ((Real.norm_eq_abs (fcTrunc f n ω)).le.trans (fcTrunc_abs_le f n ω))) x

/-- The difference-norm of the approximating sequence, as a `lintegral` (ℝ≥0∞, blowup-free):
    `‖uₘ x − uₙ x‖² = (∫⁻ ofReal((fcTrunc m − fcTrunc n)²) dμ_x).toReal`.  From `norm_boundedFC_sub_sq`,
    the real-coercion `‖↑a − ↑b‖² = (a−b)²`, and `∫ g = (∫⁻ ofReal g).toReal`. -/
theorem fcSeq_norm_sub_sq {f : Ω → ℝ} (hf : Measurable f) (x : H) (n m : ℕ) :
    ‖P.fcSeq hf m x - P.fcSeq hf n x‖ ^ 2
      = (∫⁻ ω, ENNReal.ofReal ((fcTrunc f m ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)).toReal := by
  have hpt : ∀ ω, ‖(fcTrunc f m ω : ℂ) - (fcTrunc f n ω : ℂ)‖ ^ 2
      = (fcTrunc f m ω - fcTrunc f n ω) ^ 2 := fun ω => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ‖P.fcSeq hf m x - P.fcSeq hf n x‖ ^ 2
      = ∫ ω, ‖(fcTrunc f m ω : ℂ) - (fcTrunc f n ω : ℂ)‖ ^ 2 ∂(P.scalarMeasure x) := by
        simp only [fcSeq]; exact P.norm_boundedFC_sub_sq _ _ _ _ _ _ x
    _ = ∫ ω, (fcTrunc f m ω - fcTrunc f n ω) ^ 2 ∂(P.scalarMeasure x) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫⁻ ω, ENNReal.ofReal ((fcTrunc f m ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (((fcTrunc_measurable hf m).sub (fcTrunc_measurable hf n)).pow_const 2).aestronglyMeasurable

/-- The **squared-norm Cauchy bound** for the operator sequence (all real, finiteness from the domain):
    `‖fcSeq m x − fcSeq n x‖² ≤ 2·A_m + 2·A_n` where `A_k = ∫(f−fcTrunc k)² dμ_x` (`.toReal` of the lintegral
    tails). -/
theorem fcSeq_norm_sub_sq_le {f : Ω → ℝ} (hf : Measurable f) {x : H} (hx : x ∈ P.fcDomain f) (n m : ℕ) :
    ‖P.fcSeq hf m x - P.fcSeq hf n x‖ ^ 2
      ≤ 2 * (∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f m ω) ^ 2) ∂(P.scalarMeasure x)).toReal
        + 2 * (∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f n ω) ^ 2) ∂(P.scalarMeasure x)).toReal := by
  have hAfin : ∀ k, ∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f k ω) ^ 2) ∂(P.scalarMeasure x) ≠ ⊤ :=
    fun k => ne_top_of_le_ne_top (P.mem_fcDomain.mp hx)
      (MeasureTheory.lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (fcTrunc_sub_sq_le f k ω))
  rw [P.fcSeq_norm_sub_sq]
  refine (ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) (hAfin m),
      ENNReal.mul_ne_top (by simp) (hAfin n)⟩)
    (P.fcTrunc_diff_lintegral_le hf x n m)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (hAfin m))
      (ENNReal.mul_ne_top (by simp) (hAfin n)), ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp [ENNReal.toReal_ofNat]

/-- **The approximating sequence is Cauchy** on the domain: `boundedFC(fₙ)x` is Cauchy in `H`.  From the
    squared-norm bound `‖fcSeq m x − fcSeq n x‖² ≤ 2A_m + 2A_n` and the tail-convergence `A_k → 0`.  Its
    strong limit (next) is the unbounded operator `(∫ f dE) x`. -/
theorem fcSeq_cauchySeq {f : Ω → ℝ} (hf : Measurable f) {x : H} (hx : x ∈ P.fcDomain f) :
    CauchySeq (fun n => P.fcSeq hf n x) := by
  have hA : Filter.Tendsto
      (fun k => (∫⁻ ω, ENNReal.ofReal ((f ω - fcTrunc f k ω) ^ 2) ∂(P.scalarMeasure x)).toReal)
      Filter.atTop (nhds 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (P.fcTrunc_lintegral_sub_sq_tendsto hf hx)
    simpa using this
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at hA
  obtain ⟨N, hN⟩ := hA (ε ^ 2 / 8) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hAm := hN m hm
  have hAn := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hAm hAn
  rw [dist_eq_norm]
  have hsq : ‖P.fcSeq hf m x - P.fcSeq hf n x‖ ^ 2 < ε ^ 2 :=
    (P.fcSeq_norm_sub_sq_le hf hx n m).trans_lt (by nlinarith [hAm, hAn, pow_pos hε 2])
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- **The unbounded operator `∫ f dE` applied to `x`** — the strong limit of the bounded truncations
    `boundedFC(fₙ) x`.  (Defined for all `x` via `limUnder`; meaningful — and the limit is actually attained —
    exactly on the domain `fcDomain f`, where the sequence is Cauchy.) -/
noncomputable def fcOp {f : Ω → ℝ} (hf : Measurable f) (x : H) : H :=
  Filter.limUnder Filter.atTop (fun n => P.fcSeq hf n x)

/-- **The defining property of the operator:** on the domain, `boundedFC(fₙ) x → (∫ f dE) x`. -/
theorem fcSeq_tendsto_fcOp {f : Ω → ℝ} (hf : Measurable f) {x : H} (hx : x ∈ P.fcDomain f) :
    Filter.Tendsto (fun n => P.fcSeq hf n x) Filter.atTop (nhds (P.fcOp hf x)) :=
  (P.fcSeq_cauchySeq hf hx).tendsto_limUnder

/-- **The operator is additive** on the domain: `(∫ f dE)(x+y) = (∫ f dE)x + (∫ f dE)y`.  (Each `boundedFC(fₙ)`
    is linear, and limits respect addition.) -/
theorem fcOp_add {f : Ω → ℝ} (hf : Measurable f) {x y : H} (hx : x ∈ P.fcDomain f)
    (hy : y ∈ P.fcDomain f) (hxy : x + y ∈ P.fcDomain f) :
    P.fcOp hf (x + y) = P.fcOp hf x + P.fcOp hf y := by
  have heq : (fun n => P.fcSeq hf n (x + y)) = fun n => P.fcSeq hf n x + P.fcSeq hf n y := by
    funext n; simp only [fcSeq, map_add]
  exact tendsto_nhds_unique (heq ▸ P.fcSeq_tendsto_fcOp hf hxy)
    ((P.fcSeq_tendsto_fcOp hf hx).add (P.fcSeq_tendsto_fcOp hf hy))

/-- **The operator is `ℂ`-homogeneous** on the domain: `(∫ f dE)(c·x) = c·(∫ f dE)x`. -/
theorem fcOp_smul {f : Ω → ℝ} (hf : Measurable f) (c : ℂ) {x : H} (hx : x ∈ P.fcDomain f)
    (hcx : c • x ∈ P.fcDomain f) :
    P.fcOp hf (c • x) = c • P.fcOp hf x := by
  have heq : (fun n => P.fcSeq hf n (c • x)) = fun n => c • P.fcSeq hf n x := by
    funext n; simp only [fcSeq, map_smul]
  exact tendsto_nhds_unique (heq ▸ P.fcSeq_tendsto_fcOp hf hcx)
    ((P.fcSeq_tendsto_fcOp hf hx).const_smul c)

/-- **The operator is symmetric** on the domain: `⟨(∫ f dE) x, y⟩ = ⟨x, (∫ f dE) y⟩` (`f` real, so each
    `boundedFC(fₙ)` is self-adjoint; pass to the limit by continuity of the inner product).  This is the
    self-adjointness of the (real) functional-calculus operator at the form level — the modular Hamiltonian's
    reality/symmetry. -/
theorem fcOp_symmetric {f : Ω → ℝ} (hf : Measurable f) {x y : H} (hx : x ∈ P.fcDomain f)
    (hy : y ∈ P.fcDomain f) :
    inner ℂ (P.fcOp hf x) y = inner ℂ x (P.fcOp hf y) := by
  have hsa : ∀ n, inner ℂ (P.fcSeq hf n x) y = inner ℂ x (P.fcSeq hf n y) := fun n =>
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (P.boundedFC_isSelfAdjoint (Complex.continuous_ofReal.measurable.comp (fcTrunc_measurable hf n))
        n.cast_nonneg
        (fun ω => (Complex.norm_real (fcTrunc f n ω)).le.trans
          ((Real.norm_eq_abs (fcTrunc f n ω)).le.trans (fcTrunc_abs_le f n ω)))
        (fun ω => Complex.conj_ofReal _))) x y
  have h1 : Filter.Tendsto (fun n => inner ℂ (P.fcSeq hf n x) y) Filter.atTop
      (nhds (inner ℂ (P.fcOp hf x) y)) := (P.fcSeq_tendsto_fcOp hf hx).inner tendsto_const_nhds
  have h2 : Filter.Tendsto (fun n => inner ℂ x (P.fcSeq hf n y)) Filter.atTop
      (nhds (inner ℂ x (P.fcOp hf y))) := tendsto_const_nhds.inner (P.fcSeq_tendsto_fcOp hf hy)
  exact tendsto_nhds_unique ((funext hsa : _ = _) ▸ h1) h2

/-- The exponential symbol `e^{itf}` is bounded by `1` (it is unimodular). -/
theorem norm_expSymbol_le {f : Ω → ℝ} (t : ℝ) (ω : Ω) :
    ‖Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (f ω : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem measurable_expSymbol {f : Ω → ℝ} (hf : Measurable f) (t : ℝ) :
    Measurable (fun ω => Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ))) := by
  fun_prop

/-- **The FC-exponential group law** `∫ e^{i(s+t)f} dE = (∫ e^{isf} dE)·(∫ e^{itf} dE)`:
    `boundedFC(e^{i(s+t)f}) = boundedFC(e^{isf}) · boundedFC(e^{itf})`.  The bounded-operator content of
    `exp(itK)` being a one-parameter group (`K = ∫ f dE`) — from `boundedFC_mul` + `Complex.exp_add`. -/
theorem boundedFC_expSymbol_add {f : Ω → ℝ} (hf : Measurable f) (s t : ℝ) :
    P.boundedFC (measurable_expSymbol hf (s + t)) zero_le_one (norm_expSymbol_le (s + t))
      = P.boundedFC (measurable_expSymbol hf s) zero_le_one (norm_expSymbol_le s)
        * P.boundedFC (measurable_expSymbol hf t) zero_le_one (norm_expSymbol_le t) := by
  have hpm : Measurable (fun ω => Complex.exp (Complex.I * (s : ℂ) * (f ω : ℂ))
      * Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ))) :=
    (measurable_expSymbol hf s).mul (measurable_expSymbol hf t)
  have hpb : ∀ ω, ‖Complex.exp (Complex.I * (s : ℂ) * (f ω : ℂ))
      * Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ))‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    nlinarith [norm_expSymbol_le (f := f) s ω, norm_expSymbol_le (f := f) t ω,
      norm_nonneg (Complex.exp (Complex.I * (s : ℂ) * (f ω : ℂ))),
      norm_nonneg (Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ)))]
  have hsym : (fun ω => Complex.exp (Complex.I * ((s + t : ℝ) : ℂ) * (f ω : ℂ)))
      = fun ω => Complex.exp (Complex.I * (s : ℂ) * (f ω : ℂ))
        * Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ)) := by
    funext ω
    have harg : Complex.I * ((s + t : ℝ) : ℂ) * (f ω : ℂ)
        = Complex.I * (s : ℂ) * (f ω : ℂ) + Complex.I * (t : ℂ) * (f ω : ℂ) := by
      rw [Complex.ofReal_add]; ring
    rw [harg, Complex.exp_add]
  rw [← P.boundedFC_mul (measurable_expSymbol hf s) zero_le_one (norm_expSymbol_le (f := f) s)
    (measurable_expSymbol hf t) zero_le_one (norm_expSymbol_le (f := f) t) hpm zero_le_one hpb]
  exact P.boundedFC_congr (measurable_expSymbol hf (s + t)) zero_le_one
    (norm_expSymbol_le (f := f) (s + t)) hpm zero_le_one hpb hsym

/-- **The FC-exponential is an isometry/unitary** `(∫e^{itf}dE)† (∫e^{itf}dE) = 1`:
    `boundedFC(e^{itf})† · boundedFC(e^{itf}) = 1`.  From `boundedFC_adjoint_mul_self` (`T†T = boundedFC(|g|²)`)
    with `|e^{itf}|² = 1`.  Together with `boundedFC_expSymbol_add` (the group law) this is the full
    bounded-operator content of `exp(itK)` being a one-parameter *unitary* group. -/
theorem boundedFC_expSymbol_adjoint_mul {f : Ω → ℝ} (hf : Measurable f) (t : ℝ) :
    ContinuousLinearMap.adjoint
        (P.boundedFC (measurable_expSymbol hf t) zero_le_one (norm_expSymbol_le t))
      * P.boundedFC (measurable_expSymbol hf t) zero_le_one (norm_expSymbol_le t) = 1 := by
  have hsym : (fun ω => (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ)))
      * Complex.exp (Complex.I * (t : ℂ) * (f ω : ℂ))) = fun _ => (1 : ℂ) := by
    funext ω
    rw [← Complex.exp_conj, ← Complex.exp_add,
      show (starRingEnd ℂ) (Complex.I * (t : ℂ) * (f ω : ℂ)) + Complex.I * (t : ℂ) * (f ω : ℂ) = 0 from by
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring,
      Complex.exp_zero]
  rw [P.boundedFC_adjoint_mul_self (measurable_expSymbol hf t) zero_le_one (norm_expSymbol_le t),
    P.boundedFC_congr _ _ _ measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl) hsym,
    P.boundedFC_const, one_smul]

/-- **Bounded-symbol compatibility:** for a bounded symbol the unbounded FC agrees with the bounded one,
    `(∫ f dE) x = boundedFC(↑f) x`.  (The truncations are eventually `= f`, so the sequence is eventually
    the constant `boundedFC(↑f) x`.)  This ties the unbounded operator back to `boundedFC` — e.g. the
    modular flow `Δ^{it} = boundedFC(((2−r)/r)^{it})` lives in the same calculus as its generator. -/
theorem fcOp_eq_boundedFC {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ω, |f ω| ≤ C) (x : H) :
    P.fcOp hf x = P.boundedFC (Complex.continuous_ofReal.measurable.comp hf) hC0
      (fun ω => (Complex.norm_real (f ω)).le.trans
        ((Real.norm_eq_abs (f ω)).le.trans (hC ω))) x := by
  have hxdom : x ∈ P.fcDomain f := by rw [P.fcDomain_eq_top_of_bounded hC]; exact Submodule.mem_top
  obtain ⟨N, hN⟩ := exists_nat_ge C
  have hev : (fun n => P.fcSeq hf n x) =ᶠ[Filter.atTop] fun _ =>
      P.boundedFC (Complex.continuous_ofReal.measurable.comp hf) hC0
        (fun ω => (Complex.norm_real (f ω)).le.trans
          ((Real.norm_eq_abs (f ω)).le.trans (hC ω))) x := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hsymeq : (fun ω => ((fcTrunc f n ω : ℝ) : ℂ)) = fun ω => ((f ω : ℝ) : ℂ) := by
      funext ω
      have hfeq : fcTrunc f n ω = f ω := by
        simp only [fcTrunc, Set.indicator_of_mem
          (show ω ∈ {ω | |f ω| ≤ (n : ℝ)} from (hC ω).trans (hN.trans (by exact_mod_cast hn)))]
      rw [hfeq]
    simp only [fcSeq]
    exact DFunLike.congr_fun (P.boundedFC_congr _ _ _ _ _ _ hsymeq) x
  exact tendsto_nhds_unique (P.fcSeq_tendsto_fcOp hf hxdom)
    (Filter.Tendsto.congr' hev.symm tendsto_const_nhds)

/-- **The operator's diagonal expectation** (the operator-level first law `⟨K⟩ = ∫ f dμ`):
    `⟨x, (∫ f dE) x⟩ = ∫ f dμ_x` on the domain.  The bounded diagonals `⟨x, boundedFC(fₙ)x⟩ = ∫ fcTrunc f n dμ_x`
    converge (inner continuity + the `L¹` tail-convergence) to `∫ f dμ_x`. -/
theorem fcOp_inner_self {f : Ω → ℝ} (hf : Measurable f) {x : H} (hx : x ∈ P.fcDomain f) :
    inner ℂ x (P.fcOp hf x) = ((∫ ω, f ω ∂(P.scalarMeasure x) : ℝ) : ℂ) := by
  have h2 : (fun n => inner ℂ x (P.fcSeq hf n x))
      = fun n => ((∫ ω, fcTrunc f n ω ∂(P.scalarMeasure x) : ℝ) : ℂ) := by
    funext n; simp only [fcSeq]; rw [P.inner_boundedFC_self _ _ _ x]; exact integral_ofReal
  have h1 : Filter.Tendsto (fun n => inner ℂ x (P.fcSeq hf n x)) Filter.atTop
      (nhds (inner ℂ x (P.fcOp hf x))) := tendsto_const_nhds.inner (P.fcSeq_tendsto_fcOp hf hx)
  rw [h2] at h1
  exact tendsto_nhds_unique h1
    ((Complex.continuous_ofReal.tendsto _).comp (P.fcTrunc_integral_tendsto hf hx))

end QIQTH.Spectral.ProjectionValuedMeasure
