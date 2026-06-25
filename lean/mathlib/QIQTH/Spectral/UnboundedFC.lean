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

end QIQTH.Spectral.ProjectionValuedMeasure
